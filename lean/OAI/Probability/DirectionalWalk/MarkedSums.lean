import OAI.Probability.DirectionalWalk.SumLaws

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

section MarkedSums
variable {G : Type*} [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [AddCommGroup G]

noncomputable def sumKernel (ν : Measure G) : Kernel ℕ G where
  toFun := sumLaw ν
  measurable' := measurable_of_countable _

instance sumKernel_markov (ν : Measure G) [IsProbabilityMeasure ν] : IsMarkovKernel (sumKernel ν) :=
  ⟨fun n => sumLaw_probability ν n⟩

noncomputable def markedSumLaw (ν : Measure G) (θ : Measure ℕ) : Measure (ℕ × G) :=
  θ ⊗ₘ sumKernel ν

instance markedSumLaw_probability (ν : Measure G) [IsProbabilityMeasure ν]
    (θ : Measure ℕ) [IsProbabilityMeasure θ] : IsProbabilityMeasure (markedSumLaw ν θ) :=
  inferInstanceAs (IsProbabilityMeasure (θ ⊗ₘ sumKernel ν))

lemma markedSumLaw_atom (ν : Measure G) [IsProbabilityMeasure ν]
    (θ : Measure ℕ) [IsProbabilityMeasure θ] (n : ℕ) (x : G) :
    markedSumLaw ν θ {(n,x)} = θ {n} * sumLaw ν n {x} := compProd_atom θ (sumKernel ν) (n,x)

lemma markedSumLaw_fst (ν : Measure G) [IsProbabilityMeasure ν]
    (θ : Measure ℕ) [IsProbabilityMeasure θ] : (markedSumLaw ν θ).fst = θ :=
  Measure.fst_compProd θ (sumKernel ν)

lemma markedSumLaw_conv (ν : Measure G) [IsProbabilityMeasure ν]
    (θ η : Measure ℕ) [IsProbabilityMeasure θ] [IsProbabilityMeasure η] :
    (markedSumLaw ν θ).conv (markedSumLaw ν η) = markedSumLaw ν (θ.conv η) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [Measure.lintegral_conv hf]
  change (∫⁻ x, ∫⁻ y, f (x+y) ∂η ⊗ₘ sumKernel ν ∂θ ⊗ₘ sumKernel ν) =
    ∫⁻ x, f x ∂(θ.conv η) ⊗ₘ sumKernel ν
  rw [Measure.lintegral_compProd (measurable_of_countable _),
    Measure.lintegral_compProd hf]
  change (∫⁻ n, ∫⁻ x, ∫⁻ y, f ((n,x)+y) ∂η ⊗ₘ sumKernel ν ∂sumLaw ν n ∂θ) =
    ∫⁻ n, ∫⁻ x, f (n,x) ∂sumLaw ν n ∂θ.conv η
  rw [Measure.lintegral_conv (measurable_of_countable _)]
  apply lintegral_congr
  intro n
  simp_rw [Measure.lintegral_compProd (measurable_of_countable _)]
  rw [lintegral_lintegral_swap (measurable_of_countable _).aemeasurable]
  apply lintegral_congr
  intro m
  change (∫⁻ x, ∫⁻ y, f (n+m,x+y) ∂sumLaw ν m ∂sumLaw ν n) =
    ∫⁻ x, f (n+m,x) ∂sumLaw ν (n+m)
  rw [sumLaw_add,Measure.lintegral_conv (measurable_of_countable _)]

lemma conditionalInfo_markedSum (ν : Measure G) [IsProbabilityMeasure ν]
    (θ : Measure ℕ) [IsProbabilityMeasure θ] :
    conditionalInfo (markedSumLaw ν θ) =ᵐ[markedSumLaw ν θ]
      fun p => atomInfo (sumLaw ν p.1) p.2 := by
  filter_upwards [ae_atom_real_pos (markedSumLaw ν θ)] with p hp
  have hf : 0 < θ.real {p.1} := by
    have hh := atom_le_fst (markedSumLaw ν θ) p
    rw [markedSumLaw_fst] at hh
    exact hp.trans_le (ENNReal.toReal_mono (by finiteness) hh)
  dsimp [conditionalInfo]
  rw [markedSumLaw_fst]
  have hx : (markedSumLaw ν θ).real {p} = θ.real {p.1} * (sumLaw ν p.1).real {p.2} := by
    rw [measureReal_def,show p = (p.1,p.2) from rfl,markedSumLaw_atom,ENNReal.toReal_mul]
    rfl
  rw [hx,mul_div_cancel_left₀ _ hf.ne']
  rfl

lemma markedSumLaw_conditional_entropy (ν : Measure G) [IsProbabilityMeasure ν]
    (θ : Measure ℕ) [IsProbabilityMeasure θ]
    (hi : ∀ n, Integrable (informationOf (sumLaw ν n) id) (sumLaw ν n))
    (hh : Integrable (fun n => entropyOf (sumLaw ν n) id) θ) :
    Integrable (conditionalInfo (markedSumLaw ν θ)) (markedSumLaw ν θ) ∧
      conditionalEntropy (markedSumLaw ν θ) = ∫ n, entropyOf (sumLaw ν n) id ∂θ := by
  have hin (n : ℕ) : Integrable (atomInfo (sumLaw ν n)) (sumLaw ν n) := by
    simpa only [Measure.map_id] using (integrable_informationOf_iff _ id).mp (hi n)
  have ha : Integrable (fun p : ℕ × G => atomInfo (sumLaw ν p.1) p.2) (markedSumLaw ν θ) := by
    apply (Measure.integrable_compProd_iff (measurable_of_countable _).aestronglyMeasurable).mpr
    constructor
    · exact Eventually.of_forall hin
    · change Integrable (fun n => ∫ y, ‖atomInfo (sumLaw ν n) y‖ ∂sumLaw ν n) θ
      simpa only [Real.norm_eq_abs,abs_of_nonneg (atomInfo_nonneg _ _),
        entropyOf_eq_discreteEntropy,Measure.map_id,discreteEntropy] using hh
  refine ⟨ha.congr (conditionalInfo_markedSum ν θ).symm,?_⟩
  change (∫ p, conditionalInfo (markedSumLaw ν θ) p ∂markedSumLaw ν θ) = _
  rw [integral_congr_ae (conditionalInfo_markedSum ν θ)]
  change (∫ p, atomInfo (sumLaw ν p.1) p.2 ∂θ ⊗ₘ sumKernel ν) = _
  rw [Measure.integral_compProd ha]
  change (∫ n, discreteEntropy (sumLaw ν n) ∂θ) = _
  simp only [entropyOf_eq_discreteEntropy,Measure.map_id]
end MarkedSums
section CommonMoments
variable {α : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]

lemma commonBlock_integrable_total (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (hW : Integrable (fun Z => (firstCommonWidth L Z : ℝ)) (twoTapeLaw ν))
    (b : Bool) (D : α → ℝ) (hi : Integrable D (ν b)) :
    Integrable (fun a => listTotal D (a b)) (commonBlockLaw ν L) := by
  rw [commonBlockLaw,integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
    (measurable_firstCommonBlock L).aemeasurable]
  refine ⟨((measurable_of_countable _).comp (measurable_firstCommonBlock L)).aestronglyMeasurable,?_⟩
  apply lt_of_le_of_lt _ ((commonBlock_cost_bound ν L hL he b (fun a => ‖D a‖ₑ)).trans_lt ?_)
  · apply lintegral_mono
    intro Z
    exact enorm_sum_le Finset.univ (fun i => D ((firstCommonBlock L Z b).2 i))
  · apply ENNReal.mul_lt_top
    · have hw := (hasFiniteIntegral_iff_ofReal (Eventually.of_forall
        (fun Z => Nat.cast_nonneg (α := ℝ) (firstCommonWidth L Z)))).mp hW.hasFiniteIntegral
      simpa only [ENNReal.ofReal_natCast] using hw
    · exact hi.hasFiniteIntegral

lemma commonGapLaw_lattice_integrable {q : ℕ}
    (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (hW : Integrable (fun Z => (firstCommonWidth L Z : ℝ)) (twoTapeLaw ν))
    (D : Bool → α → (Fin q → ℤ))
    (hi : ∀ b i, Integrable (fun a => (D b a i : ℝ)) (ν b)) (i : Fin q) :
    Integrable (fun x => |(x i : ℝ)|) (commonGapLaw ν L D) := by
  rw [commonGapLaw,integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
    (measurable_of_countable _).aemeasurable]
  have h0 := commonBlock_integrable_total ν L hL he hW false (fun a => (D false a i : ℝ)) (hi false i)
  have h1 := commonBlock_integrable_total ν L hL he hW true (fun a => (D true a i : ℝ)) (hi true i)
  simpa only [Function.comp_def,pairTotal,listTotal,Pi.add_apply,Finset.sum_apply,Int.cast_add,Int.cast_sum] using (h0.add h1).abs
end CommonMoments

section MarkedEntropy
variable {G : Type*} [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [AddCommGroup G]

lemma markedSumLaw_entropy (ν : Measure G) [IsProbabilityMeasure ν]
    (θ : Measure ℕ) [IsProbabilityMeasure θ]
    (hi : ∀ n, Integrable (informationOf (sumLaw ν n) id) (sumLaw ν n))
    (hθ : Integrable (atomInfo θ) θ)
    (hh : Integrable (fun n => entropyOf (sumLaw ν n) id) θ) :
    Integrable (informationOf (markedSumLaw ν θ) id) (markedSumLaw ν θ) ∧
      entropyOf (markedSumLaw ν θ) id = discreteEntropy θ + ∫ n, entropyOf (sumLaw ν n) id ∂θ := by
  have hc := markedSumLaw_conditional_entropy ν θ hi hh
  have hfst : Integrable (informationOf (markedSumLaw ν θ) Prod.fst) (markedSumLaw ν θ) := by
    rw [integrable_informationOf_iff]
    change Integrable (atomInfo (markedSumLaw ν θ).fst) (markedSumLaw ν θ).fst
    rwa [markedSumLaw_fst]
  have he : conditionedInformation (markedSumLaw ν θ) Prod.snd Prod.fst =ᵐ[markedSumLaw ν θ]
      conditionalInfo (markedSumLaw ν θ) := by
    have h := conditionedInformation_eq (markedSumLaw ν θ) Prod.snd Prod.fst
    simpa only [show (fun p : ℕ × G => (p.1,p.2)) = id from rfl,Measure.map_id] using h
  have hcond : Integrable (conditionedInformation (markedSumLaw ν θ) Prod.snd Prod.fst) (markedSumLaw ν θ) :=
    hc.1.congr he.symm
  constructor
  · change Integrable (informationOf (markedSumLaw ν θ) (fun p => (p.1,p.2))) (markedSumLaw ν θ)
    rw [informationOf_pair_chain]
    exact hfst.add hcond
  · change entropyOf (markedSumLaw ν θ) (fun p => (p.1,p.2)) = _
    rw [entropyOf_pair_chain _ _ _ hfst hcond,entropyOf_eq_discreteEntropy]
    change discreteEntropy (markedSumLaw ν θ).fst + _ = _
    rw [markedSumLaw_fst]
    congr 1
    change (∫ p, conditionedInformation (markedSumLaw ν θ) Prod.snd Prod.fst p ∂markedSumLaw ν θ) = _
    rw [integral_congr_ae he]
    exact hc.2

lemma entropyOf_nonneg {Ω : Type*} [Countable Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    {A : Type*} [Countable A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → A) : 0 ≤ entropyOf μ X :=
  integral_nonneg (informationOf_nonneg μ X)

lemma sum_entropy_integrable_bounded (ν : Measure G) [IsProbabilityMeasure ν]
    (θ : Measure ℕ) [IsProbabilityMeasure θ]
    (hi : ∀ n, Integrable (informationOf (sumLaw ν n) id) (sumLaw ν n))
    (M : ℕ) (hM : ∀ᵐ n ∂θ, n ≤ M) :
    Integrable (fun n => entropyOf (sumLaw ν n) id) θ := by
  apply (integrable_const (entropyOf (sumLaw ν M) id)).mono' (measurable_of_countable _).aestronglyMeasurable
  filter_upwards [hM] with n hn
  rw [Real.norm_eq_abs,abs_of_nonneg (entropyOf_nonneg _ _)]
  exact sumLaw_entropy_monotone ν hi hn

lemma markedSumLaw_entropy_bounds (ν : Measure G) [IsProbabilityMeasure ν]
    (θ : Measure ℕ) [IsProbabilityMeasure θ]
    (hi : ∀ n, Integrable (informationOf (sumLaw ν n) id) (sumLaw ν n))
    (hθ : Integrable (atomInfo θ) θ)
    (m M : ℕ) (hM : ∀ᵐ n ∂θ, m ≤ n ∧ n ≤ M) :
    Integrable (informationOf (markedSumLaw ν θ) id) (markedSumLaw ν θ) ∧
      discreteEntropy θ + entropyOf (sumLaw ν m) id ≤ entropyOf (markedSumLaw ν θ) id ∧
      entropyOf (markedSumLaw ν θ) id ≤ discreteEntropy θ + entropyOf (sumLaw ν M) id := by
  have hb := sum_entropy_integrable_bounded ν θ hi M (hM.mono (fun _ h => h.2))
  have hh := markedSumLaw_entropy ν θ hi hθ hb
  refine ⟨hh.1,?_,?_⟩
  · rw [hh.2]
    apply add_le_add le_rfl
    calc
      _ = ∫ _ : ℕ, entropyOf (sumLaw ν m) id ∂θ := by simp
      _ ≤ _ := integral_mono_ae (integrable_const _) hb (hM.mono (fun _ h => sumLaw_entropy_monotone ν hi h.1))
  · rw [hh.2]
    apply add_le_add le_rfl
    calc
      _ ≤ ∫ _ : ℕ, entropyOf (sumLaw ν M) id ∂θ :=
        integral_mono_ae hb (integrable_const _) (hM.mono (fun _ h => sumLaw_entropy_monotone ν hi h.2))
      _ = _ := by simp
end MarkedEntropy

end DirectionalZeroOne

end OAI
