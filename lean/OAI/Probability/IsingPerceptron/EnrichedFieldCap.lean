import Mathlib
import OAI.Probability.IsingPerceptron.MonomialGgAtMinimum

namespace OAI

/-! Enriched Field Cap. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

variable {I : Type*} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

def finiteLogIntegral (ν : Measure I) (H : I → ℝ) : ℝ := Real.log (∫ x, Real.exp (H x) ∂ν)

omit [Fintype I] [MeasurableSingletonClass I] in
lemma finiteLogIntegral_eq_logMean (ν : Measure I) (H : I → ℝ) :
    finiteLogIntegral ν H = logMean 1 ν H := by simp [finiteLogIntegral,logMean]

lemma measurable_finiteLogIntegral (ν : Measure I) : Measurable (finiteLogIntegral ν) := by
  unfold finiteLogIntegral
  have hm : Measurable (fun p : (I → ℝ) × I => Real.exp (p.1 p.2)) :=
    measurable_from_prod_countable_left (fun i => (measurable_pi_apply i).exp)
  exact hm.stronglyMeasurable.integral_prod_right.measurable.log

lemma finiteLogIntegral_lipschitz (ν : Measure I) [IsProbabilityMeasure ν] (H G : I → ℝ) :
    |finiteLogIntegral ν H-finiteLogIntegral ν G| ≤ ‖H-G‖ := by
  rw [finiteLogIntegral_eq_logMean,finiteLogIntegral_eq_logMean]
  apply logMean_abs_sub_le ν (by norm_num)
    (show Integrable (fun x => Real.exp (1*H x)) ν from Integrable.of_finite)
    (show Integrable (fun x => Real.exp (1*G x)) ν from Integrable.of_finite)
  intro x
  simpa only [Pi.sub_apply,Real.norm_eq_abs] using norm_le_pi_norm (H-G) x

lemma finiteLogIntegral_linearGrowth (ν : Measure I) [IsProbabilityMeasure ν] :
    HasLinearGrowth (finiteLogIntegral ν) := by
  refine ⟨0,1,le_rfl,zero_le_one,fun H => ?_⟩
  simpa only [finiteLogIntegral,Pi.zero_apply,Real.exp_zero,integral_const,probReal_univ,
    one_smul,Real.log_one,sub_zero,one_mul,zero_add] using finiteLogIntegral_lipschitz ν H 0

lemma finiteLogIntegral_add_const (ν : Measure I) [IsProbabilityMeasure ν] (H : I → ℝ) (c : ℝ) :
    finiteLogIntegral ν (fun x => c+H x) = c+finiteLogIntegral ν H := by
  simp_rw [finiteLogIntegral_eq_logMean]
  exact logMean_const_add ν one_ne_zero (by simpa only [one_mul] using
    (Integrable.of_finite : Integrable (fun x => Real.exp (H x)) ν)) c

def energyRecursion (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure (I → ℝ))
    (ν : Measure I) (H : I → ℝ) : ℝ :=
  cascadeRecursion n b μ (fun _ p => p.1+p.2) (finiteLogIntegral ν) H

lemma measurable_energyRecursion (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) :
    Measurable (energyRecursion n b μ ν) :=
  measurable_cascadeRecursion n b μ (fun _ => measurable_fst.add measurable_snd)
    (measurable_finiteLogIntegral ν)

lemma energyRecursion_lipschitz (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ)))
    (hb : ∀ i < n, 0 < b i) (H G : I → ℝ) :
    |energyRecursion n b μ ν H-energyRecursion n b μ ν G| ≤ ‖H-G‖ := by
  simpa only [one_mul,energyRecursion] using cascadeRecursion_lipschitz n b μ hμ
    (measurable_finiteLogIntegral ν) (finiteLogIntegral_linearGrowth ν)
    (L := 1) (fun H G => by simpa only [one_mul] using finiteLogIntegral_lipschitz ν H G) hb H G

lemma energyRecursion_linearGrowth (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ)))
    (hb : ∀ i < n, 0 < b i) : HasLinearGrowth (energyRecursion n b μ ν) :=
  cascadeRecursion_linearGrowth n b μ hμ (measurable_finiteLogIntegral ν)
    (finiteLogIntegral_linearGrowth ν) hb

omit [MeasurableSpace I] [MeasurableSingletonClass I] in

lemma finite_gaussian_exponentialNormMoments [Nonempty I] {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → I → ℝ}
    (hX : Measurable X) (m : I → ℝ) (v : I → ℝ≥0)
    (hlaw : ∀ i, P.map (fun ω => X ω i) = gaussianReal (m i) (v i)) :
    ExponentialNormMoments (P.map X) := by
  intro a
  have hi (i : I) : Integrable (fun ω => Real.exp (|a| * |X ω i|)) P := by
    have hh := gaussianReal_exponentialNormMoments (m i) (v i) (|a|)
    rw [← hlaw i] at hh
    have hm : Measurable (fun ω => X ω i) := (measurable_pi_apply i).comp hX
    simpa only [Function.comp_def,Real.norm_eq_abs] using
      (integrable_map_measure (by fun_prop) hm.aemeasurable).mp hh
  apply (integrable_map_measure (by fun_prop) hX.aemeasurable).mpr
  apply (integrable_finsetSum Finset.univ (fun i _ => hi i)).mono'
  · fun_prop
  · apply ae_of_all
    intro ω
    obtain ⟨i,_,hi⟩ := Finset.exists_max_image Finset.univ (fun i : I => |X ω i|) Finset.univ_nonempty
    have hn : ‖X ω‖ ≤ |X ω i| := (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr
      (fun j => by simpa only [Real.norm_eq_abs] using hi j (Finset.mem_univ _))
    change |Real.exp (a * ‖X ω‖)| ≤ _
    rw [abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (|a| * |X ω i|) := Real.exp_le_exp.mpr
        (le_trans (mul_le_mul_of_nonneg_right (le_abs_self a) (norm_nonneg _))
          (mul_le_mul_of_nonneg_left hn (abs_nonneg a)))
      _ ≤ ∑ j : I, Real.exp (|a| * |X ω j|) :=
        Finset.single_le_sum (f := fun j : I => Real.exp (|a| * |X ω j|)) (fun j _ => (Real.exp_pos _).le) (Finset.mem_univ i)

end IsingPerceptron

namespace IsingPerceptron

theorem variance_of_conditional_center {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {F : A × B → ℝ} {X : A → ℝ} (hF : Measurable F) (hX : MemLp X 2 μ)
    (hi : ∀ a, Integrable (fun b => (F (a,b)-X a)^2) ν)
    (hc : ∀ a, ∫ b, F (a,b) ∂ν = X a) {C : ℝ}
    (hb : ∀ a, (∫ b, (F (a,b)-X a)^2 ∂ν) ≤ C) :
    MemLp F 2 (μ.prod ν) ∧ Var[F; μ.prod ν] ≤ C+Var[X; μ] := by
  let D : A × B → ℝ := fun p => F p-X p.1
  have hd : AEStronglyMeasurable D (μ.prod ν) :=
    hF.aestronglyMeasurable.sub (hX.aestronglyMeasurable.comp_measurePreserving
      (measurePreserving_fst (μ := μ) (ν := ν)))
  have hdi : Integrable (fun p => (D p)^2) (μ.prod ν) := by
    apply (integrable_prod_iff (hd.pow 2)).mpr
    refine ⟨ae_of_all _ hi, ?_⟩
    have hnorm : (fun a => ∫ b, ‖(D (a,b))^2‖ ∂ν) =
        fun a => ∫ b, (D (a,b))^2 ∂ν := by
      ext a
      apply integral_congr_ae
      apply ae_of_all
      intro b
      exact Real.norm_of_nonneg (sq_nonneg _)
    change Integrable (fun a => ∫ b, ‖(D (a,b))^2‖ ∂ν) μ
    rw [hnorm]
    apply Integrable.of_bound (hd.pow 2).integral_prod_right' C
    apply ae_of_all
    intro a
    change ‖∫ b, (D (a,b))^2 ∂ν‖ ≤ C
    rw [Real.norm_of_nonneg (integral_nonneg (fun b => sq_nonneg (D (a,b))))]
    exact hb a
  have hDLp : MemLp D 2 (μ.prod ν) := (memLp_two_iff_integrable_sq hd).mpr hdi
  have hfLp : MemLp F 2 (μ.prod ν) := by
    convert hDLp.add (hX.comp_measurePreserving (measurePreserving_fst (μ := μ) (ν := ν))) using 1
    ext p
    simp [D]
  refine ⟨hfLp, ?_⟩
  have hsecLp (a : A) : MemLp (fun b => F (a,b)) 2 ν := by
    have hdm : Measurable (fun b => F (a,b)-X a) :=
      (hF.comp (measurable_const.prodMk measurable_id)).sub measurable_const
    have hL := (memLp_two_iff_integrable_sq hdm.aestronglyMeasurable).mpr (hi a)
    convert hL.add (memLp_const (X a)) using 1
    ext b
    simp
  have hsec (a : A) : (∫ b, F (a,b)^2 ∂ν) ≤ C+(X a)^2 := by
    have hv := hb a
    have he := variance_eq_integral (hsecLp a).aemeasurable
    rw [hc a] at he
    rw [← he, variance_eq_sub (hsecLp a)] at hv
    simp only [Pi.pow_apply,hc a] at hv
    linarith
  have hh := integral_mono hfLp.integrable_sq.integral_prod_left
    ((integrable_const C).add hX.integrable_sq) hsec
  simp only [Pi.add_apply] at hh
  rw [integral_add (integrable_const _) hX.integrable_sq,integral_const,
    probReal_univ,one_smul] at hh
  rw [variance_eq_sub hfLp,variance_eq_sub hX]
  simp only [Pi.pow_apply]
  rw [integral_prod _ hfLp.integrable_sq,
    integral_prod _ (hfLp.integrable (by norm_num))]
  simp_rw [hc]
  linarith

variable {I : Type} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

def cascadeEnergyLog (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure (I → ℝ))
    (ν : Measure I) (H : I → ℝ) (T : NoiseTree (I → ℝ) n) : ℝ :=
  Real.log ((terminalTreeFactor n b μ (fun _ p => p.1+p.2) (finiteLogIntegral ν) H T).toReal /
    (noiseTreeTotal (I → ℝ) n T).toReal)

lemma measurable_cascadeEnergyLog (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure (I → ℝ))
    (ν : Measure I) : Measurable (fun p : (I → ℝ) × NoiseTree (I → ℝ) n =>
      cascadeEnergyLog n b μ ν p.1 p.2) := by
  have hm := measurable_noiseTreeFactor n b μ
    (fun _ => measurable_finiteLogIntegral ν) (fun _ => measurable_fst.add measurable_snd)
  simp only [noiseTreeFactor_terminal] at hm
  exact hm.ennreal_toReal.div
    (((measurable_noiseTreeTotal (I → ℝ) n).comp measurable_snd).ennreal_toReal) |>.log

theorem cascadeEnergyLog_conditional (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ))) (H : I → ℝ) :
    let P := (noiseCascadeLaw (I → ℝ) n b μ : Measure (NoiseTree (I → ℝ) n))
    Integrable (cascadeEnergyLog n b μ ν H) P ∧
      (∫ T, cascadeEnergyLog n b μ ν H T ∂P) = energyRecursion n b μ ν H ∧
      Integrable (fun T => (cascadeEnergyLog n b μ ν H T-energyRecursion n b μ ν H)^2) P ∧
      (∫ T, (cascadeEnergyLog n b μ ν H T-energyRecursion n b μ ν H)^2 ∂P) ≤
        4*∫ T, (Real.log (rawTreeTotal n T).toReal)^2 ∂(rawCascadeLaw n b : Measure (RawTree n)) := by
  exact (linearGrowth_noiseCascade_recursion n b hb μ hμ
    (measurable_finiteLogIntegral ν) (finiteLogIntegral_linearGrowth ν) H).2

theorem cascadeEnergyLog_variance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ)))
    {H : Ω → I → ℝ} (hH : Measurable H) (hL : MemLp (fun ω => energyRecursion n b μ ν (H ω)) 2 P) :
    MemLp (fun p : Ω × NoiseTree (I → ℝ) n => cascadeEnergyLog n b μ ν (H p.1) p.2) 2
      (P.prod (noiseCascadeLaw (I → ℝ) n b μ : Measure (NoiseTree (I → ℝ) n))) ∧
    Var[(fun p : Ω × NoiseTree (I → ℝ) n => cascadeEnergyLog n b μ ν (H p.1) p.2);
      P.prod (noiseCascadeLaw (I → ℝ) n b μ : Measure (NoiseTree (I → ℝ) n))] ≤
        4*∫ T, (Real.log (rawTreeTotal n T).toReal)^2 ∂(rawCascadeLaw n b : Measure (RawTree n))
          +Var[(fun ω => energyRecursion n b μ ν (H ω)); P] := by
  exact variance_of_conditional_center P _
    ((measurable_cascadeEnergyLog n b μ ν).comp ((hH.comp measurable_fst).prodMk measurable_snd)) hL
    (fun ω => (cascadeEnergyLog_conditional n b hb μ ν hμ (H ω)).2.2.1)
    (fun ω => (cascadeEnergyLog_conditional n b hb μ ν hμ (H ω)).2.1)
    (fun ω => (cascadeEnergyLog_conditional n b hb μ ν hμ (H ω)).2.2.2)

end IsingPerceptron

namespace IsingPerceptron

def tagCoefficients (j : ℕ) (a : ℕ →₀ ℝ) : ℕ →₀ ℝ := Finsupp.mapDomain (Nat.pair j) a

lemma pair_left_injective (j : ℕ) : Function.Injective (Nat.pair j) := by
  intro a b h
  have := congrArg Nat.unpair h
  simpa only [Nat.unpair_pair,Prod.mk.injEq,true_and] using this

lemma tagCoefficients_apply (j : ℕ) (a : ℕ →₀ ℝ) (i : ℕ) :
    tagCoefficients j a (Nat.pair j i) = a i :=
  Finsupp.mapDomain_apply_of_injective (pair_left_injective j) a i

lemma tagCoefficients_other {j k : ℕ} (hjk : j ≠ k) (a : ℕ →₀ ℝ) (i : ℕ) :
    tagCoefficients j a (Nat.pair k i) = 0 := by
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨v,hv⟩
  have := congrArg Nat.unpair hv
  simp only [Nat.unpair_pair,Prod.mk.injEq] at this
  exact hjk this.1

lemma cylinderCross_tag (j k : ℕ) (a b : ℕ →₀ ℝ) :
    cylinderCross (tagCoefficients j a) (tagCoefficients k b) =
      if j = k then cylinderCross a b else 0 := by
  classical
  unfold cylinderCross tagCoefficients
  rw [Finsupp.sum_mapDomain_index_inj (pair_left_injective j)]
  by_cases h : j = k
  · subst k
    simp only [ite_true,Finsupp.mapDomain_apply_of_injective (pair_left_injective j)]
  · simp only [h,ite_false]
    change a.sum (fun i c => c*tagCoefficients k b (Nat.pair j i)) = 0
    simp only [tagCoefficients_other (Ne.symm h),mul_zero]
    simp [Finsupp.sum]

lemma cylinderCross_smul (r t : ℝ) (a b : ℕ →₀ ℝ) :
    cylinderCross (r • a) (t • b) = r*t*cylinderCross a b := by
  unfold cylinderCross
  rw [Finsupp.sum_smul_index (fun _ => zero_mul _)]
  simp only [Finsupp.smul_apply,smul_eq_mul,Finsupp.sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma cylinderCross_sum_right {ι : Type*} (s : Finset ι) (a : ℕ →₀ ℝ) (b : ι → ℕ →₀ ℝ) :
    cylinderCross a (∑ i ∈ s, b i) = ∑ i ∈ s, cylinderCross a (b i) := by
  classical
  simp only [cylinderCross,Finsupp.finsetSum_apply,Finsupp.sum,Finset.mul_sum]
  exact Finset.sum_comm

lemma cylinderCross_tagged_sum {m : ℕ} (a b : Fin m → ℕ →₀ ℝ) :
    cylinderCross (∑ i : Fin m, tagCoefficients i (a i)) (∑ i : Fin m, tagCoefficients i (b i)) =
      ∑ i, cylinderCross (a i) (b i) := by
  classical
  rw [cylinderCross_finset_left]
  apply Finset.sum_congr rfl
  intro i _
  rw [cylinderCross_sum_right]
  simp only [cylinderCross_tag,Fin.val_inj]
  simp

def monomialIndex (j : ℕ) : ℕ × ℕ := Nat.unpair (j+1)

lemma monomialIndex_nonzero (j : ℕ) : monomialIndex j ≠ (0,0) := by
  intro h
  have hp := congrArg (fun z : ℕ × ℕ => Nat.pair z.1 z.2) h
  simp only [monomialIndex,Nat.pair_unpair] at hp
  norm_num [Nat.pair] at hp

lemma monomialIndex_surjective (p d : ℕ) (h : p+d ≥ 1) :
    ∃ j, monomialIndex j = (p,d) := by
  have hn : Nat.pair p d ≠ 0 := by
    intro he
    have : (p,d) = (0,0) := by simpa using congrArg Nat.unpair he
    have hp := congrArg Prod.fst this
    have hd := congrArg Prod.snd this
    omega
  refine ⟨Nat.pair p d-1,?_⟩
  simp only [monomialIndex,Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn),Nat.unpair_pair]

def perturbationScale (N : ℕ) : ℝ := (N : ℝ)^(-1/16 : ℝ)
def perturbationWeight (j : ℕ) : ℝ := (1/2 : ℝ)^(j+1)

def externalFieldCoefficients {N : ℕ} (n : ℕ) (h : ℕ → ℝ)
    (s : Spin N × LabeledLeaf n) : ℕ →₀ ℝ :=
  treeFieldCoefficients n s.2 (fun i => pathAmplitude h i) (fun i => spinValue (s.1 i))

lemma externalFieldCoefficients_variance {N : ℕ} (n : ℕ) {h : ℕ → ℝ}
    (hh : Monotone h) (h0 : 0 ≤ h 0) (s : Spin N × LabeledLeaf n) :
    (externalFieldCoefficients n h s).sum (fun _ c => c^2) = N*h n := by
  rw [← cylinderCross_self,externalFieldCoefficients,treeField_path_cross n _ _ hh h0,
    labeledCommonDepth_self]
  simp only [← pow_two,spinValue_sq,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  ring

def enrichedCoefficients {N : ℕ} (n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ)
    (s : Spin N × LabeledLeaf n) : ℕ →₀ ℝ :=
  ∑ i : Fin (N+1), tagCoefficients i
    (Fin.cases (externalFieldCoefficients n h s)
      (fun j => (Real.sqrt N*perturbationScale N*perturbationWeight j*u j) •
        monomialCoefficients n (monomialIndex j).1 (monomialIndex j).2 s) i)

lemma perturbationWeight_sum (N : ℕ) :
    (∑ j : Fin N, perturbationWeight j) = 1-(1/2 : ℝ)^N := by
  rw [Fin.sum_univ_eq_sum_range]
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,ih]
    simp only [perturbationWeight,pow_succ]
    ring

lemma perturbationWeight_nonneg (j : ℕ) : 0 ≤ perturbationWeight j := by
  exact pow_nonneg (by norm_num) _
lemma perturbationWeight_le_one (j : ℕ) : perturbationWeight j ≤ 1 := by
  exact pow_le_one₀ (by norm_num) (by norm_num)

lemma enrichedCoefficients_variance_le {N : ℕ} (hN : 0 < N) (n : ℕ)
    {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0) (u : Fin N → ℝ)
    (hu : ∀ j, |u j| ≤ 2) (s : Spin N × LabeledLeaf n) :
    (enrichedCoefficients n h u s).sum (fun _ c => c^2) ≤
      N*h n+4*N*(perturbationScale N)^2 := by
  rw [← cylinderCross_self,enrichedCoefficients,cylinderCross_tagged_sum,Fin.sum_univ_succ]
  simp only [Fin.cases_zero,Fin.cases_succ]
  simp_rw [cylinderCross_smul]
  simp_rw [cylinderCross_self]
  rw [externalFieldCoefficients_variance n hh h0]
  apply add_le_add_right
  calc
    _ ≤ ∑ j : Fin N, (4*N*(perturbationScale N)^2)*perturbationWeight j := by
      apply Finset.sum_le_sum
      intro j _
      have hv := monomialCoefficients_variance_le hN n (monomialIndex j).1 (monomialIndex j).2 s
      have hw := perturbationWeight_nonneg j
      have hw1 := perturbationWeight_le_one j
      have hu2 : (u j)^2 ≤ 4 := by
        have hab := abs_le.mp (hu j)
        nlinarith
      have hs : (Real.sqrt N)^2 = (N : ℝ) := Real.sq_sqrt (Nat.cast_nonneg N)
      have ho : (Real.sqrt N*perturbationScale N*perturbationWeight j*u j) *
          (Real.sqrt N*perturbationScale N*perturbationWeight j*u j) =
          N*(perturbationScale N)^2*(perturbationWeight j)^2*(u j)^2 := by
        calc
          _ = (Real.sqrt N)^2*(perturbationScale N)^2*(perturbationWeight j)^2*(u j)^2 := by ring
          _ = _ := by rw [hs]
      rw [ho]
      calc
        _ ≤ N*(perturbationScale N)^2*(perturbationWeight j)^2*(u j)^2 :=
          mul_le_of_le_one_right (by positivity) hv
        _ ≤ N*(perturbationScale N)^2*(perturbationWeight j)^2*4 :=
          mul_le_mul_of_nonneg_left hu2 (by positivity)
        _ ≤ (4*N*(perturbationScale N)^2)*perturbationWeight j := by
          have hww : (perturbationWeight j)^2 ≤ perturbationWeight j := by nlinarith
          nlinarith [mul_le_mul_of_nonneg_left hww (show 0 ≤ 4*N*(perturbationScale N)^2 by positivity)]
    _ = (4*N*(perturbationScale N)^2)*(1-(1/2 : ℝ)^N) := by
      rw [← Finset.mul_sum,perturbationWeight_sum]
    _ ≤ _ := mul_le_of_le_one_right (by positivity) (by linarith [pow_nonneg (show (0 : ℝ) ≤ 1/2 by norm_num) N])

abbrev EnrichedBlock (N : ℕ) := Fin N ⊕ (Σ j : Fin N, Fin (monomialIndex j).1 → Fin N)

def enrichedLevelCoefficient {N : ℕ} (n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ)
    (i : ℕ) (x : Spin N) : EnrichedBlock N → ℝ
  | .inl a => pathAmplitude h i * spinValue (x a)
  | .inr ⟨j,t⟩ => (Real.sqrt N*perturbationScale N*perturbationWeight j*u j) *
      pathAmplitude (monomialPath n (monomialIndex j).2) i *
      tensorFeature (monomialIndex j).1 (spinCoordinate x) t

lemma spinValue_abs (x : Fin 2) : |spinValue x| = 1 := by
  simp only [spinValue]
  split_ifs <;> norm_num

lemma spinCoordinate_abs {N : ℕ} (x : Spin N) (i : Fin N) :
    |spinCoordinate x i| = 1/Real.sqrt N := by
  simp only [spinCoordinate,abs_div,spinValue_abs,abs_of_nonneg (Real.sqrt_nonneg _)]

lemma tensorFeature_spin_abs {N p : ℕ} (x : Spin N) (i : Fin p → Fin N) :
    |tensorFeature p (spinCoordinate x) i| = (1/Real.sqrt N)^p := by
  simp only [tensorFeature,Finset.abs_prod,spinCoordinate_abs,Finset.prod_const,
    Finset.card_univ,Fintype.card_fin]

lemma enrichedLevelCoefficient_abs {N : ℕ} (n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ)
    (i : ℕ) (x y : Spin N) (j : EnrichedBlock N) :
    |enrichedLevelCoefficient n h u i x j| = |enrichedLevelCoefficient n h u i y j| := by
  rcases j with j | ⟨j,t⟩
  · simp only [enrichedLevelCoefficient,abs_mul,spinValue_abs]
  · simp only [enrichedLevelCoefficient,abs_mul,tensorFeature_spin_abs]

lemma sum_scaled_cross {J : Type*} [Fintype J] (c : ℝ) (v w : J → ℝ) :
    (∑ j, (c*v j)*(c*w j)) = c^2*(∑ j, v j*w j) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma enrichedLevelCoefficient_cross {N : ℕ} (hN : 0 < N) (n : ℕ) {h : ℕ → ℝ}
    (hh : Monotone h) (h0 : 0 ≤ h 0) (u : Fin N → ℝ) (i : ℕ) (x y : Spin N) :
    (∑ j : EnrichedBlock N, enrichedLevelCoefficient n h u i x j * enrichedLevelCoefficient n h u i y j) =
      N*pathIncrement h i*spinOverlap x y +
      ∑ j : Fin N, (Real.sqrt N*perturbationScale N*perturbationWeight j*u j)^2 *
        pathIncrement (monomialPath n (monomialIndex j).2) i * (spinOverlap x y)^(monomialIndex j).1 := by
  classical
  rw [Fintype.sum_sum_type,Fintype.sum_sigma]
  simp only [enrichedLevelCoefficient]
  rw [sum_scaled_cross,pathAmplitude_sq hh h0]
  have he : (∑ j : Fin N, spinValue (x j)*spinValue (y j)) = N*spinOverlap x y := by
    rw [spinOverlap,mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hN.ne')]
  rw [he]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro j _
    rw [sum_scaled_cross,tensorFeature_cross,spinCoordinate_cross,mul_pow,
      pathAmplitude_sq (monomialPath_monotone n _) (monomialPath_nonneg n _ 0)]

lemma enrichedLevelCoefficient_variance {N : ℕ} (hN : 0 < N) (n : ℕ) {h : ℕ → ℝ}
    (hh : Monotone h) (h0 : 0 ≤ h 0) (u : Fin N → ℝ) (i : ℕ) (x : Spin N) :
    (∑ j : EnrichedBlock N, (enrichedLevelCoefficient n h u i x j)^2) =
      N*pathIncrement h i +
      ∑ j : Fin N, (Real.sqrt N*perturbationScale N*perturbationWeight j*u j)^2 *
        pathIncrement (monomialPath n (monomialIndex j).2) i := by
  simpa only [← pow_two,spinOverlap_self hN,one_pow,mul_one] using
    enrichedLevelCoefficient_cross hN n hh h0 u i x x

lemma enrichedRoot_envelope_sq {N : ℕ} (hN : 0 < N) (n : ℕ) {h : ℕ → ℝ}
    (hh : Monotone h) (h0 : 0 ≤ h 0) (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2) (x : Spin N) :
    (∑ j : EnrichedBlock N, |enrichedLevelCoefficient n h u 0 x j|^2) ≤ N*h 0+4*N*(perturbationScale N)^2 := by
  simp only [sq_abs,enrichedLevelCoefficient_variance hN n hh h0 u 0 x,pathIncrement]
  apply add_le_add_right
  calc
    _ ≤ ∑ j : Fin N, (4*N*(perturbationScale N)^2)*perturbationWeight j := by
      apply Finset.sum_le_sum
      intro j _
      have hv : monomialPath n (monomialIndex j).2 0 ≤ 1 :=
        (monomialPath_monotone n (monomialIndex j).2 (Nat.zero_le n)).trans
          (monomialPath_diag_le_one n (monomialIndex j).2)
      have hw := perturbationWeight_nonneg j
      have hw1 := perturbationWeight_le_one j
      have hu2 : (u j)^2 ≤ 4 := by
        have hab := abs_le.mp (hu j)
        nlinarith
      have he : (Real.sqrt N*perturbationScale N*perturbationWeight j*u j)^2 =
          N*(perturbationScale N)^2*(perturbationWeight j)^2*(u j)^2 := by
        simp only [mul_pow,Real.sq_sqrt (Nat.cast_nonneg N)]
      rw [he]
      calc
        _ ≤ N*(perturbationScale N)^2*(perturbationWeight j)^2*(u j)^2 :=
          mul_le_of_le_one_right (by positivity) hv
        _ ≤ N*(perturbationScale N)^2*(perturbationWeight j)^2*4 :=
          mul_le_mul_of_nonneg_left hu2 (by positivity)
        _ ≤ (4*N*(perturbationScale N)^2)*perturbationWeight j := by
          have hww : (perturbationWeight j)^2 ≤ perturbationWeight j := by nlinarith
          nlinarith [mul_le_mul_of_nonneg_left hww (show 0 ≤ 4*N*(perturbationScale N)^2 by positivity)]
    _ = (4*N*(perturbationScale N)^2)*(1-(1/2 : ℝ)^N) := by
      rw [← Finset.mul_sum,perturbationWeight_sum]
    _ ≤ _ := mul_le_of_le_one_right (by positivity)
      (by linarith [pow_nonneg (show (0 : ℝ) ≤ 1/2 by norm_num) N])

lemma variance_le_square_about_const {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {F : Ω → ℝ} (hF : MemLp F 2 μ) (a : ℝ) :
    Var[F; μ] ≤ ∫ x, (F x-a)^2 ∂μ := by
  have hs := variance_eq_sub (hF.sub (memLp_const a))
  simp only [Pi.sub_apply, Pi.pow_apply] at hs
  change Var[fun x => F x-a; μ] = _ at hs
  rw [variance_sub_const hF.aestronglyMeasurable a] at hs
  linarith [sq_nonneg (∫ x, F x-a ∂μ)]

lemma gaussian_coord_memLp {n : ℕ} {F : (Fin n → ℝ) → ℝ} {c : Fin n → ℝ}
    (hm : Measurable F)
    (hl : ∀ x y, |F x-F y| ≤ ∑ i, c i*|x i-y i|) (p : ℝ≥0) :
    MemLp F p (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  have hcoord (i : Fin n) : MemLp (fun x : Fin n → ℝ => c i*|x i|) p
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
    have h := (memLp_id_gaussianReal p).comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i)
    simpa only [Function.comp_def, id_eq, Pi.abs_apply] using h.abs.const_mul (c i)
  have hb := (memLp_const |F 0|).add (memLp_finsetSum Finset.univ (fun i _ => hcoord i))
  apply hb.mono' hm.aestronglyMeasurable
  refine Eventually.of_forall fun x => ?_
  have hx := hl x 0
  simp only [Pi.zero_apply, sub_zero] at hx
  simp only [Pi.add_apply, Real.norm_eq_abs]
  linarith [abs_sub_abs_le_abs_sub (F x) (F 0)]

lemma gaussian_variance_of_slope {F : ℝ → ℝ} (hm : Measurable F) {c : ℝ}
    (hl : ∀ x y, |F x-F y| ≤ c*|x-y|) : Var[F; gaussianReal 0 1] ≤ c^2 := by
  have hLp : MemLp F 2 (gaussianReal 0 1) := by
    apply ((memLp_const |F 0|).add ((memLp_id_gaussianReal 2).abs.const_mul c)).mono'
      hm.aestronglyMeasurable
    refine Eventually.of_forall fun x => ?_
    have hx := hl x 0
    simp only [sub_zero] at hx
    simp only [Real.norm_eq_abs, Pi.add_apply, Pi.abs_apply, id_eq]
    linarith [abs_sub_abs_le_abs_sub (F x) (F 0)]
  have hsq : (∫ x : ℝ, x^2 ∂gaussianReal 0 1) = 1 := by
    have h := variance_eq_sub (memLp_id_gaussianReal (μ := 0) (v := 1) 2)
    simpa only [variance_id_gaussianReal, NNReal.coe_one, integral_id_gaussianReal,
      sq, mul_zero, sub_zero, Pi.pow_apply, id_eq] using h.symm
  calc
    _ ≤ ∫ x, (F x-F 0)^2 ∂gaussianReal 0 1 := variance_le_square_about_const hLp _
    _ ≤ ∫ x : ℝ, c^2*x^2 ∂gaussianReal 0 1 := by
      apply integral_mono (hLp.sub (memLp_const _)).integrable_sq
        ((memLp_id_gaussianReal 2).integrable_sq.const_mul _)
      intro x
      have hx := hl x 0
      simp only [sub_zero] at hx
      have hh := pow_le_pow_left₀ (abs_nonneg (F x-F 0)) hx 2
      simpa only [sq_abs, mul_pow, Pi.sub_apply, id_eq] using hh
    _ = c^2 := by rw [integral_const_mul, hsq, mul_one]

lemma gaussian_slope_memLp {F : ℝ → ℝ} (hm : Measurable F) {c : ℝ}
    (hl : ∀ x y, |F x-F y| ≤ c*|x-y|) (p : ℝ≥0) :
    MemLp F p (gaussianReal 0 1) := by
  apply ((memLp_const |F 0|).add ((memLp_id_gaussianReal p).abs.const_mul c)).mono'
    hm.aestronglyMeasurable
  refine Eventually.of_forall fun x => ?_
  have hx := hl x 0
  simp only [sub_zero] at hx
  simp only [Real.norm_eq_abs, Pi.add_apply, Pi.abs_apply, id_eq]
  linarith [abs_sub_abs_le_abs_sub (F x) (F 0)]

lemma variance_prod_le_fiber {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {F : A × B → ℝ} (hLp : MemLp F 2 (μ.prod ν))
    (hsecLp : ∀ b, MemLp (fun a => F (a,b)) 2 μ)
    (hGLp : MemLp (fun b => ∫ a, F (a,b) ∂μ) 2 ν) {C : ℝ}
    (hvar : ∀ b, Var[fun a => F (a,b); μ] ≤ C) :
    Var[F; μ.prod ν] ≤ C + Var[fun b => ∫ a, F (a,b) ∂μ; ν] := by
  have hsec : ∀ b, (∫ a, F (a,b)^2 ∂μ) ≤ C + (∫ a, F (a,b) ∂μ)^2 := by
    intro b
    have h := hvar b
    rw [variance_eq_sub (hsecLp b)] at h
    simp only [Pi.pow_apply] at h
    linarith
  have hs := integral_mono hLp.integrable_sq.integral_prod_right
    ((integrable_const C).add hGLp.integrable_sq) hsec
  simp only [Pi.add_apply] at hs
  rw [integral_add (integrable_const _) hGLp.integrable_sq, integral_const,
    probReal_univ, one_smul] at hs
  rw [variance_eq_sub hLp, variance_eq_sub hGLp]
  simp only [Pi.pow_apply]
  rw [integral_prod_symm _ hLp.integrable_sq,
    integral_prod_symm _ (hLp.integrable (by norm_num))]
  linarith

theorem gaussian_variance_coordinate_bound (n : ℕ) {F : (Fin n → ℝ) → ℝ}
    (hm : Measurable F) {c : Fin n → ℝ}
    (hl : ∀ x y, |F x-F y| ≤ ∑ i, c i*|x i-y i|) :
    Var[F; Measure.pi (fun _ : Fin n => gaussianReal 0 1)] ≤ ∑ i, (c i)^2 := by
  induction n with
  | zero =>
    have hF : F = fun _ => F (fun i : Fin 0 => i.elim0) := by
      funext x
      congr 1
      funext i
      exact i.elim0
    rw [hF, variance_eq_integral measurable_const.aemeasurable]
    simp
  | succ n ih =>
    let μ := gaussianReal (0 : ℝ) (1 : ℝ≥0)
    let ν := Measure.pi (fun _ : Fin n => μ)
    have hcons : Measurable (fun z : ℝ × (Fin n → ℝ) => (Fin.cons z.1 z.2 : Fin (n+1) → ℝ)) := by
      apply Measurable.of_eval
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [Fin.cons_zero] using
          (measurable_fst : Measurable (Prod.fst : ℝ × (Fin n → ℝ) → ℝ))
      · simpa only [Fin.cons_succ, Function.comp_def] using (measurable_pi_apply j).comp
          (measurable_snd : Measurable (Prod.snd : ℝ × (Fin n → ℝ) → (Fin n → ℝ)))
    have hFm : Measurable (fun z : ℝ × (Fin n → ℝ) => F (Fin.cons z.1 z.2)) := hm.comp hcons
    have hsm (x : Fin n → ℝ) : Measurable (fun a => F (Fin.cons a x)) :=
      hFm.comp (measurable_id.prodMk measurable_const)
    have hsl (x : Fin n → ℝ) : ∀ a b,
        |F (Fin.cons a x)-F (Fin.cons b x)| ≤ c 0*|a-b| := by
      intro a b
      simpa only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
        sub_self, abs_zero, mul_zero, Finset.sum_const_zero, add_zero] using
        hl (Fin.cons a x) (Fin.cons b x)
    have hsi (x : Fin n → ℝ) : Integrable (fun a => F (Fin.cons a x)) μ :=
      (gaussian_slope_memLp (hsm x) (hsl x) 1).integrable (by norm_num)
    have hGm : Measurable (fun x => ∫ a, F (Fin.cons a x) ∂μ) :=
      hFm.stronglyMeasurable.integral_prod_left'.measurable
    have hGl : ∀ x y, |(∫ a, F (Fin.cons a x) ∂μ)-(∫ a, F (Fin.cons a y) ∂μ)| ≤
        ∑ i : Fin n, c i.succ*|x i-y i| := by
      intro x y
      rw [← integral_sub (hsi x) (hsi y)]
      have hB (a : ℝ) : |F (Fin.cons a x)-F (Fin.cons a y)| ≤
          ∑ i : Fin n, c i.succ*|x i-y i| := by
        simpa only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
          sub_self, abs_zero, mul_zero, zero_add] using hl (Fin.cons a x) (Fin.cons a y)
      simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
        (norm_integral_le_of_norm_le_const (μ := μ)
          (f := fun a => F (Fin.cons a x)-F (Fin.cons a y))
          (Eventually.of_forall (fun a => by simpa only [Real.norm_eq_abs] using hB a)))
    have hGLp := gaussian_coord_memLp hGm hGl 2
    have hpres := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) 0).symm
    have hLp : MemLp (fun z : ℝ × (Fin n → ℝ) => F (Fin.cons z.1 z.2)) 2 (μ.prod ν) := by
      have h := (gaussian_coord_memLp hm hl 2).comp_measurePreserving hpres
      simpa only [Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.zero_succAbove,
        cast_eq, ENNReal.coe_ofNat, ν] using h
    have hprod := variance_prod_le_fiber hLp
      (fun x => gaussian_slope_memLp (hsm x) (hsl x) 2) hGLp
      (fun x => gaussian_variance_of_slope (hsm x) (hsl x))
    have heq : Var[fun z : ℝ × (Fin n → ℝ) => F (Fin.cons z.1 z.2); μ.prod ν] =
        Var[F; Measure.pi (fun _ : Fin (n+1) => μ)] := by
      have h := hpres.variance_fun_comp hm.aemeasurable
      simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.zero_succAbove, cast_eq] using h
    rw [heq] at hprod
    have ht := ih hGm hGl
    rw [Fin.sum_univ_succ]
    change _ ≤ c 0 ^ 2 + Var[(fun b => ∫ a, F (Fin.cons a b) ∂μ); ν] at hprod
    dsimp only [ν, μ] at hprod ht ⊢
    linarith

end IsingPerceptron

end

end OAI
