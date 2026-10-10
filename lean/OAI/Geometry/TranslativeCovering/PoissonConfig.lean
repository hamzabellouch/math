import OAI.Geometry.TranslativeCovering.SphericalLaw

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9

namespace PoissonConfig

variable {Ω : Type u_1} [MeasurableSpace Ω]

abbrev Config (Ω : Type u_2) := Σ n : ℕ, {f : Fin n → Ω // Function.Injective f}

noncomputable def count (E : Set Ω) (x : Config Ω) : ℕ :=
  (Finset.univ.filter (fun i => x.2.val i ∈ E)).card

lemma measurableSet_sigma {β : ℕ → Type u_3} [∀ n, MeasurableSpace (β n)]
    {s : Set (Σ n, β n)} (h : ∀ n, MeasurableSet (Sigma.mk n ⁻¹' s)) :
    MeasurableSet s := by
  exact MeasurableSpace.measurableSet_iInf.mpr h

lemma measurable_sigma {β : ℕ → Type u_4} [∀ n, MeasurableSpace (β n)]
    {Γ : Type u_5} [MeasurableSpace Γ] {f : (Σ n, β n) → Γ}
    (h : ∀ n, Measurable (f ∘ Sigma.mk n)) : Measurable f := by
  intro s hs
  apply measurableSet_sigma
  intro n
  exact h n hs

lemma measurable_count {E : Set Ω} (hE : MeasurableSet E) :
    Measurable (count E) := by
  apply measurable_sigma
  intro n
  change Measurable (fun x : {f : Fin n → Ω // Function.Injective f} =>
    (Finset.univ.filter (fun i => x.val i ∈ E)).card)
  simp_rw [Finset.card_filter]
  apply Finset.measurable_sum
  intro i _
  apply Measurable.ite _ measurable_const measurable_const
  exact hE.preimage ((measurable_pi_apply i).comp measurable_subtype_coe)

noncomputable def witnessCount {I : Type u_6} [Fintype I] (E : I → Set Ω)
    (x : Config Ω) : ℕ :=
  (Finset.univ.filter (fun f : I ↪ Fin x.1 => ∀ i, x.2.val (f i) ∈ E i)).card

lemma measurable_witnessCount {I : Type u_7} [Fintype I] (E : I → Set Ω)
    (hE : ∀ i, MeasurableSet (E i)) : Measurable (witnessCount E) := by
  apply measurable_sigma
  intro n
  change Measurable (fun x : {f : Fin n → Ω // Function.Injective f} =>
    (Finset.univ.filter (fun f : I ↪ Fin n => ∀ i, x.val (f i) ∈ E i)).card)
  simp_rw [Finset.card_filter]
  apply Finset.measurable_sum
  intro f _
  apply Measurable.ite _ measurable_const measurable_const
  simp only [ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  exact (hE i).preimage ((measurable_pi_apply (f i)).comp measurable_subtype_coe)

structure IsPoisson (μ : Measure Ω) [IsFiniteMeasure μ] (P : Measure (Config Ω)) : Prop where
  law : ∀ E : Set Ω, MeasurableSet E →
    HasLaw (count E) (poissonMeasure (μ E).toNNReal) P
  independent : ∀ {n : ℕ} (E : Fin n → Set Ω),
    (∀ c, MeasurableSet (E c)) → Pairwise (fun c d => Disjoint (E c) (E d)) →
    iIndepFun (fun c => count (E c)) P

noncomputable def occupied (E : Set Ω) (x : Config Ω) : Bool :=
  decide (0 < count E x)

lemma measurable_occupied {E : Set Ω} (hE : MeasurableSet E) :
    Measurable (occupied E) := by
  exact (measurable_of_countable (fun k : ℕ => decide (0 < k))).comp (measurable_count hE)

lemma occupied_independent {μ : Measure Ω} [IsFiniteMeasure μ]
    {P : Measure (Config Ω)} (hP : IsPoisson μ P) {C : Type u_8} [Fintype C]
    (E : C → Set Ω) (hE : ∀ c, MeasurableSet (E c))
    (hd : Pairwise (fun c d => Disjoint (E c) (E d))) :
    iIndepFun (fun c => occupied (E c)) P := by
  have hind : iIndepFun (fun c => count (E c)) P := by
    let e := (Fintype.equivFin C).symm
    apply iIndepFun.of_precomp e.surjective
    apply hP.independent (fun i => E (e i)) (fun i => hE (e i))
    intro i j hij
    exact hd (fun h => hij (e.injective h))
  exact hind.comp (fun _ k => decide (0 < k))
    (fun _ => measurable_of_countable _)

lemma count_zero_prob {μ : Measure Ω} [IsFiniteMeasure μ]
    {P : Measure (Config Ω)} (hP : IsPoisson μ P) {E : Set Ω} (hE : MeasurableSet E) :
    P.real {x | count E x = 0} = Real.exp (-μ.real E) := by
  have h := (hP.law E hE).measureReal_eq (p := fun k => k = 0) (measurableSet_singleton _)
  change P.real {x | count E x = 0} = (poissonMeasure (μ E).toNNReal).real {0} at h
  rw [poissonMeasure_real_singleton] at h
  change P.real {x | count E x = 0} = Real.exp (- ((μ E).toNNReal : ℝ))
  simpa only [pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one] using h

lemma occupied_prob {μ : Measure Ω} [IsFiniteMeasure μ]
    {P : Measure (Config Ω)} [IsProbabilityMeasure P] (hP : IsPoisson μ P)
    {E : Set Ω} (hE : MeasurableSet E) :
    P.real {x | occupied E x = true} = 1 - Real.exp (-μ.real E) := by
  have he : {x | occupied E x = true} = {x | count E x = 0}ᶜ := by
    ext x
    simp only [mem_ofPred_eq, occupied, decide_eq_true_eq, mem_compl_iff, Nat.pos_iff_ne_zero]
  have hm : MeasurableSet {x | count E x = 0} :=
    (measurable_count hE) (measurableSet_singleton 0)
  rw [he, probReal_compl_eq_one_sub hm, count_zero_prob hP hE]

structure HasVoidLaw (μ : Measure Ω) (P : Measure (Config Ω)) : Prop where
  void : ∀ E, MeasurableSet E → P {x | count E x = 0} =
    ENNReal.ofReal (Real.exp (-μ.real E))

omit [MeasurableSpace Ω] in
lemma count_zero_iff (E : Set Ω) (x : Config Ω) :
    count E x = 0 ↔ ∀ i, x.2.val i ∉ E := by
  simp [count, Finset.card_eq_zero, Finset.filter_eq_empty_iff]

lemma occupied_independent_of_void {μ : Measure Ω} [IsFiniteMeasure μ]
    {P : Measure (Config Ω)} [IsProbabilityMeasure P] (hP : HasVoidLaw μ P)
    {C : Type u_9} [Fintype C] (E : C → Set Ω) (hE : ∀ c, MeasurableSet (E c))
    (hd : Pairwise (fun c d => Disjoint (E c) (E d))) :
    iIndepFun (fun c => occupied (E c)) P := by
  let Z (c : C) := {x : Config Ω | count (E c) x = 0}
  have hZ (c : C) : MeasurableSet (Z c) :=
    (measurable_count (hE c)) (measurableSet_singleton 0)
  have hz : iIndepSet Z P := by
    apply (iIndepSet_iff_meas_biInter hZ).mpr
    intro s
    have he : (⋂ c ∈ s, Z c) = {x | count (⋃ c ∈ s, E c) x = 0} := by
      ext x
      simp only [mem_iInter, Z, mem_ofPred_eq, count_zero_iff, mem_iUnion, not_exists]
      aesop
    rw [he, hP.void _ (Finset.measurableSet_biUnion s (fun c _ => hE c)),
      measureReal_biUnion_finset (fun c _ d _ hcd => hd hcd) (fun c _ => hE c),
      ← Finset.sum_neg_distrib, Real.exp_sum, ENNReal.ofReal_prod_of_nonneg
        (fun _ _ => (Real.exp_pos _).le)]
    exact Finset.prod_congr rfl (fun c _ => (hP.void (E c) (hE c)).symm)
  have hi := (hz.iIndepFun_indicator (β := ℕ)).comp
    (fun _ k => decide (k = 0)) (fun _ => measurable_of_countable _)
  convert! hi using 1
  funext c x
  by_cases hx : count (E c) x = 0 <;>
    simp [occupied, Z, hx, Nat.pos_iff_ne_zero]

lemma occupied_prob_of_void {μ : Measure Ω} {P : Measure (Config Ω)}
    [IsProbabilityMeasure P] (hP : HasVoidLaw μ P) {E : Set Ω} (hE : MeasurableSet E) :
    P.real {x | occupied E x = true} = 1 - Real.exp (-μ.real E) := by
  have he : {x | occupied E x = true} = {x | count E x = 0}ᶜ := by
    ext x
    simp only [mem_ofPred_eq, occupied, decide_eq_true_eq, mem_compl_iff, Nat.pos_iff_ne_zero]
  have hm : MeasurableSet {x | count E x = 0} :=
    (measurable_count hE) (measurableSet_singleton 0)
  rw [he, probReal_compl_eq_one_sub hm]
  rw [measureReal_def, hP.void E hE, ENNReal.toReal_ofReal (Real.exp_pos _).le]

lemma IsPoisson.hasVoidLaw {μ : Measure Ω} [IsFiniteMeasure μ]
    {P : Measure (Config Ω)} [IsProbabilityMeasure P] (hP : IsPoisson μ P) :
    HasVoidLaw μ P := by
  constructor
  intro E hE
  rw [← ENNReal.ofReal_toReal (measure_ne_top P _)]
  exact congrArg ENNReal.ofReal (count_zero_prob hP hE)

end PoissonConfig

end OAI
