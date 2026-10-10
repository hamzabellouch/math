import Mathlib

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12
universe u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

namespace Problem336AdditiveD139.Noise

theorem indepFun_vectors_of_independent_pairs
    {I : Type u_1} {Ω : Type u_2} {A : Type u_3} {B : Type u_4} [Fintype I] [MeasurableSpace Ω]
    [MeasurableSpace A] [MeasurableSpace B]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {X : I → Ω → A} {Y : I → Ω → B}
    (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    (hpair : iIndepFun (fun i ω => (X i ω, Y i ω)) P)
    (hxy : ∀ i, IndepFun (X i) (Y i) P) :
    IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) P := by
  have hXi : iIndepFun X P := hpair.comp (fun _ => Prod.fst) (by fun_prop)
  have hYi : iIndepFun Y P := hpair.comp (fun _ => Prod.snd) (by fun_prop)
  apply (indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)).2
  have hsplit :
      (fun ω => (fun i => X i ω, fun i => Y i ω)) =
      (MeasurableEquiv.arrowProdEquivProdArrow A B I) ∘
        (fun ω i => (X i ω, Y i ω)) := rfl
  rw [hsplit, ← Measure.map_map (by fun_prop) (by fun_prop)]
  rw [hpair.map_fun_eq_pi_map (fun i => (hX i).prodMk (hY i) |>.aemeasurable)]
  simp_rw [fun i => (hxy i).map_prod_eq_prod_map_map
    (hX i).aemeasurable (hY i).aemeasurable]
  have : ∀ i, IsProbabilityMeasure (P.map (X i)) :=
    fun _ => inferInstance
  have : ∀ i, IsProbabilityMeasure (P.map (Y i)) :=
    fun _ => inferInstance
  rw [(measurePreserving_arrowProdEquivProdArrow A B I
    (fun i => P.map (X i)) (fun i => P.map (Y i))).map_eq]
  rw [hXi.map_fun_eq_pi_map (fun i => (hX i).aemeasurable),
    hYi.map_fun_eq_pi_map (fun i => (hY i).aemeasurable)]

theorem indepFun_families_of_independent_pairs
    {I : Type u_5} {Ω : Type u_6} {A : Type u_7} {B : Type u_8} [MeasurableSpace Ω]
    [MeasurableSpace A] [MeasurableSpace B]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {X : I → Ω → A} {Y : I → Ω → B}
    (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    (hpair : iIndepFun (fun i ω => (X i ω, Y i ω)) P)
    (hxy : ∀ i, IndepFun (X i) (Y i) P) :
    IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) P := by
  classical
  apply IndepFun.process_indepFun_process hX hY
  intro S T
  have hfin := indepFun_vectors_of_independent_pairs
    (I := ↥(S ∪ T)) (X := fun i => X i) (Y := fun i => Y i)
    (fun i => hX i) (fun i => hY i)
    (hpair.precomp Subtype.val_injective) (fun i => hxy i)
  exact hfin.comp
    (φ := fun x (i : S) => x ⟨i, Finset.mem_union_left T i.property⟩)
    (ψ := fun y (i : T) => y ⟨i, Finset.mem_union_right S i.property⟩)
    (by fun_prop) (by fun_prop)

theorem indepFun_families_infinitePi
    {I : Type u_9} {Ω : Type u_10} {A : Type u_11} {B : Type u_12} [MeasurableSpace Ω]
    [MeasurableSpace A] [MeasurableSpace B]
    (P : I → Measure Ω) [∀ i, IsProbabilityMeasure (P i)]
    {X : I → Ω → A} {Y : I → Ω → B}
    (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    (hxy : ∀ i, IndepFun (X i) (Y i) (P i)) :
    IndepFun (fun ω i => X i (ω i)) (fun ω i => Y i (ω i))
      (Measure.infinitePi P) := by
  apply indepFun_families_of_independent_pairs
    (fun i => (hX i).comp (measurable_pi_apply i))
    (fun i => (hY i).comp (measurable_pi_apply i))
  · exact iIndepFun_infinitePi (fun i => (hX i).prodMk (hY i))
  · intro i
    apply (indepFun_iff_map_prod_eq_prod_map_map
      ((hX i).comp (measurable_pi_apply i)).aemeasurable
      ((hY i).comp (measurable_pi_apply i)).aemeasurable).2
    simp only [Function.comp_apply]
    have hm (f : Ω → A × B) (hf : Measurable f) :
        (Measure.infinitePi P).map (fun ω => f (ω i)) = (P i).map f := by
      rw [← Function.comp_def, ← Measure.map_map hf (measurable_pi_apply i),
        Measure.infinitePi_map_eval]
    rw [hm (fun ω => (X i ω, Y i ω)) ((hX i).prodMk (hY i))]
    rw [(hxy i).map_prod_eq_prod_map_map (hX i).aemeasurable (hY i).aemeasurable]
    congr 1
    · rw [← Measure.map_map (hX i) (measurable_pi_apply i), Measure.infinitePi_map_eval]
    · rw [← Measure.map_map (hY i) (measurable_pi_apply i), Measure.infinitePi_map_eval]

theorem brownian_iid_shift_indep_past
    {I : Type u_13} {Ω : Type u_14} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t)) (u : ℝ≥0) :
    IndepFun (fun (ω : I → Ω) i t => B (u + t) (ω i) - B u (ω i))
      (fun (ω : I → Ω) i (t : Set.Iic u) => B t (ω i))
      (Measure.infinitePi (fun _ : I => P)) := by
  apply indepFun_families_infinitePi (fun _ : I => P)
    (X := fun _ ω t => B (u + t) ω - B u ω)
    (Y := fun _ ω (t : Set.Iic u) => B t ω)
  · intro i
    exact Measurable.of_eval fun t => (hm (u + t)).sub (hm u)
  · intro i
    exact Measurable.of_eval fun t => hm t
  · intro i
    exact hB.indepFun_shift u

theorem brownian_iid_weighted_increment_indep_past
    {I : Type u_15} {Ω : Type u_16} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (u h : ℝ≥0) (S : Finset I) (θ : I → ℝ) :
    IndepFun (fun (ω : I → Ω) => ∑ i ∈ S, θ i * (B (u + h) (ω i) - B u (ω i)))
      (fun (ω : I → Ω) i (t : Set.Iic u) => B t (ω i))
      (Measure.infinitePi (fun _ : I => P)) := by
  exact (brownian_iid_shift_indep_past hB hm u).comp
    (φ := fun z : I → ℝ≥0 → ℝ => ∑ i ∈ S, θ i * z i h)
    (ψ := id) (by fun_prop) measurable_id

theorem hasLaw_finsetSum_gaussian
    {I : Type u_17} {Ω : Type u_18} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : I → Ω → ℝ} {m : I → ℝ} {v : I → ℝ≥0}
    (hX : ∀ i, HasLaw (X i) (gaussianReal (m i) (v i)) P)
    (hind : iIndepFun X P) (S : Finset I) :
    HasLaw (∑ i ∈ S, X i) (gaussianReal (∑ i ∈ S, m i) (∑ i ∈ S, v i)) P := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      change HasLaw (fun _ : Ω => (0 : ℝ)) (gaussianReal 0 0) P
      exact ⟨aemeasurable_const, by simp [gaussianReal_zero_var, Measure.map_const]⟩
  | @insert i S hi ih =>
      simp only [Finset.sum_insert hi]
      refine ⟨(hX i).aemeasurable.add ih.aemeasurable, ?_⟩
      exact gaussianReal_add_gaussianReal_of_indepFun
        (hind.indepFun_finsetSum_of_notMem₀ (fun i => (hX i).aemeasurable) hi).symm
        (hX i) ih

theorem hasLaw_infinitePi_eval
    {I : Type u_19} {Ω : Type u_20} [MeasurableSpace Ω]
    (P : I → Measure Ω) [∀ i, IsProbabilityMeasure (P i)] (i : I) :
    HasLaw (fun ω : I → Ω => ω i) (P i) (Measure.infinitePi P) :=
  ⟨(measurable_pi_apply i).aemeasurable, Measure.infinitePi_map_eval P i⟩

theorem brownian_iid_weighted_increment_hasLaw
    {I : Type u_21} {Ω : Type u_22} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (u h : ℝ≥0) (S : Finset I) (θ : I → ℝ) :
    HasLaw (fun (ω : I → Ω) => ∑ i ∈ S, θ i * (B (u + h) (ω i) - B u (ω i)))
      (gaussianReal 0 (∑ i ∈ S, (NNReal.mk (θ i ^ 2) (sq_nonneg _)) * h))
      (Measure.infinitePi (fun _ : I => P)) := by
  have hlaw (i : I) :
      HasLaw (fun (ω : I → Ω) => θ i * (B (u + h) (ω i) - B u (ω i)))
        (gaussianReal 0 ((NNReal.mk (θ i ^ 2) (sq_nonneg _)) * h))
        (Measure.infinitePi (fun _ : I => P)) := by
    simpa only [Function.comp_def, mul_zero] using
      (gaussianReal_const_mul ((hB.shift u).hasLaw_eval h) (θ i)).comp
      (hasLaw_infinitePi_eval (fun _ : I => P) i)
  have hind : iIndepFun
      (fun i (ω : I → Ω) => θ i * (B (u + h) (ω i) - B u (ω i)))
      (Measure.infinitePi (fun _ : I => P)) :=
    iIndepFun_infinitePi (fun i => ((hm (u + h)).sub (hm u)).const_mul (θ i))
  convert hasLaw_finsetSum_gaussian hlaw hind S using 1
  · ext ω
    simp only [Finset.sum_apply]
  · simp

end Problem336AdditiveD139.Noise

end

end OAI
