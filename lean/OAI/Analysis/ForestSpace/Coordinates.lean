import OAI.Analysis.ForestSpace.Renorming

namespace OAI

open scoped BigOperators
open Finset

namespace ForestSpace

noncomputable section
attribute [local instance] Classical.propDecidable

section CoordinateBounds
variable {V : Type} [PartialOrder V]

 theorem coordinate_squares_le (S : Finset V) (u : TestVector V) :
    ∑ v ∈ S, u v ^ 2 ≤ ‖u‖^2 := by
  have hh := (testBound_rho_sq (finsupp_has_testBound u.toFinsupp))
    S inferInstance (fun v : S => {(v : V)})
    (fun v => isSegment_singleton (v : V))
    (by
      intro i j hij
      apply Finset.disjoint_singleton.mpr
      exact fun he => hij (Subtype.ext he))
  have hh' : (∑ v : S, u (v : V)^2) ≤ ‖u‖^2 := by
    simpa only [segSum,Finset.sum_singleton,TestVector.norm_eq_rho] using hh
  rw [← Finset.sum_coe_sort S (fun v => u v^2)]
  exact hh'

 theorem norm_sum_coordinates_le (S : Finset V) (a : V → ℝ) :
    ‖∑ v ∈ S, a v • eStar v‖ ≤ Real.sqrt (∑ v ∈ S, a v ^ 2) := by
  rw [← norm_rawRestriction (∑ v ∈ S, a v • eStar v)]
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro u
  simp only [rawRestriction_apply, _root_.sum_apply, smul_apply, eStar_coe,
    smul_eq_mul, Real.norm_eq_abs]
  have hA : 0 ≤ ∑ v ∈ S, a v ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg u))).mp
  rw [sq_abs, mul_pow, Real.sq_sqrt hA]
  exact (Finset.sum_mul_sq_le_sq_mul_sq S a (fun v => u v)).trans
    (mul_le_mul_of_nonneg_left (coordinate_squares_le S u) hA)

 theorem norm_sum_eX_le (S : Finset V) (a : V → ℝ) :
    ‖∑ v ∈ S, a v • eX v‖ ≤ Real.sqrt (∑ v ∈ S, a v ^ 2) := by
  change ‖(∑ v ∈ S, a v • eX v : X V).val‖ ≤ _
  simpa only [Submodule.coe_sum, Submodule.coe_smul, eX_val] using norm_sum_coordinates_le S a

 theorem dual_vectors_squares_le {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {I : Type} (v : I → E)
    (h : ∀ (S : Finset I) (a : I → ℝ), ‖∑ i ∈ S, a i • v i‖ ≤ Real.sqrt (∑ i ∈ S, a i^2))
    (φ : StrongDual ℝ E) (S : Finset I) :
    ∑ i ∈ S, (φ (v i))^2 ≤ ‖φ‖^2 := by
  let A : ℝ := ∑ i ∈ S, (φ (v i))^2
  have hA : 0 ≤ A := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hroot := Real.sq_sqrt hA
  have hp : φ (∑ i ∈ S, φ (v i) • v i) = A := by
    simp only [map_sum, map_smul, smul_eq_mul, pow_two, A]
  have hh := φ.le_opNorm (∑ i ∈ S, φ (v i) • v i)
  rw [hp, Real.norm_of_nonneg hA] at hh
  have hh' := hh.trans (mul_le_mul_of_nonneg_left
    (h S (fun i => φ (v i))) (norm_nonneg φ))
  change A ≤ ‖φ‖*Real.sqrt A at hh'
  have hr : Real.sqrt A ≤ ‖φ‖ := by
    by_cases hz : Real.sqrt A = 0
    · simp [hz]
    · have hpos : 0 < Real.sqrt A := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hz)
      nlinarith
  change A ≤ ‖φ‖^2
  nlinarith [Real.sqrt_nonneg A, norm_nonneg φ]

 theorem weakNull_of_l2_bound {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {I : Type} (v : I → E)
    (h : ∀ (S : Finset I) (a : I → ℝ), ‖∑ i ∈ S, a i • v i‖ ≤ Real.sqrt (∑ i ∈ S, a i^2))
    (w : ℕ → I) (hw : Function.Injective w) : WeakNull (fun n => v (w n)) := by
  intro φ
  have hs : Summable (fun i : I => (φ (v i))^2) :=
    summable_of_sum_le (fun _ => sq_nonneg _) (dual_vectors_squares_le v h φ)
  have ht := (hs.comp_injective hw).tendsto_atTop_zero
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp ht
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero] using hh

 theorem weakNull_coordinates (v : ℕ → V) (hv : Function.Injective v) :
    WeakNull (fun n => eX (v n)) := by
  apply weakNull_of_l2_bound (E := X V) (eX (V := V)) ?_ v hv
  intro S a
  change ‖(∑ i ∈ S, a i • eX i : X V).val‖ ≤ _
  simpa only [Submodule.coe_sum,Submodule.coe_smul,eX_val] using norm_sum_coordinates_le S a

 theorem norm_segment_functional_le (S : Finset V) (hS : IsSegment S) :
    ‖∑ v ∈ S, eStar v‖ ≤ 1 := by
  rw [← norm_rawRestriction (∑ v ∈ S, eStar v)]
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  simp only [rawRestriction_apply, _root_.sum_apply, eStar_coe, one_mul, Real.norm_eq_abs]
  have hh := (testBound_rho_sq (finsupp_has_testBound u.toFinsupp)).single hS
  exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg u)).mp (by
    simpa only [sq_abs, TestVector.norm_eq_rho, segSum] using hh)

 theorem norm_segment_functional (S : Finset V) (hS : IsSegment S) (hne : S.Nonempty) :
    ‖∑ v ∈ S, eStar v‖ = 1 := by
  apply le_antisymm (norm_segment_functional_le S hS)
  obtain ⟨v,hv⟩ := hne
  have hh := (∑ w ∈ S, eStar w).le_opNorm (e v)
  simpa [eStar_e,hv] using hh

 theorem norm_segment_eX (S : Finset V) (hS : IsSegment S) (hne : S.Nonempty) :
    ‖∑ v ∈ S, eX v‖ = 1 := by
  change ‖(∑ v ∈ S, eX v : X V).val‖ = _
  simpa only [Submodule.coe_sum,eX_val] using norm_segment_functional S hS hne

 theorem ancestors_isSegment (hF : ForestOrder V) (v : V) (hfin : (Set.Iic v).Finite) :
    IsSegment hfin.toFinset := by
  constructor
  · intro a ha b hb
    apply hF a b v
    · simpa using ha
    · simpa using hb
  · intro a ha b hb c hac hcb
    have hbv : b ≤ v := by simpa using hb
    simpa using hcb.trans hbv

noncomputable def pathVector (v : V) (hfin : (Set.Iic v).Finite) : X V :=
  ∑ w ∈ hfin.toFinset, eX w

 theorem norm_pathVector (hF : ForestOrder V) (v : V) (hfin : (Set.Iic v).Finite) :
    ‖pathVector v hfin‖ = 1 := by
  exact norm_segment_eX _ (ancestors_isSegment hF v hfin) ⟨v,by simp⟩

end CoordinateBounds

end

end ForestSpace

end OAI
