import OAI.Probability.SignedSweeps.Model

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

def groupAverage {G E : Type*} [Group G] [Fintype G] [AddCommGroup E] [Module ℂ E]
    (ρ : Representation ℂ G E) : E →ₗ[ℂ] E :=
  (Fintype.card G : ℂ)⁻¹ • ∑ g, ρ g

lemma groupAverage_invariant {G E : Type*} [Group G] [Fintype G]
    [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ G E) (g : G) (x : E) :
    ρ g (groupAverage ρ x) = groupAverage ρ x := by
  classical
  simp only [groupAverage, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum,
    ← Module.End.mul_apply, ← map_mul]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun _ => rfl)

lemma groupAverage_fixed {G E : Type*} [Group G] [Fintype G]
    [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ G E) (x : E)
    (hx : ∀ g, ρ g x = x) : groupAverage ρ x = x := by
  have hc : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [groupAverage, LinearMap.smul_apply, LinearMap.sum_apply, hx, Finset.sum_const,
    Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]

lemma groupAverage_idempotent {G E : Type*} [Group G] [Fintype G]
    [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ G E) :
    IsIdempotentElem (groupAverage ρ) := by
  ext x
  exact groupAverage_fixed ρ _ (fun g => groupAverage_invariant ρ g x)

lemma representation_inner_inverse {G E : Type*} [Group G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (ρ : Representation ℂ G E)
    (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) (g : G) (x y : E) :
    inner ℂ (ρ g x) y = inner ℂ x (ρ g⁻¹ y) := by
  let e : E →ₗᵢ[ℂ] E := ⟨ρ g, hρ g⟩
  have he : ρ g (ρ g⁻¹ y) = y := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  calc
    inner ℂ (ρ g x) y = inner ℂ (ρ g x) (ρ g (ρ g⁻¹ y)) := congrArg _ he.symm
    _ = inner ℂ x (ρ g⁻¹ y) := e.inner_map_map x (ρ g⁻¹ y)

lemma groupAverage_symmetric {G E : Type*} [Group G] [Fintype G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (ρ : Representation ℂ G E)
    (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) : (groupAverage ρ).IsSymmetric := by
  intro x y
  simp only [groupAverage, LinearMap.smul_apply, LinearMap.sum_apply, inner_smul_left,
    inner_smul_right, inner_sum, sum_inner, map_inv₀, map_natCast]
  congr 1
  simp_rw [representation_inner_inverse ρ hρ]
  exact Fintype.sum_equiv (Equiv.inv G) _ _ (fun _ => rfl)

lemma symmetricProjection_norm_eq_iff {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (P : E →ₗ[ℂ] E) (hP : P.IsSymmetricProjection) (x : E) :
    ‖P x‖ = ‖x‖ ↔ P x = x := by
  constructor
  · intro he
    have hi : inner ℂ (P x) (x - P x) = 0 := by
      rw [inner_sub_right, ← hP.isSymmetric]
      have hid : P (P x) = P x := congrArg (fun T : E →ₗ[ℂ] E => T x) hP.isIdempotentElem
      rw [hid, sub_self]
    have hn := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (P x) (x - P x) hi
    have hz : ‖x - P x‖ = 0 := by
      rw [add_sub_cancel, he] at hn
      nlinarith [norm_nonneg (x - P x)]
    exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm
  · rintro h; rw [h]

lemma groupAverage_norm_eq_iff {G E : Type*} [Group G] [Fintype G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (ρ : Representation ℂ G E)
    (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) (x : E) :
    ‖groupAverage ρ x‖ = ‖x‖ ↔ ∀ g, ρ g x = x := by
  rw [symmetricProjection_norm_eq_iff _ ⟨groupAverage_idempotent ρ, groupAverage_symmetric ρ hρ⟩]
  constructor
  · intro h g
    simpa [h] using groupAverage_invariant ρ g x
  · exact groupAverage_fixed ρ x

lemma layerOperator_symmetricProjection {d : ℕ} (lam : Partition (2 ^ d)) (i : Fin d) :
    (layerOperator lam i).IsSymmetricProjection := by
  classical
  let ρ := (spechtRepresentation lam).comp (coordinateSubgroup d i).subtype
  exact ⟨groupAverage_idempotent ρ,
    groupAverage_symmetric ρ (fun g => spechtRepresentation_norm lam g.1)⟩

lemma layerOperator_norm_eq_iff {d : ℕ} (lam : Partition (2 ^ d)) (i : Fin d)
    (x : Specht lam) : ‖layerOperator lam i x‖ = ‖x‖ ↔
      ∀ g : coordinateSubgroup d i, spechtRepresentation lam g.1 x = x := by
  classical
  let ρ := (spechtRepresentation lam).comp (coordinateSubgroup d i).subtype
  exact groupAverage_norm_eq_iff ρ (fun g => spechtRepresentation_norm lam g.1) x

lemma list_prod_norm_eq_fixed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L : List (E →ₗ[ℂ] E))
    (hL : ∀ A ∈ L, ∀ x, ‖A x‖ ≤ ‖x‖ ∧ (‖A x‖ = ‖x‖ → A x = x))
    (x : E) (hn : ‖L.prod x‖ = ‖x‖) : L.prod x = x ∧ ∀ A ∈ L, A x = x := by
  induction L with
  | nil => simp
  | cons A L ih =>
    have ht : ‖L.prod x‖ ≤ ‖x‖ := list_prod_contraction L (fun A hA y => (hL A (by simp [hA]) y).1) x
    have hh := (hL A (by simp) (L.prod x)).1
    rw [List.prod_cons, Module.End.mul_apply] at hn
    have het : ‖L.prod x‖ = ‖x‖ := le_antisymm ht (hn ▸ hh)
    obtain ⟨hprod, htail⟩ := ih (fun A hA => hL A (by simp [hA])) het
    rw [hprod] at hn
    have hAf := (hL A (by simp) x).2 hn
    constructor
    · simpa [List.prod_cons, Module.End.mul_apply, hprod] using hAf
    · intro B hB
      rcases List.mem_cons.mp hB with rfl | hB
      · exact hAf
      · exact htail B hB

lemma sweep_norm_eq_implies_layer_fixed {d : ℕ} (lam : Partition (2 ^ d))
    (x : Specht lam) (hn : ‖sweepOperator lam x‖ = ‖x‖) :
    ∀ i (g : coordinateSubgroup d i), spechtRepresentation lam g.1 x = x := by
  have hL : ∀ A ∈ (List.ofFn (layerOperator lam)).reverse,
      ∀ x, ‖A x‖ ≤ ‖x‖ ∧ (‖A x‖ = ‖x‖ → A x = x) := by
    intro A hA y
    simp only [List.mem_reverse, List.mem_ofFn] at hA
    obtain ⟨i, rfl⟩ := hA
    exact ⟨layerOperator_contraction lam i y,
      (symmetricProjection_norm_eq_iff _ (layerOperator_symmetricProjection lam i) y).mp⟩
  have hf := (list_prod_norm_eq_fixed _ hL x hn).2
  intro i g
  have hi := hf (layerOperator lam i) (by simp)
  exact (layerOperator_norm_eq_iff lam i x).mp (congrArg norm hi) g

lemma opNorm_lt_one_of_pointwise {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E)
    (hT : ∀ x, x ≠ 0 → ‖T x‖ < ‖x‖) : ‖T.toContinuousLinearMap‖ < 1 := by
  rcases subsingleton_or_nontrivial E with h | h
  · have hzero : T = 0 := Subsingleton.elim _ _
    simp [hzero]
  · have hne : (Metric.sphere (0 : E) 1).Nonempty := by
      obtain ⟨x⟩ := NormedSpace.sphere_nonempty_rclike ℂ (E := E) (show (0 : ℝ) ≤ 1 by norm_num)
      exact ⟨x.1, x.2⟩
    obtain ⟨x, hx, hmax⟩ := (isCompact_sphere (0 : E) 1).exists_isMaxOn hne
      T.toContinuousLinearMap.continuous.norm.continuousOn
    have hnx : ‖x‖ = 1 := by simpa using hx
    have hx0 : x ≠ 0 := by intro hx0; simp [hx0] at hnx
    have ht : ‖T x‖ < 1 := (hT x hx0).trans_eq hnx
    apply lt_of_le_of_lt _ ht
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (norm_nonneg _)
    intro y hy
    exact hmax (by simpa using hy)

end SignedSweeps
end

end OAI
