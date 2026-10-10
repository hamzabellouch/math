import Mathlib
import OAI.Analysis.Commutator.ColumnModule
import OAI.Analysis.Commutator.LittleGrothendieckSequence

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace BoundedContinuousFunction

open Filter Set UniformSpace Completion

namespace Kadison.ColumnModule

open LittleGrothendieck HilbertSequence

variable {A E : Type*} [CStarAlgebra A]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

lemma sequence_module_bound (ω : Ultrafilter ℕ) (T : A →L[ℂ] E)
    {M : ℝ} (hM : 0≤M) (hmod : ∀ a b : A, ‖T (a*b)‖≤ M*‖a‖*‖T b‖)
    (a b : ℕ →ᵇ A) :
    ‖sequenceMap ω T (a*b)‖≤ M*‖a‖*‖sequenceMap ω T b‖ := by
  apply le_of_tendsto_of_tendsto (sequenceMap_norm_tendsto ω T (a*b))
    (tendsto_const_nhds.mul (sequenceMap_norm_tendsto ω T b))
  apply Filter.Eventually.of_forall
  intro n
  exact (hmod (a n) (b n)).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (a.norm_coe_le_norm n) hM) (norm_nonneg _))

theorem sum_norm_sq_le {ι : Type*} [Fintype ι] (T : A →L[ℂ] E)
    {M : ℝ} (hM : 0≤M) (hmod : ∀ a b : A, ‖T (a*b)‖≤ M*‖a‖*‖T b‖)
    (a : ι → A) : ∑ i, ‖T (a i)‖^2≤ M^2*‖T‖^2*‖∑ i,star (a i)*a i‖ := by
  classical
  obtain ⟨ω,u,hu⟩ := exists_sequence_unitary_max T
  let : PartialOrder (ℕ →ᵇ A) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (ℕ →ᵇ A) := CStarAlgebra.spectralOrderedRing _
  have h := sum_sq_at_max (sequenceMap ω T) hM (sequence_module_bound ω T hM hmod)
    u hu (fun i => BoundedContinuousFunction.const ℕ (a i))
  simp only [sequenceMap_const,LinearIsometry.norm_map] at h
  have hc : (∑ i,star (BoundedContinuousFunction.const ℕ (a i))*
      BoundedContinuousFunction.const ℕ (a i))=
      BoundedContinuousFunction.const ℕ (∑ i,star (a i)*a i) := by
    ext n
    simp
  rw [hc,BoundedContinuousFunction.norm_const_eq] at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (sequenceMap_norm_le ω T) 2) (sq_nonneg M)) (norm_nonneg _))

def homOrbit (φ : A →ₐ[ℂ] (E →L[ℂ] E)) {M : ℝ} (_hM : 0≤M)
    (hφ : ∀ a, ‖φ a‖≤ M*‖a‖) (ξ : E) : A →L[ℂ] E :=
  LinearMap.mkContinuous
    { toFun a := φ a ξ
      map_add' a b := by simp only [map_add,_root_.add_apply]
      map_smul' z a := by simp only [map_smul,_root_.smul_apply, RingHom.id_apply] }
    (M*‖ξ‖) (by
    intro a
    exact ((φ a).le_opNorm ξ).trans (by
      nlinarith [hφ a,norm_nonneg ξ]))

@[simp] lemma homOrbit_apply (φ : A →ₐ[ℂ] (E →L[ℂ] E)) {M : ℝ} (hM : 0≤M)
    (hφ : ∀ a, ‖φ a‖≤ M*‖a‖) (ξ : E) (a : A) : homOrbit φ hM hφ ξ a=φ a ξ := rfl

lemma homOrbit_norm (φ : A →ₐ[ℂ] (E →L[ℂ] E)) {M : ℝ} (hM : 0≤M)
    (hφ : ∀ a, ‖φ a‖≤ M*‖a‖) (ξ : E) : ‖homOrbit φ hM hφ ξ‖≤ M*‖ξ‖ :=
  LinearMap.mkContinuous_norm_le _ (mul_nonneg hM (norm_nonneg ξ)) _

theorem hom_column_sq {ι : Type*} [Fintype ι]
    (φ : A →ₐ[ℂ] (E →L[ℂ] E)) {M : ℝ} (hM : 0≤M)
    (hφ : ∀ a, ‖φ a‖≤ M*‖a‖) (a : ι → A) (ξ : E) :
    ∑ i, ‖φ (a i) ξ‖^2 ≤ M^4*‖ξ‖^2*‖∑ i,star (a i)*a i‖ := by
  have hm (a b : A) : ‖homOrbit φ hM hφ ξ (a*b)‖≤ M*‖a‖*‖homOrbit φ hM hφ ξ b‖ := by
    simp only [homOrbit_apply,map_mul,mul_apply_eq_comp]
    exact ((φ a).le_opNorm (φ b ξ)).trans
      (mul_le_mul_of_nonneg_right (hφ a) (norm_nonneg _))
  have h := sum_norm_sq_le (homOrbit φ hM hφ ξ) hM hm a
  calc
    _ ≤ M^2*‖homOrbit φ hM hφ ξ‖^2*‖∑ i,star (a i)*a i‖ := h
    _ ≤ M^2*(M*‖ξ‖)^2*‖∑ i,star (a i)*a i‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (homOrbit_norm φ hM hφ ξ) 2) (sq_nonneg M)) (norm_nonneg _)
    _ = _ := by ring

end Kadison.ColumnModule

end

end
end

end OAI
