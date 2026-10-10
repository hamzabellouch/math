import OAI.NumberTheory.JointDickman.Amplification.FullSmallArcModel

namespace OAI

/-! # Exact normalization of the retained full-frequency model -/

namespace JointDickman
open Finset MeasureTheory

theorem fullSmallMajorArcModel_denominators {B j Q : ℕ} [NeZero j]
    (hQ : Q ≤ B^12) (X : ℝ) (F W : ℝ → ℂ) (a : ℕ+ → ℂ) :
    fullSmallMajorArcModel B j X Q F W a =
      (1/(j : ℂ))*∑ q ∈ positiveDenominators Q, a q*
        ∑ r : ZMod (j*(q : ℕ)), if r.val.Coprime (q : ℕ) then
          ∫ ξ : ℝ, F ((r.val : ℝ)/(j*(q : ℕ) : ℕ)+ξ/((j : ℝ)*X))*W ξ else 0 := by
  classical
  have hf : (positiveDenominators (B^12)).filter (fun q : ℕ+ => (q : ℕ) ≤ Q) = positiveDenominators Q := by
    ext q
    simp only [mem_filter,mem_positiveDenominators]
    exact ⟨And.right,fun h => ⟨h.trans hQ,h⟩⟩
  unfold fullSmallMajorArcModel
  rw [← sum_filter,hf]
  congr 1
  apply sum_congr rfl
  intro q _
  rw [mul_sum]
  apply sum_congr rfl
  intro r _
  split_ifs <;> simp only [mul_zero]

theorem fullSmallMajorArcModel_scalar_denominators {B j Q : ℕ} [NeZero j]
    (hQ : Q ≤ B^12) (X : ℝ) (F W : ℝ → ℂ) (a : ℕ+ → ℂ) (c : ℂ) :
    fullSmallMajorArcModel B j X Q F (fun ξ => c*W ξ) a =
      (c/(j : ℂ))*∑ q ∈ positiveDenominators Q, a q*
        ∑ r : ZMod (j*(q : ℕ)), if r.val.Coprime (q : ℕ) then
          ∫ ξ : ℝ, W ξ*F ((r.val : ℝ)/(j*(q : ℕ) : ℕ)+ξ/((j : ℝ)*X)) else 0 := by
  rw [fullSmallMajorArcModel_denominators hQ]
  have hi (q : ℕ+) (r : ZMod (j*(q : ℕ))) :
      (∫ ξ : ℝ, F ((r.val : ℝ)/(j*(q : ℕ) : ℕ)+ξ/((j : ℝ)*X))*(c*W ξ)) =
        c*(∫ ξ : ℝ, W ξ*F ((r.val : ℝ)/(j*(q : ℕ) : ℕ)+ξ/((j : ℝ)*X))) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun ξ => by ring)
  simp_rw [hi]
  simp only [div_eq_mul_inv,mul_sum,mul_ite,mul_zero]
  apply sum_congr rfl
  intro q _
  apply sum_congr rfl
  intro r _
  split_ifs <;> ring

end JointDickman

end OAI
