import OAI.Geometry.HeilbronnTriangle.AuxiliarySupport
import OAI.Geometry.HeilbronnTriangle.PrimitiveNormal

namespace OAI


namespace Problem355.AuxiliarySet

open scoped BigOperators

theorem coordinate_abs_le_of_euclidean_norm_le
    {x : PrimitiveNormal.Vector} {H : ℕ}
    (hx : ‖PrimitiveNormal.toEuclidean x‖ ≤ (H : ℝ)) :
    ∀ i, |x i| ≤ (H : ℤ) := by
  intro i
  have hi := (PiLp.norm_apply_le (PrimitiveNormal.toEuclidean x) i).trans hx
  have hi' : |(x i : ℝ)| ≤ (H : ℝ) := by
    simpa [PrimitiveNormal.toEuclidean, Real.norm_eq_abs] using hi
  exact_mod_cast hi'

theorem cast_mulVec_eq_zero {q : ℕ}
    {A : Matrix (Fin 3) (Fin 3) ℤ} {x : Fin 3 → ℤ}
    (hx : A.mulVec x = 0) :
    (A.map (Int.castRingHom (ZMod q))).mulVec (fun i => (x i : ZMod q)) = 0 := by
  funext i
  have hi := congrArg (fun z : ℤ => (z : ZMod q)) (congrFun hx i)
  simpa [Matrix.mulVec, dotProduct, Matrix.map_apply] using hi

theorem kernel_norm_gt_of_positive_auxiliary_inclusion
    {q H w : ℕ} [Fact q.Prime] (hH : 1 ≤ H) (hHq : H < q)
    {S : Finset (Fin 3 → ZMod q)}
    (hS : AuxiliaryCap.IsCap (S : Set (Fin 3 → ZMod q)))
    (hbox : ∀ v ∈ S, (v 0).val < w)
    {Θ : Type*} (T : Finset Θ) (μ : Θ → ℝ)
    (a : Θ → Fin 3 → ZMod q)
    (G : Θ → ((Fin 3 → ZMod q) ≃ₗ[ZMod q] (Fin 3 → ZMod q)))
    (ha : ∀ θ ∈ T, ∀ n : ℕ, 1 ≤ n → n ≤ 3 * H →
      (n : ZMod q) * a θ 0 ∉ Auxiliary.integerWindow q (3 * H * w))
    (A : Matrix (Fin 3) (Fin 3) ℤ)
    [DecidablePred (fun θ =>
      ∀ j, (fun i => (A i j : ZMod q)) ∈ transformed S (a θ) (G θ))]
    (hpositive : 0 < ∑ θ ∈ T,
      if ∀ j, (fun i => (A i j : ZMod q)) ∈ transformed S (a θ) (G θ)
        then μ θ else 0)
    (hAI : AffineIndependent (ZMod q) (fun j => fun i => (A i j : ZMod q)))
    {x : PrimitiveNormal.Vector} (hne : x ≠ 0) (hkernel : A.mulVec x = 0) :
    (H : ℝ) < ‖PrimitiveNormal.toEuclidean x‖ := by
  classical
  by_contra hnot
  have hnorm : ‖PrimitiveNormal.toEuclidean x‖ ≤ (H : ℝ) := le_of_not_gt hnot
  have hsupport := matrix_support_of_inclusion_sum_pos hH hHq hS hbox T μ a G ha
    (fun i j => (A i j : ZMod q)) hpositive
  have hno := hsupport.2.2 hAI x (coordinate_abs_le_of_euclidean_norm_le hnorm) hne
  exact hno (cast_mulVec_eq_zero hkernel)

end Problem355.AuxiliarySet

end OAI
