import OAI.Geometry.RCD.Sobolev.BochnerShiftedQuadratic

namespace OAI

/-! # The scalar dimensional inequality excludes an extra orthogonal square

The vectors in this calculation represent centered squares of regular
test functions.  Their sources and mixed Bochner densities are the exact
quantities computed by the local product rules.
-/

open Finset
noncomputable section
namespace RegularPointCoordinates

theorem dimensional_square_residual_zero {N r : ℝ} (hN : 0<N)
    (h : ∀ t : ℝ, (N+t*r)^2≤N*(N+t^2*r^2)) : r=0 := by
  by_contra hne
  have hi := h r⁻¹
  have hm : r⁻¹*r=1 := inv_mul_cancel₀ hne
  have hs : (r⁻¹)^2*r^2=1 := by rw [← mul_pow,hm,one_pow]
  rw [hm,hs] at hi
  nlinarith only [hi,hN]

theorem bochner_square_saturation {E : Type*} [AddCommGroup E] [Module ℝ E]
    {n : ℕ} (hn : 0<n) (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (D : E →ₗ[ℝ] ℝ)
    (hBE : ∀ a, (D a)^2≤(n:ℝ)*B a a)
    (z : Fin n → E) (w : E) {r : ℝ}
    (hDz : ∀ i, D (z i)=2)
    (hBz : ∀ i j, B (z i) (z j)=if i=j then 4 else 0)
    (hzw : ∀ i, B (z i) w=0) (hwz : ∀ i, B w (z i)=0)
    (hDw : D w=2*r) (hBw : B w w=4*r^2) : r=0 := by
  classical
  let q := (1/2:ℝ) • ∑ i, z i
  let v := (1/2:ℝ) • w
  have hDq : D q=(n:ℝ) := by
    simp [q,map_sum,hDz]
    ring
  have hDv : D v=r := by simp [v,hDw]
  have hBq : B q q=(n:ℝ) := by
    simp [q,map_sum,hBz]
    ring
  have hBv : B v v=r^2 := by simp [v,hBw]; ring
  have hqv : B q v=0 := by simp [q,v,map_sum,hzw]
  have hvq : B v q=0 := by simp [q,v,map_sum,hwz]
  apply dimensional_square_residual_zero (N := (n:ℝ)) (by exact_mod_cast hn)
  intro t
  have hh := hBE (q+t • v)
  simp only [map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,
    hDq,hDv,hBq,hBv,hqv,hvq,mul_zero,add_zero,zero_add] at hh
  convert hh using 1
  ring

end RegularPointCoordinates

end

end OAI
