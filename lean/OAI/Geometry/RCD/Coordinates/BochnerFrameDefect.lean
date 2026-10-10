import OAI.Geometry.RCD.Metric.QuantitativeDimensionalCross

namespace OAI

/-! # A quantitative frame-energy identity from centered square data -/

open Finset Real
noncomputable section
namespace RegularPointCoordinates

theorem bochner_frame_defect {E : Type*} [AddCommGroup E] [Module ℝ E]
    {n : ℕ} (hn : 0<n) (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (L : E →ₗ[ℝ] ℝ)
    (hsym : ∀ a b, B a b=B b a) (hBE : ∀ a, (L a)^2≤(n:ℝ)*B a a)
    (z : Fin n → E) (w : E) (G : Fin n → Fin n → ℝ)
    (r : ℝ) (a : Fin n → ℝ) {D : ℝ} (hD : 0≤D) (hD1 : D≤1)
    (hLz : ∀ i, L (z i)=2*G i i)
    (hBz : ∀ i j, B (z i) (z j)=4*(G i j)^2)
    (hLw : L w=2*r) (hBw : B w w=4*r^2)
    (hcross : ∀ i, B (z i) w=4*(a i)^2)
    (htrace : |∑ i, G i i-(n:ℝ)|≤D)
    (hsquare : |∑ i, ∑ j, (G i j)^2-(n:ℝ)|≤D) :
    |r-∑ i, (a i)^2|≤√(6*D)*|r| := by
  classical
  let q := (1/2:ℝ) • ∑ i, z i
  let v := (1/2:ℝ) • w
  have hLq : L q=∑ i, G i i := by
    simp only [q,map_smul,map_sum,hLz,smul_eq_mul,← mul_sum]
    ring
  have hLv : L v=r := by simp [v,hLw]
  have hBq : B q q=∑ i, ∑ j, (G i j)^2 := by
    conv_rhs => rw [Finset.sum_comm]
    simp only [q,map_smul,map_sum,LinearMap.smul_apply,LinearMap.sum_apply,smul_eq_mul,hBz,
      ← mul_sum]
    ring
  have hBv : B v v=r^2 := by simp [v,hBw]; ring
  have hqv : B q v=∑ i, (a i)^2 := by
    simp only [q,v,map_smul,map_sum,LinearMap.smul_apply,LinearMap.sum_apply,smul_eq_mul,
      hcross,← mul_sum]
    ring
  have hvq : B v q=∑ i, (a i)^2 := (hsym v q).trans hqv
  apply dimensional_cross_abs_defect (N := (n:ℝ)) (by exact_mod_cast hn)
    hD hD1 htrace hsquare
  intro t
  have hh := hBE (q+t • v)
  simp only [map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,
    hLq,hLv,hBq,hBv,hqv,hvq] at hh
  convert hh using 1
  ring

end RegularPointCoordinates

end

end OAI
