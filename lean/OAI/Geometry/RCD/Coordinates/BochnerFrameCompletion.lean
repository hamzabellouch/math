import OAI.Geometry.RCD.Sobolev.BochnerSquareSaturation
import OAI.Geometry.RCD.Sobolev.FiniteDimensionalBochnerAE

namespace OAI

/-! # Exact frame completion from the scalar dimensional Bochner inequality -/

open Finset Set Filter MeasureTheory TopologicalSpace
noncomputable section
namespace RegularPointCoordinates

theorem ae_finite_bochner_bound {X : Type*} [MeasurableSpace X] {m : ℕ}
    (μ : Measure X) (B : X → Euclidean m →ₗ[ℝ] Euclidean m →ₗ[ℝ] ℝ)
    (D : X → Euclidean m →ₗ[ℝ] ℝ) (N : ℝ)
    (h : ∀ a, ∀ᵐ x ∂μ, (D x a)^2≤N*B x a a) :
    ∀ᵐ x ∂μ, ∀ a, (D x a)^2≤N*B x a a := by
  obtain ⟨S,hS,hdense⟩ := exists_countable_dense (Euclidean m)
  let : Countable S := hS.to_subtype
  filter_upwards [MeasureTheory.ae_all_iff.mpr (fun a : S => h a)] with x hx
  have hc : IsClosed {a : Euclidean m | (D x a)^2≤N*B x a a} :=
    isClosed_le ((D x).toContinuousLinearMap.continuous.pow 2)
      (continuous_const.mul (bilinear_diagonal_continuous (B x)))
  have hall := closure_minimal (fun a ha => hx ⟨a,ha⟩) hc
  rw [hdense.closure_eq] at hall
  exact fun a => hall (Set.mem_univ a)

theorem dimensional_cross_equality {N r s : ℝ} (hN : 0<N)
    (h : ∀ t : ℝ, (N+t*r)^2≤N*(N+2*t*s+t^2*r^2)) : r=s := by
  have hq (t : ℝ) : 0≤(N*r^2-r^2)*(t*t)+(2*N*(s-r))*t+0 := by
    have hh := h t
    nlinarith only [hh]
  have hd := discrim_le_zero hq
  simp only [discrim,mul_zero,sub_zero] at hd
  have hz : 2*N*(s-r)=0 := by nlinarith only [hd,sq_nonneg (2*N*(s-r))]
  rcases mul_eq_zero.mp hz with ha | ha
  · exact (ne_of_gt (mul_pos (by norm_num) hN) ha).elim
  · linarith

theorem centered_square_bochner_pair {E : Type*} [AddCommGroup E] [Module ℝ E]
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (v w zv zw : E) (f g H P : ℝ)
    (hpair : B zv zw=2*g*B zv w+4*f*H+4*P^2)
    (hlinear : B v zw=2*g*B v w+2*H) :
    B (zv-(2*f) • v) (zw-(2*g) • w)=4*P^2 := by
  simp only [map_sub,map_smul,LinearMap.sub_apply,LinearMap.smul_apply,smul_eq_mul]
  rw [hpair,hlinear]
  ring

theorem centered_square_source {E : Type*} [AddCommGroup E] [Module ℝ E]
    (D : E →ₗ[ℝ] ℝ) (v z : E) (f G : ℝ)
    (hz : D z=2*f*D v+2*G) : D (z-(2*f) • v)=2*G := by
  simp only [map_sub,map_smul,smul_eq_mul,hz]
  ring

theorem bochner_frame_completion {E : Type*} [AddCommGroup E] [Module ℝ E]
    {n : ℕ} (hn : 0<n) (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (D : E →ₗ[ℝ] ℝ)
    (hsym : ∀ a b, B a b=B b a) (hBE : ∀ a, (D a)^2≤(n:ℝ)*B a a)
    (z : Fin n → E) (w : E) (r : ℝ) (a : Fin n → ℝ)
    (hDz : ∀ i, D (z i)=2)
    (hBz : ∀ i j, B (z i) (z j)=if i=j then 4 else 0)
    (hDw : D w=2*r) (hBw : B w w=4*r^2)
    (hcross : ∀ i, B (z i) w=4*(a i)^2) : r=∑ i, (a i)^2 := by
  classical
  let q := (1/2:ℝ) • ∑ i, z i
  let v := (1/2:ℝ) • w
  have hDq : D q=(n:ℝ) := by simp [q,map_sum,hDz]; ring
  have hDv : D v=r := by simp [v,hDw]
  have hBq : B q q=(n:ℝ) := by simp [q,map_sum,hBz]; ring
  have hBv : B v v=r^2 := by simp [v,hBw]; ring
  have hqv : B q v=∑ i, (a i)^2 := by
    simp only [q,v,map_smul,map_sum,LinearMap.smul_apply,LinearMap.sum_apply,smul_eq_mul,hcross]
    rw [← mul_sum]
    ring
  have hvq : B v q=∑ i, (a i)^2 := (hsym v q).trans hqv
  apply dimensional_cross_equality (N := (n:ℝ)) (by exact_mod_cast hn)
  intro t
  have hh := hBE (q+t • v)
  simp only [map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,
    hDq,hDv,hBq,hBv,hqv,hvq] at hh
  convert hh using 1
  ring

end RegularPointCoordinates

end

end OAI
