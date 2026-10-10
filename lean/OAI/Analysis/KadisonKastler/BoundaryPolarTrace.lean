import OAI.Analysis.KadisonKastler.BoundaryDiagonal
import OAI.Analysis.KadisonKastler.TracialProducts

namespace OAI

/-! # Tracial continuity of the near-identity polar factor

The proof uses the trace pairing and the norm bound on each positive
polar factor. It does not require a measurable functional-calculus
selection or an operator-topology continuity theorem.
-/

namespace KadisonKastler

noncomputable section

variable {B : Type*} [CStarAlgebra B]

/-- In a tracial state, taking the adjoint of one factor does not change
the real pairing with a selfadjoint factor. -/
theorem FaithfulTracialState.re_star_mul_selfAdjoint (τ : FaithfulTracialState B)
    (y p : B) (hp : IsSelfAdjoint p) :
    (τ.toLinearMap (star y * p)).re = (τ.toLinearMap (y * p)).re := by
  calc
    _ = (τ.toLinearMap (p * star y)).re := congrArg Complex.re (τ.tracial _ _)
    _ = (τ.toLinearMap (star (y * p))).re := by rw [star_mul, hp.star_eq]
    _ = (star (τ.toLinearMap (y * p))).re := by rw [τ.map_star]
    _ = _ := by simp

/-- A trace estimate for one bounded right factor. -/
theorem FaithfulTracialState.norm_square_pairing_le (τ : FaithfulTracialState B)
    (x d : B) : ‖τ.toLinearMap (star x * x * d)‖ ≤ ‖d‖ * traceTwoNorm τ x ^ 2 := by
  calc
    _ = ‖τ.toLinearMap (star x * (x * d))‖ := by rw [mul_assoc]
    _ ≤ traceTwoNorm τ x * traceTwoNorm τ (x * d) := τ.cauchySchwarz x (x * d)
    _ ≤ traceTwoNorm τ x * (traceTwoNorm τ x * ‖d‖) :=
      mul_le_mul_of_nonneg_left (traceTwoNorm_mul_le_right τ x d) (traceTwoNorm_nonneg τ x)
    _ = _ := by ring

/-- Exact real trace identity underlying the polar Lipschitz estimate. -/
theorem polar_trace_pairing_identity (τ : FaithfulTracialState B)
    (u v : unitary B) (p q : B) (hp : IsSelfAdjoint p) (hq : IsSelfAdjoint q) :
    2 * (τ.toLinearMap (star ((u : B) - (v : B)) * ((u : B) * p - (v : B) * q))).re =
      (τ.toLinearMap (star ((u : B) - (v : B)) * ((u : B) - (v : B)) * (p + q))).re := by
  have he1 : star ((u : B) - (v : B)) * ((u : B) * p - (v : B) * q) =
      p + q - star (u : B) * (v : B) * q - star (v : B) * (u : B) * p := by
    calc
      _ = (star (u : B) * (u : B)) * p + (star (v : B) * (v : B)) * q -
          star (u : B) * (v : B) * q - star (v : B) * (u : B) * p := by
        rw [star_sub]
        noncomm_ring
      _ = _ := by rw [Unitary.star_mul_self_of_mem u.property,
        Unitary.star_mul_self_of_mem v.property, one_mul, one_mul]
  have he2 : star ((u : B) - (v : B)) * ((u : B) - (v : B)) * (p + q) =
      p + q + p + q - star (u : B) * (v : B) * p - star (u : B) * (v : B) * q -
        star (v : B) * (u : B) * p - star (v : B) * (u : B) * q := by
    calc
      _ = (star (u : B) * (u : B)) * (p + q) +
          (star (v : B) * (v : B)) * (p + q) -
          star (u : B) * (v : B) * p - star (u : B) * (v : B) * q -
          star (v : B) * (u : B) * p - star (v : B) * (u : B) * q := by
        rw [star_sub]
        noncomm_ring
      _ = _ := by
        simp only [Unitary.star_mul_self_of_mem u.property,
          Unitary.star_mul_self_of_mem v.property, one_mul]
        noncomm_ring
  have hsp := τ.re_star_mul_selfAdjoint (star (v : B) * (u : B)) p hp
  have hsq := τ.re_star_mul_selfAdjoint (star (v : B) * (u : B)) q hq
  simp only [star_mul, star_star] at hsp hsq
  rw [he1, he2]
  simp only [map_add, map_sub, Complex.add_re, Complex.sub_re]
  linarith

/-- Positive polar factors within radius `r` of one give a tracial
Lipschitz bound, with no commutation requirement between the factors. -/
theorem polar_traceTwoNorm_bound_of_factors (τ : FaithfulTracialState B)
    (u v : unitary B) (p q : B) (hp : IsSelfAdjoint p) (hq : IsSelfAdjoint q)
    {r : ℝ} (hpn : ‖p - 1‖ ≤ r) (hqn : ‖q - 1‖ ≤ r) :
    (1 - r) * traceTwoNorm τ ((u : B) - (v : B)) ≤
      traceTwoNorm τ ((u : B) * p - (v : B) * q) := by
  let x : B := (u : B) - (v : B)
  let e : B := (u : B) * p - (v : B) * q
  change (1 - r) * traceTwoNorm τ x ≤ traceTwoNorm τ e
  have hpair := polar_trace_pairing_identity τ u v p q hp hq
  change 2 * (τ.toLinearMap (star x * e)).re =
    (τ.toLinearMap (star x * x * (p + q))).re at hpair
  have hdecomp : star x * x * (p + q) = star x * x + star x * x +
      star x * x * (p - 1) + star x * x * (q - 1) := by noncomm_ring
  rw [hdecomp, map_add, map_add, map_add, Complex.add_re, Complex.add_re,
    Complex.add_re, ← traceTwoNorm_sq τ x] at hpair
  have hlow (d : B) (hd : ‖d‖ ≤ r) :
      -r * traceTwoNorm τ x ^ 2 ≤ (τ.toLinearMap (star x * x * d)).re := by
    have hn := (τ.norm_square_pairing_le x d).trans
      (mul_le_mul_of_nonneg_right hd (sq_nonneg _))
    have hl := (abs_le.mp (Complex.abs_re_le_norm (τ.toLinearMap (star x * x * d)))).1
    linarith
  have hlp := hlow (p - 1) hpn
  have hlq := hlow (q - 1) hqn
  have hl : (1 - r) * traceTwoNorm τ x ^ 2 ≤ (τ.toLinearMap (star x * e)).re := by
    nlinarith
  have hu := (Complex.re_le_norm (τ.toLinearMap (star x * e))).trans (τ.cauchySchwarz x e)
  have hn := traceTwoNorm_nonneg τ x
  by_cases hx : traceTwoNorm τ x = 0
  · simpa only [hx, mul_zero] using traceTwoNorm_nonneg τ e
  · have hxpos : 0 < traceTwoNorm τ x := lt_of_le_of_ne hn (Ne.symm hx)
    have hmul : traceTwoNorm τ x * ((1 - r) * traceTwoNorm τ x) ≤
        traceTwoNorm τ x * traceTwoNorm τ e := by nlinarith
    exact (mul_le_mul_iff_right₀ hxpos).mp hmul

local instance boundaryPolarTraceOrder : PartialOrder B := CStarAlgebra.spectralOrder B
local instance boundaryPolarTraceStarOrder : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B

/-- Near-identity unitary polar factors are Lipschitz for the faithful
tracial two-norm. -/
theorem polar_traceTwoNorm_lipschitz (τ : FaithfulTracialState B)
    (b c : B) (u v : unitary B)
    (hu : (u : B) * CFC.abs b = b) (hv : (v : B) * CFC.abs c = c)
    {r : ℝ} (hr : r < 1) (hb : ‖b - 1‖ ≤ r) (hc : ‖c - 1‖ ≤ r) :
    (1 - r) * traceTwoNorm τ ((u : B) - (v : B)) ≤ traceTwoNorm τ (b - c) := by
  have h10 : (1 : B) ≠ 0 := by
    intro h
    have hm := τ.map_one
    rw [h, map_zero] at hm
    exact zero_ne_one hm
  let : Nontrivial B := ⟨⟨1, 0, h10⟩⟩
  have hab (x : B) (hx : ‖x - 1‖ ≤ r) : ‖CFC.abs x - 1‖ ≤ r := by
    let t : Bˣ := Units.ofNearby 1 x (by simpa using hx.trans_lt hr)
    exact (norm_abs_sub_one_le t (by exact hx.trans_lt hr)).trans hx
  have h := polar_traceTwoNorm_bound_of_factors τ u v (CFC.abs b) (CFC.abs c)
    (CFC.abs_nonneg b).isSelfAdjoint (CFC.abs_nonneg c).isSelfAdjoint (hab b hb) (hab c hc)
  simpa only [hu, hv] using h


/-- The explicit Lipschitz constant on a fixed neighborhood of one. -/
theorem polar_traceTwoNorm_le_inv_mul (τ : FaithfulTracialState B)
    (b c : B) (u v : unitary B)
    (hu : (u : B) * CFC.abs b = b) (hv : (v : B) * CFC.abs c = c)
    {r : ℝ} (hr : r < 1) (hb : ‖b - 1‖ ≤ r) (hc : ‖c - 1‖ ≤ r) :
    traceTwoNorm τ ((u : B) - (v : B)) ≤ (1 - r)⁻¹ * traceTwoNorm τ (b - c) := by
  have h := polar_traceTwoNorm_lipschitz τ b c u v hu hv hr hb hc
  calc
    _ ≤ traceTwoNorm τ (b - c) / (1 - r) :=
      (le_div_iff₀ (sub_pos.mpr hr)).mpr (by simpa only [mul_comm] using h)
    _ = _ := by rw [div_eq_mul_inv, mul_comm]

end

end KadisonKastler

end OAI
