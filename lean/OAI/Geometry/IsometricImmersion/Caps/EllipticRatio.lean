import OAI.Geometry.IsometricImmersion.Caps.EllipticCutoff
import OAI.Geometry.IsometricImmersion.Caps.EllipticAbsorption

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Weighted

open SmoothLocal.Geometry

def ellipticRatioConstant (D c Cv M : ℝ) : ℝ :=
  2 * (1 + M) * Cv ^ 2 * (D ^ 2 + D ^ 3) ^ 2 +
    2 * D ^ 6 * M ^ 2 + 8 * D ^ 5 * M ^ 2 / c

theorem ellipticRatioConstant_nonneg {D c Cv M : ℝ}
    (hD : 0 ≤ D) (hc : 0 < c) (hM : 0 ≤ M) :
    0 ≤ ellipticRatioConstant D c Cv M := by
  unfold ellipticRatioConstant
  positivity

theorem square_bound_of_abs_bound {x R : ℝ} (hx : |x| ≤ R) :
    x ^ 2 ≤ R ^ 2 := by
  calc
    x ^ 2 = |x| ^ 2 := (sq_abs x).symm
    _ ≤ R ^ 2 := pow_le_pow_left₀ (abs_nonneg x) hx 2

theorem elliptic_ratio_scalar
    {d D c Cv M v vt vs A As B C : ℝ}
    (hd : 0 < d) (hdD : d ≤ D) (hc : 0 < c) (hCv : 0 ≤ Cv) (hM : 0 ≤ M)
    (hv : 0 < v) (hvd : v ≤ d ^ 6)
    (hvt : |vt| ≤ Cv * Real.sqrt v * (d ^ 2 + d ^ 3))
    (hvs : |vs| ≤ Cv * Real.sqrt v * (d ^ 2 + d ^ 3))
    (hAlo : c * d ≤ A) (hAhi : |A| ≤ M)
    (hAs : |As| ≤ M) (hB : |B| ≤ M) (hC : |C| ≤ M) :
    (vt - v * B) ^ 2 / v + (As * v + A * vs - v * C) ^ 2 / (A * v) ≤
      ellipticRatioConstant D c Cv M := by
  have hD : 0 ≤ D := hd.le.trans hdD
  have hA : 0 < A := (mul_pos hc hd).trans_le hAlo
  have hAM : A ≤ M := (le_abs_self A).trans hAhi
  let W : ℝ := Cv ^ 2 * (d ^ 2 + d ^ 3) ^ 2
  have hW : 0 ≤ W := mul_nonneg (pow_nonneg hCv 2) (sq_nonneg _)
  have hvt2 : vt ^ 2 ≤ v * W := by
    calc
      vt ^ 2 ≤ (Cv * Real.sqrt v * (d ^ 2 + d ^ 3)) ^ 2 :=
        square_bound_of_abs_bound hvt
      _ = Cv ^ 2 * (Real.sqrt v) ^ 2 * (d ^ 2 + d ^ 3) ^ 2 := by ring
      _ = v * W := by rw [Real.sq_sqrt hv.le]; dsimp [W]; ring
  have hvs2 : vs ^ 2 ≤ v * W := by
    calc
      vs ^ 2 ≤ (Cv * Real.sqrt v * (d ^ 2 + d ^ 3)) ^ 2 :=
        square_bound_of_abs_bound hvs
      _ = Cv ^ 2 * (Real.sqrt v) ^ 2 * (d ^ 2 + d ^ 3) ^ 2 := by ring
      _ = v * W := by rw [Real.sq_sqrt hv.le]; dsimp [W]; ring
  have hB2 := square_bound_of_abs_bound hB
  have hb : |As - C| ≤ 2 * M := by
    calc
      |As - C| ≤ |As| + |C| := by
        simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le As 0 C
      _ ≤ M + M := add_le_add hAs hC
      _ = 2 * M := by ring
  have hb2 : (As - C) ^ 2 ≤ 4 * M ^ 2 := by
    nlinarith only [square_bound_of_abs_bound hb]
  have ht : (vt - v * B) ^ 2 / v ≤ 2 * W + 2 * v * M ^ 2 := by
    apply (div_le_iff₀ hv).2
    have hBv := mul_le_mul_of_nonneg_left hB2 (sq_nonneg v)
    nlinarith only [hvt2, hBv, sq_nonneg (vt + v * B)]
  have hvsdiv : vs ^ 2 / v ≤ W := (div_le_iff₀ hv).2 (by nlinarith only [hvs2])
  have hsum : (As * v + A * vs - v * C) ^ 2 ≤
      2 * (A * vs) ^ 2 + 2 * (v * (As - C)) ^ 2 := by
    nlinarith only [sq_nonneg (A * vs - v * (As - C))]
  have hsraw : (As * v + A * vs - v * C) ^ 2 / (A * v) ≤
      2 * A * W + 8 * (v / A) * M ^ 2 := by
    calc
      _ ≤ (2 * (A * vs) ^ 2 + 2 * (v * (As - C)) ^ 2) / (A * v) :=
        div_le_div_of_nonneg_right hsum (mul_pos hA hv).le
      _ = 2 * A * (vs ^ 2 / v) + 2 * (v / A) * (As - C) ^ 2 := by
        field_simp [hA.ne', hv.ne']
      _ ≤ 2 * A * W + 2 * (v / A) * (4 * M ^ 2) :=
        add_le_add
          (mul_le_mul_of_nonneg_left hvsdiv (by positivity))
          (mul_le_mul_of_nonneg_left hb2 (by positivity))
      _ = 2 * A * W + 8 * (v / A) * M ^ 2 := by ring
  have hva : v / A ≤ d ^ 5 / c := by
    apply (div_le_iff₀ hA).2
    calc
      v ≤ d ^ 6 := hvd
      _ = (d ^ 5 / c) * (c * d) := by field_simp [hc.ne']
      _ ≤ (d ^ 5 / c) * A := mul_le_mul_of_nonneg_left hAlo (by positivity)
  have hvsD : v / A ≤ D ^ 5 / c := hva.trans
    (div_le_div_of_nonneg_right (pow_le_pow_left₀ hd.le hdD 5) hc.le)
  have hvD : v ≤ D ^ 6 := hvd.trans (pow_le_pow_left₀ hd.le hdD 6)
  have hWD : W ≤ Cv ^ 2 * (D ^ 2 + D ^ 3) ^ 2 := by
    dsimp [W]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg Cv)
    apply pow_le_pow_left₀ (by positivity : 0 ≤ d ^ 2 + d ^ 3)
    exact add_le_add (pow_le_pow_left₀ hd.le hdD 2) (pow_le_pow_left₀ hd.le hdD 3)
  have hAW : 2 * A * W ≤ 2 * M * W := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hAM (by norm_num)) hW
  calc
    _ ≤ (2 * W + 2 * v * M ^ 2) + (2 * A * W + 8 * (v / A) * M ^ 2) :=
      add_le_add ht hsraw
    _ ≤ 2 * (1 + M) * W + 2 * v * M ^ 2 + 8 * (v / A) * M ^ 2 := by
      nlinarith only [hAW]
    _ ≤ 2 * (1 + M) * (Cv ^ 2 * (D ^ 2 + D ^ 3) ^ 2) +
        2 * D ^ 6 * M ^ 2 + 8 * (D ^ 5 / c) * M ^ 2 := by
      apply add_le_add
      · exact add_le_add
          (mul_le_mul_of_nonneg_left hWD (by positivity))
          (by nlinarith only [mul_le_mul_of_nonneg_right hvD (sq_nonneg M)])
      · nlinarith only [mul_le_mul_of_nonneg_right hvsD (sq_nonneg M)]
    _ = ellipticRatioConstant D c Cv M := by unfold ellipticRatioConstant; ring

theorem actual_elliptic_ratio
    {A B C v : Coord → ℝ} {p : Coord} {d D c Cv M : ℝ}
    (hAd : DifferentiableAt ℝ A p) (hvdiff : DifferentiableAt ℝ v p)
    (hd : 0 < d) (hdD : d ≤ D) (hc : 0 < c) (hCv : 0 ≤ Cv) (hM : 0 ≤ M)
    (hv : 0 < v p) (hvd : v p ≤ d ^ 6)
    (hvt : |coordPartial 0 v p| ≤ Cv * Real.sqrt (v p) * (d ^ 2 + d ^ 3))
    (hvs : |coordPartial 1 v p| ≤ Cv * Real.sqrt (v p) * (d ^ 2 + d ^ 3))
    (hAlo : c * d ≤ A p) (hAhi : |A p| ≤ M)
    (hAs : |coordPartial 1 A p| ≤ M) (hB : |B p| ≤ M) (hC : |C p| ≤ M) :
    (ellipticErrorT B v p) ^ 2 / v p + (ellipticErrorS A C v p) ^ 2 / (A p * v p) ≤
      ellipticRatioConstant D c Cv M := by
  rw [ellipticErrorT, ellipticErrorS, HessianCalculus.coordPartial_mul_at hAd hvdiff 1]
  exact elliptic_ratio_scalar hd hdD hc hCv hM hv hvd hvt hvs hAlo hAhi hAs hB hC

def ellipticCutoffDerivativeConstant (c MK X : ℝ) : ℝ :=
  2 * (3 + X + (2 * transitionDerivativeBound / c) * (MK + c))

theorem ellipticCutoffDerivativeConstant_nonneg {c MK X : ℝ}
    (hc : 0 < c) (hMK : 0 ≤ MK) (hX : 0 ≤ X) :
    0 ≤ ellipticCutoffDerivativeConstant c MK X := by
  have htheta := transitionDerivativeBound_pos.le
  unfold ellipticCutoffDerivativeConstant
  positivity

theorem ellipticWeight_partial_bound_common {b c MK X : ℝ}
    {chi K : Coord → ℝ} {p : Coord}
    (hc : 0 < c) (hd : 0 < edgeDistance b p) (hMK : 0 ≤ MK) (hX : 0 ≤ X)
    (hchi : DifferentiableAt ℝ chi p) (hK : DifferentiableAt ℝ K p)
    (hchiRange : 0 ≤ chi p ∧ chi p ≤ 1) (i : Fin 2)
    (hchii : |coordPartial i chi p| ≤ X) (hKi : |coordPartial i K p| ≤ MK) :
    |coordPartial i (ellipticWeight b c chi K) p| ≤
      ellipticCutoffDerivativeConstant c MK X * Real.sqrt (ellipticWeight b c chi K p) *
        (edgeDistance b p ^ 2 + edgeDistance b p ^ 3) := by
  let P := (2 * transitionDerivativeBound / c) * (MK + c)
  have hP : 0 ≤ P := by
    have htheta := transitionDerivativeBound_pos.le
    dsimp [P]
    positivity
  have hcompare : 3 * edgeDistance b p ^ 2 + edgeDistance b p ^ 3 * X +
      edgeDistance b p ^ 2 * P ≤
      (3 + X + P) * (edgeDistance b p ^ 2 + edgeDistance b p ^ 3) := by
    nlinarith [mul_nonneg hX (sq_nonneg (edgeDistance b p)),
      mul_nonneg hP (pow_pos hd 3).le]
  calc
    _ ≤ 2 * Real.sqrt (ellipticWeight b c chi K p) *
        (3 * edgeDistance b p ^ 2 + edgeDistance b p ^ 3 * X +
          edgeDistance b p ^ 2 * P) :=
      ellipticWeight_partial_bound hc hd hMK hchi hK hchiRange i hchii hKi
    _ ≤ 2 * Real.sqrt (ellipticWeight b c chi K p) *
        ((3 + X + P) * (edgeDistance b p ^ 2 + edgeDistance b p ^ 3)) :=
      mul_le_mul_of_nonneg_left hcompare (by positivity)
    _ = _ := by unfold ellipticCutoffDerivativeConstant; dsimp [P]; ring

theorem ellipticCutoff_actual_ratio
    {b c MK X D g0 M : ℝ} {chi K G1 B C : Coord → ℝ} {p : Coord}
    (hc : 0 < c) (hd : 0 < edgeDistance b p) (hdD : edgeDistance b p ≤ D)
    (hMK : 0 ≤ MK) (hX : 0 ≤ X) (hg0 : 0 < g0) (hM : 0 ≤ M)
    (hchi : DifferentiableAt ℝ chi p) (hK : DifferentiableAt ℝ K p)
    (hG1 : DifferentiableAt ℝ G1 p)
    (hchiRange : 0 ≤ chi p ∧ chi p ≤ 1)
    (hchii : ∀ i : Fin 2, |coordPartial i chi p| ≤ X)
    (hKi : ∀ i : Fin 2, |coordPartial i K p| ≤ MK)
    (hv : 0 < ellipticWeight b c chi K p) (hGlow : g0 ≤ G1 p)
    (hAhi : |G1 p * K p| ≤ M)
    (hAs : |coordPartial 1 (fun q => G1 q * K q) p| ≤ M)
    (hB : |B p| ≤ M) (hC : |C p| ≤ M) :
    (ellipticErrorT B (ellipticWeight b c chi K) p) ^ 2 /
        ellipticWeight b c chi K p +
      (ellipticErrorS (fun q => G1 q * K q) C (ellipticWeight b c chi K) p) ^ 2 /
        (G1 p * K p * ellipticWeight b c chi K p) ≤
      ellipticRatioConstant D (g0 * c / 2) (ellipticCutoffDerivativeConstant c MK X) M := by
  have hKlo : c / 2 * edgeDistance b p < K p :=
    ellipticWeight_pos_implies_curvature hc (sub_pos.mp hd) hv
  have hKpos : 0 < K p := (mul_pos (by positivity) hd).trans hKlo
  have hAlo : (g0 * c / 2) * edgeDistance b p ≤ G1 p * K p := by
    have hfirst := mul_le_mul_of_nonneg_left hKlo.le hg0.le
    have hsecond := mul_le_mul_of_nonneg_right hGlow hKpos.le
    nlinarith [hfirst, hsecond]
  have hvdiff : DifferentiableAt ℝ (ellipticWeight b c chi K) p := by
    unfold ellipticWeight
    have hdiffer : DifferentiableAt ℝ (edgeDistance b) p :=
      (differentiableAt_const b).sub (differentiableAt_apply (𝕜 := ℝ) 1 p)
    have hgate : DifferentiableAt ℝ (fun q => ellipticPhi c (K q / edgeDistance b q)) p :=
      ellipticGate_differentiableAt hK hd.ne'
    exact ((hdiffer.pow 6).mul (hchi.pow 2)).mul (hgate.pow 2)
  exact actual_elliptic_ratio (hG1.mul hK) hvdiff hd hdD (by positivity)
    (ellipticCutoffDerivativeConstant_nonneg hc hMK hX) hM hv
    (ellipticWeight_le_distance_six b c chi K p hchiRange)
    (ellipticWeight_partial_bound_common hc hd hMK hX hchi hK hchiRange 0 (hchii 0) (hKi 0))
    (ellipticWeight_partial_bound_common hc hd hMK hX hchi hK hchiRange 1 (hchii 1) (hKi 1))
    hAlo hAhi hAs hB hC

end SmoothLocal.Weighted

end

end OAI
