import OAI.Geometry.IsometricImmersion.Immersions.HeightCoefficientRegularity
import OAI.Geometry.IsometricImmersion.Energy.DirectedCoercivity

namespace OAI

noncomputable section
open scoped ContDiff

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry

def directedPrincipalBound (ell : ℕ) (epsilon R MAs MAt : ℝ) : ℝ :=
  ((ell : ℝ) + 1 / 2) * MAs + epsilon * R * MAt / 2

theorem directedPrincipal_abs_bound {A : Coord → ℝ} {p : Coord}
    (ell : ℕ) {epsilon R MAs MAt : ℝ} (heps : 0 ≤ epsilon)
    (ht : |p 0| ≤ R) (hAs : |coordPartial 1 A p| ≤ MAs)
    (hAt : |coordPartial 0 A p| ≤ MAt) :
    |directedPrincipal A ell epsilon p| ≤ directedPrincipalBound ell epsilon R MAs MAt := by
  have hR : 0 ≤ R := (abs_nonneg _).trans ht
  have hMAt : 0 ≤ MAt := (abs_nonneg _).trans hAt
  have hbeta : 0 ≤ (ell : ℝ) + 1 / 2 := by positivity
  have hfirst : |-((ell : ℝ) + 1 / 2) * coordPartial 1 A p| ≤ ((ell : ℝ) + 1 / 2) * MAs := by
    rw [abs_mul, abs_neg, abs_of_nonneg hbeta]
    exact mul_le_mul_of_nonneg_left hAs hbeta
  have hsecond : |epsilon * p 0 * coordPartial 0 A p / 2| ≤ epsilon * R * MAt / 2 := by
    rw [abs_div, abs_mul, abs_mul, abs_of_nonneg heps, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact div_le_div_of_nonneg_right
      (mul_le_mul (mul_le_mul_of_nonneg_left ht heps) hAt (abs_nonneg _) (mul_nonneg heps hR))
      (by norm_num)
  exact (abs_add_le _ _).trans (add_le_add hfirst hsecond)

theorem primitive_directed_farnegative_coercivity
    {B : Coord → ℝ} {R a b : ℝ} {p : Coord}
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b)) (hR : 0 < R)
    (hp : p ∈ coordinateRectangle R a b) (A C r : Coord → ℝ)
    (hA : DifferentiableAt ℝ A p) (edge lambda epsilon : ℝ) (ell : ℕ)
    (hedge : p 1 < edge) (hlambda : 0 < lambda)
    (heps : 0 ≤ epsilon) (heps1 : epsilon ≤ 1)
    (hC : C p = ((ell : ℝ) + 1) * coordPartial 1 A p + A p * r p)
    (MI MB Mr MA MAs MAt mu alpha : ℝ) (hmu : 0 < mu)
    (hIs : |coordPartial 1 (coordinatePrimitive B) p| ≤ MI)
    (hBp : |B p| ≤ MB) (hr : |r p| ≤ Mr)
    (hAp : |A p| ≤ MA) (hAs : |coordPartial 1 A p| ≤ MAs)
    (hTbudget : 2 * (MI + epsilon + epsilon * R * MB) ≤ lambda)
    (hEbudget : (MI + 1 + R * MB) / 2 + Mr ≤ lambda / 8)
    (hsmall : 4 * (R * ((ell : ℝ) * MAs + MA * Mr + MA * MI + 1)) ^ 2 *
      epsilon ^ 2 * MA ≤ 1 / 8)
    (hloss : (4 * (R * ((ell : ℝ) * MAs + MA * Mr + MA * MI + 1)) ^ 2 *
      epsilon ^ 2) / lambda ≤ mu / 4)
    (hAt : |coordPartial 0 A p| ≤ MAt)
    (halpha : 0 < alpha) (hAfar : A p ≤ -alpha)
    (hdominance : directedPrincipalBound ell epsilon R MAs MAt + mu ≤ lambda * alpha / 4)
    (x y : ℝ) :
    min (lambda / 8) (mu / 2) * directedWeight edge lambda (coordinatePrimitive B) p *
      (x ^ 2 + y ^ 2) ≤
      multiplierT B (directedM edge lambda (coordinatePrimitive B))
          (directedN edge lambda epsilon (coordinatePrimitive B)) p * x ^ 2 +
        multiplierS A C (directedM edge lambda (coordinatePrimitive B))
          (directedN edge lambda epsilon (coordinatePrimitive B)) p * y ^ 2 +
        multiplierJ A B C (directedM edge lambda (coordinatePrimitive B))
          (directedN edge lambda epsilon (coordinatePrimitive B)) p * x * y := by
  let W := directedWeight edge lambda (coordinatePrimitive B) p
  let H := weightH0 edge lambda p
  let Cj := R * ((ell : ℝ) * MAs + MA * Mr + MA * MI + 1)
  let L := 4 * Cj ^ 2 * epsilon ^ 2
  let E := (MI + 1 + R * MB) / 2 + Mr
  have hMI : 0 ≤ MI := (abs_nonneg _).trans hIs
  have hMB : 0 ≤ MB := (abs_nonneg _).trans hBp
  have hMr : 0 ≤ Mr := (abs_nonneg _).trans hr
  have hMA : 0 ≤ MA := (abs_nonneg _).trans hAp
  have hMAs : 0 ≤ MAs := (abs_nonneg _).trans hAs
  have hCj : 0 ≤ Cj := by dsimp [Cj]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hW : 0 < W := directedWeight_pos _ _ _ _ hedge
  have hlH : lambda ≤ H := by
    dsimp [H, weightH0]
    exact le_add_of_nonneg_right (div_nonneg (by norm_num) (sub_pos.mpr hedge).le)
  have hH : 0 < H := hlambda.trans_le hlH
  have hCA : |C p - coordPartial 1 A p| ≤ (ell : ℝ) * MAs + MA * Mr := by
    have he : C p - coordPartial 1 A p =
        (ell : ℝ) * coordPartial 1 A p + A p * r p := by rw [hC]; ring
    rw [he]
    calc
      _ ≤ |(ell : ℝ) * coordPartial 1 A p| + |A p * r p| := abs_add_le _ _
      _ = (ell : ℝ) * |coordPartial 1 A p| + |A p| * |r p| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg ell)]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hAs (Nat.cast_nonneg ell))
        (mul_le_mul hAp hr (abs_nonneg _) hMA)
  have hT := primitive_directedT_lower_bound hB hR hp edge lambda epsilon MI MB
    heps hedge hIs hBp hTbudget
  have hJ0 := primitive_directedJ_bound hB hR hp A C hA edge lambda epsilon
    ((ell : ℝ) * MAs + MA * Mr) MA MI heps hedge hH.le hCA hAp hIs
  have hJ : |multiplierJ A B C (directedM edge lambda (coordinatePrimitive B))
      (directedN edge lambda epsilon (coordinatePrimitive B)) p| ≤
      W * Cj * epsilon * (1 + H * |A p|) := by
    refine hJ0.trans ?_
    have hD : 0 ≤ (ell : ℝ) * MAs + MA * Mr + MA * MI := by positivity
    have hh : 0 ≤ H * |A p| := mul_nonneg hH.le (abs_nonneg _)
    have hbase : (ell : ℝ) * MAs + MA * Mr + MA * MI + H * |A p| ≤
        ((ell : ℝ) * MAs + MA * Mr + MA * MI + 1) * (1 + H * |A p|) := by
      nlinarith [mul_nonneg hD hh]
    have hm := mul_le_mul_of_nonneg_left hbase (mul_nonneg (mul_nonneg hW.le heps) hR.le)
    convert hm using 1
    dsimp only [W, H, Cj]
    ring
  have hcross := actual_normalized_cross_loss hW hH hCj heps hT hJ
  have he : |directedSResidual B r ell epsilon p| ≤ E :=
    directedSResidual_bound heps heps1 hR.le (abs_lt.mpr hp.1).le hIs hBp hr
  have hEH : E ≤ H / 8 := hEbudget.trans (by linarith)
  have hLH : L / H ≤ mu / 4 := by
    apply (div_le_iff₀ hH).2
    have hh : L ≤ (mu / 4) * lambda := (div_le_iff₀ hlambda).1 hloss
    exact hh.trans (mul_le_mul_of_nonneg_left hlH (by positivity))
  have hmargin : mu / 2 ≤ directedPrincipal A ell epsilon p - H * A p / 2 +
      A p * directedSResidual B r ell epsilon p - L * (H⁻¹ + H * (A p) ^ 2) := by
    have hn : A p ≤ 0 := hAfar.trans (by linarith)
    have hAa : alpha ≤ |A p| := by rw [abs_of_nonpos hn]; linarith
    have hprincipal : -directedPrincipalBound ell epsilon R MAs MAt ≤
        directedPrincipal A ell epsilon p :=
      (abs_le.mp (directedPrincipal_abs_bound ell heps (abs_lt.mpr hp.1).le hAs hAt)).1
    have hbudget : directedPrincipalBound ell epsilon R MAs MAt + mu ≤ H * alpha / 4 :=
      hdominance.trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hlH halpha.le) (by norm_num))
    exact normalized_negative_far_coercivity hH hL hmu hn hAp hsmall hLH he hEH
      hprincipal hAa hbudget
  exact actual_quadratic_coercivity hW hH hlambda hmu hlH hT
    (primitive_directedS_expansion hB hR hp A C r hA edge lambda epsilon ell hedge hC)
    hcross hmargin

end SmoothLocal.Weighted

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.Weighted

theorem heightChartA_negative_of_curvature
    (g : MetricField) (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ) (p : Coord)
    {cG delta : ℝ} (hcG : 0 < cG) (hdelta : 0 < delta)
    (hG : cG ≤ heightChartG1 g z Y p)
    (hK : capPullback Y (gaussianCurvature g) p ≤ -delta) :
    heightChartA g z Y p ≤ -(cG * delta) := by
  rw [heightChartA_eq]
  have hGpos : 0 ≤ heightChartG1 g z Y p := (hcG.trans_le hG).le
  calc
    _ ≤ heightChartG1 g z Y p * (-delta) := mul_le_mul_of_nonneg_left hK hGpos
    _ ≤ cG * (-delta) := mul_le_mul_of_nonpos_right hG (by linarith)
    _ = _ := by ring

end SmoothLocal.Flow

end

end OAI
