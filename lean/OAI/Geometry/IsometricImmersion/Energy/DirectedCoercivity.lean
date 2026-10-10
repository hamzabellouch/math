import OAI.Geometry.IsometricImmersion.Energy.DirectedBounds

namespace OAI

noncomputable section
open scoped ContDiff

namespace SmoothLocal.Weighted

open SmoothLocal.Geometry

def directedPrincipal (A : Coord → ℝ) (ell : ℕ) (epsilon : ℝ) (p : Coord) : ℝ :=
  -((ell : ℝ) + 1 / 2) * coordPartial 1 A p + epsilon * p 0 * coordPartial 0 A p / 2

def directedSResidual (B r : Coord → ℝ) (_ : ℕ) (epsilon : ℝ) (p : Coord) : ℝ :=
  (coordPartial 1 (coordinatePrimitive B) p + epsilon + epsilon * p 0 * B p) / 2 - r p

theorem primitive_directedS_expansion
    {B : Coord → ℝ} {R a b : ℝ} {p : Coord}
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b)) (hR : 0 < R)
    (hp : p ∈ coordinateRectangle R a b) (A C r : Coord → ℝ)
    (hA : DifferentiableAt ℝ A p) (edge lambda epsilon : ℝ) (ell : ℕ)
    (hedge : p 1 < edge)
    (hC : C p = ((ell : ℝ) + 1) * coordPartial 1 A p + A p * r p) :
    multiplierS A C (directedM edge lambda (coordinatePrimitive B))
      (directedN edge lambda epsilon (coordinatePrimitive B)) p =
      directedWeight edge lambda (coordinatePrimitive B) p *
        (directedPrincipal A ell epsilon p - weightH0 edge lambda p * A p / 2 +
          A p * directedSResidual B r ell epsilon p) := by
  have hI : DifferentiableAt ℝ (coordinatePrimitive B) p :=
    ((coordinatePrimitive_contDiffOn hB).contDiffAt
      ((coordinateRectangle_isOpen R a b).mem_nhds hp)).differentiableAt (by simp)
  rw [directedS_transverse_expansion A B C edge lambda epsilon ell (r p) hA hI
    (sub_pos.mpr hedge).ne' hC, coordinatePrimitive_partial_t hB hR hp]
  rfl

theorem directedSResidual_bound {B r : Coord → ℝ} {ell : ℕ} {epsilon R MI MB Mr : ℝ}
    {p : Coord} (heps : 0 ≤ epsilon) (heps1 : epsilon ≤ 1) (hR : 0 ≤ R)
    (ht : |p 0| ≤ R) (hI : |coordPartial 1 (coordinatePrimitive B) p| ≤ MI)
    (hB : |B p| ≤ MB) (hr : |r p| ≤ Mr) :
    |directedSResidual B r ell epsilon p| ≤ (MI + 1 + R * MB) / 2 + Mr := by
  have hMB : 0 ≤ MB := (abs_nonneg _).trans hB
  have hprod : |epsilon * p 0 * B p| ≤ R * MB := by
    rw [abs_mul, abs_mul, abs_of_nonneg heps]
    have het : epsilon * |p 0| ≤ R :=
      (mul_le_mul_of_nonneg_left ht heps).trans (by nlinarith)
    exact (mul_le_mul het hB (abs_nonneg _) hR)
  unfold directedSResidual
  calc
    _ ≤ |(coordPartial 1 (coordinatePrimitive B) p + epsilon + epsilon * p 0 * B p) / 2| +
        |r p| := abs_sub _ _
    _ = |coordPartial 1 (coordinatePrimitive B) p + epsilon + epsilon * p 0 * B p| / 2 +
        |r p| := by rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ ((|coordPartial 1 (coordinatePrimitive B) p| + |epsilon|) +
        |epsilon * p 0 * B p|) / 2 + |r p| := by
      have hsum : |coordPartial 1 (coordinatePrimitive B) p + epsilon + epsilon * p 0 * B p| ≤
          (|coordPartial 1 (coordinatePrimitive B) p| + |epsilon|) + |epsilon * p 0 * B p| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      exact add_le_add (div_le_div_of_nonneg_right hsum (by norm_num : (0 : ℝ) ≤ 2)) le_rfl
    _ ≤ (MI + 1 + R * MB) / 2 + Mr := by rw [abs_of_nonneg heps]; linarith

theorem directedPrincipal_product {G K : Coord → ℝ} {p : Coord}
    (hG : DifferentiableAt ℝ G p) (hK : DifferentiableAt ℝ K p)
    (hGne : G p ≠ 0) (ell : ℕ) (epsilon : ℝ) :
    directedPrincipal (fun q => G q * K q) ell epsilon p =
      G p * (-((ell : ℝ) + 1 / 2) * coordPartial 1 K p +
        epsilon * p 0 * coordPartial 0 K p / 2) + G p * K p *
      ((-((ell : ℝ) + 1 / 2) * coordPartial 1 G p +
        epsilon * p 0 * coordPartial 0 G p / 2) / G p) := by
  unfold directedPrincipal
  rw [HessianCalculus.coordPartial_mul_at hG hK 1,
    HessianCalculus.coordPartial_mul_at hG hK 0]
  field_simp [hGne]
  ring

theorem directed_geometric_expression
    {G K : Coord → ℝ} {p : Coord} {rho Ky kappa q epsilon : ℝ}
    (ell : ℕ) (hrho : rho ≠ 0)
    (hKs : coordPartial 1 K p = Ky / rho)
    (hKt : coordPartial 0 K p = 2 * kappa * p 0 - q * Ky) :
    G p * (-((ell : ℝ) + 1 / 2) * coordPartial 1 K p +
      epsilon * p 0 * coordPartial 0 K p / 2) =
      G p * (-(((ell : ℝ) + 1 / 2) / rho + epsilon * p 0 * q / 2) * Ky +
        epsilon * kappa * (p 0) ^ 2) := by
  rw [hKs, hKt]
  field_simp [hrho]
  ring

theorem normalized_loss_budget {H A MA L mu : ℝ}
    (hH : 0 < H) (hL : 0 ≤ L) (hA : |A| ≤ MA)
    (hsmall : L * MA ≤ 1 / 8) (hloss : L / H ≤ mu / 4) :
    L * (H⁻¹ + H * A ^ 2) ≤ mu / 4 + H * |A| / 8 := by
  have hLA : L * |A| ≤ 1 / 8 :=
    (mul_le_mul_of_nonneg_left hA hL).trans hsmall
  have hLA2 : L * A ^ 2 ≤ |A| / 8 := by
    have hm := mul_le_mul_of_nonneg_right hLA (abs_nonneg A)
    nlinarith [sq_abs A]
  have hmul := mul_le_mul_of_nonneg_left hLA2 hH.le
  calc
    _ = L / H + H * (L * A ^ 2) := by ring
    _ ≤ mu / 4 + H * (|A| / 8) := add_le_add hloss hmul
    _ = _ := by ring

theorem residual_abs_error_bound {A e E H : ℝ}
    (he : |e| ≤ E) (hEH : E ≤ H / 8) :
    -(H * |A| / 8) ≤ A * e := by
  have habs : |A * e| ≤ H * |A| / 8 := by
    rw [abs_mul]
    have h := mul_le_mul_of_nonneg_left (he.trans hEH) (abs_nonneg A)
    nlinarith only [h]
  exact (abs_le.mp habs).1

theorem normalized_negative_near_coercivity {H A MA L mu Q e E : ℝ}
    (hH : 0 < H) (hL : 0 ≤ L) (hmu : 0 < mu) (hA : A ≤ 0) (hAM : |A| ≤ MA)
    (hsmall : L * MA ≤ 1 / 8) (hloss : L / H ≤ mu / 4)
    (he : |e| ≤ E) (hEH : E ≤ H / 8) (hQ : mu ≤ Q) :
    mu / 2 + H * |A| / 4 ≤ Q - H * A / 2 + A * e - L * (H⁻¹ + H * A ^ 2) := by
  have hcross := normalized_loss_budget hH hL hAM hsmall hloss
  have herr := residual_abs_error_bound (A := A) he hEH
  rw [abs_of_nonpos hA] at *
  nlinarith

theorem normalized_positive_strip_coercivity {H A MA L mu Q e E : ℝ}
    (hH : 0 < H) (hL : 0 ≤ L) (_ : 0 < mu) (hA : 0 ≤ A) (hAM : |A| ≤ MA)
    (hsmall : L * MA ≤ 1 / 8) (hloss : L / H ≤ mu / 4)
    (he : |e| ≤ E) (hEH : E ≤ H / 8) (hQ : mu ≤ Q) (hstrip : H * A ≤ mu / 3) :
    mu / 2 ≤ Q - H * A / 2 + A * e - L * (H⁻¹ + H * A ^ 2) := by
  have hcross := normalized_loss_budget hH hL hAM hsmall hloss
  have herr := residual_abs_error_bound (A := A) he hEH
  rw [abs_of_nonneg hA] at *
  nlinarith

theorem normalized_negative_far_coercivity {H A MA L mu Q e E alpha Pmax : ℝ}
    (hH : 0 < H) (hL : 0 ≤ L) (hmu : 0 < mu) (hA : A ≤ 0) (hAM : |A| ≤ MA)
    (hsmall : L * MA ≤ 1 / 8) (hloss : L / H ≤ mu / 4)
    (he : |e| ≤ E) (hEH : E ≤ H / 8) (hQ : -Pmax ≤ Q)
    (halpha : alpha ≤ |A|) (hbudget : Pmax + mu ≤ H * alpha / 4) :
    mu / 2 ≤ Q - H * A / 2 + A * e - L * (H⁻¹ + H * A ^ 2) := by
  have hcross := normalized_loss_budget hH hL hAM hsmall hloss
  have herr := residual_abs_error_bound (A := A) he hEH
  have hmargin : Pmax + mu ≤ H * |A| / 4 := by
    have hm := mul_le_mul_of_nonneg_left halpha hH.le
    nlinarith
  rw [abs_of_nonpos hA] at *
  nlinarith

theorem actual_quadratic_coercivity {T S J W H lambda mu Q e A L x y : ℝ}
    (hW : 0 < W) (hH : 0 < H) (_ : 0 < lambda) (_ : 0 < mu)
    (hlH : lambda ≤ H) (hT : W * H / 4 ≤ T)
    (hS : S = W * (Q - H * A / 2 + A * e))
    (hcross : J ^ 2 / (2 * T * W) ≤ L * (H⁻¹ + H * A ^ 2))
    (hmargin : mu / 2 ≤ Q - H * A / 2 + A * e - L * (H⁻¹ + H * A ^ 2)) :
    min (lambda / 8) (mu / 2) * W * (x ^ 2 + y ^ 2) ≤ T * x ^ 2 + S * y ^ 2 + J * x * y := by
  have hTpos : 0 < T := (show 0 < W * H / 4 by positivity).trans_le hT
  have hcross' : J ^ 2 / (2 * T) ≤ W * (L * (H⁻¹ + H * A ^ 2)) := by
    have hm := mul_le_mul_of_nonneg_right hcross hW.le
    have he : J ^ 2 / (2 * T * W) * W = J ^ 2 / (2 * T) := by
      field_simp [hTpos.ne', hW.ne']
    rw [he] at hm
    nlinarith only [hm]
  have hSlo : mu / 2 * W ≤ S - J ^ 2 / (2 * T) := by
    have hm := mul_le_mul_of_nonneg_left hmargin hW.le
    rw [hS]
    nlinarith only [hm, hcross']
  have hTlo : lambda / 8 * W ≤ T / 2 := by
    have hm := mul_le_mul_of_nonneg_left hlH hW.le
    nlinarith only [hm, hT]
  have hxlo : min (lambda / 8) (mu / 2) * W ≤ T / 2 :=
    (mul_le_mul_of_nonneg_right (min_le_left _ _) hW.le).trans hTlo
  have hylo : min (lambda / 8) (mu / 2) * W ≤ S - J ^ 2 / (2 * T) :=
    (mul_le_mul_of_nonneg_right (min_le_right _ _) hW.le).trans hSlo
  have hx := mul_le_mul_of_nonneg_right hxlo (sq_nonneg x)
  have hy := mul_le_mul_of_nonneg_right hylo (sq_nonneg y)
  have hq := quadratic_cross_absorption (S := S) (J := J) (u := x) (v := y) hTpos
  nlinarith only [hx, hy, hq]

theorem actual_normalized_cross_loss {T J W H A Cj epsilon : ℝ}
    (hW : 0 < W) (hH : 0 < H) (hCj : 0 ≤ Cj) (heps : 0 ≤ epsilon)
    (hT : W * H / 4 ≤ T)
    (hJ : |J| ≤ W * Cj * epsilon * (1 + H * |A|)) :
    J ^ 2 / (2 * T * W) ≤ 4 * Cj ^ 2 * epsilon ^ 2 * (H⁻¹ + H * A ^ 2) := by
  have hh := cross_loss_bound hW hH hCj heps hT hJ
  have hTpos : 0 < T := (show 0 < W * H / 4 by positivity).trans_le hT
  have he : J ^ 2 / (2 * T * W) = (J ^ 2 / (T * W)) / 2 := by
    field_simp [hTpos.ne', hW.ne']
  rw [he]
  nlinarith only [hh]

theorem primitive_directed_near_coercivity
    {B : Coord → ℝ} {R a b : ℝ} {p : Coord}
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b)) (hR : 0 < R)
    (hp : p ∈ coordinateRectangle R a b) (A C r : Coord → ℝ)
    (hA : DifferentiableAt ℝ A p) (edge lambda epsilon : ℝ) (ell : ℕ)
    (hedge : p 1 < edge) (hlambda : 0 < lambda)
    (heps : 0 ≤ epsilon) (heps1 : epsilon ≤ 1)
    (hC : C p = ((ell : ℝ) + 1) * coordPartial 1 A p + A p * r p)
    (MI MB Mr MA MAs mu : ℝ) (hmu : 0 < mu)
    (hIs : |coordPartial 1 (coordinatePrimitive B) p| ≤ MI)
    (hBp : |B p| ≤ MB) (hr : |r p| ≤ Mr)
    (hAp : |A p| ≤ MA) (hAs : |coordPartial 1 A p| ≤ MAs)
    (hTbudget : 2 * (MI + epsilon + epsilon * R * MB) ≤ lambda)
    (hEbudget : (MI + 1 + R * MB) / 2 + Mr ≤ lambda / 8)
    (hsmall : 4 * (R * ((ell : ℝ) * MAs + MA * Mr + MA * MI + 1)) ^ 2 *
      epsilon ^ 2 * MA ≤ 1 / 8)
    (hloss : (4 * (R * ((ell : ℝ) * MAs + MA * Mr + MA * MI + 1)) ^ 2 *
      epsilon ^ 2) / lambda ≤ mu / 4)
    (hprincipal : mu ≤ directedPrincipal A ell epsilon p)
    (hstrip : 0 < A p → weightH0 edge lambda p * A p ≤ mu / 3)
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
    by_cases hn : A p ≤ 0
    · have hh := normalized_negative_near_coercivity hH hL hmu hn hAp hsmall hLH he hEH hprincipal
      have hbonus : 0 ≤ H * |A p| / 4 := by positivity
      linarith
    · exact normalized_positive_strip_coercivity hH hL hmu (lt_of_not_ge hn).le hAp
        hsmall hLH he hEH hprincipal (hstrip (lt_of_not_ge hn))
  exact actual_quadratic_coercivity hW hH hlambda hmu hlH hT
    (primitive_directedS_expansion hB hR hp A C r hA edge lambda epsilon ell hedge hC)
    hcross hmargin

end SmoothLocal.Weighted

end

end OAI
