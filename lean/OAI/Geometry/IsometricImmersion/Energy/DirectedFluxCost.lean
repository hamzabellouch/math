import OAI.Geometry.IsometricImmersion.Caps.CapEllipticOverlap

namespace OAI

noncomputable section
open Set
open scoped ContDiff

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry

theorem scalarQuadratic_abs_bound {alpha beta gamma a b c x y : ℝ}
    (ha : |alpha| ≤ a) (hb : |beta| ≤ b) (hc : |gamma| ≤ c) :
    |alpha*x^2 + beta*(x*y) + gamma*y^2| ≤ (a+b+c)*(x^2+y^2) := by
  have ha0 := (abs_nonneg alpha).trans ha
  have hb0 := (abs_nonneg beta).trans hb
  have hc0 := (abs_nonneg gamma).trans hc
  have hE : 0 ≤ x^2+y^2 := add_nonneg (sq_nonneg x) (sq_nonneg y)
  have hxy : |x*y| ≤ x^2+y^2 := by
    have hh := weighted_young 1 x y (by norm_num)
    norm_num only [one_mul, div_one] at hh
    linarith
  have hxa : |alpha| *x^2 ≤ a*(x^2+y^2) :=
    (mul_le_mul_of_nonneg_right ha (sq_nonneg x)).trans
      (mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg y]) ha0)
  have hxb : |beta| *|x*y| ≤ b*(x^2+y^2) := mul_le_mul hb hxy (abs_nonneg _) hb0
  have hxc : |gamma| *y^2 ≤ c*(x^2+y^2) :=
    (mul_le_mul_of_nonneg_right hc (sq_nonneg y)).trans
      (mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg x]) hc0)
  calc
    _ ≤ |alpha*x^2 + beta*(x*y)| + |gamma*y^2| := abs_add_le _ _
    _ ≤ (|alpha*x^2| + |beta*(x*y)|) + |gamma*y^2| :=
      add_le_add (abs_add_le _ _) le_rfl
    _ = |alpha| *x^2 + |beta| *|x*y| + |gamma| *y^2 := by
      rw [abs_mul alpha, abs_mul beta, abs_mul gamma, abs_of_nonneg (sq_nonneg x),
        abs_of_nonneg (sq_nonneg y)]
    _ ≤ a*(x^2+y^2)+b*(x^2+y^2)+c*(x^2+y^2) := add_le_add (add_le_add hxa hxb) hxc
    _ = _ := by ring

theorem directedFlux_scalar_bound {eta A M x y : ℝ}
    (he : |eta| ≤ 2) (hA : |A| ≤ M) :
    |-x*y + eta*x^2/2 - eta*A*y^2/2| ≤ 3*(M+1)*(x^2+y^2) ∧
    |-A*y^2/2 + eta*A*x*y + x^2/2| ≤ 3*(M+1)*(x^2+y^2) := by
  have hM : 0 ≤ M := (abs_nonneg A).trans hA
  have hetaA : |eta*A| ≤ 2*M := by
    rw [abs_mul]
    exact mul_le_mul he hA (abs_nonneg _) (by norm_num)
  have hehalf : |eta/2| ≤ (1 : ℝ) := by rw [abs_div]; norm_num; linarith
  have hAhalf : |-(A/2)| ≤ M := by rw [abs_neg, abs_div]; norm_num; linarith
  have hetaAhalf : |-(eta*A/2)| ≤ M := by
    calc
      _ = |eta*A| / 2 := by rw [abs_neg, abs_div]; norm_num
      _ ≤ M := by linarith only [hetaA]
  have hE : 0 ≤ x^2+y^2 := add_nonneg (sq_nonneg x) (sq_nonneg y)
  constructor
  · have hh := scalarQuadratic_abs_bound (x := x) (y := y) hehalf
      (show |(-1 : ℝ)| ≤ 1 by norm_num) hetaAhalf
    have heq : -x*y + eta*x^2/2 - eta*A*y^2/2 =
        (eta/2)*x^2 + (-1)*(x*y) + (-(eta*A/2))*y^2 := by ring
    rw [heq]
    exact hh.trans (mul_le_mul_of_nonneg_right (by linarith) hE)
  · have hh := scalarQuadratic_abs_bound (x := x) (y := y)
      (show |(1/2 : ℝ)| ≤ 1 by norm_num) hetaA hAhalf
    have heq : -A*y^2/2 + eta*A*x*y + x^2/2 =
        (1/2)*x^2 + (eta*A)*(x*y) + (-(A/2))*y^2 := by ring
    rw [heq]
    exact hh.trans (mul_le_mul_of_nonneg_right (by linarith) hE)

theorem directedWeight_le_seven {b lambda D S MI : ℝ} {I : Coord → ℝ} {p : Coord}
    (hlambda : 0 ≤ lambda) (hd : 0 ≤ edgeDistance b p) (hdD : edgeDistance b p ≤ D)
    (hs : |p 1| ≤ S) (hI : |I p| ≤ MI) :
    directedWeight b lambda I p ≤ D * Real.exp (lambda*S+MI) * edgeDistance b p^7 := by
  have hphase : weightPhase lambda I p ≤ lambda*S+MI := by
    have hs' : -p 1 ≤ S := by linarith [(abs_le.mp hs).1]
    have hm := mul_le_mul_of_nonneg_left hs' hlambda
    unfold weightPhase
    linarith [(abs_le.mp hI).2]
  have he := Real.exp_le_exp.mpr hphase
  have hprod := mul_le_mul hdD he (Real.exp_pos _).le (hd.trans hdD)
  have hh := mul_le_mul_of_nonneg_left hprod (pow_nonneg hd 7)
  calc
    _ = edgeDistance b p^7 * (edgeDistance b p * Real.exp (weightPhase lambda I p)) := by
      unfold directedWeight
      ring
    _ ≤ edgeDistance b p^7 * (D*Real.exp (lambda*S+MI)) := hh
    _ = _ := by ring

theorem directedCutoffError_abs_le_seven
    {A chi I u : Coord → ℝ} {p : Coord} {b lambda epsilon D S MI M X : ℝ}
    (hlambda : 0 ≤ lambda) (heps : 0 ≤ epsilon) (heps1 : epsilon ≤ 1)
    (ht : |p 0| ≤ 2) (hd : 0 ≤ edgeDistance b p) (hdD : edgeDistance b p ≤ D)
    (hs : |p 1| ≤ S) (hI : |I p| ≤ MI) (hA : |A p| ≤ M)
    (hchi : ∀ i : Fin 2, |coordPartial i chi p| ≤ X) :
    |directedCutoffError A chi I u b lambda epsilon p| ≤
      (6*X*D*Real.exp (lambda*S+MI)*(M+1)) * weightedGradient b u p := by
  have hM : 0 ≤ M := (abs_nonneg _).trans hA
  have hX : 0 ≤ X := (abs_nonneg _).trans (hchi 0)
  have hD : 0 ≤ D := hd.trans hdD
  have hW : 0 ≤ directedWeight b lambda I p := by unfold directedWeight; positivity
  have he : |epsilon*p 0| ≤ (2 : ℝ) := by
    rw [abs_mul, abs_of_nonneg heps]
    exact (mul_le_mul_of_nonneg_left ht heps).trans (by linarith)
  obtain ⟨hT, hS⟩ := directedFlux_scalar_bound (x := coordPartial 0 u p)
    (y := coordPartial 1 u p) he hA
  obtain ⟨hFt, hFs⟩ := directed_flux_factor A u I b lambda epsilon p
  have hT' : |multiplierFluxT A (directedM b lambda I) (directedN b lambda epsilon I) u p| ≤
      directedWeight b lambda I p * (3*(M+1)*((coordPartial 0 u p)^2+(coordPartial 1 u p)^2)) := by
    rw [hFt, abs_mul, abs_of_nonneg hW]
    exact mul_le_mul_of_nonneg_left hT hW
  have hS' : |multiplierFluxS A (directedM b lambda I) (directedN b lambda epsilon I) u p| ≤
      directedWeight b lambda I p * (3*(M+1)*((coordPartial 0 u p)^2+(coordPartial 1 u p)^2)) := by
    rw [hFs, abs_mul, abs_of_nonneg hW]
    exact mul_le_mul_of_nonneg_left hS hW
  have hbound : 0 ≤ directedWeight b lambda I p *
      (3*(M+1)*((coordPartial 0 u p)^2+(coordPartial 1 u p)^2)) := by positivity
  have hbase : |directedCutoffError A chi I u b lambda epsilon p| ≤
      6*X*(M+1)*directedWeight b lambda I p*((coordPartial 0 u p)^2+(coordPartial 1 u p)^2) := by
    unfold directedCutoffError multiplierCutoffError
    calc
      _ ≤ |coordPartial 0 chi p * multiplierFluxT A (directedM b lambda I) (directedN b lambda epsilon I) u p| +
          |coordPartial 1 chi p * multiplierFluxS A (directedM b lambda I) (directedN b lambda epsilon I) u p| :=
        abs_add_le _ _
      _ ≤ X*(directedWeight b lambda I p*(3*(M+1)*((coordPartial 0 u p)^2+(coordPartial 1 u p)^2))) +
          X*(directedWeight b lambda I p*(3*(M+1)*((coordPartial 0 u p)^2+(coordPartial 1 u p)^2))) := by
        simp only [abs_mul]
        exact add_le_add (mul_le_mul (hchi 0) hT' (abs_nonneg _) hX)
          (mul_le_mul (hchi 1) hS' (abs_nonneg _) hX)
      _ = _ := by ring
  have hWbound := directedWeight_le_seven hlambda hd hdD hs hI
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hWbound
    (show 0 ≤ 6*X*(M+1) by positivity))
      (add_nonneg (sq_nonneg (coordPartial 0 u p)) (sq_nonneg (coordPartial 1 u p)))
  exact hbase.trans (by
    convert hh using 1
    unfold weightedGradient
    ring)

def capSpatialDerivativeConstant (L R A : ℝ) : ℝ :=
  threeEdgeDerivativeConstant (capOuterEdge L) (capInnerEdge L)
    (-capInnerEdge (-R)) (-capOuterEdge (-R)) (capOuterEdge A) (capInnerEdge A)

theorem capSpatialCutoff_partial_uniform {L R A : ℝ}
    (hL : -2 < L) (hR : R < 2) (hA : -2 < A) (p : Coord) (i : Fin 2) :
    |coordPartial i (capSpatialCutoff L R A) p| ≤ capSpatialDerivativeConstant L R A := by
  exact threeEdgeCutoff_partial_common (capEdges_bounds hL).2.1
    (neg_lt_neg (capEdges_bounds (x := -R) (by linarith)).2.1) (capEdges_bounds hA).2.1 p i

end SmoothLocal.Weighted

end

end OAI
