import OAI.Geometry.SurfaceImmersion.Correction.JetPolynomialOperations
import OAI.Geometry.SurfaceImmersion.Correction.LocalPeriodicCorrector

namespace OAI

/-! Polynomial construction for every component of the complete periodic
corrector. Only the transverse derivative increases the highest jet order. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open PeriodicCorrector CovarianceCorrector

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

def spanCoefficient (Y C : LowJet → E) (L : E →L[ℝ] ℝ) (b : ℝ × ℝ) : LowJet × ℝ → ℝ :=
  fun z => L (spanSolve (Y z.1) (C z.1) b)

def metricCoefficient (Y C X₀ : LowJet → E) (V : LowJet → C(Period, E))
    (b : ℝ × ℝ) : LowJet × ℝ → ℝ :=
  fun z => inner ℝ (X₀ z.1 + V z.1 (z.2 : Period)) (spanSolve (Y z.1) (C z.1) b)

namespace Expression

def spanTerm (Y C : LowJet → E) (L : E →L[ℝ] ℝ) (H K : Expression) : Expression :=
  Expression.add ((Expression.coeff (spanCoefficient Y C L (1, 0))).mul H)
    ((Expression.coeff (spanCoefficient Y C L (0, 1))).mul K)

def angularSource (Y C X₀ : LowJet → E) (V : LowJet → C(Period, E))
    (h K e : Expression) : Expression :=
  e.sub (Expression.add ((Expression.coeff (metricCoefficient Y C X₀ V (1, 0))).mul h)
    ((Expression.coeff (metricCoefficient Y C X₀ V (0, 1))).mul K.angle)).fluct

def fullComponent (Y C X₀ : LowJet → E) (V : LowJet → C(Period, E))
    (q : LowJet → ℝ) (L : E →L[ℝ] ℝ) (v : Fin 2) (h j e : Expression) : Expression :=
  let H := h.primitive
  let K := (H.slow v).sub j
  Expression.add (spanTerm Y C L H K) ((angularSource Y C X₀ V h K e).covariance V q L).primitive

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma smoothCoeffs_spanTerm {O : Set LowJet} {Y C : LowJet → E}
    (hY : ContDiffOn ℝ ∞ Y O) (hC : ContDiffOn ℝ ∞ C O)
    (hd : ∀ Q ∈ O, gramDet (Y Q) (C Q) ≠ 0) (L : E →L[ℝ] ℝ)
    {H K : Expression} (hH : H.SmoothCoeffs O) (hK : K.SmoothCoeffs O) :
    (spanTerm Y C L H K).SmoothCoeffs O := by
  have hb (b : ℝ × ℝ) : ContDiffOn ℝ ∞ (spanCoefficient Y C L b) (O ×ˢ Set.univ) :=
    (L.contDiff.comp_contDiffOn (contDiffOn_spanSolve hY hC contDiffOn_const hd)).comp
      contDiffOn_fst (fun _ hz => hz.1)
  exact ⟨smoothCoeffs_mul (hb (1, 0)) hH, smoothCoeffs_mul (hb (0, 1)) hK⟩

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma smoothCoeffs_angularSource {O : Set LowJet} (hO : IsOpen O)
    {Y C X₀ : LowJet → E} {V : LowJet → C(Period, E)}
    (hY : ContDiffOn ℝ ∞ Y O) (hC : ContDiffOn ℝ ∞ C O)
    (hX : ContDiffOn ℝ ∞ X₀ O)
    (hV : ContDiffOn ℝ ∞ (fun z : LowJet × ℝ => V z.1 (z.2 : Period)) (O ×ˢ Set.univ))
    (hd : ∀ Q ∈ O, gramDet (Y Q) (C Q) ≠ 0)
    {h K e : Expression} (hh : h.SmoothCoeffs O) (hK : K.SmoothCoeffs O)
    (he : e.SmoothCoeffs O) : (angularSource Y C X₀ V h K e).SmoothCoeffs O := by
  have hb (b : ℝ × ℝ) : ContDiffOn ℝ ∞ (metricCoefficient Y C X₀ V b) (O ×ˢ Set.univ) :=
    ((hX.comp contDiffOn_fst (fun _ hz => hz.1)).add hV).inner ℝ
      ((contDiffOn_spanSolve hY hC contDiffOn_const hd).comp contDiffOn_fst (fun _ hz => hz.1))
  exact smoothCoeffs_sub he (smoothCoeffs_fluct hO
    ⟨smoothCoeffs_mul (hb (1, 0)) hh, smoothCoeffs_mul (hb (0, 1)) (smoothCoeffs_angle hO hK)⟩)

lemma smoothCoeffs_fullComponent {O : Set LowJet} (hO : IsOpen O)
    {Y C X₀ : LowJet → E} {V : LowJet → C(Period, E)} {q : LowJet → ℝ}
    (hY : ContDiffOn ℝ ∞ Y O) (hC : ContDiffOn ℝ ∞ C O) (hX : ContDiffOn ℝ ∞ X₀ O)
    (hV : ContDiffOn ℝ ∞ (fun z : LowJet × ℝ => V z.1 (z.2 : Period)) (O ×ˢ Set.univ))
    (hd : ∀ Q ∈ O, gramDet (Y Q) (C Q) ≠ 0)
    (hq : ContDiffOn ℝ ∞ q O) (hqp : ∀ Q ∈ O, 0 < q Q)
    (hcircle : ∀ Q ∈ O, ∀ t, inner ℝ (V Q t) (V Q t) = q Q)
    (L : E →L[ℝ] ℝ) (v : Fin 2) {h j e : Expression}
    (hh : h.SmoothCoeffs O) (hj : j.SmoothCoeffs O) (he : e.SmoothCoeffs O) :
    (fullComponent Y C X₀ V q L v h j e).SmoothCoeffs O := by
  have hH := smoothCoeffs_primitive hO hh
  have hK := smoothCoeffs_sub (smoothCoeffs_slow hO v hH) hj
  exact ⟨smoothCoeffs_spanTerm hY hC hd L hH hK,
    smoothCoeffs_primitive hO (smoothCoeffs_covariance hO hV hq hqp hcircle L
      (smoothCoeffs_angularSource hO hY hC hX hV hd hh hK he))⟩

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma order_spanTerm_le (Y C : LowJet → E) (L : E →L[ℝ] ℝ) (H K : Expression) :
    (spanTerm Y C L H K).order ≤ max 2 (max H.order K.order) := by
  exact max_le ((order_mul_le _ _).trans (by simp only [order]; omega))
    ((order_mul_le _ _).trans (by simp only [order]; omega))

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma loss_spanTerm_le (Y C : LowJet → E) (L : E →L[ℝ] ℝ) (H K : Expression) :
    (spanTerm Y C L H K).loss ≤ max H.loss K.loss := by
  exact max_le ((loss_mul_le _ _).trans (by simp only [loss, zero_add]; omega))
    ((loss_mul_le _ _).trans (by simp only [loss, zero_add]; omega))

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma order_angularSource_le (Y C X₀ : LowJet → E) (V : LowJet → C(Period, E))
    (h K e : Expression) :
    (angularSource Y C X₀ V h K e).order ≤ max 2 (max h.order (max K.order e.order)) := by
  unfold angularSource
  rw [order_sub, order_fluct]
  exact max_le (by omega) (max_le
    ((order_mul_le _ _).trans (by simp only [order]; omega))
    ((order_mul_le _ _).trans (by simp only [order, order_angle]; omega)))

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma loss_angularSource_le (Y C X₀ : LowJet → E) (V : LowJet → C(Period, E))
    (h K e : Expression) :
    (angularSource Y C X₀ V h K e).loss ≤ max h.loss (max K.loss e.loss) := by
  unfold angularSource
  rw [loss_sub, loss_fluct]
  exact max_le (by omega) (max_le
    ((loss_mul_le _ _).trans (by simp only [loss, zero_add]; omega))
    ((loss_mul_le _ _).trans (by simp only [loss, zero_add, loss_angle]; omega)))

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- One full periodic solve raises the jet order and scale loss by at most one. -/
theorem fullComponent_bounds (Y C X₀ : LowJet → E) (V : LowJet → C(Period, E))
    (q : LowJet → ℝ) (L : E →L[ℝ] ℝ) (v : Fin 2) (h j e : Expression)
    (N R : ℕ) (hN : 2 ≤ N) (hh : h.order ≤ N) (hj : j.order ≤ N) (he : e.order ≤ N)
    (lh : h.loss ≤ R) (lj : j.loss ≤ R) (le : e.loss ≤ R) :
    (fullComponent Y C X₀ V q L v h j e).order ≤ N + 1 ∧
      (fullComponent Y C X₀ V q L v h j e).loss ≤ R + 1 := by
  have ho := order_slow_le v h.primitive
  have hl := loss_slow_le v h.primitive
  have hos := order_spanTerm_le Y C L h.primitive ((h.primitive.slow v).sub j)
  have hls := loss_spanTerm_le Y C L h.primitive ((h.primitive.slow v).sub j)
  have hor := order_angularSource_le Y C X₀ V h ((h.primitive.slow v).sub j) e
  have hlr := loss_angularSource_le Y C X₀ V h ((h.primitive.slow v).sub j) e
  simp only [order_primitive, order_sub, loss_primitive, loss_sub] at ho hl hos hls hor hlr
  constructor
  · change max (spanTerm Y C L h.primitive ((h.primitive.slow v).sub j)).order _ ≤ _
    rw [order_primitive, order_covariance]
    omega
  · change max (spanTerm Y C L h.primitive ((h.primitive.slow v).sub j)).loss _ ≤ _
    rw [loss_primitive, loss_covariance]
    omega

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
