import OAI.Geometry.SurfaceImmersion.Correction.JetPolynomialDerivative

namespace OAI

/-! Coordinate derivatives in a second chart, expressed by finite jet
polynomials in the first chart. Only the surface and four-space dimensions
used in the primitive construction are considered. -/
noncomputable section
open Set
open scoped ContDiff BigOperators Topology
namespace ClosedSurfaceR4.JetPolynomial

/-- The position stored in a positional two-jet. -/
def lowPosition : LowJet →L[ℝ] Base :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (.inl i))

@[simp] lemma lowPosition_lowJet (G : Base → Space) (x : Base) :
    lowPosition (lowJet G x) = x := rfl

def inverseCoordinateCoefficient (T S : Base → Base) (i k : Fin 2) : LowJet × ℝ → ℝ :=
  fun z => (fderiv ℝ S (T (lowPosition z.1)) (coordinateVector i)) k

lemma inverseCoordinateCoefficient_smooth {T S : Base → Base}
    (hT : ContDiff ℝ ∞ T) (hS : ContDiff ℝ ∞ S) (i k : Fin 2) :
    ContDiff ℝ ∞ (inverseCoordinateCoefficient T S i k) := by
  have hs : ContDiff ℝ ∞ (fun x => (fderiv ℝ S x (coordinateVector i)) k) :=
    contDiff_pi.mp ((hS.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const) k
  exact hs.comp (hT.comp (lowPosition.contDiff.comp contDiff_fst))

def jetPullback (T S : Base → Base) : List (Fin 2) → Fin 4 → Expression
  | [],a => .coeff (fun z => z.1 (.inr (0,a)))
  | i::w,a => Expression.sumList Finset.univ.toList (fun k : Fin 2 =>
      (Expression.coeff (inverseCoordinateCoefficient T S i k)).mul ((jetPullback T S w a).slow k))

lemma jetPullback_smooth {T S : Base → Base}
    (hT : ContDiff ℝ ∞ T) (hS : ContDiff ℝ ∞ S) (w : List (Fin 2)) (a : Fin 4) :
    (jetPullback T S w a).SmoothCoeffs univ := by
  induction w with
  | nil =>
    change ContDiffOn ℝ ∞ (fun z : LowJet × ℝ => z.1 (.inr (0,a))) (univ ×ˢ univ)
    exact ((ContinuousLinearMap.proj (.inr (0,a)) : LowJet →L[ℝ] ℝ).contDiff.comp
      (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : LowJet × ℝ → LowJet))).contDiffOn
  | cons i w ih =>
    apply Expression.smoothCoeffs_sumList
    intro k _
    exact Expression.smoothCoeffs_mul (inverseCoordinateCoefficient_smooth hT hS i k).contDiffOn
      (Expression.smoothCoeffs_slow isOpen_univ k ih)

lemma jetPullback_order (T S : Base → Base) (w : List (Fin 2)) (a : Fin 4) :
    (jetPullback T S w a).order ≤ w.length+2 := by
  induction w with
  | nil => exact le_rfl
  | cons i w ih =>
    apply Expression.order_sumList_le _ _ _ (by simp)
    intro k _
    apply (Expression.order_mul_le _ _).trans
    apply max_le
    · simp [Expression.order]
    · exact (Expression.order_slow_le k _).trans (by
        simp only [List.length_cons]
        omega)

lemma jetPullback_loss (T S : Base → Base) (w : List (Fin 2)) (a : Fin 4) :
    (jetPullback T S w a).loss ≤ w.length := by
  induction w with
  | nil => exact Nat.zero_le _
  | cons i w ih =>
    apply Expression.loss_sumList_le
    intro k _
    apply (Expression.loss_mul_le _ _).trans
    simp only [Expression.loss,zero_add,List.length_cons]
    exact (Expression.loss_slow_le k _).trans (Nat.add_le_add_right ih 1)

lemma coordinate_basis_expansion (v : Base) :
    (∑ k : Fin 2, v k • coordinateVector k) = v := by
  ext i
  simp [coordinateVector,Pi.single_apply]

/-- The polynomial is the actual ordered coordinate derivative in the
other chart. The inverse differential condition is local and exact. -/
theorem jetPullback_eval {T S : Base → Base}
    (hT : ContDiff ℝ ∞ T) (hS : ContDiff ℝ ∞ S)
    {U : Set Base} (hU : IsOpen U)
    (hinv : ∀ x ∈ U, (fderiv ℝ T x).comp (fderiv ℝ S (T x)) = ContinuousLinearMap.id ℝ Base)
    {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (hrel : ∀ x ∈ U, H x = G (T x))
    (w : List (Fin 2)) (a : Fin 4) (t : ℝ) :
    ∀ x ∈ U, (jetPullback T S w a).eval H (x,t) = jet G w a (T x) := by
  induction w with
  | nil =>
    intro x hx
    change H x a = G (T x) a
    exact congrFun (hrel x hx) a
  | cons i w ih =>
    intro x hx
    have heq : (fun y => (jetPullback T S w a).eval H (y,t)) =ᶠ[𝓝 x]
        (fun y => jet G w a (T y)) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact ih y hy
    have hs := jet_smooth hG w a
    have hd : fderiv ℝ (fun y => (jetPullback T S w a).eval H (y,t)) x =
        (fderiv ℝ (jet G w a) (T x)).comp (fderiv ℝ T x) := by
      rw [heq.fderiv_eq]
      exact fderiv_comp x (hs.differentiable (by simp) _) (hT.differentiable (by simp) x)
    rw [jetPullback,Expression.eval_sumList,← List.sum_toFinset _ Finset.univ.nodup_toList,
      Finset.toList_toFinset]
    simp only [Expression.eval_mul,Expression.eval,inverseCoordinateCoefficient,lowPosition_lowJet]
    simp_rw [Expression.eval_slow isOpen_univ hU hH (mapsTo_univ _ _) _
      (jetPullback_smooth hT hS w a) hx,hd,ContinuousLinearMap.comp_apply]
    have hsum : (∑ k : Fin 2, (fderiv ℝ S (T x) (coordinateVector i)) k *
        fderiv ℝ (jet G w a) (T x) (fderiv ℝ T x (coordinateVector k))) =
        fderiv ℝ (jet G w a) (T x)
          (fderiv ℝ T x (fderiv ℝ S (T x) (coordinateVector i))) := by
      conv_rhs => rw [← coordinate_basis_expansion (fderiv ℝ S (T x) (coordinateVector i))]
      simp only [map_sum,map_smul,smul_eq_mul]
    rw [hsum]
    have hi := congrArg (fun L : Base →L[ℝ] Base => L (coordinateVector i)) (hinv x hx)
    rw [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] at hi
    rw [hi]
    rfl


namespace Expression

/-- Pull back a finite expression through a fixed coordinate change. The
low-jet substitution is supplied by the finite-dimensional chain rule. -/
def coordinatePullback (T S : Base → Base) (K : LowJet → LowJet) : Expression → Expression
  | .coeff c => .coeff (fun z => c (K z.1,z.2))
  | .atom w a e => (jetPullback T S w a).mul (coordinatePullback T S K e)
  | .add e f => .add (coordinatePullback T S K e) (coordinatePullback T S K f)

lemma coordinatePullback_order (T S : Base → Base) (K : LowJet → LowJet)
    (e : Expression) : (e.coordinatePullback T S K).order ≤ e.order+2 := by
  induction e with
  | coeff c => simp [coordinatePullback,order]
  | atom w a e ih =>
    apply (order_mul_le _ _).trans
    simp only [order]
    exact max_le
      ((jetPullback_order T S w a).trans (by omega)) (ih.trans (by omega))
  | add e f ihe ihf => simp only [coordinatePullback,order] at *; omega

lemma coordinatePullback_smooth {T S : Base → Base} {K : LowJet → LowJet}
    (hT : ContDiff ℝ ∞ T) (hS : ContDiff ℝ ∞ S) (hK : ContDiff ℝ ∞ K)
    {e : Expression} (he : e.SmoothCoeffs univ) :
    (e.coordinatePullback T S K).SmoothCoeffs univ := by
  induction e with
  | coeff c =>
    have hc : ContDiff ℝ ∞ c := contDiffOn_univ.mp (by simpa only [SmoothCoeffs,univ_prod_univ] using he)
    exact (hc.comp ((hK.comp contDiff_fst).prodMk contDiff_snd)).contDiffOn
  | atom w a e ih => exact smoothCoeffs_mul (jetPullback_smooth hT hS w a) (ih he)
  | add e f ihe ihf => exact ⟨ihe he.1,ihf he.2⟩

lemma coordinatePullback_eval {T S : Base → Base} {K : LowJet → LowJet}
    (hT : ContDiff ℝ ∞ T) (hS : ContDiff ℝ ∞ S)
    {U : Set Base} (hU : IsOpen U)
    (hinv : ∀ x ∈ U, (fderiv ℝ T x).comp (fderiv ℝ S (T x)) = ContinuousLinearMap.id ℝ Base)
    {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (hrel : ∀ x ∈ U, H x = G (T x))
    (hjet : ∀ x ∈ U, lowJet G (T x) = K (lowJet H x))
    (e : Expression) (t : ℝ) {x : Base} (hx : x ∈ U) :
    (e.coordinatePullback T S K).eval H (x,t) = e.eval G (T x,t) := by
  induction e with
  | coeff c =>
    change c (K (lowJet H x),t) = c (lowJet G (T x),t)
    rw [hjet x hx]
  | atom w a e ih =>
    rw [coordinatePullback,eval_mul,jetPullback_eval hT hS hU hinv hG hH hrel w a t x hx,ih]
    rfl
  | add e f ihe ihf =>
    change (e.coordinatePullback T S K).eval H (x,t)+
      (f.coordinatePullback T S K).eval H (x,t) = _
    rw [ihe,ihf]
    rfl

end Expression

end ClosedSurfaceR4.JetPolynomial

end

end OAI
