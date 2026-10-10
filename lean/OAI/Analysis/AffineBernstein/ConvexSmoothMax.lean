import Mathlib
import OAI.Analysis.AffineBernstein.MatrixConcavity
import OAI.Analysis.AffineBernstein.SmoothPositivePart

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology

lemma hessian_sub_on {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u v : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω) (hv : ContDiffOn ℝ ∞ v Ω)
    {x : Space n} (hx : x ∈ Ω) :
    hessian (fun y => u y-v y) x = hessian u x-hessian v x := by
  have h := hessian_add_on hΩ (hu.sub hv) hv hx
  have he : (fun y => (u y-v y)+v y) = u := by funext y; ring
  rw [he] at h
  exact eq_sub_iff_add_eq.mpr h.symm

lemma hessian_convex_smooth_max {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u q : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω) (hq : ContDiffOn ℝ ∞ q Ω)
    (ε : ℝ) {x : Space n} (hx : x ∈ Ω) :
    hessian (fun y => u y + smoothPositivePart ε (q y-u y)) x =
      (1-deriv (smoothPositivePart ε) (q x-u x)) • hessian u x +
      deriv (smoothPositivePart ε) (q x-u x) • hessian q x +
      deriv (deriv (smoothPositivePart ε)) (q x-u x) •
        Matrix.vecMulVec (fun i => dirDeriv (coordinateVector n i) (fun y => q y-u y) x)
          (fun i => dirDeriv (coordinateVector n i) (fun y => q y-u y) x) := by
  have hs : ContDiffOn ℝ ∞ (fun y => smoothPositivePart ε (q y-u y)) Ω :=
    (smoothPositivePart_smooth ε).comp_contDiffOn (hq.sub hu)
  rw [hessian_add_on hΩ hu hs hx]
  ext i j
  have hc := second_dirDeriv_comp_scalar hΩ (hq.sub hu) (smoothPositivePart_smooth ε)
    hx (coordinateVector n j) (coordinateVector n i)
  change hessian u x i j + _ = _
  change hessian u x i j + dirDeriv (coordinateVector n i)
    (dirDeriv (coordinateVector n j) (fun y => smoothPositivePart ε (q y-u y))) x = _
  rw [hc]
  change hessian u x i j + (_ + _ * hessian (fun y => q y-u y) x i j) = _
  rw [hessian_sub_on hΩ hq hu hx]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply, Matrix.vecMulVec_apply]
  ring

lemma posDef_convex_combination {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) : ((1-t) • A + t • B).PosDef := by
  rcases eq_or_lt_of_le ht with he | hp
  · subst t
    simpa using hA
  · exact Matrix.PosDef.posSemidef_add (hA.posSemidef.smul (sub_nonneg.mpr ht1)) (hB.smul hp)

lemma hessian_convex_smooth_max_posDef {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u q : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω) (hq : ContDiffOn ℝ ∞ q Ω)
    {ε : ℝ} (hε : 0 < ε) {x : Space n} (hx : x ∈ Ω)
    (hpu : (hessian u x).PosDef) (hpq : (hessian q x).PosDef) :
    (hessian (fun y => u y + smoothPositivePart ε (q y-u y)) x).PosDef := by
  rw [hessian_convex_smooth_max hΩ hu hq ε hx]
  have hb := smoothPositivePart_deriv_bounds ε (q x-u x)
  have hr : (Matrix.vecMulVec
      (fun i => dirDeriv (coordinateVector n i) (fun y => q y-u y) x)
      (fun i => dirDeriv (coordinateVector n i) (fun y => q y-u y) x)).PosSemidef := by
    simpa using Matrix.posSemidef_vecMulVec_self_star
      (fun i => dirDeriv (coordinateVector n i) (fun y => q y-u y) x)
  exact (posDef_convex_combination hpu hpq hb.1 hb.2).add_posSemidef
    (hr.smul (smoothPositivePart_second_nonneg hε _))

/-- The exact quadratics used in the positive-cap comparison. -/
def capQuadratic {n : ℕ} (c : Space n) (b α : ℝ) (x : Space n) : ℝ :=
  b + α * ‖x-c‖^2

lemma capQuadratic_smooth {n : ℕ} (c : Space n) (b α : ℝ) :
    ContDiff ℝ ∞ (capQuadratic c b α) := by
  unfold capQuadratic
  exact contDiff_const.add (contDiff_const.mul ((contDiff_norm_sq ℝ : ContDiff ℝ ∞ (fun y : Space n => ‖y‖^2)).comp
    (contDiff_id.sub contDiff_const)))

lemma dirDeriv_capQuadratic {n : ℕ} (c : Space n) (b α : ℝ) (x v : Space n) :
    dirDeriv v (capQuadratic c b α) x = 2*α*inner ℝ (x-c) v := by
  have hd := ((((hasFDerivAt_id x).sub_const c).norm_sq).const_mul α).const_add b
  change fderiv ℝ (fun y => b+α*‖y-c‖^2) x v = _
  simp only [id_eq] at hd
  rw [hd.fderiv]
  simp [inner_sub_left, mul_assoc, mul_comm]

lemma hessian_capQuadratic {n : ℕ} (c : Space n) (b α : ℝ) (x : Space n) :
    hessian (capQuadratic c b α) x = (2*α) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  change dirDeriv (coordinateVector n i) (dirDeriv (coordinateVector n j) (capQuadratic c b α)) x = _
  have he : dirDeriv (coordinateVector n j) (capQuadratic c b α) =
      (fun y => 2*α*(inner ℝ (coordinateVector n j) y-inner ℝ (coordinateVector n j) c)) := by
    funext y
    rw [dirDeriv_capQuadratic, real_inner_comm, inner_sub_right]
  rw [he]
  have hd := (((innerSL ℝ (coordinateVector n j)).hasFDerivAt (x := x)).sub_const
    (inner ℝ (coordinateVector n j) c)).const_mul (2*α)
  change fderiv ℝ _ x (coordinateVector n i) = _
  have heq := congrArg (fun L : Space n →L[ℝ] ℝ => L (coordinateVector n i)) hd.fderiv
  convert! heq using 1
  simp [coordinateVector, EuclideanSpace.inner_single_left, eq_comm]

lemma hessian_capQuadratic_posDef {n : ℕ} (c : Space n) (b : ℝ) {α : ℝ}
    (hα : 0 < α) (x : Space n) : (hessian (capQuadratic c b α) x).PosDef := by
  rw [hessian_capQuadratic]
  exact Matrix.PosDef.one.smul (by positivity)

lemma affineAreaDensity_capQuadratic {n : ℕ} (c : Space n) (b : ℝ) {α : ℝ}
    (hα : 0 < α) (x : Space n) :
    affineAreaDensity (capQuadratic c b α) x =
      Real.rpow (2*α) ((n : ℝ)/((n : ℝ)+2)) := by
  unfold affineAreaDensity
  rw [hessian_capQuadratic, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  rw [← Real.rpow_natCast]
  change ((2*α)^(n : ℝ))^(1/((n : ℝ)+2)) = (2*α)^((n : ℝ)/((n : ℝ)+2))
  rw [← Real.rpow_mul (by positivity)]
  congr 1
  ring

end AffineBernstein
end

end OAI
