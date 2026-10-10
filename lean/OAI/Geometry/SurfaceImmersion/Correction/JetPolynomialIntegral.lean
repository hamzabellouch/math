import OAI.Geometry.SurfaceImmersion.Correction.JetPolynomialDerivative

namespace OAI

/-! Angular derivatives, averaging, and normalized primitives act only on
smooth low-jet coefficients, preserving polynomial jet order and scale loss. -/
noncomputable section
open MeasureTheory
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open SmoothPeriodicCalculus

namespace Expression

lemma eval_slice_smooth {O : Set LowJet} (hO : IsOpen O) {e : Expression}
    (he : e.SmoothCoeffs O) (G : Base → Space) {p : Base} (hp : lowJet G p ∈ O) :
    ContDiff ℝ ∞ (fun t => e.eval G (p, t)) := by
  induction e with
  | coeff c => exact LocalPeriodicCalculus.smooth_slice hO he hp
  | atom w a e ih =>
    change ContDiff ℝ ∞ (fun t => jet G w a p * e.eval G (p, t))
    exact contDiff_const.mul (ih he)
  | add e f ihe ihf => exact (ihe he.1).add (ihf he.2)

def angle (e : Expression) : Expression := e.mapCoeff angleDerivative

def mean (e : Expression) : Expression :=
  e.mapCoeff (fun c z => ∫ t in 0..1, c (z.1, t))

def primitive (e : Expression) : Expression :=
  e.mapCoeff (fun c z => PeriodicPrimitive.primitive (fun t => c (z.1, t)) z.2)

lemma smoothCoeffs_angle {O : Set LowJet} (hO : IsOpen O) {e : Expression}
    (he : e.SmoothCoeffs O) : e.angle.SmoothCoeffs O :=
  smoothCoeffs_map e _ (fun _ hc => LocalPeriodicCalculus.angle_smooth hO hc) he

lemma smoothCoeffs_mean {O : Set LowJet} (hO : IsOpen O) {e : Expression}
    (he : e.SmoothCoeffs O) : e.mean.SmoothCoeffs O := by
  apply smoothCoeffs_map e _ _ he
  intro c hc
  exact (SmoothParameterIntegral.contDiffOn_integral hO hc 0 1).comp contDiffOn_fst
    (fun _ hz => hz.1)

lemma smoothCoeffs_primitive {O : Set LowJet} (hO : IsOpen O) {e : Expression}
    (he : e.SmoothCoeffs O) : e.primitive.SmoothCoeffs O :=
  smoothCoeffs_map e _ (fun _ hc => PeriodicPrimitive.contDiffOn_primitive_joint hO hc) he

@[simp] lemma order_angle (e : Expression) : e.angle.order = e.order := order_mapCoeff _ _
@[simp] lemma loss_angle (e : Expression) : e.angle.loss = e.loss := loss_mapCoeff _ _
@[simp] lemma order_mean (e : Expression) : e.mean.order = e.order := order_mapCoeff _ _
@[simp] lemma loss_mean (e : Expression) : e.mean.loss = e.loss := loss_mapCoeff _ _
@[simp] lemma order_primitive (e : Expression) : e.primitive.order = e.order := order_mapCoeff _ _
@[simp] lemma loss_primitive (e : Expression) : e.primitive.loss = e.loss := loss_mapCoeff _ _

lemma eval_angle {O : Set LowJet} (hO : IsOpen O) {e : Expression}
    (he : e.SmoothCoeffs O) (G : Base → Space) {p : Base} (hp : lowJet G p ∈ O) (t : ℝ) :
    e.angle.eval G (p, t) = deriv (fun s => e.eval G (p, s)) t := by
  induction e with
  | coeff c => exact (LocalPeriodicCalculus.angle_hasDerivAt hO he hp t).deriv.symm
  | atom w a e ih =>
    change jet G w a p * e.angle.eval G (p, t) =
      deriv (fun s => jet G w a p * e.eval G (p, s)) t
    rw [deriv_const_mul _ ((eval_slice_smooth hO (e := e) he G hp).differentiable (by simp) t),
      ih he]
  | add e f ihe ihf =>
    change e.angle.eval G (p, t) + f.angle.eval G (p, t) =
      deriv (fun s => e.eval G (p, s) + f.eval G (p, s)) t
    rw [deriv_fun_add ((eval_slice_smooth hO he.1 G hp).differentiable (by simp) t)
      ((eval_slice_smooth hO he.2 G hp).differentiable (by simp) t), ihe he.1, ihf he.2]

lemma eval_mean {O : Set LowJet} (hO : IsOpen O) {e : Expression}
    (he : e.SmoothCoeffs O) (G : Base → Space) {p : Base} (hp : lowJet G p ∈ O) (t : ℝ) :
    e.mean.eval G (p, t) = ∫ s in 0..1, e.eval G (p, s) := by
  induction e with
  | coeff c => rfl
  | atom w a e ih =>
    change jet G w a p * e.mean.eval G (p, t) = ∫ s in 0..1, jet G w a p * e.eval G (p, s)
    rw [intervalIntegral.integral_const_mul, ih he]
  | add e f ihe ihf =>
    change e.mean.eval G (p, t) + f.mean.eval G (p, t) =
      ∫ s in 0..1, (e.eval G (p, s) + f.eval G (p, s))
    rw [intervalIntegral.integral_add
      ((eval_slice_smooth hO he.1 G hp).continuous.intervalIntegrable 0 1)
      ((eval_slice_smooth hO he.2 G hp).continuous.intervalIntegrable 0 1), ihe he.1, ihf he.2]

lemma normalizedPrimitive_const_mul (c : ℝ) (f : ℝ → ℝ) (t : ℝ) :
    PeriodicPrimitive.primitive (fun s => c * f s) t = c * PeriodicPrimitive.primitive f t := by
  simp only [PeriodicPrimitive.primitive, PeriodicPrimitive.rawPrimitive,
    intervalIntegral.integral_const_mul, mul_sub]

lemma normalizedPrimitive_add {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) (t : ℝ) :
    PeriodicPrimitive.primitive (fun s => f s + g s) t =
      PeriodicPrimitive.primitive f t + PeriodicPrimitive.primitive g t := by
  have hi (s : ℝ) : PeriodicPrimitive.rawPrimitive (fun x => f x + g x) s =
      PeriodicPrimitive.rawPrimitive f s + PeriodicPrimitive.rawPrimitive g s :=
    intervalIntegral.integral_add (hf.intervalIntegrable 0 s) (hg.intervalIntegrable 0 s)
  simp only [PeriodicPrimitive.primitive, hi]
  rw [intervalIntegral.integral_add
    ((PeriodicPrimitive.rawPrimitive_continuous hf).intervalIntegrable 0 1)
    ((PeriodicPrimitive.rawPrimitive_continuous hg).intervalIntegrable 0 1)]
  ring

lemma eval_primitive {O : Set LowJet} (hO : IsOpen O) {e : Expression}
    (he : e.SmoothCoeffs O) (G : Base → Space) {p : Base} (hp : lowJet G p ∈ O) (t : ℝ) :
    e.primitive.eval G (p, t) = PeriodicPrimitive.primitive (fun s => e.eval G (p, s)) t := by
  induction e with
  | coeff c => rfl
  | atom w a e ih =>
    change jet G w a p * e.primitive.eval G (p, t) =
      PeriodicPrimitive.primitive (fun s => jet G w a p * e.eval G (p, s)) t
    rw [normalizedPrimitive_const_mul, ih he]
  | add e f ihe ihf =>
    change e.primitive.eval G (p, t) + f.primitive.eval G (p, t) =
      PeriodicPrimitive.primitive (fun s => e.eval G (p, s) + f.eval G (p, s)) t
    rw [normalizedPrimitive_add (eval_slice_smooth hO he.1 G hp).continuous
      (eval_slice_smooth hO he.2 G hp).continuous, ihe he.1, ihf he.2]

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
