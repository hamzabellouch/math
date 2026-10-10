import OAI.Geometry.SurfaceImmersion.Correction.JetPolynomialFullEvaluation
import OAI.Geometry.SurfaceImmersion.Primitive.LocalPeriodicFamilyAlgebra

namespace OAI

/-! Four coordinate polynomials represent the actual vector families used by
the metric recursion. Dot products and both derivatives preserve representation. -/
noncomputable section
open scoped ContDiff Topology BigOperators

namespace ClosedSurfaceR4.JetPolynomial
open LocalPeriodicExpansion SmoothPeriodicCalculus

abbrev R4 := EuclideanSpace ℝ (Fin 4)
abbrev VectorExpression := Fin 4 → Expression

namespace VectorExpression

def SmoothCoeffs (O : Set LowJet) (R : VectorExpression) : Prop :=
  ∀ i, (R i).SmoothCoeffs O

def Represents {S : TopologicalSpace.Opens Base} (G : Base → Space)
    (R : VectorExpression) (U : Family S R4) : Prop :=
  ∀ i p, p ∈ S → ∀ t : ℝ, (R i).eval G (p, t) = U.val p (t : CovarianceCorrector.Period) i

def add (R T : VectorExpression) : VectorExpression := fun i => .add (R i) (T i)
def slow (R : VectorExpression) (v : Fin 2) : VectorExpression := fun i => (R i).slow v
def angle (R : VectorExpression) : VectorExpression := fun i => (R i).angle
def mean (R : VectorExpression) : VectorExpression := fun i => (R i).mean
def primitive (R : VectorExpression) : VectorExpression := fun i => (R i).primitive

def dot (R T : VectorExpression) : Expression :=
  Expression.sumList Finset.univ.toList (fun i : Fin 4 => (R i).mul (T i))

lemma smoothCoeffs_dot {O : Set LowJet} {R T : VectorExpression}
    (hR : R.SmoothCoeffs O) (hT : T.SmoothCoeffs O) : (R.dot T).SmoothCoeffs O := by
  apply Expression.smoothCoeffs_sumList
  intro i _
  exact Expression.smoothCoeffs_mul (hR i) (hT i)

lemma order_dot_le {R T : VectorExpression} {N : ℕ} (hN : 2 ≤ N)
    (hR : ∀ i, (R i).order ≤ N) (hT : ∀ i, (T i).order ≤ N) : (R.dot T).order ≤ N := by
  apply Expression.order_sumList_le _ _ _ hN
  intro i _
  exact (Expression.order_mul_le _ _).trans (max_le (hR i) (hT i))

lemma loss_dot_le {R T : VectorExpression} {a b : ℕ}
    (hR : ∀ i, (R i).loss ≤ a) (hT : ∀ i, (T i).loss ≤ b) : (R.dot T).loss ≤ a + b := by
  apply Expression.loss_sumList_le
  intro i _
  exact (Expression.loss_mul_le _ _).trans (Nat.add_le_add (hR i) (hT i))

lemma order_slow_le {R : VectorExpression} {N : ℕ} (hN : 2 ≤ N)
    (hR : ∀ i, (R i).order ≤ N) (v : Fin 2) : ∀ i, (R.slow v i).order ≤ N + 1 := by
  intro i
  have hi := hR i
  exact (Expression.order_slow_le v (R i)).trans (by omega)

lemma loss_slow_le {R : VectorExpression} {N : ℕ}
    (hR : ∀ i, (R i).loss ≤ N) (v : Fin 2) : ∀ i, (R.slow v i).loss ≤ N + 1 := by
  intro i
  exact (Expression.loss_slow_le v (R i)).trans (Nat.add_le_add_right (hR i) 1)

lemma represents_add {S : TopologicalSpace.Opens Base} {G : Base → Space}
    {R T : VectorExpression} {U W : Family S R4} (hR : Represents G R U)
    (hT : Represents G T W) : Represents G (R.add T) (U + W) := by
  intro i p hp t
  simp only [add, Expression.eval, hR i p hp t, hT i p hp t, Family.add_apply]
  rfl

lemma eval_dot {S : TopologicalSpace.Opens Base} {G : Base → Space}
    {R T : VectorExpression} {U W : Family S R4} (hR : Represents G R U)
    (hT : Represents G T W) {p : Base} (hp : p ∈ S) (t : ℝ) :
    (R.dot T).eval G (p, t) = inner ℝ (U.val p (t : CovarianceCorrector.Period))
      (W.val p (t : CovarianceCorrector.Period)) := by
  rw [dot, Expression.eval_sumList, ← List.sum_toFinset _ Finset.univ.nodup_toList,
    Finset.toList_toFinset]
  simp only [Expression.eval_mul, hR _ p hp t, hT _ p hp t]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change (∑ i : Fin 4, U.val p (t : CovarianceCorrector.Period) i *
    W.val p (t : CovarianceCorrector.Period) i) =
    ∑ i : Fin 4, W.val p (t : CovarianceCorrector.Period) i * U.val p (t : CovarianceCorrector.Period) i
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

lemma represents_slow {S : TopologicalSpace.Opens Base} {O : Set LowJet} (hO : IsOpen O)
    {G : Base → Space} (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) S O)
    {R : VectorExpression} {U : Family S R4} (hRs : R.SmoothCoeffs O)
    (hR : Represents G R U) (v : Fin 2) : Represents G (R.slow v) (U.slow (coordinateVector v)) := by
  intro i p hp t
  rw [slow, Expression.eval_slow hO S.isOpen hG hQ v (hRs i) hp]
  let L : R4 →L[ℝ] ℝ := EuclideanSpace.proj i
  have heq : (fun x => (R i).eval G (x, t)) =ᶠ[𝓝 p]
      (fun x => L (U.val x (t : CovarianceCorrector.Period))) := by
    filter_upwards [S.isOpen.mem_nhds hp] with x hx
    exact hR i x hx t
  rw [heq.fderiv_eq]
  have hU : DifferentiableAt ℝ (fun x => U.val x (t : CovarianceCorrector.Period)) p :=
    ((U.smooth.contDiffAt ((S.isOpen.prod isOpen_univ).mem_nhds ⟨hp, Set.mem_univ t⟩)).comp p
      (contDiff_id.prodMk contDiff_const).contDiffAt).differentiableAt (by simp)
  change fderiv ℝ (L ∘ fun x => U.val x (t : CovarianceCorrector.Period)) p
    (coordinateVector v) = _
  rw [(L.hasFDerivAt.comp p hU.hasFDerivAt).fderiv]
  rw [Family.slow_apply U (coordinateVector v) hp t,
    ← LocalPeriodicCalculus.fderiv_slice S.isOpen U.smooth hp]
  rfl

lemma represents_angle {S : TopologicalSpace.Opens Base} {O : Set LowJet} (hO : IsOpen O)
    {G : Base → Space} (hQ : Set.MapsTo (lowJet G) S O)
    {R : VectorExpression} {U : Family S R4} (hRs : R.SmoothCoeffs O)
    (hR : Represents G R U) : Represents G R.angle U.angle := by
  intro i p hp t
  rw [angle, Expression.eval_angle hO (hRs i) G (hQ hp)]
  have heq : (fun s => (R i).eval G (p, s)) =
      (fun s : ℝ => U.val p (s : CovarianceCorrector.Period) i) := funext (hR i p hp)
  rw [heq]
  let L : R4 →L[ℝ] ℝ := EuclideanSpace.proj i
  exact (L.hasFDerivAt.comp_hasDerivAt t (U.angle_hasDerivAt hp t)).deriv

lemma represents_mean {S : TopologicalSpace.Opens Base} {O : Set LowJet} (hO : IsOpen O)
    {G : Base → Space} (hQ : Set.MapsTo (lowJet G) S O)
    {R : VectorExpression} {U : Family S R4} (hRs : R.SmoothCoeffs O)
    (hR : Represents G R U) : Represents G R.mean U.vectorMean := by
  intro i p hp t
  rw [mean, Expression.eval_mean hO (hRs i) G (hQ hp)]
  simp only [hR i p hp, Family.vectorMean_apply]
  let L : R4 →L[ℝ] ℝ := EuclideanSpace.proj i
  change (∫ s in (0 : ℝ)..1, L (U.val p (s : CovarianceCorrector.Period))) =
    L (CovarianceCorrector.average (U.val p))
  have hInt : IntervalIntegrable (fun s : ℝ => U.val p (s : CovarianceCorrector.Period))
      MeasureTheory.volume 0 1 :=
    ((U.val p).continuous.comp (AddCircle.continuous_mk' 1)).intervalIntegrable 0 1
  rw [L.intervalIntegral_comp_comm hInt, PeriodicPrimitive.integral_lift_eq_haar]
  rfl

lemma represents_primitive {S : TopologicalSpace.Opens Base} {O : Set LowJet} (hO : IsOpen O)
    {G : Base → Space} (hQ : Set.MapsTo (lowJet G) S O)
    {R : VectorExpression} {U : Family S R4} (hRs : R.SmoothCoeffs O)
    (hR : Represents G R U) (hm : ∀ p ∈ S, CovarianceCorrector.average (U.val p) = 0) :
    Represents G R.primitive (U.primitive hm) := by
  intro i p hp t
  rw [primitive, Expression.eval_primitive hO (hRs i) G (hQ hp)]
  have heq : (fun s => (R i).eval G (p, s)) =
      (fun s : ℝ => U.val p (s : CovarianceCorrector.Period) i) := funext (hR i p hp)
  rw [heq, Family.primitive, Family.ofLocal_apply _ _ hp,
    LocalPeriodicCalculus.primitiveOn_apply _ _ _ _ _ hp]
  let L : R4 →L[ℝ] ℝ := EuclideanSpace.proj i
  exact (primitive_map L ((U.val p).continuous.comp (AddCircle.continuous_mk' 1)) t).symm

end VectorExpression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
