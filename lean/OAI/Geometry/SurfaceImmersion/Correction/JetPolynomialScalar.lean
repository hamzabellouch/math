import OAI.Geometry.SurfaceImmersion.Correction.PolynomialCorrectorRepresentation

namespace OAI

/-! Scalar polynomial representations of the finite metric coefficients. -/
noncomputable section
open scoped BigOperators

namespace ClosedSurfaceR4.JetPolynomial.Expression
open LocalPeriodicExpansion CovarianceCorrector

def Represents {S : TopologicalSpace.Opens Base} (G : Base → Space)
    (e : Expression) (f : Family S ℝ) : Prop :=
  ∀ p ∈ S, ∀ t : ℝ, e.eval G (p, t) = f.val p (t : Period)

def scale (a : ℝ) (e : Expression) : Expression :=
  e.mapCoeff (fun c z => a * c z)

def sumFinset {ι : Type*} (s : Finset ι) (f : ι → Expression) : Expression :=
  sumList s.toList f

@[simp] lemma eval_scale (a : ℝ) (e : Expression) (G : Base → Space) (z : Base × ℝ) :
    (e.scale a).eval G z = a * e.eval G z := eval_mapCoeff_mul e G (fun _ => a) z

@[simp] lemma order_scale (a : ℝ) (e : Expression) : (e.scale a).order = e.order := order_mapCoeff _ _
@[simp] lemma loss_scale (a : ℝ) (e : Expression) : (e.scale a).loss = e.loss := loss_mapCoeff _ _

lemma smoothCoeffs_scale {O : Set LowJet} (a : ℝ) {e : Expression} (he : e.SmoothCoeffs O) :
    (e.scale a).SmoothCoeffs O := smoothCoeffs_map e _ (fun _ hc => contDiffOn_const.mul hc) he

lemma represents_add {S : TopologicalSpace.Opens Base} {G : Base → Space}
    {e f : Expression} {U W : Family S ℝ} (he : Represents G e U) (hf : Represents G f W) :
    Represents G (.add e f) (U + W) := by
  intro p hp t
  simp only [eval, he p hp t, hf p hp t, Family.add_apply]

lemma represents_scale {S : TopologicalSpace.Opens Base} {G : Base → Space}
    {e : Expression} {U : Family S ℝ} (he : Represents G e U) (a : ℝ) :
    Represents G (e.scale a) (a • U) := by
  intro p hp t
  simp only [eval_scale, he p hp t, Family.smul_apply, smul_eq_mul]

lemma represents_fluct {S : TopologicalSpace.Opens Base} {O : Set LowJet} (hO : IsOpen O)
    {G : Base → Space} (hQ : Set.MapsTo (lowJet G) S O)
    {e : Expression} {U : Family S ℝ} (hs : e.SmoothCoeffs O) (he : Represents G e U) :
    Represents G e.fluct U.fluct := by
  intro p hp t
  rw [eval_fluct hO hs G (hQ hp)]
  simp only [he p hp, Family.fluct_apply, fluctuation]
  rw [PeriodicPrimitive.integral_lift_eq_haar]
  rfl

lemma represents_sumFinset {ι : Type*} {S : TopologicalSpace.Opens Base} {G : Base → Space}
    (a : Finset ι) {e : ι → Expression} {U : ι → Family S ℝ}
    (he : ∀ i ∈ a, Represents G (e i) (U i)) :
    Represents G (sumFinset a e) (∑ i ∈ a, U i) := by
  classical
  intro p hp t
  rw [sumFinset, eval_sumList, ← List.sum_toFinset _ a.nodup_toList, Finset.toList_toFinset,
    Family.sum_apply]
  exact Finset.sum_congr rfl (fun i hi => he i hi p hp t)

lemma smoothCoeffs_sumFinset {ι : Type*} {O : Set LowJet} (a : Finset ι) (e : ι → Expression)
    (he : ∀ i ∈ a, (e i).SmoothCoeffs O) : (sumFinset a e).SmoothCoeffs O := by
  apply smoothCoeffs_sumList
  intro i hi
  exact he i (Finset.mem_toList.mp hi)

lemma order_sumFinset_le {ι : Type*} (a : Finset ι) (e : ι → Expression) (N : ℕ)
    (hN : 2 ≤ N) (he : ∀ i ∈ a, (e i).order ≤ N) : (sumFinset a e).order ≤ N := by
  apply order_sumList_le _ _ _ hN
  intro i hi
  exact he i (Finset.mem_toList.mp hi)

lemma loss_sumFinset_le {ι : Type*} (a : Finset ι) (e : ι → Expression) (N : ℕ)
    (he : ∀ i ∈ a, (e i).loss ≤ N) : (sumFinset a e).loss ≤ N := by
  apply loss_sumList_le
  intro i hi
  exact he i (Finset.mem_toList.mp hi)

lemma represents_dot {S : TopologicalSpace.Opens Base} {G : Base → Space}
    {R T : VectorExpression} {U W : Family S R4} (hR : VectorExpression.Represents G R U)
    (hT : VectorExpression.Represents G T W) : Represents G (R.dot T) (U.inner W) := by
  intro p hp t
  rw [VectorExpression.eval_dot hR hT hp, Family.inner_apply]

end ClosedSurfaceR4.JetPolynomial.Expression

end

end OAI
