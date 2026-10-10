import Mathlib
import OAI.Geometry.TamingCompatibility.Charts.ChartUnitaryData
import OAI.Geometry.TamingCompatibility.Functional.NormalSymbol

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge AntiInvariantFrame LocalMatrixOperator Set
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α)
  (ht : Tames α J) (p : X) (D : Data J α ht p)

def coordinateTest (q : Space → EuclideanEnergy.Pair) : Space → MetricForms.Form Space 2 :=
  frameTest (fun x => realPart (coordinateMetric J α ht p x) (fun i => D.frame i x))
    (fun x => imagPart (coordinateMetric J α ht p x) (fun i => D.frame i x)) q

omit [T2Space X] in
lemma coordinateTest_support (q : Space → EuclideanEnergy.Pair) :
    tsupport (coordinateTest J α ht p D q) ⊆ tsupport q := frameTest_tsupport _ _ _

include hs in
omit [T2Space X] in
lemma coordinateTest_smooth {q : Space → EuclideanEnergy.Pair} (hq : ContDiff ℝ ∞ q)
    (hqD : tsupport q ⊆ D.domain) : ContDiff ℝ ∞ (coordinateTest J α ht p D q) :=
  frameTest_smooth D.domain_open
    (realPart_smooth ((coordinateMetric_smooth J α hs ht p).mono D.domain_subset) D.frame_smooth)
    (imagPart_smooth ((coordinateMetric_smooth J α hs ht p).mono D.domain_subset) D.frame_smooth) hq hqD

omit [T2Space X] in
lemma coordinateTest_anti {q : Space → EuclideanEnergy.Pair} (hqD : tsupport q ⊆ D.domain)
    (z : Space) : (coordinateTest J α ht p D q z).compContinuousLinearMap (coordinateJ J p z) =
      -coordinateTest J α ht p D q z := by
  by_cases hz : z ∈ tsupport q
  · obtain ⟨h0,h1,h2,h3⟩ := D.frame_complex z (hqD hz)
    have hψ := realPart_antiInvariant (coordinateMetric J α ht p z) (by simp [Space])
      (fun i => D.frame i z) (D.frame_gram z (hqD hz)) (coordinateJ J p z) h0 h1 h2 h3
    have hχ := imagPart_antiInvariant (coordinateMetric J α ht p z) (by simp [Space])
      (fun i => D.frame i z) (D.frame_gram z (hqD hz)) (coordinateJ J p z) h0 h1 h2 h3
    apply ContinuousAlternatingMap.ext
    intro v
    have hψv := congrArg (fun a : MetricForms.Form Space 2 => a v) hψ
    have hχv := congrArg (fun a : MetricForms.Form Space 2 => a v) hχ
    simp only [coordinateTest,frameTest,ContinuousAlternatingMap.compContinuousLinearMap_apply,
      ContinuousAlternatingMap.add_apply,ContinuousAlternatingMap.smul_apply,
      ContinuousAlternatingMap.neg_apply,smul_eq_mul] at hψv hχv ⊢
    rw [hψv,hχv]
    ring
  · have hzq := image_eq_zero_of_notMem_tsupport hz
    have ht : coordinateTest J α ht p D q z = 0 := frameTest_zero hzq
    rw [ht]
    ext v
    simp

def manifoldTest (q : Space → EuclideanEnergy.Pair) : TwoForm X :=
  antiInvariantPart J (chartLift p (coordinateTest J α ht p D q))

include hs in
lemma manifoldTest_smooth {q : Space → EuclideanEnergy.Pair} (hq : ContDiff ℝ ∞ q)
    (hc : HasCompactSupport q) (hqD : tsupport q ⊆ D.domain) :
    IsSmooth (manifoldTest J α ht p D q) :=
  IsSmooth.antiInvariantPart (chartLift_smooth p (coordinateTest_smooth J α hs ht p D hq hqD)
    (frameTest_compact _ _ hc) ((coordinateTest_support J α ht p D q).trans
      (hqD.trans D.domain_subset))) J

omit [T2Space X] in
lemma manifoldTest_anti (q : Space → EuclideanEnergy.Pair) :
    antiInvariantPart J (manifoldTest J α ht p D q) = manifoldTest J α ht p D q :=
  antiInvariantPart_idempotent J _

omit [T2Space X] in
lemma pullback_manifoldTest {q : Space → EuclideanEnergy.Pair} (hqD : tsupport q ⊆ D.domain)
    {z : Space} (hz : z ∈ (extChartAt Model p).target) :
    pullback (manifoldTest J α ht p D q) (extChartAt Model p).symm z = coordinateTest J α ht p D q z :=
  pullback_lift_antiInvariantPart J p _ hz (coordinateTest_anti J α ht p D hqD z)

end TamingCompatibility.GeometricChart

end
end

section
noncomputable section
namespace TamingCompatibility.ScalarPair
open MeasureTheory LineDeriv
open scoped SchwartzMap LineDeriv ContDiff
abbrev F := EuclideanSpace ℂ (Fin 2)

def inject (j : Fin 2) : ℝ →L[ℝ] F :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℂ)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.single ℝ (fun _ : Fin 2 => ℂ) j ∘L Complex.ofRealCLM

lemma inject_apply (j i : Fin 2) (s : ℝ) : inject j s i = if i=j then (s : ℂ) else 0 := by
  simp [inject]

def make {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (s t : 𝓢(E,ℝ)) : 𝓢(E,F) :=
  SchwartzMap.postcompCLM (inject 0) s + SchwartzMap.postcompCLM (inject 1) t

lemma make_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s t : 𝓢(E,ℝ)) (x : E) (i : Fin 2) : make s t x i = if i=0 then (s x : ℂ) else (t x : ℂ) := by
  fin_cases i <;> simp [make,inject_apply]

lemma make_norm_sq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s t : 𝓢(E,ℝ)) (x : E) : ‖make s t x‖^2 = (s x)^2 + (t x)^2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp [Fin.sum_univ_two,make_apply,Complex.norm_real,Real.norm_eq_abs,sq_abs]

lemma postcomp_derivative {E G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (L : G →L[ℝ] H) (u : 𝓢(E,G)) (v : E) :
    ∂_{v} (SchwartzMap.postcompCLM L u) = SchwartzMap.postcompCLM L (∂_{v} u) := by
  ext x
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  change fderiv ℝ (L ∘ u) x v = L (fderiv ℝ u x v)
  rw [(L.hasFDerivAt.comp x (u.differentiableAt (x := x)).hasFDerivAt).fderiv]
  rfl

lemma make_derivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s t : 𝓢(E,ℝ)) (v : E) : ∂_{v} (make s t) = make (∂_{v} s) (∂_{v} t) := by
  simp only [make,lineDerivOp_add,postcomp_derivative]
end TamingCompatibility.ScalarPair

namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldLocalization Set
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

omit [CompactSpace X] in
lemma scalar_add (p : A.centers) (a b : TwoForm X) (j : Fin 4) :
    scalar A J α ht D p (a+b) j = scalar A J α ht D p a j + scalar A J α ht D p b j := by
  ext x
  unfold scalar
  by_cases hx : x ∈ (D p).domain
  · simp only [indicator_of_mem hx,Pi.add_apply,localizedFunction_add,ContinuousAlternatingMap.add_apply]
  · simp only [indicator_of_notMem hx,Pi.add_apply,add_zero]

omit [CompactSpace X] in
lemma scalar_smul (p : A.centers) (c : ℝ) (a : TwoForm X) (j : Fin 4) :
    scalar A J α ht D p (c • a) j = c • scalar A J α ht D p a j := by
  ext x
  unfold scalar
  by_cases hx : x ∈ (D p).domain
  · simp only [indicator_of_mem hx,Pi.smul_apply,localizedFunction_smul,ContinuousAlternatingMap.smul_apply]
  · simp only [indicator_of_notMem hx,Pi.smul_apply,smul_zero]

def scalarLinear (p : A.centers) (j : Fin 4) : smoothForms X 2 →ₗ[ℝ] 𝓢(Space,ℝ) where
  toFun a := scalarSchwartz A J α ht D hD p a.val a.property j
  map_add' a b := by
    ext x
    exact congrFun (scalar_add A J α ht D p a.val b.val j) x
  map_smul' c a := by
    ext x
    exact congrFun (scalar_smul A J α ht D p c a.val j) x

def pairLinear (p : A.centers) : smoothForms X 2 →ₗ[ℝ] 𝓢(Space,ScalarPair.F) :=
  (SchwartzMap.postcompCLM (ScalarPair.inject 0)).toLinearMap ∘ₗ scalarLinear A J α ht D hD p 2 +
    (SchwartzMap.postcompCLM (ScalarPair.inject 1)).toLinearMap ∘ₗ scalarLinear A J α ht D hD p 3

lemma pairLinear_eq_make (p : A.centers) (a : smoothForms X 2) :
    pairLinear A J α ht D hD p a = ScalarPair.make
      (scalarSchwartz A J α ht D hD p a.val a.property 2)
      (scalarSchwartz A J α ht D hD p a.val a.property 3) := rfl
end TamingCompatibility.GeometricChart

end
end

end
end
end

end OAI
