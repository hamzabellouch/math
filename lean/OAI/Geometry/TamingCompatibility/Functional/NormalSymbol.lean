import Mathlib
import OAI.Geometry.TamingCompatibility.Charts.LocalMatrixOperator
import OAI.Geometry.TamingCompatibility.Charts.ChartLift

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.LocalMatrixOperator
open MetricModel MetricForms MetricHodge ExteriorForms ContinuousAlternatingMap
open EuclideanEnergy
open scoped RealInnerProductSpace

def normalSymbol (ξ : V) : Pair →L[ℝ] V :=
  combine (WithLp.toLp 2 ![-ξ 2,ξ 3,ξ 0,-ξ 1])
    (WithLp.toLp 2 ![-ξ 3,-ξ 2,ξ 1,ξ 0])

lemma normalSymbol_inner (ξ : V) (q r : Pair) :
    ⟪normalSymbol ξ q, normalSymbol ξ r⟫ = ⟪ξ,ξ⟫ * ⟪q,r⟫ := by
  simp only [PiLp.inner_apply]
  simp [normalSymbol,combine_apply,Fin.sum_univ_succ]
  ring

lemma normalSymbol_polarized (ξ η : V) (q r : Pair) :
    ⟪normalSymbol ξ q,normalSymbol η r⟫ +
      ⟪normalSymbol η q,normalSymbol ξ r⟫ = 2 * ⟪ξ,η⟫ * ⟪q,r⟫ := by
  simp only [PiLp.inner_apply]
  simp [normalSymbol,combine_apply,Fin.sum_univ_succ]
  ring

lemma normalSymbol_adjoint (ξ : V) :
    (normalSymbol ξ).adjoint ∘L normalSymbol ξ = ⟪ξ,ξ⟫ • ContinuousLinearMap.id ℝ Pair := by
  apply ContinuousLinearMap.ext
  intro q
  apply ext_inner_left ℝ
  intro r
  simp only [ContinuousLinearMap.comp_apply,_root_.smul_apply,
    ContinuousLinearMap.id_apply,inner_smul_right]
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact normalSymbol_inner ξ r q

lemma normalSymbol_adjoint_polarized (ξ η : V) :
    (normalSymbol ξ).adjoint ∘L normalSymbol η +
      (normalSymbol η).adjoint ∘L normalSymbol ξ =
        (2 * ⟪ξ,η⟫) • ContinuousLinearMap.id ℝ Pair := by
  apply ContinuousLinearMap.ext
  intro q
  apply ext_inner_left ℝ
  intro r
  simp only [_root_.add_apply,ContinuousLinearMap.comp_apply,
    _root_.smul_apply,ContinuousLinearMap.id_apply,inner_smul_right,inner_add_right]
  rw [ContinuousLinearMap.adjoint_inner_right,ContinuousLinearMap.adjoint_inner_right]
  exact normalSymbol_polarized ξ η r q

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable (g : Metric E) (hdim : Module.finrank ℝ E = 4) (b : Fin 4 → E)
  (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0)
  (J : E →L[ℝ] E) (h0 : J (b 0) = b 1) (h1 : J (b 1) = -b 0)
  (h2 : J (b 2) = b 3) (h3 : J (b 3) = -b 2)
  (F : MetricForms.Form E 2) (hF : ∀ u v, F ![u,v] = g.bilinear (J u) v)

include hdim hb h0 h1 h2 h3 hF in

lemma normalSymbol_geometric (ξ : E →L[ℝ] ℝ) (q : Pair) (i : Fin 4) :
    starThree g F (wedgeOne ξ (q 0 • AntiInvariantFrame.realPart g b +
      q 1 • AntiInvariantFrame.imagPart g b)) ![b i] =
        normalSymbol (WithLp.toLp 2 (fun k => ξ (b k))) q i := by
  have he : wedgeOne ξ (q 0 • AntiInvariantFrame.realPart g b +
      q 1 • AntiInvariantFrame.imagPart g b) =
        q 0 • wedgeOne ξ (AntiInvariantFrame.realPart g b) +
          q 1 • wedgeOne ξ (AntiInvariantFrame.imagPart g b) := by
    change (wedgeOneBilinear (E := E) (ofSubsingletonLIE (0 : Fin 1) ξ)) _ = _
    rw [_root_.map_add,_root_.map_smul,_root_.map_smul]
    rfl
  rw [he,starThree_add,starThree_smul,starThree_smul]
  simp only [ContinuousAlternatingMap.add_apply,ContinuousAlternatingMap.smul_apply,smul_eq_mul]
  rw [AntiInvariantFrame.star_wedge_real g hdim b hb J h0 h1 h2 h3 F hF,
    AntiInvariantFrame.star_wedge_imag g hdim b hb J h0 h1 h2 h3 F hF]
  rfl

end TamingCompatibility.LocalMatrixOperator

end
end

section
noncomputable section
namespace TamingCompatibility.LocalMatrixOperator
open MetricModel MetricForms MetricHodge ExteriorForms ContinuousAlternatingMap
open EuclideanEnergy AntiInvariantFrame Function Set
open scoped ContDiff RealInnerProductSpace SchwartzMap Topology

def frameTest (ψ χ : V → MetricForms.Form V 2) (q : V → Pair) : V → MetricForms.Form V 2 :=
  fun x => q x 0 • ψ x + q x 1 • χ x

lemma frameTest_zero {ψ χ : V → MetricForms.Form V 2} {q : V → Pair} {x : V}
    (hq : q x = 0) : frameTest ψ χ q x = 0 := by
  simp [frameTest,hq]

lemma frameTest_tsupport (ψ χ : V → MetricForms.Form V 2) (q : V → Pair) :
    tsupport (frameTest ψ χ q) ⊆ tsupport q := by
  apply closure_minimal _ (isClosed_tsupport q)
  intro x hx
  by_contra h
  exact hx (frameTest_zero (image_eq_zero_of_notMem_tsupport h))

lemma frameTest_smooth {U : Set V} (hU : IsOpen U) {ψ χ : V → MetricForms.Form V 2}
    (hψ : ContDiffOn ℝ ∞ ψ U) (hχ : ContDiffOn ℝ ∞ χ U) {q : V → Pair}
    (hq : ContDiff ℝ ∞ q) (hqU : tsupport q ⊆ U) : ContDiff ℝ ∞ (frameTest ψ χ q) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ tsupport q
  · have hxU := hU.mem_nhds (hqU hx)
    exact (((EuclideanSpace.proj 0).contDiff.comp hq).contDiffAt.smul
      ((hψ x (hqU hx)).contDiffAt hxU)).add
      (((EuclideanSpace.proj 1).contDiff.comp hq).contDiffAt.smul
        ((hχ x (hqU hx)).contDiffAt hxU))
  · have he : frameTest ψ χ q =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [(isClosed_tsupport q).isOpen_compl.mem_nhds hx] with y hy
      exact frameTest_zero (image_eq_zero_of_notMem_tsupport hy)
    exact contDiffAt_const.congr_of_eventuallyEq he

lemma frameTest_compact (ψ χ : V → MetricForms.Form V 2) {q : V → Pair}
    (hq : HasCompactSupport q) : HasCompactSupport (frameTest ψ χ q) :=
  hq.of_isClosed_subset (isClosed_tsupport _) (frameTest_tsupport ψ χ q)

end TamingCompatibility.LocalMatrixOperator

namespace TamingCompatibility.ManifoldForms
open Set
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
lemma pullback_antiInvariantPart (J : AlmostComplexStructure X) (a : TwoForm X)
    (p : X) {z : Space} (hz : z ∈ (extChartAt Model p).target) :
    pullback (antiInvariantPart J a) (extChartAt Model p).symm z =
      (1/2:ℝ) • (pullback a (extChartAt Model p).symm z -
        (pullback a (extChartAt Model p).symm z).compContinuousLinearMap
          (ManifoldHodge.coordinateJ J p z)) := by
  have h := pullback_jAction_chart (⟨J.endomorphism,J.square,J.smooth⟩ :
    SmoothAlmostComplex.AlmostComplexStructure X) a p hz
  change pullback (TamingCompatibility.jAction J a) (extChartAt Model p).symm z =
    (pullback a (extChartAt Model p).symm z).compContinuousLinearMap
      (ManifoldHodge.coordinateJ J p z) at h
  rw [← h]
  rfl

lemma pullback_lift_antiInvariantPart (J : AlmostComplexStructure X) (p : X)
    (β : Space → MetricForms.Form Space 2) {z : Space} (hz : z ∈ (extChartAt Model p).target)
    (hβ : (β z).compContinuousLinearMap (ManifoldHodge.coordinateJ J p z) = -β z) :
    pullback (antiInvariantPart J (chartLift p β)) (extChartAt Model p).symm z = β z := by
  rw [pullback_antiInvariantPart J _ p hz,pullback_chartLift p β hz,hβ]
  module
end TamingCompatibility.ManifoldForms

end
end

end
end
end

end OAI
