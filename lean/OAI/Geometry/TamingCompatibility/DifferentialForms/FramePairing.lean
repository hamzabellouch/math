import Mathlib
import OAI.Geometry.TamingCompatibility.Charts.ChartEnergyIntegral

namespace OAI

section
section
section

section

noncomputable section
namespace TamingCompatibility.AntiInvariantFrame
open ContinuousAlternatingMap MetricModel MetricForms
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma pairing_combination (g : Metric E) (hdim : Module.finrank ℝ E = 4)
    (b : Fin 4 → E) (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0)
    (A B : ℝ) :
    pairing g (A • realPart g b + B • imagPart g b) (A • realPart g b + B • imagPart g b) =
      2 * (A^2+B^2) := by
  rw [pairing_two_eq_sum g hdim b hb]
  simp only [ContinuousAlternatingMap.add_apply,ContinuousAlternatingMap.smul_apply,smul_eq_mul,
    realPart_apply,imagPart_apply,hb]
  simp [Fin.sum_univ_succ,FormMetric.pairLeft,FormMetric.pairRight]
  ring
end TamingCompatibility.AntiInvariantFrame

namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldLocalization ManifoldHodge ManifoldVolume
open Set MetricForms AntiInvariantFrame
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
include hD in
lemma localizedPairing_scalars (p : A.centers) {a : TwoForm X} (ha : antiInvariantPart J a = a)
    (z : Space) :
    pairing (coordinateMetric J α ht p.val z) (localizedFunction A p a z) (localizedFunction A p a z) =
      2 * ((scalar A J α ht D p a 2 z)^2 + (scalar A J α ht D p a 3 z)^2) := by
  by_cases hz : z ∈ (D p).domain
  · rw [scalar_expansion A J α ht D hD p ha]
    exact pairing_combination _ (by simp [Space]) _ ((D p).frame_gram z hz) _ _
  · have hK : z ∉ coordinateSupport A p := fun h => hz (coordinateSupport_domain A J α ht D hD p h)
    rw [localizedFunction_zero_off A p a hK,scalar_zero_off A J α ht D p a 2 hK,
      scalar_zero_off A J α ht D p a 3 hK]
    simp only [(pairing_self_eq_zero _ _).mpr rfl,zero_pow (by decide : 2≠0),add_zero,mul_zero]
end TamingCompatibility.GeometricChart

end
end

section

noncomputable section
namespace TamingCompatibility.AntiInvariantFrame
open ContinuousAlternatingMap MetricModel MetricForms MetricHodge ExteriorForms
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable (g : Metric E) (hdim : Module.finrank ℝ E = 4) (b : Fin 4 → E)
  (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0)
  (J : E →L[ℝ] E) (h0 : J (b 0) = b 1) (h1 : J (b 1) = -b 0)
  (h2 : J (b 2) = b 3) (h3 : J (b 3) = -b 2)
  (F : MetricForms.Form E 2) (hF : ∀ u v, F ![u,v] = g.bilinear (J u) v)
include hdim hb h0 h1 h2 h3 hF in
lemma star_wedge_combination (ξ : E →L[ℝ] ℝ) (A B : ℝ) :
    let a := A • realPart g b + B • imagPart g b
    pairing g (starThree g F (wedgeOne ξ a)) (starThree g F (wedgeOne ξ a)) =
      pairing g (ofSubsingletonLIE (0 : Fin 1) ξ) (ofSubsingletonLIE (0 : Fin 1) ξ) * (A^2+B^2) := by
  dsimp only
  have he : wedgeOne ξ (A • realPart g b + B • imagPart g b) =
      A • wedgeOne ξ (realPart g b) + B • wedgeOne ξ (imagPart g b) := by
    change (wedgeOneBilinear (E := E) (ofSubsingletonLIE (0 : Fin 1) ξ)) _ = _
    rw [_root_.map_add,_root_.map_smul,_root_.map_smul]
    rfl
  rw [he,starThree_add,starThree_smul,starThree_smul,pairing_one_eq_sum g hdim b hb,
    pairing_one_eq_sum g hdim b hb]
  simp only [ContinuousAlternatingMap.add_apply,ContinuousAlternatingMap.smul_apply,smul_eq_mul]
  simp_rw [star_wedge_real g hdim b hb J h0 h1 h2 h3 F hF,
    star_wedge_imag g hdim b hb J h0 h1 h2 h3 F hF]
  simp [Fin.sum_univ_succ]
  ring

include hdim hb h0 h1 h2 h3 hF in
lemma star_wedge_anti (ξ : E →L[ℝ] ℝ) (a : MetricForms.Form E 2)
    (ha : a.compContinuousLinearMap J = -a) :
    pairing g (starThree g F (wedgeOne ξ a)) (starThree g F (wedgeOne ξ a)) =
      (1/2:ℝ) * pairing g (ofSubsingletonLIE (0 : Fin 1) ξ) (ofSubsingletonLIE (0 : Fin 1) ξ) *
        pairing g a a := by
  have he := expansion g hdim b hb J h0 h1 h2 h3 a ha
  rw [he,star_wedge_combination g hdim b hb J h0 h1 h2 h3 F hF,
    pairing_combination g hdim b hb]
  ring
end TamingCompatibility.AntiInvariantFrame

end
end

section

noncomputable section
namespace TamingCompatibility.ManifoldForms
open Bundle ContinuousAlternatingMap
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

def scalarDifferential (f : X → ℝ) : Form X 1 := fun x =>
  ofSubsingletonLIE (𝕜 := ℝ) (E := Space) (F := ℝ) (0 : Fin 1) (mfderiv Model 𝓘(ℝ,ℝ) f x)

omit [IsManifold Model ∞ X] in
lemma pullback_scalarDifferential {f : X → ℝ} {g : Space → X} {z : Space}
    (hf : MDifferentiableAt Model 𝓘(ℝ,ℝ) f (g z))
    (hg : MDifferentiableAt Model Model g z) :
    pullback (scalarDifferential f) g z =
      ofSubsingletonLIE (0 : Fin 1) (fderiv ℝ (f ∘ g) z) := by
  rw [← mfderiv_eq_fderiv,mfderiv_comp z hf hg]
  ext v
  rfl

omit [IsManifold Model ∞ X] in
lemma scalarDifferential_smooth {f : X → ℝ} (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f) :
    Smooth (scalarDifferential f) := by
  intro g U hU hg
  have hc : ContDiffOn ℝ ∞ (f ∘ g) U := (hf.comp_contMDiffOn hg).contDiffOn
  have hd := (contDiffOn_infty_iff_fderivWithin hU.uniqueDiffOn).mp hc |>.2
  apply ((ofSubsingletonLIE (𝕜 := ℝ) (E := Space) (F := ℝ) (0 : Fin 1)).contDiff.comp_contDiffOn hd).congr
  intro z hz
  rw [pullback_scalarDifferential (hf.mdifferentiable (by simp) _) ((hg z hz).contMDiffAt (hU.mem_nhds hz) |>.mdifferentiableAt (by simp)),
    Function.comp_apply,fderivWithin_of_mem_nhds (hU.mem_nhds hz)]

lemma mfderiv_inverseChart_self (x : X) :
    mfderiv Model Model (extChartAt Model x).symm (extChartAt Model x x) =
      ContinuousLinearMap.id ℝ Space := by
  have h := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' (I := Model)
    (x := x) (y := x) (mem_extChartAt_source x)
  rw [ModelWithCorners.Boundaryless.range_eq_univ,mfderivWithin_univ,mfderiv_extChartAt_self] at h
  ext u
  exact congrArg (fun L => L u) h

lemma exteriorDerivative_fun_smul {k : ℕ} {f : X → ℝ} (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f)
    {a : Form X k} (ha : Smooth a) :
    exteriorDerivative (fun x => f x • a x) =
      (fun x => f x • exteriorDerivative a x) + wedgeOne (scalarDifferential f) a := by
  funext x
  let e := extChartAt Model x
  let z := e x
  have hz : z ∈ e.target := e.map_source (mem_extChartAt_source x)
  have hc : ContDiffAt ℝ ∞ (f ∘ e.symm) z :=
    (((hf.comp_contMDiffOn (contMDiffOn_extChartAt_symm x)).contDiffOn) z hz).contDiffAt
      ((isOpen_extChartAt_target x).mem_nhds hz)
  have hca := ((smooth_chart a ha x) z hz).contDiffAt ((isOpen_extChartAt_target x).mem_nhds hz)
  have he : pullback (fun y => f y • a y) e.symm = fun y => (f ∘ e.symm) y • pullback a e.symm y := by
    funext y; ext v; rfl
  change extDeriv (pullback (fun y => f y • a y) e.symm) z = _
  rw [he,ExteriorForms.extDeriv_variable_smul (hc.differentiableAt (by simp)) (hca.differentiableAt (by simp))]
  have hdf : fderiv ℝ (f ∘ e.symm) z = mfderiv Model 𝓘(ℝ,ℝ) f x := by
    rw [← mfderiv_eq_fderiv,mfderiv_comp z (hf.mdifferentiable (by simp) _)
      (((contMDiffOn_extChartAt_symm (n := ∞) x) z hz).contMDiffAt ((isOpen_extChartAt_target x).mem_nhds hz) |>.mdifferentiableAt (by simp))]
    have hinv : e.symm z = x := e.left_inv (mem_extChartAt_source x)
    rw [hinv]
    have hi : mfderiv Model Model e.symm z = ContinuousLinearMap.id ℝ Space := by
      exact mfderiv_inverseChart_self x
    rw [hi]
    rfl
  have hpa : pullback a e.symm z = a x := by
    unfold pullback
    rw [e.left_inv (mem_extChartAt_source x)]
    have hi : mfderiv Model Model e.symm z = ContinuousLinearMap.id ℝ Space :=
      mfderiv_inverseChart_self x
    rw [hi]
    rfl
  have hinv : (f ∘ e.symm) z = f x := congrArg f (e.left_inv (mem_extChartAt_source x))
  rw [hinv,hdf,hpa]
  rfl
end TamingCompatibility.ManifoldForms

end
end

end
end
end

end OAI
