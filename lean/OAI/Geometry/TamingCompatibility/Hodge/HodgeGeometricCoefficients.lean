import Mathlib
import OAI.Geometry.TamingCompatibility.Elliptic.LocalMatrixGarding
import OAI.Geometry.TamingCompatibility.Hodge.HodgeFrameDifferential

namespace OAI

section
section

section
noncomputable section
open scoped ContDiff RealInnerProductSpace
namespace TamingCompatibility.HodgeGeometricCoefficients
open MetricModel MetricForms MetricHodge ExteriorForms ContinuousAlternatingMap
open EuclideanEnergy HodgeFrame HodgeNormalOperator
open HodgeNormalSymbol (W Q)

def baseSymbol (u : W) : V →L[ℝ] Q := LinearMap.toContinuousLinearMap {
  toFun := fun ξ => HodgeNormalSymbol.symbol ξ u
  map_add' := by
    intro a b; ext i; fin_cases i <;>
      simp [HodgeNormalSymbol.symbol,UnitaryFrame.interior] <;> ring
  map_smul' := by
    intro c a; ext i; fin_cases i <;>
      simp [HodgeNormalSymbol.symbol,UnitaryFrame.interior] <;> ring }

def frame (g : V → Metric V) (b : Fin 4 → V → V) (j : Fin 6) (x : V) : MetricForms.Form V 2 :=
  basisForm (g x) (fun i => b i x) j
def starFrame (g : V → Metric V) (J : V → V →L[ℝ] V) (F : V → MetricForms.Form V 2)
    (b : Fin 4 → V → V) (j : Fin 6) (x : V) : MetricForms.Form V 2 :=
  starTwo (g x) (J x) (F x) (frame g b j x)
def principal (b : Fin 4 → V → V) (i : Fin 4) (x : V) : W →L[ℝ] Q :=
  HodgeFrozenEnergy.coefficient (fun j => b j x) i
def lower (g : V → Metric V) (J : V → V →L[ℝ] V) (F : V → MetricForms.Form V 2)
    (b : Fin 4 → V → V) (x : V) : W →L[ℝ] Q :=
  HodgeNormalOperator.lower (g x) (F x) (fun i => b i x) (frame g b) (starFrame g J F b) x

lemma principal_smooth {b : Fin 4 → V → V} {U : Set V}
    (hb : ∀ i, ContDiffOn ℝ ∞ (b i) U) (i : Fin 4) :
    ContDiffOn ℝ ∞ (principal b i) U := by
  apply contDiffOn_clm_apply.mpr
  intro u
  change ContDiffOn ℝ ∞ (fun x => baseSymbol u (WithLp.toLp 2 (fun j => b j x i))) U
  apply (baseSymbol u).contDiff.comp_contDiffOn
  apply (contDiffOn_piLp 2).mpr
  intro j
  exact (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp_contDiffOn (hb j)

lemma frame_smooth {g : V → Metric V} {b : Fin 4 → V → V} {U : Set V}
    (hg : ContDiffOn ℝ ∞ (fun x => (g x).bilinear) U)
    (hb : ∀ i, ContDiffOn ℝ ∞ (b i) U) (j : Fin 6) :
    ContDiffOn ℝ ∞ (frame g b j) U := basisForm_smooth hg hb j

lemma frameVector_smooth {b : Fin 4 → V → V} {a : V → MetricForms.Form V 1} {U : Set V}
    (hb : ∀ i, ContDiffOn ℝ ∞ (b i) U) (ha : ContDiffOn ℝ ∞ a U) :
    ContDiffOn ℝ ∞ (fun x => LocalMatrixOperator.frameVector (fun i => b i x) (a x)) U := by
  apply (contDiffOn_piLp 2).mpr
  intro i
  apply FormSmooth.contDiffOn_apply ha
  intro k
  fin_cases k
  exact hb i

lemma derivative_smooth {a : V → MetricForms.Form V 2} {U : Set V}
    (hU : IsOpen U) (ha : ContDiffOn ℝ ∞ a U) :
    ContDiffOn ℝ ∞ (extDeriv a) U := by
  change ContDiffOn ℝ ∞ (fun x => (alternatizeUncurryFinCLM ℝ V ℝ) (fderiv ℝ a x)) U
  exact (alternatizeUncurryFinCLM ℝ V ℝ).contDiff.comp_contDiffOn
    (ha.fderiv_of_isOpen (m := ∞) hU (by simp))

variable (g : V → Metric V) (J : V → V →L[ℝ] V) (F : V → MetricForms.Form V 2)
  (b : Fin 4 → V → V) {U : Set V} (hU : IsOpen U)
  (hg : ContDiffOn ℝ ∞ (fun x => (g x).bilinear) U) (hJ : ContDiffOn ℝ ∞ J U)
  (hJs : ∀ x ∈ U, ∀ u, J x (J x u) = -u)
  (hgJ : ∀ x ∈ U, ∀ u v, (g x).bilinear (J x u) (J x v) = (g x).bilinear u v)
  (hF : ContDiffOn ℝ ∞ F U) (hb : ∀ i, ContDiffOn ℝ ∞ (b i) U)
include hU hg hJ hJs hgJ hF hb
lemma starFrame_smooth (j : Fin 6) : ContDiffOn ℝ ∞ (starFrame g J F b j) U :=
  SmoothHodge.starTwo_contDiffOn g J (by simp [V]) hU hg hJ hJs hgJ hF (frame_smooth hg hb j)

lemma lower_smooth : ContDiffOn ℝ ∞ (lower g J F b) U := by
  have hstar := SmoothHodge.starThreeCLM_contDiffOn g J (by simp [V]) hU hg hJ hJs hgJ hF
  have hψ (j : Fin 6) := derivative_smooth hU (frame_smooth hg hb j)
  have hφ (j : Fin 6) := derivative_smooth hU (starFrame_smooth g J F b hU hg hJ hJs hgJ hF hb j)
  apply contDiffOn_clm_apply.mpr
  intro q
  have he (x : V) : lower g J F b x q = join
      (LocalMatrixOperator.frameVector (fun i => b i x)
        (starThreeCLM (g x) (F x) (∑ j, q j • extDeriv (starFrame g J F b j) x)))
      (LocalMatrixOperator.frameVector (fun i => b i x)
        (starThreeCLM (g x) (F x) (∑ j, q j • extDeriv (frame g b j) x))) := by
    simp only [lower,HodgeNormalOperator.lower,_root_.add_apply,ContinuousLinearMap.comp_apply,
      combineThree_apply,left_add_right]
  simp_rw [he]
  change ContDiffOn ℝ ∞ (fun x => joinCLM (_, _)) U
  apply joinCLM.contDiff.comp_contDiffOn
  apply ContDiffOn.prodMk
  · apply frameVector_smooth hb
    apply hstar.clm_apply
    exact ContDiffOn.sum (fun j _ => (hφ j).const_smul (q j))
  · apply frameVector_smooth hb
    apply hstar.clm_apply
    exact ContDiffOn.sum (fun j _ => (hψ j).const_smul (q j))
end TamingCompatibility.HodgeGeometricCoefficients

end
end

section
noncomputable section
open MeasureTheory Filter Topology
open scoped SchwartzMap
namespace TamingCompatibility.HodgeMatrixEnergy
open EuclideanEnergy
open MatrixEnergy (continuous_cutoff cutoff_bound exists_small_error)
variable {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
def patchPrincipal (c : Fin 4 → W →L[ℝ] Q) (a : Fin 4 → V → W →L[ℝ] Q)
    {x₀ : V} (φ : ContDiffBump x₀) : Fin 4 → V → W →L[ℝ] Q :=
  fun i x => φ x • (a i x-c i) + c i

def patchLower (b : V → W →L[ℝ] Q) {x₀ : V} (φ : ContDiffBump x₀) : V → W →L[ℝ] Q :=
  fun x => φ x • b x

lemma patchPrincipal_continuous {U : Set V} (hU : IsOpen U)
    (c : Fin 4 → W →L[ℝ] Q) (a : Fin 4 → V → W →L[ℝ] Q)
    (ha : ∀ i, ContinuousOn (a i) U) {x₀ : V} (φ : ContDiffBump x₀)
    (hφ : tsupport φ ⊆ U) (i : Fin 4) : Continuous (patchPrincipal c a φ i) :=
  (continuous_cutoff hU ((ha i).sub continuousOn_const) φ hφ).add continuous_const

lemma patchPrincipal_bound {U : Set V} (c : Fin 4 → W →L[ℝ] Q)
    (a : Fin 4 → V → W →L[ℝ] Q) {δ : ℝ} (hδ : 0 ≤ δ)
    (ha : ∀ x ∈ U, ∀ i, ‖a i x-c i‖ ≤ δ) {x₀ : V} (φ : ContDiffBump x₀)
    (hφ : tsupport φ ⊆ U) (x : V) (i : Fin 4) : ‖patchPrincipal c a φ i x-c i‖ ≤ δ := by
  simpa only [patchPrincipal,add_sub_cancel_right] using
    cutoff_bound hδ (fun x hx => ha x hx i) φ hφ x

lemma system_patch_eq (c : Fin 4 → W →L[ℝ] Q)
    (a : Fin 4 → V → W →L[ℝ] Q) (b : V → W →L[ℝ] Q)
    {x₀ : V} (φ : ContDiffBump x₀) (f : Field)
    (hf : ∀ j, tsupport (f j) ⊆ Metric.closedBall x₀ φ.rIn) (x : V) :
    system (patchPrincipal c a φ) (patchLower b φ) f x = system a b f x := by
  by_cases hx : x ∈ Metric.closedBall x₀ φ.rIn
  · simp only [system,patchPrincipal,patchLower,φ.one_of_mem_closedBall hx,
      one_smul,sub_add_cancel]
  · have hn (j : Fin 6) : x ∉ tsupport (f j) := fun h => hx (hf j h)
    have hv : value f x = 0 := by
      ext j
      change f j x = 0
      exact image_eq_zero_of_notMem_tsupport (hn j)
    have hd (i : Fin 4) : derivative f i x = 0 := by
      ext j
      change coordinateDeriv i (f j) x = 0
      exact image_eq_zero_of_notMem_tsupport (fun h => hn j (SchwartzMap.tsupport_lineDerivOp_subset _ _ h))
    simp only [system,hv,hd,map_zero,Finset.sum_const_zero,add_zero]

theorem local_garding (c : Fin 4 → W →L[ℝ] Q) {K : ℝ} (hK : 0 < K)
    (henergy : ∀ f : Field, (∫ x, gradient f x) ≤
      K * (∫ x, ‖constantSystem c f x‖^2))
    {U : Set V} (hU : IsOpen U) {x₀ : V} (hx₀ : x₀ ∈ U)
    (a : Fin 4 → V → W →L[ℝ] Q) (b : V → W →L[ℝ] Q)
    (ha : ∀ i, ContinuousOn (a i) U) (hb : ContinuousOn b U)
    (ha₀ : ∀ i, a i x₀ = c i) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧ Metric.closedBall x₀ (2*r) ⊆ U ∧
      ∀ f : Field, (∀ j, tsupport (f j) ⊆ Metric.closedBall x₀ r) →
        (∫ x, gradient f x) ≤ 4*K * (∫ x, ‖system a b f x‖^2) +
          8*K*C^2 * (∫ x, ‖value f x‖^2) := by
  obtain ⟨δ,hδ,hsmall⟩ := exists_small_error hK
  let C := ‖b x₀‖ + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  have hae : ∀ᶠ x in 𝓝 x₀, ∀ i, ‖a i x-c i‖ ≤ δ := by
    apply Filter.eventually_all.mpr
    intro i
    have hc : ContinuousAt (fun x => ‖a i x-c i‖) x₀ :=
      (((ha i).continuousAt (hU.mem_nhds hx₀)).sub continuousAt_const).norm
    have hz : ‖a i x₀-c i‖ < δ := by simpa only [ha₀ i,sub_self,norm_zero] using hδ
    exact (hc.eventually (gt_mem_nhds hz)).mono (fun _ h => h.le)
  have hbe : ∀ᶠ x in 𝓝 x₀, ‖b x‖ ≤ C := by
    have hz : ‖b x₀‖ < C := by dsimp only [C]; linarith
    exact (((hb.continuousAt (hU.mem_nhds hx₀)).norm).eventually
      (gt_mem_nhds hz)).mono (fun _ h => h.le)
  have he : ∀ᶠ x in 𝓝 x₀, x ∈ U ∧ (∀ i, ‖a i x-c i‖ ≤ δ) ∧ ‖b x‖ ≤ C :=
    (show ∀ᶠ x in 𝓝 x₀, x ∈ U from hU.mem_nhds hx₀).and (hae.and hbe)
  obtain ⟨ε,hε,hεgood⟩ := Metric.mem_nhds_iff.mp he
  let φ : ContDiffBump x₀ := {
    rIn := ε/4
    rOut := ε/2
    rIn_pos := by positivity
    rIn_lt_rOut := by linarith }
  have hgood (x : V) (hx : x ∈ tsupport φ) :
      x ∈ U ∧ (∀ i, ‖a i x-c i‖ ≤ δ) ∧ ‖b x‖ ≤ C := by
    rw [φ.tsupport_eq] at hx
    apply hεgood
    have hh := Metric.mem_closedBall.mp hx
    change dist x x₀ ≤ ε/2 at hh
    exact Metric.mem_ball.mpr (by linarith)
  have hφU : tsupport φ ⊆ U := fun x hx => (hgood x hx).1
  have ha' := patchPrincipal_continuous hU c a ha φ hφU
  have hb' : Continuous (patchLower b φ) := continuous_cutoff hU hb φ hφU
  have hap (x : V) (i : Fin 4) : ‖patchPrincipal c a φ i x-c i‖ ≤ δ :=
    patchPrincipal_bound c a hδ.le (fun x hx => (hgood x hx).2.1) φ (Set.Subset.refl _) x i
  have hbp (x : V) : ‖patchLower b φ x‖ ≤ C :=
    cutoff_bound hC.le (fun x hx => (hgood x hx).2.2) φ (Set.Subset.refl _) x
  refine ⟨ε/4,C,by positivity,hC,?_,?_⟩
  · intro x hx
    apply hφU
    rw [φ.tsupport_eq]
    simpa only [φ,show (2:ℝ)*(ε/4) = ε/2 by ring] using hx
  · intro f hf
    have h := garding c hK hsmall henergy (patchPrincipal c a φ) (patchLower b φ)
      ha' hb' hap hbp f
    simpa only [system_patch_eq c a b φ f hf] using h

end TamingCompatibility.HodgeMatrixEnergy

end
end

end
end

end OAI
