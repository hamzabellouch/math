import Mathlib
import OAI.Geometry.TamingCompatibility.Elliptic.MatrixGarding
import OAI.Geometry.TamingCompatibility.Charts.CoefficientCutoff

namespace OAI

section
section
section

section

noncomputable section
open MeasureTheory
open scoped SchwartzMap
namespace TamingCompatibility.MatrixEnergy
open EuclideanEnergy
open Filter Topology

theorem local_garding (c : Fin 4 → Pair →L[ℝ] V) {K : ℝ} (hK : 0 < K)
    (henergy : ∀ A B : S, (∫ x, gradientEnergy A B x) ≤
      K * (∫ x, ‖constantSystem c A B x‖^2))
    {U : Set V} (hU : IsOpen U) {x₀ : V} (hx₀ : x₀ ∈ U)
    (a : Fin 4 → V → Pair →L[ℝ] V) (b : V → Pair →L[ℝ] V)
    (ha : ∀ i, ContinuousOn (a i) U) (hb : ContinuousOn b U)
    (ha₀ : ∀ i, a i x₀ = c i) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧ Metric.closedBall x₀ (2*r) ⊆ U ∧
      ∀ A B : S, tsupport A ⊆ Metric.closedBall x₀ r →
        tsupport B ⊆ Metric.closedBall x₀ r →
        (∫ x, gradientEnergy A B x) ≤ 4*K * (∫ x, ‖system a b A B x‖^2) +
          8*K*C^2 * (∫ x, (A x)^2+(B x)^2) := by
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
  · intro A B hA hB
    have h := garding c hK hsmall henergy (patchPrincipal c a φ) (patchLower b φ)
      ha' hb' hap hbp A B
    simpa only [system_patch_eq c a b φ A B hA hB] using h

end TamingCompatibility.MatrixEnergy

end
end

section

noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff SchwartzMap
namespace TamingCompatibility.LocalMatrixOperator
open EuclideanEnergy MetricModel MetricForms MetricHodge ExteriorForms AntiInvariantFrame

lemma supported_operator_eq {U : Set V} (hU : IsOpen U)
    (g : V → Metric V) (F ψ χ : V → MetricForms.Form V 2)
    (hψ : ContDiffOn ℝ ∞ ψ U) (hχ : ContDiffOn ℝ ∞ χ U)
    (A B : S) (hA : tsupport A ⊆ U) (hB : tsupport B ⊆ U) (x : V) :
    oneVector (starThree (g x) (F x)
      (extDeriv (fun y => A y • ψ y + B y • χ y) x)) =
      MatrixEnergy.system (fun i x => principal (g x) (F x) (ψ x) (χ x) i)
        (fun x => lower (g x) (F x) ψ χ x) A B x := by
  by_cases hx : x ∈ U
  · simpa only [MatrixEnergy.system,coordinateDeriv,
      SchwartzMap.lineDerivOp_apply_eq_fderiv] using
      operator_expansion (g x) (F x) (A.differentiableAt) (B.differentiableAt)
        ((hψ.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hx))
        ((hχ.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hx))
  · have hnA : x ∉ tsupport A := fun h => hx (hA h)
    have hnB : x ∉ tsupport B := fun h => hx (hB h)
    have hAz := image_eq_zero_of_notMem_tsupport hnA
    have hBz := image_eq_zero_of_notMem_tsupport hnB
    have hdA : fderiv ℝ A x = 0 := fderiv_of_notMem_tsupport ℝ hnA
    have hdB : fderiv ℝ B x = 0 := fderiv_of_notMem_tsupport ℝ hnB
    have he : (fun y => A y • ψ y + B y • χ y) =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hnA,
        notMem_tsupport_iff_eventuallyEq.mp hnB] with y hAy hBy
      simp only [hAy,hBy,zero_smul,add_zero,Pi.zero_apply]
    have hd : extDeriv (fun y => A y • ψ y + B y • χ y) x = 0 := by
      unfold extDeriv
      rw [he.fderiv_eq, fderiv_fun_const]
      exact map_zero _
    simp only [hd,starThree_zero,map_zero,MatrixEnergy.system,coordinateDeriv,
      SchwartzMap.lineDerivOp_apply_eq_fderiv,hdA,hdB,zero_apply,
      hAz,hBz,show pair 0 0 = 0 by ext i; fin_cases i <;> rfl,Finset.sum_const_zero,add_zero]

theorem geometric_local_garding {U : Set V} (hU : IsOpen U) {x₀ : V} (hx₀ : x₀ ∈ U)
    (g : V → Metric V) (F ψ χ : V → MetricForms.Form V 2)
    (hstar : ContDiffOn ℝ ∞ (fun x => starThreeCLM (g x) (F x)) U)
    (hψ : ContDiffOn ℝ ∞ ψ U) (hχ : ContDiffOn ℝ ∞ χ U)
    (b : Module.Basis (Fin 4) ℝ V)
    (hb : ∀ i j, (g x₀).bilinear (b i) (b j) = if i = j then 1 else 0)
    (J : V →L[ℝ] V) (h0 : J (b 0) = b 1) (h1 : J (b 1) = -b 0)
    (h2 : J (b 2) = b 3) (h3 : J (b 3) = -b 2)
    (hF : ∀ u v, F x₀ ![u,v] = (g x₀).bilinear (J u) v)
    (hψ₀ : ψ x₀ = realPart (g x₀) b) (hχ₀ : χ x₀ = imagPart (g x₀) b) :
    ∃ r K C : ℝ, 0 < r ∧ 0 < K ∧ 0 < C ∧ Metric.closedBall x₀ (2*r) ⊆ U ∧
      ∀ A B : S, tsupport A ⊆ Metric.closedBall x₀ r →
        tsupport B ⊆ Metric.closedBall x₀ r →
        (∫ x, gradientEnergy A B x) ≤ K * (∫ x,
          ‖oneVector (starThree (g x) (F x)
            (extDeriv (fun y => A y • ψ y + B y • χ y) x))‖^2) +
          C * (∫ x, (A x)^2+(B x)^2) := by
  let K := DirectionalEnergy.coordinateConstant b * evaluationConstant b
  have hK : 0 < K := mul_pos (DirectionalEnergy.coordinateConstant_pos b)
    (evaluationConstant_pos b)
  let c := principal (g x₀) (F x₀) (realPart (g x₀) b) (imagPart (g x₀) b)
  have henergy := frozen_geometric_energy (g x₀) b hb J h0 h1 h2 h3 (F x₀) hF
  obtain ⟨r,C,hr,hC,hrU,he⟩ := MatrixEnergy.local_garding c hK henergy hU hx₀
    (fun i x => principal (g x) (F x) (ψ x) (χ x) i)
    (fun x => lower (g x) (F x) ψ χ x)
    (fun i => (principal_smooth hstar hψ hχ i).continuousOn)
    (lower_smooth hU hstar hψ hχ).continuousOn (fun _ => by simp only [hψ₀,hχ₀,c])
  refine ⟨r,4*K,8*K*C^2,hr,by positivity,by positivity,hrU,?_⟩
  intro A B hA hB
  have hrU' : Metric.closedBall x₀ r ⊆ U :=
    (Metric.closedBall_subset_closedBall (by linarith)).trans hrU
  simpa only [supported_operator_eq hU g F ψ χ hψ hχ A B (hA.trans hrU') (hB.trans hrU')]
    using he A B hA hB

end TamingCompatibility.LocalMatrixOperator

end
end

end
end
end

end OAI
