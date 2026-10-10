import Mathlib
import OAI.Geometry.WeakMTW.Geodesics.FlowVariationInjective
import OAI.Geometry.WeakMTW.Geodesics.LocalFanVariation

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal ChartMetric CoordinateGeometry
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 def chartKinetic (x : M) (q : Model n × Model n) : ℝ := metric x q.1 q.2 q.2 / 2

 omit [IsRiemannianManifold (model n) M] [CompactSpace M] in
 theorem chartKinetic_smooth (x : M) :
    ContDiffOn ℝ ∞ (chartKinetic (n := n) x) (stateChart (E := Model n) x).target := by
  have hg : ContDiffOn ℝ ∞ (fun q : Model n × Model n => metric x q.1) (stateChart (E := Model n) x).target :=
    (metric_smooth x).comp contDiffOn_fst (fun q hq => (stateChart_target x q).mp hq)
  exact ((hg.clm_apply contDiffOn_snd).clm_apply contDiffOn_snd).div_const 2

 theorem fanMomentum_coord_deriv_on (x : M) {P : ℝ → TangentBundle (model n) M} {S : Set ℝ}
    (hS : IsOpen S) (h₀ : (0 : ℝ) ∈ S)
    (hP : ContMDiffOn 𝓘(ℝ,ℝ) ((model n).prod (model n)) ∞ P S) {t : ℝ}
    (ht : (t,0) ∈ fanDomain x P) :
    fanMomentum P t = metric x (fanCoordinates x P (t,0)).1
      (fanCoordinates x P (t,0)).2
      (deriv (fun s => (fanCoordinates x P (t,s)).1) 0) := by
  have hm : (t,0) ∈ (Prod.snd ⁻¹' S) ∩ fanDomain x P := ⟨h₀,ht⟩
  have hq := ((fanCoordinates_smooth_on x hP _ hm).contDiffAt
    ((localFanDomain_open x hS hP).mem_nhds hm)).differentiableAt (by simp)
  rw [(FirstVariation.parameter_hasDerivAt hq.fst).deriv]
  exact fanMomentum_coord_on x hS h₀ hP ht

 theorem chart_flow_boundary (x y : M) (t : ℝ) {q : Model n × Model n}
    (hq : q ∈ (stateChart (E := Model n) x).target)
    (hy : geodesicFlow t ((stateChart (E := Model n) x).symm q) ∈ (stateChart (E := Model n) y).source)
    (k : Model n × Model n) :
    metric y (stateChart (E := Model n) y (geodesicFlow t ((stateChart (E := Model n) x).symm q))).1
      (stateChart (E := Model n) y (geodesicFlow t ((stateChart (E := Model n) x).symm q))).2
      (fderiv ℝ (fun r => stateChart (E := Model n) y (geodesicFlow t ((stateChart (E := Model n) x).symm r))) q k).1 =
      metric x q.1 q.2 k.1 + t * fderiv ℝ (chartKinetic x) q k := by
  let a : ℝ → Model n × Model n := fun s => q+s•k
  let S := a ⁻¹' (stateChart (E := Model n) x).target
  let P : ℝ → TangentBundle (model n) M := fun s => (stateChart (E := Model n) x).symm (a s)
  have ha : ContDiff ℝ ∞ a := contDiff_const.add (contDiff_id.smul contDiff_const)
  have ha₀ : a 0 = q := by simp [a]
  have hS : IsOpen S := (stateChart (E := Model n) x).open_target.preimage ha.continuous
  have h₀ : (0 : ℝ) ∈ S := by simpa only [S,mem_preimage,ha₀] using hq
  have hsym : ContMDiffOn 𝓘(ℝ,Model n × Model n) ((model n).prod (model n)) ∞
      (stateChart (E := Model n) x).symm (stateChart (E := Model n) x).target := by
    rw [modelWithCornersSelf_prod]
    exact contMDiffOn_chart_symm (I := (model n).prod (model n))
      (x := (⟨x,0⟩ : TangentBundle (model n) M))
  have hP : ContMDiffOn 𝓘(ℝ,ℝ) ((model n).prod (model n)) ∞ P S :=
    hsym.comp (contMDiff_iff_contDiff.mpr ha).contMDiffOn (fun _ hs => hs)
  have hxP : (0,0) ∈ fanDomain x P := by
    change geodesicFlow 0 ((stateChart (E := Model n) x).symm (a 0)) ∈ (stateChart (E := Model n) x).source
    rw [geodesicFlow_zero,ha₀]
    exact (stateChart (E := Model n) x).map_target hq
  have hyP : (t,0) ∈ fanDomain y P := by
    change geodesicFlow t ((stateChart (E := Model n) x).symm (a 0)) ∈ (stateChart (E := Model n) y).source
    rwa [ha₀]
  have hda : HasDerivAt a k 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).smul_const k).const_add q using 1 <;> (first | rfl | simp)
  have hi : (fun s => fanCoordinates x P (0,s)) =ᶠ[𝓝 (0 : ℝ)] a := by
    filter_upwards [hS.mem_nhds h₀] with s hs
    change stateChart (E := Model n) x (geodesicFlow 0 ((stateChart (E := Model n) x).symm (a s))) = a s
    rw [geodesicFlow_zero,(stateChart (E := Model n) x).right_inv hs]
  have hida : HasDerivAt (fun s => (a s).1) k.1 0 := hda.fst
  have hid : HasDerivAt (fun s => (fanCoordinates x P (0,s)).1) k.1 0 :=
    hida.congr_of_eventuallyEq (hi.mono (fun _ h => congrArg Prod.fst h))
  let Φ : (Model n × Model n) → (Model n × Model n) := fun r => stateChart (E := Model n) y (geodesicFlow t ((stateChart (E := Model n) x).symm r))
  have hΦ := chart_flow_smooth x y t hq hy
  have hDt : HasFDerivAt Φ (fderiv ℝ Φ q) (a 0) := by simpa only [ha₀] using (hΦ.differentiableAt (by simp)).hasFDerivAt
  have htd : HasDerivAt (fun s => (fanCoordinates y P (t,s)).1) (fderiv ℝ Φ q k).1 0 :=
    (hDt.comp_hasDerivAt 0 hda).fst
  have hki := (chartKinetic_smooth x q hq).contDiffAt ((stateChart (E := Model n) x).open_target.mem_nhds hq)
  have hDk : HasFDerivAt (chartKinetic x) (fderiv ℝ (chartKinetic x) q) (a 0) := by
    simpa only [ha₀] using (hki.differentiableAt (by simp)).hasFDerivAt
  have hene : (fun s => ‖(P s).2‖^2) =ᶠ[𝓝 (0 : ℝ)] (fun s => 2*chartKinetic x (a s)) := by
    filter_upwards [hS.mem_nhds h₀] with s hs
    have hps : P s ∈ (stateChart (E := Model n) x).source := (stateChart (E := Model n) x).map_target hs
    have hh := stateChart_pairing x (P s).1 ((stateChart_source x _).mp hps) (P s).2 (P s).2
    have hcoords : stateChart (E := Model n) x (P s) = a s := (stateChart (E := Model n) x).right_inv hs
    have hh' : metric x (stateChart (E := Model n) x (P s)).1 (stateChart (E := Model n) x (P s)).2 (stateChart (E := Model n) x (P s)).2 = ‖(P s).2‖^2 := by
      convert (show metric x (chartAt (Model n) x (P s).1) (stateChart (E := Model n) x (P s)).2 (stateChart (E := Model n) x (P s)).2 = ‖(P s).2‖^2 from
        by simpa only [real_inner_self_eq_norm_sq] using hh) using 1
      rfl
    rw [hcoords] at hh'
    dsimp only [chartKinetic]
    linarith
  have hed := (((hDk.comp_hasDerivAt 0 hda).const_mul 2).congr_of_eventuallyEq hene).deriv
  have hm := fanMomentum_affine_on hS h₀ hP t
  rw [fanMomentum_coord_deriv_on y hS h₀ hP hyP,
    fanMomentum_coord_deriv_on x hS h₀ hP hxP,hid.deriv,htd.deriv,hed] at hm
  have hi₀ : fanCoordinates x P (0,0) = q := (hi.eq_of_nhds).trans ha₀
  rw [hi₀] at hm
  have ht₀ : fanCoordinates y P (t,0) = Φ q := by change Φ (a 0) = Φ q; rw [ha₀]
  rw [ht₀] at hm
  convert hm using 1
  ring

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
