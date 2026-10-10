import OAI.Geometry.SurfaceImmersion.Whitney.QuadraticCrosscapNormalForm
import OAI.Geometry.SurfaceImmersion.Whitney.SurfaceQuadraticDoubleChart

namespace OAI

/-! Source and target charts putting an actual prepared surface crosscap
into the standard umbrella form. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

theorem surface_crosscap_normal_form (F : M → ProjectionTarget 3) (p q : M)
    (hp : p ∈ (chart q).source) {φ : Base → ProjectionTarget 3}
    (hφ : ContDiff ℝ ∞ φ)
    (he : F =ᶠ[𝓝 p] (centeredSurfaceTaylor φ (chart q p)) ∘ chart q)
    (b : Bool) (t : ℝ) (hz : surfaceDirection φ b (chart q p,t) = 0)
    (hreg : Function.Bijective (fderiv ℝ (surfaceDirection φ b) (chart q p,t))) :
    ∃ (c : OpenPartialHomeomorph M Base)
      (e : OpenPartialHomeomorph (Base × ℝ) (ProjectionTarget 3)),
      p ∈ c.source ∧ c p = 0 ∧ 0 ∈ e.source ∧ e 0 = F p ∧
      ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ c c.source ∧
      ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ c.symm c.target ∧
      ContDiff ℝ ∞ e ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      (∀ x ∈ c.source, standardCrosscap (c x) ∈ e.source ∧ F x = e (standardCrosscap (c x))) := by
  let a := chart q p
  obtain ⟨S,e,h0e,he0,heS,heI,hfactor⟩ := quadratic_crosscap_normal_form hφ a b t hz hreg
  let h : Base ≃ₜ Base := (Homeomorph.addRight (-a)).trans S.symm.toHomeomorph
  let c₀ := (chart q).transHomeomorph h
  have hc₀ : (c₀ : M → Base) = fun x => S.symm (chart q x-a) := rfl
  have hc₀i : (c₀.symm : Base → M) = fun x => (chart q).symm (S x+a) := by
    funext x
    change (chart q).symm (S x - -a) = _
    rw [sub_neg_eq_add]
  have hpc : p ∈ c₀.source := hp
  have hcp : c₀ p = 0 := by rw [hc₀]; simp [a]
  have hcS : ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ c₀ c₀.source := by
    rw [hc₀]
    exact S.symm.contDiff.contMDiff.comp_contMDiffOn ((chart_smooth q).sub contMDiffOn_const)
  have hcI : ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ c₀.symm c₀.target := by
    rw [hc₀i]
    apply (chart_symm_smooth q).comp
      (S.contDiff.contMDiff.add contMDiff_const).contMDiffOn
    intro x hx
    change S x - -a ∈ (chart q).target at hx
    change S x+a ∈ (chart q).target
    simpa only [sub_neg_eq_add] using hx
  have hpval : F p = φ a := by
    have hh := he.eq_of_nhds
    change F p = centeredSurfaceTaylor φ a a at hh
    have ha := centeredSurfaceTaylor_value (f := φ) a 0
    have ha' : centeredSurfaceTaylor φ a a = φ a := by
      simpa only [add_zero,map_zero,smul_zero] using ha
    exact hh.trans ha'
  obtain ⟨U,hEq,hU,hpU⟩ := eventually_nhds_iff.mp he
  let W := U ∩ (c₀.source ∩ c₀ ⁻¹' (standardCrosscap ⁻¹' e.source))
  have hW : IsOpen W := hU.inter (c₀.isOpen_inter_preimage
    (e.open_source.preimage standardCrosscap_smooth.continuous))
  have hstd : standardCrosscap (0 : Base) = 0 := by
    apply Prod.ext
    · ext i
      fin_cases i <;> norm_num [standardCrosscap]
    · rfl
  have hpW : p ∈ W := ⟨hpU,hpc,by simpa only [mem_preimage,hcp,hstd] using h0e⟩
  let c := c₀.restrOpen W hW
  refine ⟨c,e,⟨hpc,hpW⟩,hcp,h0e,he0.trans hpval.symm,
    hcS.mono (fun _ hx => hx.1),?_,heS,heI,?_⟩
  · exact hcI.mono (fun x hx => hx.1)
  · intro x hx
    refine ⟨hx.2.2.2,?_⟩
    have hEqx := hEq x hx.2.1
    change F x = centeredSurfaceTaylor φ a (chart q x) at hEqx
    rw [hEqx]
    have hfac := hfactor (c₀ x)
    have hcoord : a+S (c₀ x) = chart q x := by
      rw [hc₀,S.apply_symm_apply]
      abel
    rw [hcoord] at hfac
    exact hfac

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
