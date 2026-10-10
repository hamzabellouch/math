import OAI.Geometry.SurfaceImmersion.Whitney.SmoothDoubleAtlas

namespace OAI

/-! A regular smooth curve lying in an actual double-locus chart has a
smooth local scalar parameter with nonzero derivative. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
namespace SmoothDoubleChart
variable {f : M → ProjectionTarget 3}

theorem curve_parameter (c : SmoothDoubleChart f) {γ : ℝ → surfaceDoublePairs f} {x : ℝ}
    (hc : ContinuousAt γ x) (hx : γ x ∈ c.coord.source)
    (hA : ContMDiffAt 𝓘(ℝ) planeModel ∞ (fun t => (γ t).val.1) x)
    (hB : ContMDiffAt 𝓘(ℝ) planeModel ∞ (fun t => (γ t).val.2) x)
    (hpair : Function.Injective
      ((mfderiv 𝓘(ℝ) planeModel (fun t => (γ t).val.1) x).prod
        (mfderiv 𝓘(ℝ) planeModel (fun t => (γ t).val.2) x))) :
    ∃ h : ℝ → ℝ, ContDiffAt ℝ ∞ h x ∧ deriv h x ≠ 0 ∧
      h x = c.coord (γ x) ∧ γ =ᶠ[𝓝 x] c.coord.symm ∘ h := by
  let h : ℝ → ℝ := fun t => c.expression
    (chart c.left (γ t).val.1,chart c.right (γ t).val.2)
  have hsource := c.source_formula (γ x) hx
  have hleft := ((chart_smooth c.left).contMDiffAt
    ((chart c.left).open_source.mem_nhds hsource.1)).comp x hA
  have hright := ((chart_smooth c.right).contMDiffAt
    ((chart c.right).open_source.mem_nhds hsource.2.1)).comp x hB
  have hh : ContDiffAt ℝ ∞ h x := c.expression_smooth.contDiffAt.comp x
    (hleft.contDiffAt.prodMk hright.contDiffAt)
  have hnear : ∀ᶠ t in 𝓝 x, γ t ∈ c.coord.source := hc.eventually (c.coord.open_source.mem_nhds hx)
  have he : h =ᶠ[𝓝 x] c.coord ∘ γ := by
    filter_upwards [hnear] with t ht
    exact (c.source_formula (γ t) ht).2.2.symm
  have hval : h x = c.coord (γ x) := he.eq_of_nhds
  have hinv : γ =ᶠ[𝓝 x] c.coord.symm ∘ h := by
    filter_upwards [hnear,he] with t ht ht'
    change γ t = c.coord.symm (h t)
    rw [ht']
    exact (c.coord.left_inv ht).symm
  have htarget : h x ∈ c.coord.target := hval ▸ c.coord.map_source hx
  have hDA := c.inverse_left_smooth.contMDiffAt (c.coord.open_target.mem_nhds htarget)
  have hDB := c.inverse_right_smooth.contMDiffAt (c.coord.open_target.mem_nhds htarget)
  have heA : (fun t => (γ t).val.1) =ᶠ[𝓝 x] (fun t => (c.coord.symm t).val.1) ∘ h :=
    hinv.mono fun _ ht => congrArg (fun p => p.val.1) ht
  have heB : (fun t => (γ t).val.2) =ᶠ[𝓝 x] (fun t => (c.coord.symm t).val.2) ∘ h :=
    hinv.mono fun _ ht => congrArg (fun p => p.val.2) ht
  have hDiffeo := hh.contMDiffAt.mdifferentiableAt (by simp)
  have hAD := heA.mfderiv_eq (I := 𝓘(ℝ)) (I' := planeModel)
  have hBD := heB.mfderiv_eq (I := 𝓘(ℝ)) (I' := planeModel)
  rw [mfderiv_comp x (hDA.mdifferentiableAt (by simp)) hDiffeo] at hAD
  rw [mfderiv_comp x (hDB.mdifferentiableAt (by simp)) hDiffeo] at hBD
  refine ⟨h,hh,?_,hval,hinv⟩
  intro hz
  have hhz : HasDerivAt h 0 x := by
    simpa only [hz] using (hh.differentiableAt (by simp)).hasDerivAt
  have hmf : HasMFDerivAt 𝓘(ℝ) 𝓘(ℝ) h x (0 : ℝ →L[ℝ] ℝ) := by
    simpa using hhz.hasFDerivAt.hasMFDerivAt
  have hDz := hmf.mfderiv
  rw [hDz] at hAD hBD
  have hA1 := congrArg (fun L => L (1:ℝ)) hAD
  have hB1 := congrArg (fun L => L (1:ℝ)) hBD
  change (mfderiv 𝓘(ℝ) planeModel (fun t => (γ t).val.1) x) 1 =
    (mfderiv 𝓘(ℝ) planeModel (fun t => (c.coord.symm t).val.1) (h x)) 0 at hA1
  change (mfderiv 𝓘(ℝ) planeModel (fun t => (γ t).val.2) x) 1 =
    (mfderiv 𝓘(ℝ) planeModel (fun t => (c.coord.symm t).val.2) (h x)) 0 at hB1
  rw [map_zero] at hA1 hB1
  have h10 :
      ((mfderiv 𝓘(ℝ) planeModel (fun t => (γ t).val.1) x).prod
        (mfderiv 𝓘(ℝ) planeModel (fun t => (γ t).val.2) x)) 1 =
      ((mfderiv 𝓘(ℝ) planeModel (fun t => (γ t).val.1) x).prod
        (mfderiv 𝓘(ℝ) planeModel (fun t => (γ t).val.2) x)) 0 := by
    apply Prod.ext
    · exact hA1.trans (map_zero _).symm
    · exact hB1.trans (map_zero _).symm
  have hn := hpair h10
  change (1:ℝ) = 0 at hn
  exact one_ne_zero hn

end SmoothDoubleChart
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
