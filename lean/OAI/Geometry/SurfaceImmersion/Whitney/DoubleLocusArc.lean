import OAI.Geometry.SurfaceImmersion.Whitney.DoubleLocusChart

namespace OAI

/-! A regular zero of the pair-chart difference map has an actual smooth,
injective interval parametrization of its local zero set. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

theorem double_locus_local_arc {f : Base × Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (p : Base × Base) (hp : f p = 0)
    (hsurj : Function.Surjective (fderiv ℝ f p)) :
    ∃ (U : Set (Base × Base)) (ε : ℝ) (γ : ℝ → Base × Base),
      IsOpen U ∧ p ∈ U ∧ 0 < ε ∧ γ 0 = p ∧
      ContDiffOn ℝ ∞ γ (Ioo (-ε) ε) ∧ (Ioo (-ε) ε).InjOn γ ∧
      γ '' Ioo (-ε) ε = U ∩ f ⁻¹' {0} := by
  obtain ⟨e,hpe,hef,he,heinv⟩ := double_locus_submersion_chart hf p hsurj
  let c := (e p).2
  let τ : ℝ → ProjectionTarget 3 × ℝ := fun t => (0,c+t)
  have hτ : ContDiff ℝ ∞ τ := contDiff_const.prodMk (contDiff_const.add contDiff_id)
  have hτ0 : τ 0 = e p := by
    apply Prod.ext
    · exact (hef p).trans hp |>.symm
    · simp [τ,c]
  have hpre : ∀ᶠ t in 𝓝 (0 : ℝ), τ t ∈ e.target :=
    hτ.continuous.continuousAt.preimage_mem_nhds (by rw [hτ0]; exact e.open_target.mem_nhds (e.map_source hpe))
  obtain ⟨ε,hε,hεtarget⟩ := Metric.eventually_nhds_iff.mp hpre
  let J := Ioo (-ε) ε
  have hJ (t : ℝ) (ht : t ∈ J) : τ t ∈ e.target := by
    apply hεtarget
    rw [dist_zero_right,Real.norm_eq_abs,abs_lt]
    exact ht
  let U := e.source ∩ e ⁻¹' {z | z.2 ∈ Ioo (c-ε) (c+ε)}
  let γ : ℝ → Base × Base := e.symm ∘ τ
  have hU : IsOpen U := e.isOpen_inter_preimage (isOpen_Ioo.preimage continuous_snd)
  have hpU : p ∈ U := by
    refine ⟨hpe,?_⟩
    change c ∈ Ioo (c-ε) (c+ε)
    constructor <;> linarith
  have hγ0 : γ 0 = p := by
    change e.symm (τ 0) = p
    rw [hτ0,e.left_inv hpe]
  have hγ : ContDiffOn ℝ ∞ γ J := heinv.comp hτ.contDiffOn hJ
  have hinj : J.InjOn γ := by
    intro s hs t ht hst
    have hh := e.symm.injOn (hJ s hs) (hJ t ht) hst
    have hsec := congrArg Prod.snd hh
    exact add_left_cancel hsec
  refine ⟨U,ε,γ,hU,hpU,hε,hγ0,hγ,hinj,?_⟩
  apply Set.Subset.antisymm
  · rintro x ⟨t,ht,rfl⟩
    have htT := hJ t ht
    have hback : e (γ t) = τ t := e.right_inv htT
    refine ⟨⟨e.map_target htT,?_⟩,?_⟩
    · change (e (γ t)).2 ∈ Ioo (c-ε) (c+ε)
      rw [hback]
      change c+t ∈ Ioo (c-ε) (c+ε)
      constructor <;> have := ht.1 <;> have := ht.2 <;> linarith
    · change f (γ t) = 0
      rw [← hef,hback]
  · intro x hx
    have hxt : (e x).2 ∈ Ioo (c-ε) (c+ε) := hx.1.2
    let t := (e x).2-c
    have ht : t ∈ J := by
      constructor <;> dsimp [t] <;> have := hxt.1 <;> have := hxt.2 <;> linarith
    refine ⟨t,ht,?_⟩
    change e.symm (τ t) = x
    have hτt : τ t = e x := by
      apply Prod.ext
      · exact ((hef x).trans hx.2).symm
      · change c+((e x).2-c) = (e x).2
        ring
    rw [hτt,e.left_inv hx.1.1]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
