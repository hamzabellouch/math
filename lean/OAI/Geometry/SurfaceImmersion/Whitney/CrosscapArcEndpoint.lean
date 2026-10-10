import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapPairCoordinates
import Mathlib.Topology.UnitInterval

namespace OAI

/-! A continuous ordered double arc ending at a prepared crosscap lies
in its source chart on a full initial parameter interval. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {f : M → ProjectionTarget 3} {p : M}

 theorem crosscap_arc_endpoint (c : SurfaceCrosscapCoordinates f p)
    {Γ : I → M × M} (hΓ : Continuous Γ) (hzero : Γ 0 = (p,p))
    (heq : ∀ t, f (Γ t).1 = f (Γ t).2)
    (hne : ∀ t : I, 0 < (t:ℝ) → (t:ℝ) < 1 → (Γ t).1 ≠ (Γ t).2) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1/3 ∧ ∀ t : I, (t:ℝ) ≤ ε →
      (Γ t).1 ∈ c.source.source ∧ (Γ t).2 ∈ c.source.source ∧
      c.source (Γ t).1 0 = 0 ∧ c.source (Γ t).2 0 = 0 ∧
      c.source (Γ t).1 1 = -c.source (Γ t).2 1 ∧
      (0 < (t:ℝ) → c.source (Γ t).1 1 ≠ 0) := by
  let Θ : ℝ → M × M := Γ ∘ projIcc 0 1 zero_le_one
  have hΘ : Continuous Θ := hΓ.comp continuous_projIcc
  have hΘ0 : Θ 0 = (p,p) := by
    change Γ (projIcc 0 1 zero_le_one 0) = _
    have hp : projIcc 0 1 zero_le_one 0 = (0:I) := Subtype.ext (by simp [projIcc_left])
    rw [hp]
    exact hzero
  have hU : IsOpen (Θ ⁻¹' (c.source.source ×ˢ c.source.source)) :=
    (c.source.open_source.prod c.source.open_source).preimage hΘ
  have h0 : (0:ℝ) ∈ Θ ⁻¹' (c.source.source ×ˢ c.source.source) := by
    change (Θ 0).1 ∈ c.source.source ∧ (Θ 0).2 ∈ c.source.source
    rw [hΘ0]
    exact ⟨c.source_mem,c.source_mem⟩
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0)
  let ε : ℝ := min (r/2) (1/4)
  have hε : 0 < ε := lt_min (half_pos hr) (by norm_num)
  have hεsmall : ε < 1/3 := (min_le_right _ _).trans_lt (by norm_num)
  have hε1 : ε < 1 := hεsmall.trans (by norm_num)
  have hεr : ε < r := (min_le_left _ _).trans_lt (half_lt_self hr)
  refine ⟨ε,hε,hεsmall,?_⟩
  intro t ht
  have hmem : Θ (t:ℝ) ∈ c.source.source ×ˢ c.source.source := by
    apply hball
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg t.property.1]
    exact ht.trans_lt hεr
  have hΘt : Θ (t:ℝ) = Γ t := by
    change Γ (projIcc 0 1 zero_le_one (t:ℝ)) = Γ t
    rw [projIcc_val]
  rw [hΘt] at hmem
  refine ⟨hmem.1,hmem.2,?_⟩
  by_cases ht0 : (t:ℝ) = 0
  · have htz : t = 0 := Subtype.ext ht0
    rw [htz,hzero]
    simp [c.source_center]
  · have hp := c.double_pair hmem.1 hmem.2
      (hne t (lt_of_le_of_ne t.property.1 (Ne.symm ht0)) (ht.trans_lt hε1)) (heq t)
    exact ⟨hp.1,hp.2.1,hp.2.2.1,fun _ => hp.2.2.2⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
