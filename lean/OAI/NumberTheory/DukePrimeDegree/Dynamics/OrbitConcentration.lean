import OAI.NumberTheory.DukePrimeDegree.Dynamics.OrbitSupport

namespace OAI

/-!
# Concentration from compactly controlled returns

If nearby returns of an ergodic action lie in a fixed compact set of
translations in a larger group, the whole measure lies on one orbit of
that group. This is the topological-measure argument in the reverse
implication of EKL (2006), Proposition 4.3.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology Classical

namespace DukePrimeDegree

variable {H C Y : Type*} [Group H] [Countable H] [Group C]
  [TopologicalSpace C] [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [OpensMeasurableSpace Y]
  [MulAction H Y] [MeasurableConstSMul H Y] [MulAction C Y] [ContinuousSMul C Y]

/-- Strong returns with compact translation parameters force a single
orbit, once the ergodic component has a support point in the return set. -/
theorem ae_on_single_orbit_of_compact_returns
    (μ : Measure Y) [ErgodicSMul H Y μ]
    (φ : H →* C) (hφ : ∀ h : H, ∀ y : Y, (φ h) • y = h • y)
    (K : Set Y) (hK : MeasurableSet K)
    (z : Y) (hz : z ∈ (μ.restrict K).support)
    (V : Set Y) (hV : IsOpen V) (hzV : z ∈ V)
    (L : Set C) (hL : IsCompact L)
    (hret : ∀ u ∈ K ∩ V, ∀ h : H, h • u ∈ K ∩ V →
      ∃ c ∈ L, c • u = h • u) :
    ∀ᵐ y ∂μ, ∃ c : C, c • z = y := by
  filter_upwards [ae_restricted_support_subset_orbit_closure (H := H) μ K hK] with y hy
  let F : Set Y := {w | w ∈ K ∧ ∃ h : H, h • y = w}
  have hzF : z ∈ closure F := hy hz
  obtain ⟨u, huV, huK, h, hhu⟩ := mem_closure_iff.mp hzF V hV hzV
  have hu : u ∈ K ∩ V := ⟨huK, huV⟩
  let P : Set Y := (fun c : C => c • u) '' L
  have hP : IsClosed P := (hL.image (continuous_id.smul continuous_const)).isClosed
  have hsub : V ∩ F ⊆ P := by
    rintro w ⟨hwV, hwK, k, hkw⟩
    have hkhu : (k * h⁻¹) • u = w := by
      rw [← hhu, mul_smul, inv_smul_smul]
      exact hkw
    obtain ⟨c, hc, hcu⟩ := hret u hu (k * h⁻¹) (by rw [hkhu]; exact ⟨hwK, hwV⟩)
    exact ⟨c, hc, hcu.trans hkhu⟩
  have hzVF : z ∈ closure (V ∩ F) := by
    apply mem_closure_iff.mpr
    intro W hW hzW
    obtain ⟨w, hwWV, hwF⟩ := mem_closure_iff.mp hzF (W ∩ V) (hW.inter hV) ⟨hzW, hzV⟩
    exact ⟨w, hwWV.1, hwWV.2, hwF⟩
  have hzP : z ∈ P := hP.closure_subset_iff.mpr hsub hzVF
  obtain ⟨c, _, hcu⟩ := hzP
  have heq : (c * φ h) • y = z := by
    rw [mul_smul, hφ, hhu]
    exact hcu
  refine ⟨(c * φ h)⁻¹, ?_⟩
  rw [← heq, inv_smul_smul]

end DukePrimeDegree

end

end OAI
