import Mathlib
import OAI.Geometry.PrescribedPotential.FiniteSobolevEmbedding
import OAI.Geometry.PrescribedPotential.GlobalPartition
import OAI.Geometry.PrescribedPotential.GlobalStrongEmbedding
import OAI.Geometry.PrescribedPotential.KaehlerClosedDerivatives

namespace OAI

/-! Global Finite Embedding. -/

section

 

noncomputable section
open Set Filter Topology
open scoped ContDiff Classical
namespace GlobalElliptic
open Anticanonical EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace Localizers
variable (D : Localizers A ι)

omit [T2Space X] [CompactSpace X] in
lemma exists_weight_ne_zero (x : X) : ∃ p, D.weight p x ≠ 0 := by
  by_contra! hn
  have h := D.sum_one x
  simp only [hn, Finset.sum_const_zero] at h
  exact zero_ne_one h

lemma strong_contDiffOn (s : ℝ) (hs : (Module.finrank ℝ (EC d) : ℝ) < 2*s)
    (N : ℕ) (hN : (Module.finrank ℝ (EC d) : ℝ) < 2*(s - 2*N))
    (u : D.Sobolev s) (i : Fin A.count) :
    ContDiffOn ℝ N ((D.strong s u) ∘ (A.euclideanChart i).symm)
      (A.euclideanChart i).target := by
  intro z hz
  let q := A.euclideanChart i
  let x := q.symm z
  obtain ⟨p,hp⟩ := D.exists_weight_ne_zero x
  let e := A.euclideanChart (D.index p)
  have hx : x ∈ e.source := D.support_sub p (subset_tsupport _ hp)
  let t := q.symm.trans e
  have ht : z ∈ t.source := ⟨hz,hx⟩
  have hf := (strongEmbedding_contDiff s hs N hN (u.val p)).contDiffAt (x := t z)
  have htrans := ((A.euclidean_transition_smooth i (D.index p)).contDiffAt
    (t.open_source.mem_nhds ht)).of_le (show (N : ℕ∞ω) ≤ ∞ from ENat.natCast_le_of_coe_top_le_withTop le_rfl N)
  have hw := ((D.weight p).smooth i).contDiffAt (q.open_target.mem_nhds hz)
  have hn : (D.weight p ∘ q.symm) z ≠ 0 := hp
  have hsm := (hf.comp z htrans).mul ((hw.of_le (show (N : ℕ∞ω) ≤ ∞ from ENat.natCast_le_of_coe_top_le_withTop le_rfl N)).inv hn)
  apply (hsm.congr_of_eventuallyEq ?_).contDiffWithinAt
  have hne : ∀ᶠ y in 𝓝 z, (D.weight p ∘ q.symm) y ≠ 0 :=
    hw.continuousAt.eventually_ne hn
  filter_upwards [t.open_source.mem_nhds ht, hne] with y hy hny
  change D.strong s u (q.symm y) = strongEmbedding s hs (u.val p) (e (q.symm y)) /
    D.weight p (q.symm y)
  rw [D.strong_localized s hs]
  have hyv : q.symm y ∈ e.source := hy.2
  change D.strong s u (q.symm y) = (if e (q.symm y) ∈ e.target then
    D.weight p (e.symm (e (q.symm y))) * D.strong s u (e.symm (e (q.symm y))) else 0) / _
  rw [ite_eq_left (e.mapsTo hyv), e.left_inv hyv]
  exact (mul_div_cancel_left₀ _ hny).symm
end Localizers
end GlobalElliptic

end
end

end OAI
