import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Metrizable.Basic

namespace OAI

/-!
# A small weakly open piece of a norm-separable compact set

The Baire-category step of the isometric fixed-point argument. It is used
only on the compact orbit hull of a countably generated unitary subgroup.
-/

noncomputable section

open Topology TopologicalSpace

namespace BoundedHochschild
namespace KadisonRingrose

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma weak_closedBall (a : E) (r : ℝ) :
    IsClosed ((toWeakSpace ℂ E) '' Metric.closedBall a r) := by
  rw [← closure_eq_iff_isClosed, ← (convex_closedBall a r).toWeakSpace_closure ℂ,
    Metric.isClosed_closedBall.closure_eq]

/-- A nonempty weakly compact, norm-separable set has a nonempty relatively
weakly open subset of arbitrarily small norm diameter. -/
theorem weakCompact_small_open_piece (K : Set (WeakSpace ℂ E))
    (hK : IsCompact K) (hne : K.Nonempty)
    (hsep : IsSeparable ((toWeakSpace ℂ E).symm '' K))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ U : Set (WeakSpace ℂ E), IsOpen U ∧ (K ∩ U).Nonempty ∧
      ∀ x ∈ K ∩ U, ∀ y ∈ K ∩ U,
        ‖(toWeakSpace ℂ E).symm x - (toWeakSpace ℂ E).symm y‖ < ε := by
  classical
  obtain ⟨S, _hSK, hcount, hdense⟩ := hsep.exists_countable_dense_subset
  have : Countable S := hcount.to_subtype
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have : Nonempty K := hne.to_subtype
  let B (a : S) : Set K := {x | (toWeakSpace ℂ E).symm x.val ∈ Metric.closedBall a.val (ε / 3)}
  have hc (a : S) : IsClosed (B a) := by
    have heq : B a = Subtype.val ⁻¹' ((toWeakSpace ℂ E) '' Metric.closedBall a.val (ε / 3)) := by
      ext x
      simp only [B, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_image]
      exact ⟨fun hx => ⟨_, hx, (toWeakSpace ℂ E).apply_symm_apply x.val⟩,
        fun ⟨z, hz, he⟩ => by simpa only [← he, LinearEquiv.symm_apply_apply] using hz⟩
    rw [heq]
    exact (weak_closedBall a.val (ε / 3)).preimage continuous_subtype_val
  have hcover : ⋃ a : S, B a = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx : (toWeakSpace ℂ E).symm x.val ∈ closure S := hdense ⟨x.val, x.property, rfl⟩
    obtain ⟨a, haS, hdist⟩ := Metric.mem_closure_iff.mp hx (ε / 3) (by positivity)
    exact Set.mem_iUnion.mpr ⟨⟨a, haS⟩, hdist.le⟩
  obtain ⟨a, x, hx⟩ := nonempty_interior_of_iUnion_of_closed hc hcover
  obtain ⟨U, hU, heq⟩ := isOpen_induced_iff.mp (show IsOpen (interior (B a)) from isOpen_interior)
  refine ⟨U, hU, ⟨x.val, x.property, ?_⟩, ?_⟩
  · have : x ∈ Subtype.val ⁻¹' U := heq ▸ hx
    exact this
  · intro y hy z hz
    have hyB : (toWeakSpace ℂ E).symm y ∈ Metric.closedBall a.val (ε / 3) := by
      change (⟨y, hy.1⟩ : K) ∈ B a
      apply interior_subset (s := B a)
      rw [← heq]
      exact hy.2
    have hzB : (toWeakSpace ℂ E).symm z ∈ Metric.closedBall a.val (ε / 3) := by
      change (⟨z, hz.1⟩ : K) ∈ B a
      apply interior_subset (s := B a)
      rw [← heq]
      exact hz.2
    have hy' := Metric.mem_closedBall.mp hyB
    have hz' := Metric.mem_closedBall.mp hzB
    have hd := dist_triangle ((toWeakSpace ℂ E).symm y) a.val ((toWeakSpace ℂ E).symm z)
    rw [dist_comm a.val] at hd
    rw [← dist_eq_norm]
    linarith

end KadisonRingrose
end BoundedHochschild

end

end OAI
