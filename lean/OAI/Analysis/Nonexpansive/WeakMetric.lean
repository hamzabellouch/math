import OAI.Analysis.Nonexpansive.WeakCompactness
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.UniformSpace.Pi
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

namespace OAI

/-!
# Metrizability of norm-separable weakly compact sets

For a dense sequence in the norm carrier, choose a norming functional for
each pairwise difference. These countably many functionals separate the
points of the set. Their evaluations embed the compact weak carrier into
a countable product of real lines. No separability of the ambient space,
or of its entire dual, is assumed.
-/

noncomputable section

open Set TopologicalSpace NormedSpace
open scoped Pointwise

namespace ReflexiveFixedPoints

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- One actual norming functional for each difference of dense points. -/
def pairNormingFunctional {K : Set X} (z : ℕ → K) (ij : ℕ × ℕ) : StrongDual ℝ X :=
  Classical.choose (exists_dual_vector'' ℝ ((z ij.1 : X) - (z ij.2 : X)))

theorem pairNormingFunctional_norm {K : Set X} (z : ℕ → K) (ij : ℕ × ℕ) :
    ‖pairNormingFunctional z ij‖ ≤ 1 :=
  (Classical.choose_spec (exists_dual_vector'' ℝ ((z ij.1 : X) - (z ij.2 : X)))).1

theorem pairNormingFunctional_apply {K : Set X} (z : ℕ → K) (ij : ℕ × ℕ) :
    pairNormingFunctional z ij ((z ij.1 : X) - (z ij.2 : X)) =
      ‖(z ij.1 : X) - (z ij.2 : X)‖ :=
  (Classical.choose_spec (exists_dual_vector'' ℝ ((z ij.1 : X) - (z ij.2 : X)))).2

/-- The selected countable family separates the original norm carrier. -/
theorem pairNormingFunctional_separates {K : Set X} (z : ℕ → K)
    (hz : DenseRange z) :
    Function.Injective (fun a : K => fun ij => pairNormingFunctional z ij a) := by
  intro a b hab
  apply Subtype.ext
  by_contra hne
  have hd : 0 < ‖(a : X) - (b : X)‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨i, hi⟩ := hz.exists_dist_lt a
    (show 0 < ‖(a : X) - (b : X)‖ / 8 by linarith)
  obtain ⟨j, hj⟩ := hz.exists_dist_lt b
    (show 0 < ‖(a : X) - (b : X)‖ / 8 by linarith)
  have hai : ‖(a : X) - (z i : X)‖ < ‖(a : X) - (b : X)‖ / 8 := by
    simpa only [Subtype.dist_eq, dist_eq_norm] using hi
  have hbj : ‖(b : X) - (z j : X)‖ < ‖(a : X) - (b : X)‖ / 8 := by
    simpa only [Subtype.dist_eq, dist_eq_norm] using hj
  let w : X := (a : X) - (b : X)
  let t : X := (z i : X) - (z j : X)
  let f : StrongDual ℝ X := pairNormingFunctional z (i, j)
  have hf0 : f w = 0 := by
    change f ((a : X) - (b : X)) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr (congr_fun hab (i, j))
  have hft : f t = ‖t‖ := pairNormingFunctional_apply z (i, j)
  have hfn : ‖f‖ ≤ 1 := pairNormingFunctional_norm z (i, j)
  have he : ‖t - w‖ < ‖w‖ / 4 := by
    have heq : t - w = ((z i : X) - (a : X)) - ((z j : X) - (b : X)) := by
      dsimp [t, w]
      abel
    rw [heq]
    have htri := norm_sub_le ((z i : X) - (a : X)) ((z j : X) - (b : X))
    rw [norm_sub_rev (z i : X) (a : X), norm_sub_rev (z j : X) (b : X)] at htri
    dsimp [w]
    linarith
  have ht : ‖t‖ ≤ ‖t - w‖ := calc
    ‖t‖ = f t := hft.symm
    _ = f (t - w) := by rw [map_sub f t w, hf0, sub_zero]
    _ ≤ ‖f (t - w)‖ := le_abs_self _
    _ ≤ ‖f‖ * ‖t - w‖ := f.le_opNorm _
    _ ≤ 1 * ‖t - w‖ := mul_le_mul_of_nonneg_right hfn (norm_nonneg _)
    _ = ‖t - w‖ := one_mul _
  have hw : ‖w‖ ≤ ‖t‖ + ‖t - w‖ := calc
    ‖w‖ = ‖t - (t - w)‖ := by congr 1; abel
    _ ≤ ‖t‖ + ‖t - w‖ := norm_sub_le _ _
  change 0 < ‖w‖ at hd
  linarith

/-- The actual weak topology on a norm-separable weakly compact set is
metrizable. The empty set and zero ambient space are included. -/
theorem weakCarrier_metrizable {K : Set X} (hsep : IsSeparable K)
    (hcompact : WeaklyCompact K) : MetrizableSpace (WeakCarrier K) := by
  classical
  let : CompactSpace (WeakCarrier K) := hcompact.compactSpace
  by_cases hne : K.Nonempty
  · let : Nonempty K := hne.to_subtype
    let : SeparableSpace K := hsep.separableSpace
    obtain ⟨z, hz⟩ := exists_dense_seq K
    let e : WeakCarrier K → (ℕ × ℕ) → ℝ :=
      fun a ij => pairNormingFunctional z ij ((normToWeak K).symm a)
    have he : Continuous e := by
      apply continuous_pi
      intro ij
      exact (WeakBilin.eval_continuous (topDualPairing ℝ X).flip
        (pairNormingFunctional z ij)).comp continuous_subtype_val
    have hinj : Function.Injective e := by
      intro a b hab
      apply (normToWeak K).symm.injective
      exact pairNormingFunctional_separates z hz hab
    let : MetrizableSpace ((ℕ × ℕ) → ℝ) := UniformSpace.metrizableSpace
    exact (he.isClosedEmbedding hinj).isEmbedding.metrizableSpace
  · have hinj : Function.Injective (fun _ : WeakCarrier K => (0 : ℝ)) := by
      intro a b _
      exact (hne ⟨(toWeakSpace ℝ X).symm a, a.property⟩).elim
    exact ((continuous_const : Continuous (fun _ : WeakCarrier K => (0 : ℝ))).isClosedEmbedding
      hinj).isEmbedding.metrizableSpace

/-- The difference set of a separable set is separable in the original norm. -/
theorem differences_isSeparable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {K : Set X} (hsep : IsSeparable K) :
    IsSeparable (K - K) := by
  have h := (hsep.prod hsep).image
    (continuous_fst.sub continuous_snd : Continuous (fun p : X × X => p.1 - p.2))
  rw [← Set.sub_image_prod]
  exact h

/-- Closing the real linear span preserves separability. -/
theorem differenceSpan_isSeparable {K : Set X} (hsep : IsSeparable K) :
    IsSeparable (differenceSpan K : Set X) := by
  change IsSeparable (closure (Submodule.span ℝ (K - K) : Set X))
  exact (differences_isSeparable hsep).span.closure

theorem differenceSpan_separableSpace {K : Set X} (hsep : IsSeparable K) :
    SeparableSpace (differenceSpan K) :=
  (differenceSpan_isSeparable hsep).separableSpace

end ReflexiveFixedPoints

end

end OAI
