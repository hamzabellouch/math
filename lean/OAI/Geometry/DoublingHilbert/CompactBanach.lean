import Mathlib
import OAI.Geometry.DoublingHilbert.CompactModel
import OAI.Geometry.DoublingHilbert.FiniteWitness
import OAI.Geometry.DoublingHilbert.Auerbach
import OAI.Geometry.DoublingHilbert.ClusterPlacement
import OAI.Geometry.DoublingHilbert.ClusterCover
import OAI.Geometry.DoublingHilbert.FiniteTargets
import OAI.Geometry.DoublingHilbert.Main

namespace OAI

open Set Metric
open scoped BigOperators
open Filter
open scoped Topology
noncomputable section
universe u v
namespace CompactBanach

theorem main : ∃ Λ : ℕ, ∀ (B : Type u) [NormedAddCommGroup B] [NormedSpace ℝ B]
    [CompleteSpace B], ¬ FiniteDimensional ℝ B →
    ∃ K : Set B, IsCompact K ∧ DoublingAtMost K Λ ∧
      ∀ (E : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E], ¬ AdmitsBiLipschitzEmbedding K E := by
  classical
  refine ⟨1 + 5 * (76800 ^ 8) ^ 2, ?_⟩
  intro B _ _ _ hB
  have hS : AmbientDoubling DoublingHilbert.constructedSet 76800 :=
    doubling_iff_ambient.mp (fun x r hr => DoublingHilbert.constructedSet_cover x hr)
                                                                                     
  have hw (j : ℕ) := finite_witness_card (Nat.unpair j).1
    (A := ((Nat.unpair j).2 : ℝ) + 1) (le_add_of_nonneg_left (Nat.cast_nonneg _))
  choose X hXcard hX using hw
  obtain ⟨v, hv, hvcoord⟩ := exists_auerbach_vectors (ι := Unit) hB
  have hvunit : ‖v ()‖ = 1 := by
    apply le_antisymm (hv ())
    simpa using hvcoord (fun _ => 1) ()
  have hp (j : ℕ) := cluster_placement hB hS (X j) (v ()) (clusterScale_pos j)
  choose f hloc hdoubling a ha hd using hp
  let C : ℕ → Finset B := fun j => Finset.univ.image (f j)
  have hCset (j : ℕ) : (C j : Set B) = Set.range (f j) := by
    ext z
    simp [C]
  have hCloc : ∀ j z, z ∈ C j →
      dist z (clusterScale j • v ()) ≤ clusterScale j / 100 := by
    intro j z hz
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hz
    exact hloc j x
  have hCdouble : ∀ j, DoublingAtMost (C j : Set B) (76800 ^ 8) := by
    intro j
    rw [hCset]
    exact hdoubling j
  let K : Set B := {0} ∪ ⋃ j : ℕ, (C j : Set B)
  obtain ⟨hcompact, hdouble⟩ := compact_doubling_clusters C hvunit hCloc hCdouble
  refine ⟨K, hcompact, hdouble, ?_⟩
  intro E _ _ _ hF
  obtain ⟨F, b, hb, D, hD, hF⟩ := hF
  obtain ⟨g, c, hc, A, hA, hg⟩ := euclidean_embedding_of_finite_dimensional F hb hD hF
  obtain ⟨n, hn⟩ := exists_nat_gt (36 * A)
  let j : ℕ := Nat.pair (Module.finrank ℝ E) n
  have hjdim : (Nat.unpair j).1 = Module.finrank ℝ E := by simp [j]
  have hjn : (Nat.unpair j).2 = n := by simp [j]
  let intoK : X j → K := fun x =>
    ⟨f j x, Or.inr (Set.mem_iUnion.mpr ⟨j,
      Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩⟩)⟩
  have hbad := hX j
  rw [hjdim, hjn] at hbad
  apply hbad
  refine ⟨g ∘ intoK, c * a j, mul_pos hc (ha j), ?_⟩
  intro x y
  have hgg := hg (intoK x) (intoK y)
  change c * dist (f j x) (f j y) ≤ dist (g (intoK x)) (g (intoK y)) ∧
    dist (g (intoK x)) (g (intoK y)) ≤ A * c * dist (f j x) (f j y) at hgg
  dsimp only [Function.comp_apply]
  constructor
  · calc
      _ = c * (a j * dist x y) := by ring
      _ ≤ c * dist (f j x) (f j y) := mul_le_mul_of_nonneg_left (hd j x y).1 hc.le
      _ ≤ _ := hgg.1
  · have hApos : 0 ≤ A := le_trans zero_le_one hA
    have hn' : 36 * A ≤ (n : ℝ) + 1 := by linarith
    calc
      _ ≤ A * c * dist (f j x) (f j y) := hgg.2
      _ ≤ A * c * (36 * a j * dist x y) :=
        mul_le_mul_of_nonneg_left (hd j x y).2 (mul_nonneg hApos hc.le)
      _ = (36 * A) * (c * a j) * dist x y := by ring
      _ ≤ ((n : ℝ) + 1) * (c * a j) * dist x y :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hn' (mul_nonneg hc.le (ha j).le)) dist_nonneg

end CompactBanach
end

end OAI
