import OAI.MeasureTheory.Falconer.Incidence.PlanarLeafInjection
import OAI.MeasureTheory.Falconer.Geometry.CubeBallPacking

namespace OAI

/-! Transfer finite prefix bounds to geometric closed-ball counts. The
factor 7^d is the existing bounded overlap of dyadic cubes. -/
namespace Falconer
open Set Metric Regularization

noncomputable def pointPrefixFiber {d : ℕ} (P : Finset (Space d))
    (l : Space d → CellPath d) (n : ℕ) (q : CellPath d) : Finset (Space d) := by
  classical
  exact P.filter fun x => (l x).take n = q

theorem pointPrefixFiber_card_eq {P : Finset (Space 2)} {l : Space 2 → CellPath 2}
    (hl : Set.InjOn l (P : Set (Space 2))) (n : ℕ) (q : CellPath 2) :
    (pointPrefixFiber P l n q).card = (prefixFiber (P.image l) n q).card :=
  (leaf_image_prefixFiber_card hl n q).symm

theorem finite_point_ball_count {d N n : ℕ} (Q : DyadicCube d) (hQ : 0 < Q.side)
    {P : Finset (Space d)} {l : Space d → CellPath d}
    (hleaf : ∀ x ∈ P, l x ∈ cubePaths d N ∧ x ∈ (Q.descendant (l x)).carrier)
    (hn : n ≤ N) {r M : ℝ} (hr : 0 < r) (hM : 0 ≤ M)
    (hscale : 2*r ≤ Q.side/(2 : ℝ)^n)
    (hfiber : ∀ q ∈ (P.image l).image (List.take n),
      ((pointPrefixFiber P l n q).card : ℝ) ≤ M) (z : Space d) :
    ((P.filter fun x => dist x z ≤ r).card : ℝ) ≤ (7^d : ℕ)*M := by
  classical
  let S := P.filter fun x => dist x z ≤ r
  let H := cubeBallHits Q n z (2*r)
  have hmap (x : Space d) (hx : x ∈ S) : (l x).take n ∈ H := by
    obtain ⟨hxP,hxz⟩ := Finset.mem_filter.mp hx
    have hl := hleaf x hxP
    apply (mem_cubeBallHits Q n z (2*r) _).2
    refine ⟨?_,x,descendant_subset_take Q hQ _ _ hl.2,?_⟩
    · simp only [List.length_take,(mem_cubePaths _ _ _).mp hl.1,Nat.min_eq_left hn]
    · exact mem_ball.mpr (by linarith)
  have hsum : (S.card : ℝ) = ∑ q ∈ H,
      ((S.filter fun x => (l x).take n = q).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise hmap
  calc
    _ = ∑ q ∈ H, ((S.filter fun x => (l x).take n = q).card : ℝ) := hsum
    _ ≤ ∑ _q ∈ H, M := by
      apply Finset.sum_le_sum
      intro q hq
      by_cases hex : (S.filter fun x => (l x).take n = q).Nonempty
      · obtain ⟨x,hx⟩ := hex
        obtain ⟨hxS,hxq⟩ := Finset.mem_filter.mp hx
        have hxP := (Finset.mem_filter.mp hxS).1
        have hqi : q ∈ (P.image l).image (List.take n) := by
          exact Finset.mem_image.mpr ⟨l x,Finset.mem_image.mpr ⟨x,hxP,rfl⟩,hxq⟩
        have hsub : (S.filter fun x => (l x).take n = q) ⊆ pointPrefixFiber P l n q := by
          intro y hy
          obtain ⟨hyS,hyq⟩ := Finset.mem_filter.mp hy
          exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hyS).1,hyq⟩
        exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hfiber q hqi)
      · rw [Finset.not_nonempty_iff_eq_empty.mp hex,Finset.card_empty,Nat.cast_zero]
        exact hM
    _ = (H.card : ℝ)*M := by simp
    _ ≤ (7^d : ℕ)*M := by
      apply mul_le_mul_of_nonneg_right _ hM
      exact_mod_cast cubeBallHits_card Q hQ n z hscale

end Falconer

end OAI
