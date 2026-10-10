import OAI.MeasureTheory.Falconer.Estimates.DyadicCenters

namespace OAI

/-! # A ball meets a bounded number of dyadic cubes of comparable side -/
namespace Falconer
open Set Metric

noncomputable def cubeBallHits {d : ℕ} (Q : DyadicCube d) (n : ℕ)
    (x : Space d) (r : ℝ) : Finset (List (Fin d → Bool)) := by
  classical
  exact (cubePaths d n).filter fun p => ((Q.descendant p).carrier ∩ ball x r).Nonempty

theorem mem_cubeBallHits {d : ℕ} (Q : DyadicCube d) (n : ℕ)
    (x : Space d) (r : ℝ) (p : List (Fin d → Bool)) :
    p ∈ cubeBallHits Q n x r ↔ p.length = n ∧
      ((Q.descendant p).carrier ∩ ball x r).Nonempty := by
  classical
  simp [cubeBallHits]

theorem cubeBallHits_coordinate_bound {d n : ℕ} (Q : DyadicCube d)
    (hQ : 0 < Q.side) (x : Space d) {r : ℝ}
    (hr : r ≤ Q.side/(2:ℝ)^n) {p q : List (Fin d → Bool)}
    (hp : p ∈ cubeBallHits Q n x r) (hq : q ∈ cubeBallHits Q n x r) (i : Fin d) :
    |dyadicCode p i - dyadicCode q i| ≤ (3 : ℤ) := by
  obtain ⟨hp, u, hu, hux⟩ := (mem_cubeBallHits Q n x r p).mp hp
  obtain ⟨hq, v, hv, hvx⟩ := (mem_cubeBallHits Q n x r q).mp hq
  have hui := hu i
  have hvi := hv i
  rw [Q.descendant_origin,Q.descendant_side,hp] at hui
  rw [Q.descendant_origin,Q.descendant_side,hq] at hvi
  have huv : |u i-v i| ≤ 2*r := by
    have hb : dist u v < 2*r :=
      (dist_triangle u x v).trans_lt (by
        rw [dist_comm x v]
        linarith [mem_ball.mp hux,mem_ball.mp hvx])
    exact (PiLp.norm_apply_le (u-v) i).trans (by simpa only [dist_eq_norm] using hb.le)
  have ht : 0 < Q.side/(2:ℝ)^n := by positivity
  have hh : |(dyadicCode p i:ℝ)-(dyadicCode q i:ℝ)| ≤ 3 := by
    rw [abs_le] at huv ⊢
    constructor <;> nlinarith
  exact_mod_cast hh

theorem cubeBallHits_card {d : ℕ} (Q : DyadicCube d) (hQ : 0 < Q.side)
    (n : ℕ) (x : Space d) {r : ℝ} (hr : r ≤ Q.side/(2:ℝ)^n) :
    (cubeBallHits Q n x r).card ≤ 7^d := by
  classical
  let S := cubeBallHits Q n x r
  change S.card ≤ 7^d
  by_cases hS : S.Nonempty
  · obtain ⟨p₀,hp₀⟩ := hS
    have hinj : Set.InjOn dyadicCode (S : Set (List (Fin d → Bool))) := by
      intro p hp q hq hpq
      exact dyadicCode_injective_at_depth
        ((mem_cubeBallHits Q n x r p).mp hp).1
        ((mem_cubeBallHits Q n x r q).mp hq).1 hpq
    have hc : (S.image dyadicCode).card = S.card := Finset.card_image_iff.mpr hinj
    rw [← hc]
    exact grid_box_card (L := 3) (S.image dyadicCode) (dyadicCode p₀) (by
      intro z hz i
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
      exact cubeBallHits_coordinate_bound Q hQ x hr hp hp₀ i)
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hS,Finset.card_empty]
    exact Nat.zero_le _

end Falconer

end OAI
