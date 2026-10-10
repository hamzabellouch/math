import OAI.MeasureTheory.Falconer.Estimates.DyadicAncestors

namespace OAI

/-! # Local counts of actual all-dimensional dyadic ancestors -/

namespace Falconer
open Metric Set

theorem dyadic_center_diameter_count {d n L : ℕ} (Q : DyadicCube d) (hQ : 0 < Q.side)
    (S : Finset (List (Fin d → Bool))) (hS : ∀ p ∈ S, p.length = n)
    {r : ℝ} (hL : r*((2:ℝ)^n/Q.side) ≤ L)
    (hdiam : ∀ p ∈ S, ∀ q ∈ S, dist (Q.descendant p).center (Q.descendant q).center ≤ r) :
    S.card ≤ (2*L+1)^d := by
  classical
  by_cases hne : S.Nonempty
  · obtain ⟨q,hq⟩ := hne
    have hi : Set.InjOn dyadicCode (S : Set (List (Fin d → Bool))) := by
      intro p hp t ht he
      exact dyadicCode_injective_at_depth (hS p hp) (hS t ht) he
    rw [← Finset.card_image_of_injOn hi]
    apply grid_ball_card (by positivity) hL (S.image dyadicCode) (dyadicCode q)
    intro z hz
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
    rw [← Q.center_sub_eq_grid_sub p q (hS p hp) (hS q hq)]
    simpa only [dist_eq_norm] using hdiam p hp q hq
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.card_empty,Nat.zero_le]

theorem DyadicCube.center_distance_ancestor {d n g : ℕ} (Q : DyadicCube d)
    (hQ : 0 < Q.side) (p : List (Fin d → Bool)) (hp : p.length = n) (hg : g ≤ n) :
    dist (Q.descendant p).center (Q.descendant (p.take g)).center ≤
      Real.sqrt d * (Q.side/(2:ℝ)^g) := by
  have h := (Q.descendant (p.take g)).dist_le (Q.descendant_side_pos hQ _).le
    (Q.center_mem_ancestor hQ p g)
    ((Q.descendant (p.take g)).center_mem (Q.descendant_side_pos hQ _))
  simpa only [Q.descendant_side,List.length_take,hp,min_eq_left hg] using h

theorem dyadic_ancestor_ball_count {d n g : ℕ} (Q : DyadicCube d) (hQ : 0 < Q.side)
    (S : Finset (List (Fin d → Bool))) (hS : ∀ p ∈ S, p.length = n) (hg : g ≤ n)
    (x : Space d) {r C : ℝ} (_hC : 0 ≤ C) (hr : r ≤ C*(Q.side/(2:ℝ)^g))
    (hball : ∀ p ∈ S, dist (Q.descendant p).center x ≤ r) :
    (S.image (List.take g)).card ≤ (2*Nat.ceil (2*C+2*Real.sqrt d)+1)^d := by
  classical
  let a := Q.side/(2:ℝ)^g
  have ha : 0 < a := by dsimp [a]; positivity
  have hcenter (p : List (Fin d → Bool)) (hp : p ∈ S) :
      dist (Q.descendant (p.take g)).center x ≤ r+Real.sqrt d*a := by
    calc
      _ ≤ dist (Q.descendant (p.take g)).center (Q.descendant p).center +
          dist (Q.descendant p).center x := dist_triangle _ _ _
      _ ≤ Real.sqrt d*a+r := add_le_add
        (by simpa only [dist_comm] using Q.center_distance_ancestor hQ p (hS p hp) hg) (hball p hp)
      _ = _ := add_comm _ _
  apply dyadic_center_diameter_count (n := g) Q hQ (S.image (List.take g))
    (fun p hp => by
      obtain ⟨q,hq',rfl⟩ := Finset.mem_image.mp hp
      simp only [List.length_take,hS q hq',min_eq_left hg])
    (r := 2*r+2*Real.sqrt d*a)
  · have hc : 2*C+2*Real.sqrt d ≤ (Nat.ceil (2*C+2*Real.sqrt d):ℝ) := Nat.le_ceil _
    have hh : 2*r+2*Real.sqrt d*a ≤ (2*C+2*Real.sqrt d)*a := by nlinarith [hr]
    calc
      _ ≤ ((2*C+2*Real.sqrt d)*a)*((2:ℝ)^g/Q.side) :=
        mul_le_mul_of_nonneg_right hh (by positivity)
      _ = 2*C+2*Real.sqrt d := by dsimp [a]; field_simp
      _ ≤ _ := hc
  · intro p hp q hq
    obtain ⟨p',hp',rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨q',hq',rfl⟩ := Finset.mem_image.mp hq
    calc
      _ ≤ dist (Q.descendant (p'.take g)).center x +
          dist x (Q.descendant (q'.take g)).center := dist_triangle _ _ _
      _ ≤ (r+Real.sqrt d*a)+(r+Real.sqrt d*a) :=
        add_le_add (hcenter p' hp') (by simpa only [dist_comm] using hcenter q' hq')
      _ = _ := by ring

end Falconer

end OAI
