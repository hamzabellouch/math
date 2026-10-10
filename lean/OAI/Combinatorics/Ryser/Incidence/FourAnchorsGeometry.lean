import OAI.Combinatorics.Ryser.Incidence.FourAnchorsCounting
import OAI.Combinatorics.Ryser.Geometry.ProjectiveJoins

namespace OAI

noncomputable section

open scoped BigOperators

namespace RyserCoveringCounterexample.Incidence

attribute [local instance] Classical.propDecidable

variable {Pt Ln : Type*} [DecidableEq Pt] [instDecidableEqLn : DecidableEq Ln]

theorem joinedNeighbors_card_lower (R : Pt → Ln → Prop)
    (hunique : ∀ {x y : Pt} {l m : Ln}, x ≠ y →
      R x l → R y l → R x m → R y m → l = m)
    (P : Finset Pt) (L : Finset Ln) (x : Pt) (hx : x ∈ P)
    {d : ℝ} (hd : 1 ≤ d)
    (hpoint : d ≤ ((L.filter fun l => R x l).card : ℝ))
    (hlines : ∀ l ∈ L, d ≤ ((P.filter fun p => R p l).card : ℝ)) :
    d * (d - 1) ≤ ((joinedNeighbors R P L x).card : ℝ) := let _ := instDecidableEqLn; by
  classical
  let I := L.filter fun l => R x l
  let S := I.sigma fun l => (P.filter fun p => R p l).erase x
  have hcard : S.card ≤ (joinedNeighbors R P L x).card := by
    apply Finset.card_le_card_of_injOn (fun w : Σ _ : Ln, Pt => w.2)
    · intro w hw
      obtain ⟨hl, hp⟩ := Finset.mem_sigma.mp hw
      obtain ⟨hyx, hy⟩ := Finset.mem_erase.mp hp
      obtain ⟨hyP, hyl⟩ := Finset.mem_filter.mp hy
      obtain ⟨hlL, hxl⟩ := Finset.mem_filter.mp hl
      exact Finset.mem_filter.mpr ⟨hyP, Ne.symm hyx, w.1, hlL, hxl, hyl⟩
    · intro w hw v hv heq
      obtain ⟨hl, hp⟩ := Finset.mem_sigma.mp hw
      obtain ⟨hm, hq⟩ := Finset.mem_sigma.mp hv
      obtain ⟨hyx, hy⟩ := Finset.mem_erase.mp hp
      obtain ⟨_, hz⟩ := Finset.mem_erase.mp hq
      have hlm : w.1 = v.1 := hunique (Ne.symm hyx)
        (Finset.mem_filter.mp hl).2 (Finset.mem_filter.mp hy).2
        (Finset.mem_filter.mp hm).2 (by simpa only [heq] using (Finset.mem_filter.mp hz).2)
      rcases w with ⟨l, y⟩
      rcases v with ⟨m, z⟩
      dsimp at hlm heq
      subst m
      subst z
      rfl
  have hS : (S.card : ℝ) =
      ∑ l ∈ I, (((P.filter fun p => R p l).card : ℝ) - 1) := by
    dsimp [S]
    rw [Finset.card_sigma, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro l hl
    have hxtrace : x ∈ P.filter fun p => R p l :=
      Finset.mem_filter.mpr ⟨hx, (Finset.mem_filter.mp hl).2⟩
    rw [Finset.card_erase_of_mem hxtrace, Nat.cast_sub
      (Finset.one_le_card.mpr ⟨x, hxtrace⟩)]
    norm_num
  calc
    d * (d - 1) ≤ (I.card : ℝ) * (d - 1) :=
      mul_le_mul_of_nonneg_right hpoint (by linarith)
    _ = ∑ _l ∈ I, (d - 1) := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ l ∈ I, (((P.filter fun p => R p l).card : ℝ) - 1) := by
      apply Finset.sum_le_sum
      intro l hl
      exact sub_le_sub_right (hlines l (Finset.mem_filter.mp hl).1) 1
    _ = (S.card : ℝ) := hS.symm
    _ ≤ ((joinedNeighbors R P L x).card : ℝ) := by exact_mod_cast hcard

theorem projective_joinedNeighbors_card_lower {F : Type*} [Field F] [DecidableEq F]
    (P : Finset (ProjectivePoint F)) (L : Finset (ProjectiveLine F))
    (x : ProjectivePoint F) (hx : x ∈ P)
    {d : ℝ} (hd : 1 ≤ d)
    (hpoint : d ≤ ((L.filter fun l => ProjectiveIncidence x l).card : ℝ))
    (hlines : ∀ l ∈ L,
      d ≤ ((P.filter fun p => ProjectiveIncidence p l).card : ℝ)) :
    d * (d - 1) ≤ ((joinedNeighbors ProjectiveIncidence P L x).card : ℝ) :=
  joinedNeighbors_card_lower ProjectiveIncidence
    (fun hxy hxl hyl hxm hym => eq_projectiveLine_of_common_incidence hxy hxl hyl hxm hym)
    P L x hx hd
    (by convert hpoint using 1; congr)
    (by
      intro l hl
      convert hlines l hl using 1; congr)

end RyserCoveringCounterexample.Incidence

end

end OAI
