import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega

namespace OAI

namespace MarkovSuperreflexivity

open scoped BigOperators

def FiniteRamseyBound.{u, v} {κ : Type v} (r : ℕ) (targets : κ → ℕ) (B : ℕ) : Prop :=
  ∀ (α : Type u) [DecidableEq α] (S : Finset α), B ≤ S.card →
    ∀ χ : Finset α → κ,
      ∃ i : κ, ∃ H : Finset α,
        H ⊆ S ∧ H.card = targets i ∧
          ∀ A : Finset α, A ⊆ H → A.card = r → χ A = i

private def decreaseRamseyTarget.{v} {κ : Type v} [DecidableEq κ]
    (targets : κ → ℕ) (i j : κ) : ℕ :=
  if j = i then targets j - 1 else targets j

theorem finite_ramsey_targets.{u, v} {κ : Type v} [Fintype κ] [Nonempty κ]
    (r : ℕ) (targets : κ → ℕ) :
    ∃ B : ℕ, FiniteRamseyBound.{u, v} r targets B := by
  classical
  induction r generalizing targets with
  | zero =>
      refine ⟨Finset.univ.sup targets, ?_⟩
      intro α _ S hS χ
      let i : κ := χ ∅
      have hi : targets i ≤ S.card :=
        (Finset.le_sup (Finset.mem_univ i)).trans hS
      obtain ⟨H, hHS, hHcard⟩ := Finset.exists_subset_card_eq hi
      refine ⟨i, H, hHS, hHcard, ?_⟩
      intro A _ hA
      have hAempty : A = ∅ := Finset.card_eq_zero.mp hA
      subst A
      rfl
  | succ r ih =>
      have by_sum : ∀ n : ℕ, ∀ w : κ → ℕ, (∑ i, w i) = n →
          ∃ B : ℕ, FiniteRamseyBound.{u, v} (r + 1) w B := by
        intro n
        induction n using Nat.strong_induction_on with
        | h n hn =>
            intro w hsum
            by_cases hz : ∃ i, w i = 0
            · obtain ⟨i, hi⟩ := hz
              refine ⟨0, ?_⟩
              intro α _ S _ χ
              refine ⟨i, ∅, Finset.empty_subset S, ?_, ?_⟩
              · simpa only [Finset.card_empty] using hi.symm
              · intro A hA hcard
                have hAempty : A = ∅ := Finset.subset_empty.mp hA
                subst A
                simp at hcard
            · have hpos : ∀ i, 0 < w i := by
                intro i
                exact Nat.pos_of_ne_zero (fun hi => hz ⟨i, hi⟩)
              have hsmall : ∀ i : κ,
                  ∃ B : ℕ, FiniteRamseyBound.{u, v} (r + 1)
                    (decreaseRamseyTarget w i) B := by
                intro i
                have hlt : (∑ j, decreaseRamseyTarget w i j) < n := by
                  rw [← hsum]
                  apply Finset.sum_lt_sum
                  · intro j _
                    by_cases hji : j = i
                    · simpa only [decreaseRamseyTarget, ite_eq_left hji] using
                        (Nat.sub_le (w j) 1)
                    · simpa only [decreaseRamseyTarget, ite_eq_right hji] using
                        (le_rfl : w j ≤ w j)
                  · refine ⟨i, Finset.mem_univ i, ?_⟩
                    simp only [decreaseRamseyTarget]
                    exact Nat.sub_lt (hpos i) (by decide)
                exact hn _ hlt _ rfl
              let N : κ → ℕ := fun i => Classical.choose (hsmall i)
              have hN : ∀ i : κ, FiniteRamseyBound.{u, v} (r + 1)
                  (decreaseRamseyTarget w i) (N i) := by
                intro i
                exact Classical.choose_spec (hsmall i)
              obtain ⟨D, hD⟩ := ih N
              refine ⟨D + 1, ?_⟩
              intro α _ S hS χ
              have hSnonempty : S.Nonempty := Finset.card_pos.mp (by omega)
              obtain ⟨x, hxS⟩ := hSnonempty
              have htail : D ≤ (S.erase x).card := by
                rw [Finset.card_erase_of_mem hxS]
                omega
              obtain ⟨i, H, hHS, hHcard, hHmono⟩ :=
                hD α (S.erase x) htail (fun A => χ (insert x A))
              obtain ⟨j, G, hGH, hGcard, hGmono⟩ :=
                hN i α H hHcard.ge χ
              by_cases hji : j = i
              · subst j
                have hxH : x ∉ H := by
                  intro hx
                  exact (Finset.mem_erase.mp (hHS hx)).1 rfl
                have hxG : x ∉ G := fun hx => hxH (hGH hx)
                refine ⟨i, insert x G, ?_, ?_, ?_⟩
                · apply Finset.insert_subset_iff.mpr
                  refine ⟨hxS, ?_⟩
                  exact hGH.trans (hHS.trans (Finset.erase_subset x S))
                · rw [Finset.card_insert_of_notMem hxG, hGcard]
                  simp only [decreaseRamseyTarget]
                  exact Nat.sub_add_cancel (hpos i)
                · intro A hA hcard
                  by_cases hxA : x ∈ A
                  · have herase : A.erase x ⊆ G := by
                      intro a ha
                      obtain ⟨hax, haA⟩ := Finset.mem_erase.mp ha
                      rcases Finset.mem_insert.mp (hA haA) with haeq | haG
                      · exact False.elim (hax haeq)
                      · exact haG
                    have heraseCard : (A.erase x).card = r := by
                      rw [Finset.card_erase_of_mem hxA, hcard]
                      exact Nat.add_sub_cancel r 1
                    have hcolor := hHmono (A.erase x) (herase.trans hGH) heraseCard
                    simpa only [Finset.insert_erase hxA] using hcolor
                  · apply hGmono A _ hcard
                    intro a ha
                    rcases Finset.mem_insert.mp (hA ha) with haeq | haG
                    · exact False.elim (hxA (haeq ▸ ha))
                    · exact haG
              · refine ⟨j, G, ?_, ?_, hGmono⟩
                · exact hGH.trans (hHS.trans (Finset.erase_subset x S))
                · simpa only [decreaseRamseyTarget, ite_eq_right hji] using hGcard
      exact by_sum (∑ i, targets i) targets rfl

theorem finite_ramsey_uniform_subsets.{u} (r colors target : ℕ) (hcolors : 0 < colors) :
    ∃ B : ℕ, target ≤ B ∧
      ∀ (α : Type u) [DecidableEq α] (S : Finset α), B ≤ S.card →
        ∀ χ : Finset α → Fin colors,
          ∃ H : Finset α, H ⊆ S ∧ H.card = target ∧
            ∀ A : Finset α, A ⊆ H → A.card = r →
              ∀ D : Finset α, D ⊆ H → D.card = r → χ A = χ D := by
  classical
  let : Nonempty (Fin colors) := ⟨⟨0, hcolors⟩⟩
  obtain ⟨B, hB⟩ := finite_ramsey_targets.{u, 0} r (fun _ : Fin colors => target)
  refine ⟨max target B, le_max_left _ _, ?_⟩
  intro α _ S hS χ
  obtain ⟨i, H, hHS, hHcard, hHmono⟩ :=
    hB α S ((le_max_right target B).trans hS) χ
  refine ⟨H, hHS, hHcard, ?_⟩
  intro A hA hAcard D hD hDcard
  exact (hHmono A hA hAcard).trans (hHmono D hD hDcard).symm

theorem finite_ramsey_simultaneous_subsets.{u}
    (q target : ℕ) (colors : Fin q → ℕ) (hcolors : ∀ m, 0 < colors m) :
    ∃ B : ℕ, target ≤ B ∧
      ∀ (α : Type u) [DecidableEq α] (S : Finset α), B ≤ S.card →
        ∀ χ : (m : Fin q) → Finset α → Fin (colors m),
          ∃ H : Finset α, H ⊆ S ∧ H.card = target ∧
            ∀ (m : Fin q) (A : Finset α), A ⊆ H → A.card = m.val →
              ∀ D : Finset α, D ⊆ H → D.card = m.val → χ m A = χ m D := by
  classical
  induction q generalizing target with
  | zero =>
      refine ⟨target, le_rfl, ?_⟩
      intro α _ S hS χ
      obtain ⟨H, hHS, hHcard⟩ := Finset.exists_subset_card_eq hS
      refine ⟨H, hHS, hHcard, ?_⟩
      intro m
      exact Fin.elim0 m
  | succ q ih =>
      obtain ⟨M, hMtarget, hM⟩ :=
        finite_ramsey_uniform_subsets.{u} q (colors (Fin.last q)) target
          (hcolors (Fin.last q))
      obtain ⟨B, hBM, hB⟩ :=
        ih M (fun m => colors m.castSucc) (fun m => hcolors m.castSucc)
      refine ⟨B, hMtarget.trans hBM, ?_⟩
      intro α _ S hS χ
      obtain ⟨H, hHS, hHcard, hHmono⟩ :=
        hB α S hS (fun m => χ m.castSucc)
      obtain ⟨G, hGH, hGcard, hGmono⟩ :=
        hM α H hHcard.ge (χ (Fin.last q))
      refine ⟨G, hGH.trans hHS, hGcard, ?_⟩
      intro m
      rcases Fin.eq_castSucc_or_eq_last m with ⟨m, rfl⟩ | rfl
      · intro A hA hAcard D hD hDcard
        exact hHmono m A (hA.trans hGH) hAcard D (hD.trans hGH) hDcard
      · intro A hA hAcard D hD hDcard
        exact hGmono A hA hAcard D hD hDcard

theorem finite_ordered_simultaneous_ramsey
    (k lower : ℕ)
    (colors : Fin (k + 1) → ℕ)
    (hcolors : ∀ m, 0 < colors m) :
    ∃ B : ℕ, max k lower ≤ B ∧
      ∀ χ : (m : Fin (k + 1)) →
          (Fin m.val ↪o Fin B) → Fin (colors m),
        ∃ e : Fin k ↪o Fin B,
          ∀ (m : Fin (k + 1))
            (s t : Fin m.val ↪o Fin k),
            χ m (s.trans e) = χ m (t.trans e) := by
  classical
  obtain ⟨B₀, hB₀k, hB₀⟩ :=
    finite_ramsey_simultaneous_subsets.{0} (k + 1) k colors hcolors
  let B := max B₀ lower
  have hBB₀ : B₀ ≤ B := le_max_left _ _
  have hBlower : lower ≤ B := le_max_right _ _
  refine ⟨B, max_le (hB₀k.trans hBB₀) hBlower, ?_⟩
  intro χ
  let χset : (m : Fin (k + 1)) → Finset (Fin B) → Fin (colors m) :=
    fun m A => if hA : A.card = m.val then χ m (A.orderEmbOfFin hA)
      else ⟨0, hcolors m⟩
  have hlarge : B₀ ≤ (Finset.univ : Finset (Fin B)).card := by
    simpa only [Finset.card_univ, Fintype.card_fin] using hBB₀
  obtain ⟨H, _, hHcard, hHmono⟩ := hB₀ (Fin B) Finset.univ hlarge χset
  let e : Fin k ↪o Fin B := H.orderEmbOfFin hHcard
  refine ⟨e, ?_⟩
  intro m s t
  let A : Finset (Fin B) := Finset.univ.map (s.trans e).toEmbedding
  let D : Finset (Fin B) := Finset.univ.map (t.trans e).toEmbedding
  have hAcard : A.card = m.val := by
    simp only [A, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  have hDcard : D.card = m.val := by
    simp only [D, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  have hAH : A ⊆ H := by
    intro x hx
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hx
    exact H.orderEmbOfFin_mem hHcard (s a)
  have hDH : D ⊆ H := by
    intro x hx
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hx
    exact H.orderEmbOfFin_mem hHcard (t a)
  have hAenum : A.orderEmbOfFin hAcard = s.trans e := by
    symm
    apply Finset.orderEmbOfFin_unique'
    intro a
    exact Finset.mem_map.mpr ⟨a, Finset.mem_univ a, rfl⟩
  have hDenum : D.orderEmbOfFin hDcard = t.trans e := by
    symm
    apply Finset.orderEmbOfFin_unique'
    intro a
    exact Finset.mem_map.mpr ⟨a, Finset.mem_univ a, rfl⟩
  have hcolor := hHmono m A hAH hAcard D hDH hDcard
  simpa only [χset, dite_eq_left hAcard, dite_eq_left hDcard, hAenum, hDenum] using hcolor

end MarkovSuperreflexivity

end OAI
