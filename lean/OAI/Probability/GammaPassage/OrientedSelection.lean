import OAI.Probability.FirstPassage.Paths
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Abel
import Lean.Elab.Tactic.Omega

namespace OAI

/-! Greedy extraction of separated sites from square-lattice contours. -/
namespace PlanarFPP
open Finset Set

noncomputable def orientedSelectionBox (n : ℕ) : Finset Vertex :=
  (Finset.Icc (-(n : ℤ)) n) ×ˢ (Finset.Icc (-(n : ℤ)) n)

theorem orientedSelectionBox_card (n : ℕ) : (orientedSelectionBox n).card = (2*n+1)^2 := by
  have hi : (Finset.Icc (-(n : ℤ)) n).card = 2*n+1 := by
    rw [Int.card_Icc]
    omega
  simp [orientedSelectionBox, hi, pow_two]

/-- Greedy selection in a finite symmetric neighborhood system. -/
theorem separated_selection {α : Type*} (R : α → α → Prop) [DecidableRel R]
    (hrefl : ∀ a, R a a) (hsymm : ∀ a b, R a b → R b a)
    (S : Finset α) (d : ℕ)
    (hdegree : ∀ a ∈ S, (S.filter (R a)).card ≤ d) :
    ∃ T : Finset α, T ⊆ S ∧
      Set.Pairwise (↑T : Set α) (fun a b => ¬R a b) ∧ S.card ≤ d*T.card := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    by_cases hs : S.Nonempty
    · obtain ⟨a,ha⟩ := hs
      let U := S.filter (fun b => ¬R a b)
      have hu : U ⊆ S := filter_subset _ _
      have hau : a ∉ U := by simp [U,hrefl]
      have hlt : U ⊂ S := ⟨hu,by intro hh; exact hau (hh ha)⟩
      have hdu : ∀ b ∈ U, (U.filter (R b)).card ≤ d := by
        intro b hb
        exact (Finset.card_le_card (filter_subset_filter _ hu)).trans (hdegree b (hu hb))
      obtain ⟨T,hT,hpair,hcard⟩ := ih U hlt hdu
      have hat : a ∉ T := fun hh => hau (hT hh)
      refine ⟨insert a T,?_,?_,?_⟩
      · intro b hb
        rcases mem_insert.mp hb with rfl | hb
        · exact ha
        · exact hu (hT hb)
      · intro b hb c hc hbc
        rcases mem_insert.mp hb with rfl | hbT
        · rcases mem_insert.mp hc with rfl | hcT
          · exact False.elim (hbc rfl)
          · exact (mem_filter.mp (hT hcT)).2
        · rcases mem_insert.mp hc with rfl | hcT
          · intro hr
            exact (mem_filter.mp (hT hbT)).2 (hsymm _ _ hr)
          · exact hpair hbT hcT hbc
      · have hsplit : (S.filter (R a)).card+U.card=S.card := by
          exact card_filter_add_card_filter_not (R a)
        rw [card_insert_of_notMem hat]
        have hd := hdegree a ha
        nlinarith
    · have he : S=∅ := not_nonempty_iff_eq_empty.mp hs
      subst S
      exact ⟨∅,Finset.Subset.rfl,by simp,by simp⟩

def latticeNear (k : ℕ) (p q : Vertex) : Prop :=
  (q.1-p.1).natAbs ≤ k ∧ (q.2-p.2).natAbs ≤ k

instance (k : ℕ) (p q : Vertex) : Decidable (latticeNear k p q) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem latticeNear_refl (k : ℕ) (p : Vertex) : latticeNear k p p := by
  simp [latticeNear]

theorem latticeNear_symm (k : ℕ) (p q : Vertex) : latticeNear k p q ↔ latticeNear k q p := by
  have h0 : p.1-q.1 = -(q.1-p.1) := by omega
  have h1 : p.2-q.2 = -(q.2-p.2) := by omega
  simp only [latticeNear,h0,h1,Int.natAbs_neg]

theorem near_filter_card_le (S : Finset Vertex) (k : ℕ) (p : Vertex) :
    (S.filter (latticeNear k p)).card ≤ (2*k+1)^2 := by
  classical
  have hs : S.filter (latticeNear k p) ⊆ (orientedSelectionBox k).image (fun q => p+q) := by
    intro q hq
    obtain ⟨hq0,hq1⟩ := (mem_filter.mp hq).2
    have hmem : q-p ∈ orientedSelectionBox k := by
      simp only [orientedSelectionBox,mem_product,Finset.mem_Icc,Prod.fst_sub,Prod.snd_sub]
      constructor <;> omega
    exact mem_image.mpr ⟨q-p,hmem,by abel⟩
  exact (Finset.card_le_card hs).trans ((card_image_le).trans_eq (orientedSelectionBox_card k))

/-- From N sites, retain a pairwise k-separated subfamily of size at least
N/(2k+1)^2, expressed without integer division or rounding loss. -/
theorem lattice_separated_selection (S : Finset Vertex) (k : ℕ) :
    ∃ T : Finset Vertex, T ⊆ S ∧
      Set.Pairwise (↑T : Set Vertex) (fun p q => ¬latticeNear k p q) ∧
      S.card ≤ (2*k+1)^2*T.card := by
  exact separated_selection (latticeNear k) (latticeNear_refl k)
    (fun p q => (latticeNear_symm k p q).mp) S ((2*k+1)^2)
    (fun p _ => near_filter_card_le S k p)

end PlanarFPP

end OAI
