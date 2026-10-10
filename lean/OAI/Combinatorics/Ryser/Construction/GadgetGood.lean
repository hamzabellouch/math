import OAI.Combinatorics.Ryser.Construction.GadgetProcess
import OAI.Combinatorics.Ryser.Construction.GadgetConsequences
import OAI.Combinatorics.Ryser.Construction.DeletionLines

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k : Type*} [Field k] [Fintype k] [DecidableEq k]

def GoodGadget (a : GadgetOutcome k) : Prop :=
  OriginalLineDensity a ∧
    (∀ ell : AffineLine k,
      Fintype.card k ≤ 8 * (transformedRetained a ∩ linePoints ell).card) ∧
    GadgetCoverProperty (transformedRetained a)

theorem gadgetConfig_survivors_ignoring_line
    (hcop : Nat.Coprime 3 (Fintype.card k - 1)) (hcard : 3 < Fintype.card k)
    (a : GadgetOutcome k) (ell : AffineLine k) :
    LineCover.survivors {linePoints ell} (gadgetConfig a) = transformedRetained a := by
  have hnot : linePoints ell ∉ LineCover.selected (gadgetConfig a) := by
    intro hmem
    exact selected_cubicShapes_ne_linePoints (gadgetConfig a) hcard hmem ell rfl
  calc
    _ = LineCover.survivors ∅ (gadgetConfig a) :=
      LineCover.survivors_insert_eq_of_not_selected hnot
    _ = transformedRetained a := gadgetConfig_survivors hcop a

theorem gadget_line_density_of_goodLineCover
    (hcop : Nat.Coprime 3 (Fintype.card k - 1)) (hcard : 3 < Fintype.card k)
    (a : GadgetOutcome k)
    (hgood : LineCover.GoodLineCover (1 / 4) (1 / 100) (gadgetConfig a))
    (ell : AffineLine k) :
    Fintype.card k ≤ 8 * (transformedRetained a ∩ linePoints ell).card := by
  have h := hgood.1 ell
  rw [gadgetConfig_survivors_ignoring_line hcop hcard a ell] at h
  have hreal : (Fintype.card k : ℝ) ≤
      8 * ((transformedRetained a ∩ linePoints ell).card : ℝ) := by linarith
  exact_mod_cast hreal

theorem gadget_near_pencil_of_goodLineCover
    (hcop : Nat.Coprime 3 (Fintype.card k - 1))
    (a : GadgetOutcome k)
    (hgood : LineCover.GoodLineCover (1 / 4) (1 / 100) (gadgetConfig a))
    (B : Finset (Point k)) (L : Finset (AffineLine k))
    (hcover : ∀ y ∈ transformedRetained a, y ∈ B ∨ ∃ ell ∈ L, Incidence y ell)
    (hbudget : 2 * L.card + B.card ≤ 2 * Fintype.card k) :
    ∃ p : ProjectivePoint k,
      99 * Fintype.card k ≤ 100 * (L ∩ affinePencil p).card := by
  have hL : L.card ≤ Fintype.card k := by omega
  have hB : B.card ≤ 2 * Fintype.card k := by omega
  have hmiss : (LineCover.survivors ∅ (gadgetConfig a) \ L.biUnion linePoints).card ≤
      2 * Fintype.card k := by
    rw [gadgetConfig_survivors hcop a]
    exact (Finset.card_le_card (missed_points_subset_of_mixed_cover
      (transformedRetained a) B L hcover)).trans hB
  obtain ⟨p, hp⟩ := hgood.2 L hL hmiss
  have heq : LineCover.coverPencil L p = L ∩ affinePencil p := by
    ext ell
    simp only [LineCover.mem_coverPencil, Finset.mem_inter, mem_affinePencil]
  rw [heq] at hp
  refine ⟨p, ?_⟩
  have hreal : (99 : ℝ) * Fintype.card k ≤
      100 * ((L ∩ affinePencil p).card : ℝ) := by linarith
  exact_mod_cast hreal

theorem goodGadget_of_events
    (hcop : Nat.Coprime 3 (Fintype.card k - 1)) (hcard : 3 < Fintype.card k)
    (hlarge : 200 < 19 * Fintype.card k) (a : GadgetOutcome k)
    (horiginal : OriginalLineDensity a)
    (hgood : LineCover.GoodLineCover (1 / 4) (1 / 100) (gadgetConfig a)) :
    GoodGadget a := by
  have hlines := gadget_line_density_of_goodLineCover hcop hcard a hgood
  refine ⟨horiginal, hlines, ?_⟩
  exact gadgetCoverProperty_of_near_pencils (transformedRetained a) hlarge hlines
    (gadget_near_pencil_of_goodLineCover hcop a hgood)

theorem GoodGadget.retained_nonempty {a : GadgetOutcome k} (ha : GoodGadget a) :
    (retainedPoints a).Nonempty := by
  by_contra hn
  have hY : retainedPoints a = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  have hT : transformedRetained a = ∅ := by simp [transformedRetained, hY]
  have hline := ha.2.1 (none, 0)
  rw [hT, Finset.empty_inter, Finset.card_empty, Nat.mul_zero] at hline
  exact (Nat.not_le_of_gt Fintype.card_pos) hline

end RyserCoveringCounterexample.Construction

end

end OAI
