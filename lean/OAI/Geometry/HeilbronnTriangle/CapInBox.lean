import OAI.Geometry.HeilbronnTriangle.AuxiliaryCap
import OAI.Geometry.HeilbronnTriangle.TranslateAverage

namespace OAI


namespace Problem355.AuxiliaryCap

variable {F : Type*} [Field F] [Fintype F]

theorem exists_cap_subset (hF : ringChar F ≠ 2) (B : Finset (Fin 3 → F)) :
    ∃ S : Finset (Fin 3 → F), S ⊆ B ∧
      B.card ≤ Fintype.card F * S.card ∧ IsCap (S : Set (Fin 3 → F)) := by
  classical
  obtain ⟨G, hG, hcap⟩ := exists_finset_cap hF
  obtain ⟨a, ha⟩ := TranslateAverage.exists_large_image_inter G B
  refine ⟨G.image (a + ·) ∩ B, Finset.inter_subset_right, ?_, ?_⟩
  · rw [hG, Fintype.card_fun, Fintype.card_fin] at ha
    have hmul : Fintype.card F ^ 2 * B.card ≤
        Fintype.card F ^ 2 *
          (Fintype.card F * (G.image (a + ·) ∩ B).card) := by
      simpa [pow_succ, mul_assoc] using ha
    exact Nat.le_of_mul_le_mul_left hmul (pow_pos Fintype.card_pos 2)
  · apply (hcap.translate a).mono
    intro p hp
    obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hp).1
    exact ⟨q, hq, heq⟩

theorem exists_cap_subset_real (hF : ringChar F ≠ 2) (B : Finset (Fin 3 → F)) :
    ∃ S : Finset (Fin 3 → F), S ⊆ B ∧
      (B.card : ℝ) / Fintype.card F ≤ S.card ∧ IsCap (S : Set (Fin 3 → F)) := by
  obtain ⟨S, hS, hcard, hcap⟩ := exists_cap_subset hF B
  refine ⟨S, hS, ?_, hcap⟩
  apply (div_le_iff₀ (by exact_mod_cast Fintype.card_pos (α := F))).mpr
  exact_mod_cast (by simpa [mul_comm] using hcard : B.card ≤ S.card * Fintype.card F)

noncomputable def residueInterval (q w : ℕ) : Finset (ZMod q) := by
  classical
  exact (Finset.range w).image (fun x : ℕ => (x : ZMod q))

theorem card_residueInterval {q w : ℕ} (hw : w ≤ q) :
    (residueInterval q w).card = w := by
  classical
  calc
    (residueInterval q w).card = (Finset.range w).card := by
      apply Finset.card_image_iff.mpr
      intro a ha b hb hab
      have hav : a < q := lt_of_lt_of_le (Finset.mem_range.mp ha) hw
      have hbv : b < q := lt_of_lt_of_le (Finset.mem_range.mp hb) hw
      have hv := congrArg ZMod.val hab
      simpa [ZMod.val_natCast_of_lt hav, ZMod.val_natCast_of_lt hbv] using hv
    _ = w := Finset.card_range w

@[simp] theorem mem_residueInterval {q w : ℕ} [NeZero q] (hw : w ≤ q) (x : ZMod q) :
    x ∈ residueInterval q w ↔ x.val < w := by
  classical
  constructor
  · intro hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    have haw := Finset.mem_range.mp ha
    simpa [ZMod.val_natCast_of_lt (lt_of_lt_of_le haw hw)] using haw
  · intro hx
    exact Finset.mem_image.mpr ⟨x.val, Finset.mem_range.mpr hx, ZMod.natCast_zmod_val x⟩

noncomputable def residueBox (q w : ℕ) : Finset (Fin 3 → ZMod q) :=
  Fintype.piFinset (fun _ => residueInterval q w)

@[simp] theorem card_residueBox {q w : ℕ} (hw : w ≤ q) :
    (residueBox q w).card = w ^ 3 := by
  rw [residueBox, Fintype.card_piFinset_const, card_residueInterval hw]

@[simp] theorem mem_residueBox {q w : ℕ} [NeZero q] (hw : w ≤ q)
    (p : Fin 3 → ZMod q) : p ∈ residueBox q w ↔ ∀ i, (p i).val < w := by
  simp [residueBox, Fintype.mem_piFinset, mem_residueInterval hw]

theorem exists_cap_in_residueBox {q w : ℕ} [Fact q.Prime]
    (hq : q ≠ 2) (hw : w ≤ q) :
    ∃ S : Finset (Fin 3 → ZMod q),
      (∀ p ∈ S, ∀ i, (p i).val < w) ∧ w ^ 3 ≤ q * S.card ∧
      IsCap (S : Set (Fin 3 → ZMod q)) := by
  have hchar : ringChar (ZMod q) ≠ 2 := by simpa only [ZMod.ringChar_zmod_n] using hq
  obtain ⟨S, hSB, hcard, hcap⟩ := exists_cap_subset hchar (residueBox q w)
  refine ⟨S, ?_, ?_, hcap⟩
  · intro p hp
    exact (mem_residueBox hw p).mp (hSB hp)
  · simpa [card_residueBox hw, ZMod.card] using hcard

theorem exists_cap_in_residueBox_real {q w : ℕ} [Fact q.Prime]
    (hq : q ≠ 2) (hw : w ≤ q) :
    ∃ S : Finset (Fin 3 → ZMod q),
      (∀ p ∈ S, ∀ i, (p i).val < w) ∧ (w : ℝ) ^ 3 / q ≤ S.card ∧
      IsCap (S : Set (Fin 3 → ZMod q)) := by
  obtain ⟨S, hS, hcard, hcap⟩ := exists_cap_in_residueBox hq hw
  refine ⟨S, hS, ?_, hcap⟩
  apply (div_le_iff₀ (by exact_mod_cast (Fact.out : q.Prime).pos)).mpr
  exact_mod_cast (by simpa [mul_comm] using hcard : w ^ 3 ≤ S.card * q)

end Problem355.AuxiliaryCap

end OAI
