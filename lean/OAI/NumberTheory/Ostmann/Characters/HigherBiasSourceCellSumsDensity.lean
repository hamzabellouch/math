import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceCellSumsNormalize

namespace OAI

noncomputable section
namespace Ostmann.Characters
namespace NormalizedCellSet
variable {I : Finset ℕ} (C : NormalizedCellSet I)

lemma affine_injective : Function.Injective (fun x:ℕ => C.base+C.gcd*x) := by
  intro x y h
  have hh := Nat.add_left_cancel h
  exact Nat.eq_of_mul_eq_mul_left C.gcd_pos hh

lemma card_eq : C.cells.card=I.card := by
  have h := congrArg Finset.card C.recover
  rw [Finset.card_image_of_injective _ C.affine_injective] at h
  exact h

lemma card_le_endpoint : I.card ≤ C.endpoint+1 := by
  rw [← C.card_eq]
  have hsub : C.cells ⊆ Finset.Icc 0 C.endpoint := by
    intro x hx
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le _,C.cells_le x hx⟩
  simpa only [Nat.card_Icc,Nat.sub_zero] using Finset.card_le_card hsub

lemma card_le_residue_card_add_one :
    I.card ≤ (C.cells.image (fun x:ℕ => (x:ZMod C.endpoint))).card+1 := by
  classical
  let : NeZero C.endpoint := ⟨C.endpoint_pos.ne'⟩
  have hinj : Set.InjOn (fun x:ℕ => (x:ZMod C.endpoint)) (C.cells.erase C.endpoint) := by
    intro x hx y hy hxy
    have hxm := Finset.mem_erase.mp hx
    have hym := Finset.mem_erase.mp hy
    have hxlt : x<C.endpoint := lt_of_le_of_ne (C.cells_le x hxm.2) hxm.1
    have hylt : y<C.endpoint := lt_of_le_of_ne (C.cells_le y hym.2) hym.1
    have hv := congrArg ZMod.val hxy
    simpa only [ZMod.val_natCast_of_lt hxlt,ZMod.val_natCast_of_lt hylt] using hv
  have hcard := Finset.card_le_card
    (Finset.image_subset_image (f:=fun x:ℕ => (x:ZMod C.endpoint)) (Finset.erase_subset C.endpoint C.cells))
  rw [Finset.card_image_of_injOn hinj] at hcard
  have herase := Finset.card_erase_add_one C.endpoint_mem
  rw [C.card_eq] at herase
  omega

theorem real_margins {b c : ℝ} (hb : 0<b) (hc : 0<c)
    (hlarge : 2 ≤ c*b) (hcard : c*b ≤ (I.card:ℝ))
    (hbase : b ≤ (C.base:ℝ)) (hmax : ((C.base+C.gcd*C.endpoint:ℕ):ℝ) ≤ 3*b) :
    (c/2)*b ≤ (C.gcd:ℝ)*C.endpoint ∧
      (C.gcd:ℝ) ≤ 6/c ∧ (C.endpoint:ℝ) ≤ 3*b ∧
      (c/2)*b ≤ ((C.cells.image (fun x:ℕ => (x:ZMod C.endpoint))).card:ℝ) := by
  have hcount : (I.card:ℝ) ≤ (C.endpoint:ℝ)+1 := by exact_mod_cast C.card_le_endpoint
  have hcount' : (I.card:ℝ) ≤
      ((C.cells.image (fun x:ℕ => (x:ZMod C.endpoint))).card:ℝ)+1 := by
    exact_mod_cast C.card_le_residue_card_add_one
  have hg : (1:ℝ) ≤ C.gcd := by exact_mod_cast C.gcd_pos
  have hs : (0:ℝ) ≤ C.endpoint := Nat.cast_nonneg _
  have hm : (C.base:ℝ)+(C.gcd:ℝ)*C.endpoint ≤ 3*b := by exact_mod_cast hmax
  have hsend : (c/2)*b ≤ (C.endpoint:ℝ) := by nlinarith
  have hwidth : (c/2)*b ≤ (C.gcd:ℝ)*C.endpoint := by nlinarith
  refine ⟨hwidth,?_,?_,by nlinarith⟩
  · apply (le_div_iff₀ hc).mpr
    have hh := mul_le_mul_of_nonneg_left hsend (Nat.cast_nonneg C.gcd)
    nlinarith
  · nlinarith

lemma residue_generates :
    AddSubgroup.closure (C.cells.image (fun x:ℕ => (x:ZMod C.endpoint)) : Set (ZMod C.endpoint))=⊤ := by
  have hg : (C.cells.image (fun x:ℕ => (x:ℤ))).gcd id=1 := by
    rw [cell_gcd_intCast,C.gcd_one]
    rfl
  have hh := closure_cast_eq_top_of_gcd_one (C.cells.image (fun x:ℕ => (x:ℤ))) hg C.endpoint
  simpa only [Finset.image_image,Function.comp_def,Int.cast_natCast] using hh

end NormalizedCellSet
end Ostmann.Characters

end

end OAI
