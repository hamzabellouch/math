import Mathlib
import OAI.Probability.BinarySweep.GridBounds.GroupedLogBounds
import OAI.Probability.BinarySweep.GridBounds.DiagonalDimension
import OAI.Probability.BinarySweep.YoungTheory.CutBranching

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
variable (μ : YoungDiagram) (p : ℕ)

lemma southeast_height_mul_le_card :
    (p+1)*(southeast μ p).colLen 0 ≤ Fintype.card (Cell μ) := by
  let f : Fin (p+1) × Fin ((southeast μ p).colLen 0) → Cell μ := fun a =>
    ⟨(a.2.val+p,a.1.val), μ.up_left_mem le_rfl
      (show a.1.val ≤ p from Nat.le_of_lt_succ a.1.isLt)
      (by simpa using (mem_southeast μ p _).mp (YoungDiagram.mem_iff_lt_colLen.mpr a.2.isLt))⟩
  have hf : Function.Injective f := by
    intro a b h
    have h1 := congrArg (fun x : Cell μ => x.val.1) h
    have h2 := congrArg (fun x : Cell μ => x.val.2) h
    apply Prod.ext (Fin.ext h2)
    apply Fin.ext
    change a.2.val+p = b.2.val+p at h1
    exact Nat.add_right_cancel h1
  simpa only [Fintype.card_prod,Fintype.card_fin] using Fintype.card_le_of_injective f hf

lemma southeast_width_mul_le_card :
    (p+1)*(southeast μ p).rowLen 0 ≤ Fintype.card (Cell μ) := by
  let f : Fin (p+1) × Fin ((southeast μ p).rowLen 0) → Cell μ := fun a =>
    ⟨(a.1.val,a.2.val+p), μ.up_left_mem
      (show a.1.val ≤ p from Nat.le_of_lt_succ a.1.isLt) le_rfl
      (by simpa using (mem_southeast μ p _).mp (YoungDiagram.mem_iff_lt_rowLen.mpr a.2.isLt))⟩
  have hf : Function.Injective f := by
    intro a b h
    have h1 := congrArg (fun x : Cell μ => x.val.1) h
    have h2 := congrArg (fun x : Cell μ => x.val.2) h
    apply Prod.ext (Fin.ext h1)
    apply Fin.ext
    change a.2.val+p = b.2.val+p at h2
    exact Nat.add_right_cancel h2
  simpa only [Fintype.card_prod,Fintype.card_fin] using Fintype.card_le_of_injective f hf

lemma southeast_diagonal_bound (x : Cell (southeast μ p)) :
    diagonal (southeast μ p) x < 2*(Fintype.card (Cell μ)/(p+1)) := by
  have hh : (southeast μ p).colLen 0 ≤ Fintype.card (Cell μ)/(p+1) := (Nat.le_div_iff_mul_le (show 0<p+1 by omega)).mpr
    (by simpa only [Nat.mul_comm] using southeast_height_mul_le_card μ p)
  have hw : (southeast μ p).rowLen 0 ≤ Fintype.card (Cell μ)/(p+1) := (Nat.le_div_iff_mul_le (show 0<p+1 by omega)).mpr
    (by simpa only [Nat.mul_comm] using southeast_width_mul_le_card μ p)
  have hd := diagonal_lt_height_add_width (southeast μ p) x
  omega

theorem southeast_log_dimension_lower (hk : 0 < Fintype.card (Cell (southeast μ p))) :
    (Fintype.card (Cell (southeast μ p)) : ℝ) *
      (Real.log (Fintype.card (Cell (southeast μ p))) -
        Real.log (2*(Fintype.card (Cell μ)/(p+1)) : ℕ) - 1) ≤
      Real.log (Module.finrank ℂ (SpechtSpace (southeast μ p))) := by
  have hn := Fintype.card_pos_iff.mp hk
  obtain ⟨x⟩ := hn
  have hpos : 0 < 2*(Fintype.card (Cell μ)/(p+1)) :=
    Nat.zero_lt_of_lt (southeast_diagonal_bound μ p x)
  exact log_dimension_lower_of_diagonal_bound (southeast μ p) _ hpos hk
    (southeast_diagonal_bound μ p)

end BinaryCoordinateSweeps.Young

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
open Irrep Signed

lemma hook_log_dimension_upper (μ : YoungDiagram) (p s : ℕ) (hs : 0<s)
    (hM : Fintype.card (Cell μ)≤ s) :
    Real.log (Module.finrank ℂ (SpechtSpace μ)) ≤
      Real.log (Module.finrank ℂ (SpechtSpace (hookPart μ p)))+
        Fintype.card (Cell (southeast μ p))*Real.log s := by
  have hD : (0:ℝ)<Module.finrank ℂ (SpechtSpace μ) := by
    rw [←hilbertSpecht_finrank]
    exact_mod_cast irreducible_finrank_pos (hilbertSpecht μ)
  have hG : (0:ℝ)<Module.finrank ℂ (SpechtSpace (hookPart μ p)) := by
    rw [←hilbertSpecht_finrank]
    exact_mod_cast irreducible_finrank_pos (hilbertSpecht (hookPart μ p))
  have hsp : (0:ℝ)<s := by exact_mod_cast hs
  have hb := (hook_removal_dimension_upper μ p).trans
    (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hM _))
  have hl := Real.log_le_log hD (show (Module.finrank ℂ (SpechtSpace μ):ℝ)≤
      (s:ℝ)^Fintype.card (Cell (southeast μ p))*Module.finrank ℂ (SpechtSpace (hookPart μ p)) by
    exact_mod_cast hb)
  rw [Real.log_mul (pow_pos hsp _).ne' hG.ne',Real.log_pow] at hl
  linarith

lemma southeast_dense_saving (μ : YoungDiagram) (s : ℕ) (hs : 0<s)
    (hM : Fintype.card (Cell μ)≤ s)
    (hk : (s:ℝ)^(199/200:ℝ)≤Fintype.card (Cell (southeast μ ⌊(s:ℝ)^(1/100:ℝ)⌋₊))) :
    (Fintype.card (Cell (southeast μ ⌊(s:ℝ)^(1/100:ℝ)⌋₊)):ℝ)*
      ((1/200:ℝ)*Real.log s-(Real.log 2+1)) ≤
      Real.log (Module.finrank ℂ (SpechtSpace (southeast μ ⌊(s:ℝ)^(1/100:ℝ)⌋₊))) := by
  let p := ⌊(s:ℝ)^(1/100:ℝ)⌋₊
  let k := Fintype.card (Cell (southeast μ p))
  let M := Fintype.card (Cell μ)
  let U := 2*(M/(p+1))
  have hsp : (0:ℝ)<s := by exact_mod_cast hs
  have hkR : (0:ℝ)<k := (Real.rpow_pos_of_pos hsp _).trans_le hk
  have hkN : 0<k := by exact_mod_cast hkR
  have hU : 0<U := by
    obtain ⟨x⟩ := Fintype.card_pos_iff.mp hkN
    exact Nat.zero_lt_of_lt (southeast_diagonal_bound μ p x)
  have hp : (s:ℝ)^(1/100:ℝ)≤(p:ℝ)+1 := (Nat.lt_floor_add_one _).le
  have hprod : (M/(p+1):ℕ)*(p+1)≤ s := (Nat.div_mul_le_self _ _).trans hM
  have hprodR : (M/(p+1):ℕ)*( (p:ℝ)+1)≤(s:ℝ) := by exact_mod_cast hprod
  have hquot : (M/(p+1):ℕ)≤(s:ℝ)^(99/100:ℝ) := by
    rw [show (99/100:ℝ)=1-1/100 by norm_num,Real.rpow_sub hsp,Real.rpow_one]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hsp _)).mpr
    exact (mul_le_mul_of_nonneg_left hp (by positivity)).trans hprodR
  have hUR : (U:ℝ)≤2*(s:ℝ)^(99/100:ℝ) := by dsimp [U]; push_cast; linarith
  have hlU := Real.log_le_log (show (0:ℝ)<U by exact_mod_cast hU) hUR
  rw [Real.log_mul (by norm_num : (2:ℝ)≠0) (Real.rpow_pos_of_pos hsp _).ne',Real.log_rpow hsp] at hlU
  have hlk := Real.log_le_log (Real.rpow_pos_of_pos hsp _) hk
  rw [Real.log_rpow hsp] at hlk
  have hb := southeast_log_dimension_lower μ p hkN
  change (k:ℝ)*(Real.log k-Real.log U-1)≤_ at hb
  refine le_trans ?_ hb
  apply mul_le_mul_of_nonneg_left _ hkR.le
  linarith

end BinaryCoordinateSweeps.Young

end

end OAI
