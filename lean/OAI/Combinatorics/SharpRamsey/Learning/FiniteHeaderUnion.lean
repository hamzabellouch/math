import Mathlib

namespace OAI

section
namespace SharpLogRamsey.PublicFamilies
open Finset Real
open scoped Classical BigOperators
noncomputable section

lemma union_log_bound {ι α : Type*} [DecidableEq α] (I : Finset ι) (F : ι → Finset α)
    (L : ℝ) (hL : 0≤L) (hF : ∀ i∈I,log ((F i).card+1:ℝ)≤L) :
    log (((I.biUnion F).card:ℝ)+1)≤log ((I.card:ℝ)+1)+L := by
  have hE : 1≤exp L := one_le_exp_iff.mpr hL
  have hF' : ∀ i∈I,((F i).card:ℝ)≤exp L := by
    intro i hi
    have hh := exp_le_exp.mpr (hF i hi)
    rw [exp_log (by positivity)] at hh
    linarith
  have hc : ((I.biUnion F).card:ℝ)≤∑ i∈I,((F i).card:ℝ) := by
    exact_mod_cast card_biUnion_le
  have hs := sum_le_sum hF'
  simp only [sum_const,nsmul_eq_mul] at hs
  have hh : ((I.biUnion F).card:ℝ)+1≤((I.card:ℝ)+1)*exp L := by nlinarith
  have hl := log_le_log (by positivity : 0<((I.biUnion F).card:ℝ)+1) hh
  rw [log_mul (by positivity) (ne_of_gt (exp_pos _)),log_exp] at hl
  exact hl

lemma card_le_ceil_exp {α : Type*} (F : Finset α) (L : ℝ)
    (hF : log ((F.card:ℝ)+1)≤L) : F.card≤⌈exp L⌉₊ := by
  have hh := exp_le_exp.mpr hF
  rw [exp_log (by positivity)] at hh
  have hc : (F.card:ℝ)≤exp L := by linarith
  exact_mod_cast hc.trans (Nat.le_ceil (exp L))

lemma log_ceil_exp {L : ℝ} (hL : 0≤L) :
    log ((⌈exp L⌉₊:ℝ)+1)≤L+2 := by
  have hh : (⌈exp L⌉₊:ℝ)<exp L+1 := Nat.ceil_lt_add_one (exp_pos _).le
  have hE : 1≤exp L := one_le_exp_iff.mpr hL
  have hl := log_le_log (by positivity : (0:ℝ)<(⌈exp L⌉₊:ℝ)+1)
    (show (⌈exp L⌉₊:ℝ)+1≤3*exp L by linarith)
  rw [log_mul (by norm_num : (3:ℝ)≠0) (ne_of_gt (exp_pos _)),log_exp] at hl
  have h3 := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)
  linarith

end
end SharpLogRamsey.PublicFamilies

end

end OAI
