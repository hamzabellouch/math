import OAI.NumberTheory.Ostmann.Construction.FavorableInterior
import OAI.NumberTheory.Ostmann.Construction.LogBlocks

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction
open scoped BigOperators

def favorableBlockWidth (L : ℝ) : ℝ := Real.exp ((1/100:ℝ)*L)
def favorableBlockCount (L : ℝ) : ℕ := ⌈Real.exp ((9/10:ℝ)*L)⌉₊

lemma interior_log_bounds {S : Finset ℕ} {L : ℝ} {p : ℕ}
    (hp : p∈interiorFavorable S L) :
    Real.exp ((3/50:ℝ)*L)<Real.log p ∧ Real.log p≤Real.exp ((89/100:ℝ)*L) := by
  obtain ⟨hprime,hlo,hhi⟩ := (logLogPrimeBand_mem_iff _ _ _).mp (Finset.mem_inter.mp hp).2
  have hlpos : 0<Real.log (p:ℝ) := Real.log_pos (by exact_mod_cast hprime.one_lt)
  constructor
  · have h := Real.exp_lt_exp.mpr hlo
    rwa [Real.exp_log hlpos] at h
  · have h := Real.exp_le_exp.mpr hhi
    rwa [Real.exp_log hlpos] at h

lemma interior_logBlockIndex {S : Finset ℕ} {L : ℝ} (hL : 0≤L) {p : ℕ}
    (hp : p∈interiorFavorable S L) :
    logBlockIndex (favorableBlockWidth L) p∈Finset.Icc 1 (favorableBlockCount L) := by
  obtain ⟨hlo,hhi⟩ := interior_log_bounds hp
  have hh : 0<favorableBlockWidth L := Real.exp_pos _
  have hh1 : 1≤favorableBlockWidth L := by
    unfold favorableBlockWidth
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (by positivity : (0:ℝ)≤(1/100:ℝ)*L)
  have hsmall : favorableBlockWidth L≤Real.exp ((3/50:ℝ)*L) :=
    Real.exp_le_exp.mpr (by nlinarith)
  apply Finset.mem_Icc.mpr
  constructor
  · apply (Nat.le_floor_iff (div_nonneg (Real.log_natCast_nonneg p) hh.le)).mpr
    norm_num only [Nat.cast_one]
    apply (le_div_iff₀ hh).mpr
    simpa only [one_mul] using hsmall.trans hlo.le
  · have hf : (logBlockIndex (favorableBlockWidth L) p:ℝ)≤Real.log p/favorableBlockWidth L :=
      Nat.floor_le (div_nonneg (Real.log_natCast_nonneg p) hh.le)
    have hdiv : Real.log p/favorableBlockWidth L≤Real.log p := by
      apply (div_le_iff₀ hh).mpr
      nlinarith [Real.log_natCast_nonneg p]
    have hlarge : Real.exp ((89/100:ℝ)*L)≤Real.exp ((9/10:ℝ)*L) := Real.exp_le_exp.mpr (by nlinarith)
    have hcast := hf.trans (hdiv.trans (hhi.trans (hlarge.trans (Nat.le_ceil _))))
    exact_mod_cast hcast

lemma favorableBlockCount_harmonic_le {L : ℝ} (hL : 0≤L)
    (hgap : Real.log 2≤(1/10:ℝ)*L) : (harmonic (favorableBlockCount L):ℝ)≤1+L := by
  have he1 : 1≤Real.exp ((9/10:ℝ)*L) := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (by positivity : (0:ℝ)≤(9/10:ℝ)*L)
  have he2 : 2≤Real.exp ((1/10:ℝ)*L) := by
    have h := Real.exp_le_exp.mpr hgap
    rwa [Real.exp_log (by norm_num : (0:ℝ)<2)] at h
  have hceil := (Nat.ceil_lt_add_one (Real.exp_pos ((9/10:ℝ)*L)).le).le
  have hcast : (favorableBlockCount L:ℝ)≤Real.exp L := by
    have hmul := mul_le_mul_of_nonneg_left he2 (Real.exp_pos ((9/10:ℝ)*L)).le
    rw [← Real.exp_add] at hmul
    have hex : (9/10:ℝ)*L+(1/10:ℝ)*L=L := by ring
    rw [hex] at hmul
    dsimp [favorableBlockCount]
    linarith
  have hn : (0:ℝ)<favorableBlockCount L :=
    lt_of_lt_of_le (Real.exp_pos _) (Nat.le_ceil _)
  have hlog := Real.log_le_log hn hcast
  rw [Real.log_exp] at hlog
  exact (harmonic_le_one_add_log _).trans (by linarith)

lemma favorableBlock_window_inside {S : Finset ℕ} {L : ℝ} (hL : 0≤L)
    (hgap : Real.log 2≤(1/100:ℝ)*L) {j p : ℕ}
    (hp : p∈logBlockPrimes (interiorFavorable S L) (favorableBlockWidth L) j) :
    Real.exp ((1/20:ℝ)*L)≤(j:ℝ)*favorableBlockWidth L ∧
      ((j:ℝ)+1)*favorableBlockWidth L≤Real.exp ((9/10:ℝ)*L) := by
  have hh : 0<favorableBlockWidth L := Real.exp_pos _
  obtain ⟨hlo,hhi⟩ := interior_log_bounds (Finset.mem_filter.mp hp).1
  have hb₀ := logBlock_lower hh hp
  have hb₁ := logBlock_upper hh hp
  have htwo : 2≤Real.exp ((1/100:ℝ)*L) := by
    have h := Real.exp_le_exp.mpr hgap
    rwa [Real.exp_log (by norm_num : (0:ℝ)<2)] at h
  have hs₀ : favorableBlockWidth L≤Real.exp ((1/20:ℝ)*L) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hs₁ : favorableBlockWidth L≤Real.exp ((89/100:ℝ)*L) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have he₀ := mul_le_mul_of_nonneg_left htwo (Real.exp_pos ((1/20:ℝ)*L)).le
  have he₁ := mul_le_mul_of_nonneg_left htwo (Real.exp_pos ((89/100:ℝ)*L)).le
  rw [← Real.exp_add] at he₀ he₁
  have e₀ : (1/20:ℝ)*L+(1/100:ℝ)*L=(3/50:ℝ)*L := by ring
  have e₁ : (89/100:ℝ)*L+(1/100:ℝ)*L=(9/10:ℝ)*L := by ring
  rw [e₀] at he₀
  rw [e₁] at he₁
  constructor <;> nlinarith

end Ostmann.Construction

end

end OAI
