import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.MetadataAlphabet
import OAI.Combinatorics.RamseyFive.Decoding.MetadataScalars

namespace OAI

namespace SharpRamseyFive.Metadata
open scoped Classical

noncomputable def listCap (σ : ℝ) : ℕ := ⌈4*Real.exp (σ/2)⌉₊
noncomputable def productCap (σ : ℝ) : ℕ := ⌈4*Real.exp (13*σ/15)⌉₊

lemma ceil_five_exp (x : ℝ) (hx : 0≤x) : (⌈4*Real.exp x⌉₊:ℝ)≤5*Real.exp x := by
  have hh := Nat.ceil_lt_add_one (by positivity : (0:ℝ)≤4*Real.exp x)
  have he := Real.one_le_exp_iff.mpr hx
  linarith

theorem log_card_training_le {V : Type*} [Fintype V] [Nonempty V]
    (σ : ℝ) (hσ : 100000≤σ) (hV : (Nat.card V:ℝ)≤Real.exp (5*σ)) :
    Real.log (Nat.card (TrainingCode V (listCap σ) (productCap σ) (Nat.card V)))≤Real.exp σ := by
  have hσ0 : 0≤σ := by linarith
  have hH := ceil_five_exp (σ/2) (by positivity)
  have hJ := ceil_five_exp (13*σ/15) (by positivity)
  have hv : (0:ℝ)<Nat.card V := by exact_mod_cast Nat.card_pos (α:=V)
  have he : 6≤Real.exp (σ/2) := by linarith only [Real.add_one_le_exp (σ/2),hσ]
  have hx : 2≤Real.exp σ := by linarith only [Real.add_one_le_exp σ,hσ]
  have he5 : 1≤Real.exp (5*σ) := Real.one_le_exp_iff.mpr (by positivity)
  have hh : (listCap σ:ℝ)+1≤Real.exp σ := by
    have hpow : Real.exp (σ/2)*Real.exp (σ/2)=Real.exp σ := by rw [←Real.exp_add];congr 1;ring
    dsimp only [listCap]
    nlinarith
  have hb : (Nat.card V:ℝ)+1≤Real.exp (6*σ) := by
    have hm : Real.exp σ*Real.exp (5*σ)=Real.exp (6*σ) := by rw [←Real.exp_add];congr 1;ring
    nlinarith
  have hhlog : Real.log ((listCap σ:ℝ)+1)≤σ := by
    have h := Real.log_le_log (by positivity : (0:ℝ)<(listCap σ:ℝ)+1) hh
    rwa [Real.log_exp] at h
  have hblog : Real.log ((Nat.card V:ℝ)+1)≤6*σ := by
    have h := Real.log_le_log (by positivity : (0:ℝ)<(Nat.card V:ℝ)+1) hb
    rwa [Real.log_exp] at h
  have hvlog : Real.log (Nat.card V)≤5*σ := by
    have h := Real.log_le_log hv hV
    rwa [Real.log_exp] at h
  exact (log_card_TrainingCode (V:=V) (listCap σ) (productCap σ) (Nat.card V)).trans
    (metadata_budget σ (listCap σ) (productCap σ) (Nat.card V+1) (Nat.card V)
      hσ (by positivity) (by positivity) (by positivity) hv hH hJ hhlog hblog hvlog)

lemma profile_of_lengths (σ g : ℝ) (h p : ℕ) (hg : 0≤g) (hghi : g≤σ+Real.log 4)
    (hlen : (h:ℝ)*Real.exp (2*σ)≤Real.exp (3*σ/2+g))
    (plen : (p:ℝ)*Real.exp (σ+17*g/15)≤Real.exp (3*σ/2+g)) :
    h≤listCap σ ∧ p≤listCap σ ∧ h*p≤productCap σ := by
  obtain ⟨hh,hp,hj⟩ := list_length_bounds σ g h p (by positivity) (by positivity) hg hghi hlen plen
  refine ⟨?_,?_,?_⟩
  · exact_mod_cast hh.trans (Nat.le_ceil _)
  · exact_mod_cast (hp.trans (by linarith only [Real.exp_pos (σ/2)] : Real.exp (σ/2)≤4*Real.exp (σ/2))).trans (Nat.le_ceil _)
  · exact_mod_cast hj.trans (Nat.le_ceil _)

end SharpRamseyFive.Metadata

end OAI
