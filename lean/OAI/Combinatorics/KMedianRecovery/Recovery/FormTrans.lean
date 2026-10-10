import Mathlib
import OAI.Combinatorics.KMedianRecovery.Encoding.RationalInflatedShape

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid

section
open Matrix
open scoped Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
lemma form_le_trans (A B C : Matrix V V ℝ) (hAB : (B-A).PosSemidef) (hBC : (C-B).PosSemidef) :
    (C-A).PosSemidef := by
  have hh := hAB.add hBC
  have he : B-A+(C-B)=C-A := by abel
  rwa [he] at hh

omit [Fintype V] [DecidableEq V] in
lemma form_le_smul (A B : Matrix V V ℝ) (h : (B-A).PosSemidef) (r : ℝ) (hr : 0≤r) :
    (r • B-r • A).PosSemidef := by
  simpa only [smul_sub] using h.smul hr

omit [Fintype V] [DecidableEq V] in
lemma form_scalar_mono (H : Matrix V V ℝ) (hH : H.PosSemidef) (r s : ℝ) (hrs : r ≤ s) :
    (s • H-r • H).PosSemidef := by
  simpa only [sub_smul] using hH.smul (sub_nonneg.mpr hrs)

lemma cutShape_lower (d : ℝ) (hd : 2≤d) (H : Matrix V V ℝ) (hH : H.PosDef)
    (a : V → ℝ) (ha : a≠0) : (cutShape d H a-(1/3:ℝ) • H).PosSemidef := by
  have hu := (dual_normal_properties H hH a ha).2.1
  have hc := cutMatrix_pos d (by linarith) H⁻¹ hH.inv (normalizedDual H a)
  have hs := (cutMatrix_spectral d hd H⁻¹ hH.inv (normalizedDual H a) hu).2
  have hh := inverse_antitone _ _ hc (hH.inv.smul (by norm_num : (0:ℝ)<3)) hs
  rw [inv_smul_real _ hH.inv _ (by norm_num : (3:ℝ)≠0),
    nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.mpr hH.det_pos.ne'),
    ←cutShape_inverse d (by linarith) H hH a ha] at hh
  simpa only [one_div] using hh

lemma inflatedShape_lower (H : Matrix V V ℚ) (a : V → ℚ) (hn : 2≤Fintype.card V)
    (hH : (realMatrix H).PosDef) (ha : a≠0) :
    (realMatrix (rationalInflatedShape H a)-(1/3:ℝ) • realMatrix H).PosSemidef := by
  have hn' : 2≤(Fintype.card V:ℝ) := by exact_mod_cast hn
  have hc := cutShape_pos _ (by linarith : 1<(Fintype.card V:ℝ)) _ hH _ (realVector_ne_zero a ha)
  have hl := inflation_bounds (Fintype.card V) (by linarith)
  have hl0 := inflation_pos (Fintype.card V) (by omega)
  have hrs : (1:ℝ)≤1/(1-1/(8*(Fintype.card V:ℝ)^2)) := (le_div_iff₀ hl0).mpr (by linarith [hl.2])
  have hh := form_scalar_mono _ hc.posSemidef 1 _ hrs
  rw [one_smul] at hh
  rw [real_inflatedShape]
  exact form_le_trans _ _ _ (cutShape_lower _ hn' _ hH _ (realVector_ne_zero a ha)) hh

lemma stepShape_lower (D : ℕ) (hD : 0<D) (H : Matrix V V ℚ) (a : V → ℚ)
    (hn : 2≤Fintype.card V) (hH : (realMatrix H).PosDef) (ha : a≠0) :
    (realMatrix (rationalStepShape D H a)-(1/3:ℝ) • realMatrix H).PosSemidef := by
  have hn' : 1<(Fintype.card V:ℝ) := by exact_mod_cast (show 1<Fintype.card V by omega)
  have hp : (realMatrix (rationalInflatedShape H a)).PosDef := by
    rw [real_inflatedShape]
    exact (cutShape_pos _ hn' _ hH _ (realVector_ne_zero a ha)).smul
      (one_div_pos.mpr (inflation_pos _ (by omega)))
  have hsym := realMatrix_symm _ (gridMatrix_symm D _ (rational_symm_of_real _ hp.isHermitian))
  have hh := upperRound_above _ _ hp.isHermitian hsym _ (by positivity)
    (gridMatrix_error D hD (rationalInflatedShape H a))
  rw [←real_gridShape] at hh
  exact form_le_trans _ _ _ (inflatedShape_lower H a hn hH ha) hh

lemma stepShape_pos (D : ℕ) (hD : 0<D) (H : Matrix V V ℚ) (a : V → ℚ)
    (hn : 2≤Fintype.card V) (hH : (realMatrix H).PosDef) (ha : a≠0) :
    (realMatrix (rationalStepShape D H a)).PosDef := by
  have hh := (hH.smul (by norm_num : (0:ℝ)<1/3)).add_posSemidef
    (stepShape_lower D hD H a hn hH ha)
  have he : (1/3:ℝ) • realMatrix H+(realMatrix (rationalStepShape D H a)-(1/3:ℝ) • realMatrix H)=realMatrix (rationalStepShape D H a) := by abel
  rwa [he] at hh

lemma stepShape_upper (D : ℕ) (hD : 0<D) (H : Matrix V V ℚ) (a : V → ℚ)
    (hn : 2≤Fintype.card V) (hH : (realMatrix H).PosDef) (ha : a≠0) (m : ℝ)
    (hm : (realMatrix (rationalInflatedShape H a)-m • (1:Matrix V V ℝ)).PosSemidef)
    (hprecision : 2*(Fintype.card V:ℝ)/(D:ℝ)≤(1/(8*(Fintype.card V:ℝ)^2))*m) :
    ((2:ℝ) • realMatrix H-realMatrix (rationalStepShape D H a)).PosSemidef := by
  have hn' : 2≤(Fintype.card V:ℝ) := by exact_mod_cast hn
  obtain ⟨hp,hhi,hlo⟩ := stepShape_pos_bounds D hD H a hn hH ha m hm hprecision
  rw [real_inflatedShape,inflatedShape_inverse _ (by linarith) _ hH _ (realVector_ne_zero a ha)] at hhi hlo
  have hs := (robust_spectral _ hn' _ _ hH.inv _
    (dual_normal_properties _ hH _ (realVector_ne_zero a ha)).2.1 hlo hhi).1
  have hh := inverse_antitone _ _ (hH.inv.smul (by norm_num : (0:ℝ)<1/2)) hp.inv hs
  rw [inv_smul_real _ hH.inv _ (by norm_num : (1/2:ℝ)≠0),
    nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.mpr hH.det_pos.ne'),
    nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.mpr hp.det_pos.ne')] at hh
  norm_num at hh ⊢
  exact hh

end

open Matrix
open scoped Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

def gridDenominator (n T : ℕ) : ℕ := 16*n^3*3^(T+1)

lemma gridDenominator_pos (n T : ℕ) (hn : 0<n) : 0<gridDenominator n T := by
  unfold gridDenominator
  positivity

lemma gridDenominator_precision (n T : ℕ) (hn : 0<n) :
    2*(n:ℝ)/(gridDenominator n T:ℝ)=1/(8*(n:ℝ)^2)*(1/3:ℝ)^(T+1) := by
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  simp only [gridDenominator,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,_root_.one_div_pow]
  field_simp
  ring

omit [Fintype V] in
lemma iterate_lower (H : ℕ → Matrix V V ℝ) (h0 : (H 0-1).PosSemidef)
    (hh : ∀ t, (H (t+1)-(1/3:ℝ) • H t).PosSemidef) :
    ∀ t, (H t-(1/3:ℝ)^t • (1:Matrix V V ℝ)).PosSemidef := by
  intro t
  induction t with
  | zero => simpa using h0
  | succ t ih =>
    have hs := form_le_smul _ _ ih (1/3) (by norm_num)
    rw [smul_smul,←pow_succ'] at hs
    exact form_le_trans _ _ _ hs (hh t)

lemma inflatedShape_precision (H : Matrix V V ℚ) (a : V → ℚ) (hn : 2≤Fintype.card V)
    (hH : (realMatrix H).PosDef) (ha : a≠0) (t T : ℕ) (ht : t≤T)
    (hlo : (realMatrix H-(1/3:ℝ)^t • (1:Matrix V V ℝ)).PosSemidef) :
    (realMatrix (rationalInflatedShape H a)-(1/3:ℝ)^(T+1) • (1:Matrix V V ℝ)).PosSemidef := by
  have hs := form_le_smul _ _ hlo (1/3) (by norm_num)
  rw [smul_smul,←pow_succ'] at hs
  have ht' : (1/3:ℝ)^(T+1)≤(1/3:ℝ)^(t+1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hm := form_scalar_mono (1:Matrix V V ℝ) Matrix.PosSemidef.one _ _ ht'
  exact form_le_trans _ _ _ hm (form_le_trans _ _ _ hs (inflatedShape_lower H a hn hH ha))

lemma gridDenominator_size (n T : ℕ) : gridDenominator n T≤2^(4+3*n+2*(T+1)) := by
  have hn : n≤2^n := (Nat.lt_two_pow_self).le
  have ht : 3^(T+1)≤(2^2)^(T+1) := Nat.pow_le_pow_left (by norm_num) _
  have hh := Nat.mul_le_mul (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left hn 3)) ht
  have he : 16*(2^n)^3*(2^2)^(T+1)=2^(4+3*n+2*(T+1)) := by
    calc
      _ = 2^4*(2^n)^3*(2^2)^(T+1) := rfl
      _ = _ := by rw [←pow_mul,←pow_mul,←pow_add,←pow_add]; congr 1; ring
  exact hh.trans_eq he

end MetricKMedianRecovery.Ellipsoid

end OAI
