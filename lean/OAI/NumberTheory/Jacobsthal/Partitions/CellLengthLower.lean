import OAI.NumberTheory.Jacobsthal.Estimates.PositiveProgression

namespace OAI

namespace Erdos970

section

namespace ErdosInverseTail
open ErdosInverseHits

noncomputable def commonParentLength (Y p : ℕ) (Qplus : ℝ) : ℕ :=
  ⌊(Y : ℝ)/((p : ℝ)*Qplus)⌋₊

theorem commonParentLength_le_hits (Y p q b : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hb : b ≤ p*q) (Qplus : ℝ) (hqQ : (q : ℝ) ≤ Qplus) :
    commonParentLength Y p Qplus ≤ hitLength Y (p*q) b := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hQ : 0 < Qplus := hqR.trans_le hqQ
  have hA : 0 ≤ (Y : ℝ)/((p : ℝ)*Qplus) := by positivity
  have hJ : (commonParentLength Y p Qplus : ℝ) ≤ (Y : ℝ)/((p : ℝ)*Qplus) := Nat.floor_le hA
  have hden : (p : ℝ)*q ≤ (p : ℝ)*Qplus := mul_le_mul_of_nonneg_left hqQ hpR.le
  have hJB : (commonParentLength Y p Qplus : ℝ) ≤ (Y : ℝ)/((p : ℝ)*q) :=
    hJ.trans (div_le_div_of_nonneg_left (Nat.cast_nonneg _) (mul_pos hpR hqR) hden)
  have hnat : commonParentLength Y p Qplus*(p*q) ≤ Y := by
    exact_mod_cast (le_div_iff₀ (mul_pos hpR hqR)).mp hJB
  have hdiv : commonParentLength Y p Qplus ≤ Y/(p*q) := (Nat.le_div_iff_mul_le (mul_pos hp hq)).mpr hnat
  exact hdiv.trans (Nat.div_le_div_right (by omega : Y ≤ Y+p*q-b))

theorem actual_cell_tail_length (Y p q b : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hb1 : 1 ≤ b) (hb : b ≤ p*q) (Qplus xi : ℝ)
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 1) (hqQ : (q : ℝ) ≤ Qplus) (hQq : Qplus ≤ (1+xi)*(q : ℝ)) :
    ((hitLength Y (p*q) b-commonParentLength Y p Qplus : ℕ) : ℝ) ≤
      xi*(commonParentLength Y p Qplus : ℝ)+3 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hQ : 0 < Qplus := hqR.trans_le hqQ
  have hA : 0 ≤ (Y : ℝ)/((p : ℝ)*Qplus) := by positivity
  have hJlt : (Y : ℝ)/((p : ℝ)*Qplus) < (commonParentLength Y p Qplus : ℝ)+1 := Nat.lt_floor_add_one _
  have hratio : Qplus/(q : ℝ) ≤ 1+xi := (div_le_iff₀ hqR).mpr hQq
  have hB : (Y : ℝ)/((p : ℝ)*q) ≤ (1+xi)*((Y : ℝ)/((p : ℝ)*Qplus)) := by
    calc
      _ = ((Y : ℝ)/((p : ℝ)*Qplus))*(Qplus/(q : ℝ)) := by field_simp
      _ ≤ ((Y : ℝ)/((p : ℝ)*Qplus))*(1+xi) := mul_le_mul_of_nonneg_left hratio hA
      _ = _ := by ring
  have herr := hitLength_error Y (p*q) b (mul_pos hp hq) hb1 hb
  have hN : (hitLength Y (p*q) b : ℝ) ≤ (Y : ℝ)/((p : ℝ)*q)+1 := by
    have hh := (abs_le.mp herr).2
    push_cast at hh
    linarith
  have hJN := commonParentLength_le_hits Y p q b hp hq hb Qplus hqQ
  rw [Nat.cast_sub hJN]
  have hpay := mul_le_mul_of_nonneg_left hJlt.le (by linarith : 0 ≤ 1+xi)
  nlinarith

end ErdosInverseTail

end

section

namespace ErdosInverseTail

theorem common_length_from_log (Y p q u : ℕ) (hp : 0 < p) (hq : 0 < q) (hu : 0 < u)
    (Qplus xi w aStar : ℝ) (hqQ : (q : ℝ) ≤ Qplus) (hQq : Qplus ≤ (1+xi)*(q : ℝ))
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 1) (hw : 1 < w) (ha : 0 < aStar)
    (hlen : 3*aStar/4 ≤ Real.log ((Y : ℝ)/((p : ℝ)*q*u))/Real.log w) :
    w^(3*aStar/4) ≤ 2*(commonParentLength Y p Qplus : ℝ)/(u : ℝ)+2 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hu1 : (1 : ℝ) ≤ u := by exact_mod_cast hu
  have hQ : 0 < Qplus := hqR.trans_le hqQ
  have hw0 : 0 < w := by linarith
  have hlogw : 0 < Real.log w := Real.log_pos hw
  have hlog := (le_div_iff₀ hlogw).mp hlen
  have hlogpos : 0 < Real.log ((Y : ℝ)/((p : ℝ)*q*u)) := by nlinarith
  have hR1 : 1 < (Y : ℝ)/((p : ℝ)*q*u) := (Real.log_pos_iff (by positivity)).mp hlogpos
  have hpow : w^(3*aStar/4) ≤ (Y : ℝ)/((p : ℝ)*q*u) := by
    rw [Real.rpow_def_of_pos hw0]
    calc
      _ ≤ Real.exp (Real.log ((Y : ℝ)/((p : ℝ)*q*u))) := Real.exp_le_exp.mpr (by nlinarith [hlog])
      _ = _ := Real.exp_log (by linarith)
  have hA : 0 ≤ (Y : ℝ)/((p : ℝ)*Qplus) := by positivity
  have hJlt : (Y : ℝ)/((p : ℝ)*Qplus) < (commonParentLength Y p Qplus : ℝ)+1 := Nat.lt_floor_add_one _
  have hratio : Qplus/(q : ℝ) ≤ 1+xi := (div_le_iff₀ hqR).mpr hQq
  have hRupper : (Y : ℝ)/((p : ℝ)*q*u) ≤ 2*((commonParentLength Y p Qplus : ℝ)+1)/(u : ℝ) := by
    calc
      _ = ((Y : ℝ)/((p : ℝ)*Qplus))*(Qplus/(q : ℝ))/(u : ℝ) := by field_simp
      _ ≤ ((Y : ℝ)/((p : ℝ)*Qplus))*(1+xi)/(u : ℝ) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hratio hA) huR.le
      _ ≤ ((commonParentLength Y p Qplus : ℝ)+1)*(1+xi)/(u : ℝ) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hJlt.le (by linarith)) huR.le
      _ ≤ 2*((commonParentLength Y p Qplus : ℝ)+1)/(u : ℝ) := by
        apply div_le_div_of_nonneg_right _ huR.le
        nlinarith [show (0 : ℝ) ≤ commonParentLength Y p Qplus from Nat.cast_nonneg _]
  have htwo : (2 : ℝ)/(u : ℝ) ≤ 2 := (div_le_iff₀ huR).mpr (by linarith)
  calc
    _ ≤ (Y : ℝ)/((p : ℝ)*q*u) := hpow
    _ ≤ 2*((commonParentLength Y p Qplus : ℝ)+1)/(u : ℝ) := hRupper
    _ = 2*(commonParentLength Y p Qplus : ℝ)/(u : ℝ)+2/(u : ℝ) := by ring
    _ ≤ _ := add_le_add le_rfl htwo

end ErdosInverseTail

end

end Erdos970

end OAI
