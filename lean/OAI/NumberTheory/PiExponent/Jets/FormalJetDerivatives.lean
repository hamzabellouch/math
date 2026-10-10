import Mathlib
import OAI.NumberTheory.PiExponent.Jets.JetGeometry

namespace OAI

noncomputable section
namespace PiExponent.FormalJetDerivatives
open MvPowerSeries
open PiExponent.JetGeometry

variable {σ R : Type*} [CommRing R]

theorem pderiv_mem_rationalWeightedIdeal (v : σ → ℚ) (hv : ∀ i, 0 ≤ v i)
    (H : ℚ) (f : MvPowerSeries σ R)
    (hf : f ∈ rationalWeightedIdeal v hv H) (i : σ) :
    pderiv i f ∈ rationalWeightedIdeal v hv (H - v i) := by
  intro d hd
  rw [coeff_pderiv, hf, zero_mul]
  rw [map_add, Finsupp.weight_single, one_nsmul]
  linarith

theorem mul_pderiv_mem_rationalWeightedIdeal (v : σ → ℚ) (hv : ∀ i, 0 ≤ v i)
    (H : ℚ) (f g : MvPowerSeries σ R)
    (hf : f ∈ rationalWeightedIdeal v hv H) (i : σ) :
    g * pderiv i f ∈ rationalWeightedIdeal v hv (H - v i) :=
  (rationalWeightedIdeal v hv (H - v i)).mul_mem_left g
    (pderiv_mem_rationalWeightedIdeal v hv H f hf i)

def jetFrame (m : ℕ) (i : Fin (m + 1)) :
    Derivation R (MvPowerSeries (Fin (m + 1)) R) (MvPowerSeries (Fin (m + 1)) R) :=
  if i = 0 then (1 + X (0 : Fin (m + 1)) : MvPowerSeries (Fin (m+1)) R) • pderiv 0 else pderiv i

@[simp] theorem jetFrame_zero (m : ℕ) (f : MvPowerSeries (Fin (m + 1)) R) :
    jetFrame m 0 f = (1 + X 0) * pderiv 0 f := by
  simp [jetFrame, Derivation.smul_apply, smul_eq_mul]

@[simp] theorem jetFrame_pos (m : ℕ) (i : Fin (m + 1)) (hi : i ≠ 0)
    (f : MvPowerSeries (Fin (m + 1)) R) : jetFrame m i f = pderiv i f := by
  simp [jetFrame, hi]

theorem jetFrame_mem_rationalWeightedIdeal {m : ℕ}
    (v : Fin (m + 1) → ℚ) (hv : ∀ i, 0 ≤ v i)
    (H : ℚ) (f : MvPowerSeries (Fin (m + 1)) R)
    (hf : f ∈ rationalWeightedIdeal v hv H) (i : Fin (m + 1)) :
    jetFrame m i f ∈ rationalWeightedIdeal v hv (H - v i) := by
  by_cases hi : i = 0
  · subst i
    rw [jetFrame_zero]
    exact mul_pderiv_mem_rationalWeightedIdeal v hv H f (1 + X 0) hf 0
  · rw [jetFrame_pos m i hi]
    exact pderiv_mem_rationalWeightedIdeal v hv H f hf i

def jetFrameWord (m : ℕ) (word : List (Fin (m + 1)))
    (f : MvPowerSeries (Fin (m + 1)) R) : MvPowerSeries (Fin (m + 1)) R :=
  word.foldr (fun i g => jetFrame m i g) f

theorem jetFrameWord_mem_rationalWeightedIdeal {m : ℕ}
    (v : Fin (m + 1) → ℚ) (hv : ∀ i, 0 ≤ v i)
    (H : ℚ) (f : MvPowerSeries (Fin (m + 1)) R)
    (hf : f ∈ rationalWeightedIdeal v hv H) (word : List (Fin (m + 1))) :
    jetFrameWord m word f ∈ rationalWeightedIdeal v hv (H - (word.map v).sum) := by
  induction word with
  | nil => simpa [jetFrameWord] using hf
  | cons i word ih =>
    have hh := jetFrame_mem_rationalWeightedIdeal v hv
      (H - (word.map v).sum) (jetFrameWord m word f) ih i
    simpa only [jetFrameWord, List.foldr_cons, List.map_cons, List.sum_cons,
      sub_sub, add_comm] using hh

end PiExponent.FormalJetDerivatives

end

end OAI
