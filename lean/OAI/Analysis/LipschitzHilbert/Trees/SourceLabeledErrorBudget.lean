import OAI.Analysis.LipschitzHilbert.Phase.SourceLabeledAngularErrorData
import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledErrorTail

namespace OAI

/-! Fixed profile order, geometric bounds, and selector multiplicity give
polynomial source constants without a factor counting the available labels. -/

noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert

namespace SourceLabeledLattice

theorem eventually_absoluteConstant_le (O : ℕ) (R p : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item),
      P.order ≤ O → P.ratioBound ≤ R → P.profileBound ≤ L^p →
      P.absoluteConstant ≤ L^(p+1) := by
  filter_upwards [eventually_ge_atTop (max 1 (((2:ℝ)^O*R^2)*3^(2*O)))] with L hlarge
  have hL : 0 < L := zero_lt_one.trans_le ((le_max_left _ _).trans hlarge)
  have hc : ((2:ℝ)^O*R^2)*3^(2*O) ≤ L := (le_max_right _ _).trans hlarge
  intro N κ Label Item _ _ P hO hRatio hProfile
  have hR0 : 0 ≤ P.ratioBound := zero_le_one.trans P.ratioBound_ge_one
  have hProfile0 := P.profileBound_pos.le
  have h2 : (2:ℝ)^P.order ≤ 2^O := pow_le_pow_right₀ (by norm_num) hO
  have h3 : (3:ℝ)^(2*P.order) ≤ 3^(2*O) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hRatio2 := pow_le_pow_left₀ hR0 hRatio 2
  calc
    P.absoluteConstant ≤ ((2^O*L^p)*R^2)*3^(2*O) := by
      unfold absoluteConstant
      exact mul_le_mul (mul_le_mul (mul_le_mul h2 hProfile hProfile0 (by positivity))
        hRatio2 (sq_nonneg _) (by positivity)) h3 (by positivity) (by positivity)
    _ = (((2:ℝ)^O*R^2)*3^(2*O))*L^p := by ring
    _ ≤ L*L^p := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hL.le _)
    _ = L^(p+1) := by rw [Real.rpow_add hL,Real.rpow_one]; ring

end SourceLabeledLattice

namespace LabeledAngularErrorFamily

theorem eventually_sourceAmplitude_le (K H : ℕ) (M D p : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ (N : ℕ) (Λ : Fin N → Type) (κ : Type)
      (ι : ∀ j, Λ j → Type) [∀ j, Fintype (Λ j)] [Fintype κ] [∀ j b, Fintype (ι j b)]
      (P : LabeledAngularErrorFamily N Λ κ ι),
      P.radiusBound ≤ K → P.multiplicity ≤ H →
      P.multiplierBound ≤ M → P.multiplierLip ≤ D → P.packetBound ≤ L^p →
      P.sourceAmplitude ≤ L^(p+1) := by
  let C : ℝ := ((64*(4*Real.pi)^2)*(2*((2*K+1)*H):ℕ))*(2*M+D)
  filter_upwards [eventually_ge_atTop (max 1 C)] with L hlarge
  have hL : 0 < L := zero_lt_one.trans_le ((le_max_left _ _).trans hlarge)
  have hC : C ≤ L := (le_max_right _ _).trans hlarge
  intro N Λ κ ι _ _ _ P hK hH hPM hPD hP
  have hn : 2*((2*P.radiusBound+1)*P.multiplicity) ≤ 2*((2*K+1)*H) :=
    Nat.mul_le_mul_left 2 (Nat.mul_le_mul
      (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hK) 1) hH)
  have hn' : (2*((2*P.radiusBound+1)*P.multiplicity):ℕ) ≤
      (2*((2*K+1)*H):ℕ) := hn
  have hr : ((2*((2*P.radiusBound+1)*P.multiplicity):ℕ):ℝ) ≤
      (2*((2*K+1)*H):ℕ) := by exact_mod_cast hn'
  have hB : 0 ≤ 2*P.multiplierBound+P.multiplierLip := by
    linarith [P.multiplierBound_nonneg,P.multiplierLip_nonneg]
  calc
    P.sourceAmplitude ≤ ((64*(4*Real.pi)^2)*(2*((2*K+1)*H):ℕ))*(L^p*(2*M+D)) := by
      unfold sourceAmplitude
      exact mul_le_mul (mul_le_mul_of_nonneg_left hr (by positivity))
        (mul_le_mul hP (by linarith) hB (Real.rpow_nonneg hL.le _))
        (mul_nonneg P.packetBound_nonneg hB) (by positivity)
    _ = C*L^p := by dsimp [C]; ring
    _ ≤ L*L^p := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hL.le _)
    _ = L^(p+1) := by rw [Real.rpow_add hL,Real.rpow_one]; ring

end LabeledAngularErrorFamily
end LipschitzHilbert

end

end OAI
