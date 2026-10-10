import Mathlib
import OAI.Probability.SphericalField.Sphere.Limit

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron

def stepLogRatios : (k : ℕ) → (Fin (k+1) → ℝ) → (Fin k → ℝ) → ℝ
  | 0, _, _ => 0
  | k+1, D, z => stepLogRatios k (fun i => D i.succ) (fun i => z i.succ)+
      (Real.log (D 0)-Real.log (D 1))/(2*z 0)

lemma quadraticCascadePrecision_stationary (k : ℕ) (σ : ℕ → ℝ)
    (q D : Fin (k+1) → ℝ) (z : Fin k → ℝ) (hD : ∀ i, 0 < D i)
    (hgap : ∀ i : Fin k, D i.castSucc-D i.succ=z i*(q i.succ-q i.castSucc))
    (hσ : ∀ i : Fin k, (σ (k-1-i.val))^2=(q i.succ-q i.castSucc)/(D i.castSucc*D i.succ)) :
    quadraticCascadePrecision σ (D (Fin.last k))⁻¹ k z = (D 0)⁻¹ := by
  induction k with
  | zero => simp [quadraticCascadePrecision,Fin.fin_one_eq_zero]
  | succ k ih =>
    have ht := ih (fun i => q i.succ) (fun i => D i.succ) (fun i => z i.succ)
      (fun i => hD i.succ) (fun i => hgap i.succ) (fun i => by
        have hs := hσ i.succ
        have he : k+1-1-(i.succ).val=k-1-i.val := by simp only [Fin.val_succ]; omega
        simpa only [he,Fin.castSucc_succ] using hs)
    simp only [Fin.succ_last,Fin.succ_zero_eq_one] at ht
    have hs := hσ 0
    simp only [Fin.val_zero,Nat.add_sub_cancel,Nat.sub_zero,Fin.castSucc_zero,Fin.succ_zero_eq_one] at hs
    have hg := hgap 0
    simp only [Fin.castSucc_zero,Fin.succ_zero_eq_one] at hg
    dsimp only [quadraticCascadePrecision]
    rw [ht,hs]
    have h0 := (hD 0).ne'
    have h1 := (hD 1).ne'
    field_simp
    nlinarith

lemma quadraticCascadeReciprocalSlope_stationary (k : ℕ) (σ : ℕ → ℝ)
    (q D : Fin (k+1) → ℝ) (z : Fin k → ℝ) (hD : ∀ i, 0 < D i) (hz : ∀ i, 0 < z i)
    (hgap : ∀ i : Fin k, D i.castSucc-D i.succ=z i*(q i.succ-q i.castSucc))
    (hσ : ∀ i : Fin k, (σ (k-1-i.val))^2=(q i.succ-q i.castSucc)/(D i.castSucc*D i.succ)) :
    quadraticCascadeReciprocalSlope σ (D (Fin.last k))⁻¹ k z = -(q (Fin.last k)-q 0)/2 := by
  induction k with
  | zero => simp [quadraticCascadeReciprocalSlope,Fin.fin_one_eq_zero]
  | succ k ih =>
    have hst : ∀ i : Fin k, (σ (k-1-i.val))^2 =
        (q i.succ.succ-q i.castSucc.succ)/(D i.castSucc.succ*D i.succ.succ) := by
      intro i
      have hs := hσ i.succ
      have he : k+1-1-(i.succ).val=k-1-i.val := by simp only [Fin.val_succ]; omega
      simpa only [he,Fin.castSucc_succ] using hs
    have ht := ih (fun i => q i.succ) (fun i => D i.succ) (fun i => z i.succ)
      (fun i => hD i.succ) (fun i => hz i.succ) (fun i => hgap i.succ) hst
    have hp := quadraticCascadePrecision_stationary (k+1) σ q D z hD hgap hσ
    have hpt := quadraticCascadePrecision_stationary k σ (fun i => q i.succ)
      (fun i => D i.succ) (fun i => z i.succ) (fun i => hD i.succ) (fun i => hgap i.succ) hst
    simp only [Fin.succ_last,Fin.succ_zero_eq_one] at ht hpt
    have hg := hgap 0
    simp only [Fin.castSucc_zero,Fin.succ_zero_eq_one] at hg
    rw [quadraticCascadeReciprocalSlope,ht,hp,hpt]
    simp only [one_div,inv_inv]
    have hz0 := (hz 0).ne'
    field_simp
    nlinarith

lemma quadraticCascadeOffset_stationary (k : ℕ) (σ : ℕ → ℝ)
    (q D : Fin (k+1) → ℝ) (z : Fin k → ℝ) (hD : ∀ i, 0 < D i)
    (hgap : ∀ i : Fin k, D i.castSucc-D i.succ=z i*(q i.succ-q i.castSucc))
    (hσ : ∀ i : Fin k, (σ (k-1-i.val))^2=(q i.succ-q i.castSucc)/(D i.castSucc*D i.succ)) :
    quadraticCascadeOffset σ (D (Fin.last k))⁻¹ k z = stepLogRatios k D z := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hst : ∀ i : Fin k, (σ (k-1-i.val))^2 =
        (q i.succ.succ-q i.castSucc.succ)/(D i.castSucc.succ*D i.succ.succ) := by
      intro i
      have hs := hσ i.succ
      have he : k+1-1-(i.succ).val=k-1-i.val := by simp only [Fin.val_succ]; omega
      simpa only [he,Fin.castSucc_succ] using hs
    have ht := ih (fun i => q i.succ) (fun i => D i.succ) (fun i => z i.succ)
      (fun i => hD i.succ) (fun i => hgap i.succ) hst
    have hp := quadraticCascadePrecision_stationary (k+1) σ q D z hD hgap hσ
    have hpt := quadraticCascadePrecision_stationary k σ (fun i => q i.succ)
      (fun i => D i.succ) (fun i => z i.succ) (fun i => hD i.succ) (fun i => hgap i.succ) hst
    simp only [Fin.succ_last,Fin.succ_zero_eq_one] at ht hpt
    rw [quadraticCascadeOffset,ht,hp,hpt,stepLogRatios]
    simp only [Real.log_inv]
    ring

lemma canonicalGaussianFreeValue_stationary (k : ℕ) (σ : ℕ → ℝ)
    (q D : Fin (k+1) → ℝ) (z : Fin k → ℝ) (hD : ∀ i, 0 < D i)
    (hgap : ∀ i : Fin k, D i.castSucc-D i.succ=z i*(q i.succ-q i.castSucc))
    (hσ : ∀ i : Fin k, (σ (k-1-i.val))^2=(q i.succ-q i.castSucc)/(D i.castSucc*D i.succ)) :
    canonicalGaussianFreeValue σ k z (q 0/(D 0)^2) (D (Fin.last k))⁻¹ =
      Real.log (D (Fin.last k))/2+stepLogRatios k D z+q 0/(2*D 0) := by
  rw [canonicalGaussianFreeValue,quadraticCascadePrecision_stationary k σ q D z hD hgap hσ,
    quadraticCascadeOffset_stationary k σ q D z hD hgap hσ,Real.log_inv]
  have h0 := (hD 0).ne'
  field_simp

lemma canonicalGaussianFreeValue_stationarity (k : ℕ) (σ : ℕ → ℝ)
    (q D : Fin (k+1) → ℝ) (z : Fin k → ℝ) (hD : ∀ i, 0 < D i) (hz : ∀ i, 0 < z i)
    (hend : D (Fin.last k)=1-q (Fin.last k))
    (hgap : ∀ i : Fin k, D i.castSucc-D i.succ=z i*(q i.succ-q i.castSucc))
    (hσ : ∀ i : Fin k, (σ (k-1-i.val))^2=(q i.succ-q i.castSucc)/(D i.castSucc*D i.succ)) :
    -1/(2*(D (Fin.last k))⁻¹)+quadraticCascadeReciprocalSlope σ (D (Fin.last k))⁻¹ k z-
      (q 0/(D 0)^2)/(2*(quadraticCascadePrecision σ (D (Fin.last k))⁻¹ k z)^2) = -1/2 := by
  rw [quadraticCascadePrecision_stationary k σ q D z hD hgap hσ,
    quadraticCascadeReciprocalSlope_stationary k σ q D z hD hz hgap hσ]
  have h0 := (hD 0).ne'
  have ht := (hD (Fin.last k)).ne'
  field_simp
  nlinarith

theorem expectedCoordinateSphereLog_stationary_data (k : ℕ) (σ : ℕ → ℝ)
    (q D : Fin (k+1) → ℝ) (z : Fin k → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1) (hD : ∀ i, 0 < D i)
    (hend : D (Fin.last k)=1-q (Fin.last k))
    (hgap : ∀ i : Fin k, D i.castSucc-D i.succ=z i*(q i.succ-q i.castSucc))
    (hσ : ∀ i : Fin k, (σ (k-1-i.val))^2=(q i.succ-q i.castSucc)/(D i.castSucc*D i.succ))
    (r : ℝ≥0) (hr : (r:ℝ)=q 0/(D 0)^2) :
    Tendsto (fun n : ℕ => expectedCoordinateSphereLog n k σ z r) atTop
      (𝓝 (Real.log (D (Fin.last k))/2+stepLogRatios k D z+q 0/(2*D 0)+
        ((D (Fin.last k))⁻¹-1)/2)) := by
  have hp : 0 < quadraticCascadePrecision σ (D (Fin.last k))⁻¹ k z := by
    rw [quadraticCascadePrecision_stationary k σ q D z hD hgap hσ]
    exact inv_pos.mpr (hD 0)
  have hstat := canonicalGaussianFreeValue_stationarity k σ q D z hD hz0 hend hgap hσ
  rw [← hr] at hstat
  have ht := expectedCoordinateSphereLog_tendsto k σ z hz hz0 hz1 r (D (Fin.last k))⁻¹ hp hstat
  rw [hr,canonicalGaussianFreeValue_stationary k σ q D z hD hgap hσ] at ht
  exact ht

end SphericalPerceptron
end
end

end OAI
