import OAI.NumberTheory.Ostmann.QuadraticCenter.PositiveFrequencyCutoff
import OAI.NumberTheory.Ostmann.QuadraticCenter.PositiveFrequencyNormalization

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

def positiveFrequencyQuadraticSum (d : ℕ) [NeZero d] (G : ZMod d → ℂ)
    (mInv : ZMod d) (s v P : ℕ) (a R : ℝ) : ℂ :=
  normalizedSmoothQuadraticSum P (Real.sqrt (R / ((s : ℝ)*v/d)))
    (fun w => Supply.unitaryDFT G (-((s*v*w^2 : ℕ) : ZMod d) * mInv))
    (a * ((s : ℝ)*v/d))

theorem positiveFrequencyQuadraticSum_centered {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (A : ∀ i, Finset (ZMod (p i))) (mInv : ZMod (∏ i, p i))
    (s v P : ℕ) (R h θ : ℝ) :
    positiveFrequencyQuadraticSum (∏ i, p i) (centeredProduct p hcop A) mInv s v P (h+θ) R =
      centeredQuadraticSum p hcop A mInv s v P R h θ := rfl

theorem positiveFrequencyAmplitude_square {d : ℕ} [NeZero d]
    (G : ZMod d → ℂ) (mInv : ZMod d) (a : ℝ) {R : ℝ} (hR : 0 < R)
    {s v : ℕ} (hs : 0 < s) (hv : 0 < v) (w : ℕ) :
    positiveFrequencyAmplitude d G mInv a R (s*v*w^2) =
      Supply.unitaryDFT G (-((s*v*w^2 : ℕ) : ZMod d) * mInv) *
        weylPhase ((a * ((s : ℝ)*v/d)) * (w : ℝ)^2) *
          cutoffFourier (((w : ℝ) / Real.sqrt (R / ((s : ℝ)*v/d))) ^ 2) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_neZero d
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hv' : (0 : ℝ) < v := by exact_mod_cast hv
  rw [quadraticCorrelation_cutoff_argument hd' hs' hv' hR]
  unfold positiveFrequencyAmplitude
  have hcast : ((s*v*w^2 : ℕ) : ℝ) = (s : ℝ)*v*(w : ℝ)^2 := by push_cast; rfl
  rw [hcast]
  have hphase : a * ((s : ℝ)*v*(w : ℝ)^2) / d =
      (a * ((s : ℝ)*v/d)) * (w : ℝ)^2 := by ring
  rw [hphase]

theorem positiveFrequencyAmplitude_square_cutoff_remove {d : ℕ} [NeZero d]
    (G : ZMod d → ℂ) (mInv : ZMod d) (a : ℝ) {R : ℝ} (hR : 0 < R)
    (s v P B : ℕ) (hB : R*d ≤ (B : ℝ)) :
    (∑ w ∈ (Finset.Icc 1 B).filter (fun w => s*v*w^2 ≤ B ∧ P ∣ w),
      positiveFrequencyAmplitude d G mInv a R (s*v*w^2)) =
      ∑ w ∈ (Finset.Ioc 0 B).filter (fun w => P ∣ w),
        positiveFrequencyAmplitude d G mInv a R (s*v*w^2) := by
  apply Finset.sum_subset
  · intro w hw
    obtain ⟨hw, hprod, hP⟩ := Finset.mem_filter.mp hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr
      ⟨(Finset.mem_Icc.mp hw).1, (Finset.mem_Icc.mp hw).2⟩, hP⟩
  · intro w hw hnot
    obtain ⟨hw, hP⟩ := Finset.mem_filter.mp hw
    have hprod : B < s*v*w^2 := by
      by_contra h
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
        ⟨(Finset.mem_Ioc.mp hw).1, (Finset.mem_Ioc.mp hw).2⟩, Nat.le_of_not_gt h, hP⟩)
    apply positiveFrequencyAmplitude_eq_zero G mInv a hR
    exact hB.trans (by exact_mod_cast hprod.le)

theorem positiveFrequencyAmplitude_square_sum_eq {d : ℕ} [NeZero d]
    (G : ZMod d → ℂ) (mInv : ZMod d) (a : ℝ) {R : ℝ} (hR : 0 < R)
    {s v : ℕ} (hs : 0 < s) (hv : 0 < v) (P B : ℕ) (hB : R*d ≤ (B : ℝ)) :
    (Real.sqrt (R*d) : ℂ)⁻¹ *
      (∑ w ∈ (Finset.Icc 1 B).filter (fun w => s*v*w^2 ≤ B ∧ P ∣ w),
        positiveFrequencyAmplitude d G mInv a R (s*v*w^2)) =
      (Real.sqrt (s : ℝ) : ℂ)⁻¹ * (Real.sqrt (v : ℝ) : ℂ)⁻¹ *
        positiveFrequencyQuadraticSum d G mInv s v P a R := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_neZero d
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hv' : (0 : ℝ) < v := by exact_mod_cast hv
  have hg : positiveFrequencyQuadraticSum d G mInv s v P a R =
      ((Real.sqrt (R / ((s : ℝ)*v/d)))⁻¹ : ℂ) *
        ∑ w ∈ (Finset.Ioc 0 B).filter (fun w => P ∣ w),
          positiveFrequencyAmplitude d G mInv a R (s*v*w^2) := by
    unfold positiveFrequencyQuadraticSum
    rw [normalizedSmoothQuadraticSum_truncation (by positivity)
      (positive_frequency_square_cutoff_le (Nat.pos_of_neZero d) hs hv hR hB)]
    rw [Complex.ofReal_inv]
    congr 1
    apply Finset.sum_congr rfl
    intro w hw
    exact (positiveFrequencyAmplitude_square G mInv a hR hs hv w).symm
  rw [positiveFrequencyAmplitude_square_cutoff_remove G mInv a hR s v P B hB, hg]
  have hn := congrArg (fun x : ℝ => (x : ℂ)) (positive_frequency_sqrt_normalization hR hd' hs' hv')
  push_cast at hn
  rw [hn]
  ring

end Ostmann.QuadraticCenter

end

end OAI
