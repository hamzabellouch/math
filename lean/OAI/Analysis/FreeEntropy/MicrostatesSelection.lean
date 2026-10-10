import OAI.Analysis.FreeEntropy.GaussianProjectionMoments

namespace OAI

noncomputable section
open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal Topology
namespace FiniteEntropySeparation
 def matrixVolumeEntropy {n d : ℕ} (s : Set (MatrixCoordinates n d)) : EReal :=
  ((((d:ℝ)^2)⁻¹:ℝ):EReal)*(volume s).log+(((n:ℝ)/2*Real.log d:ℝ):EReal)
 theorem matrixVolumeEntropy_ne_bot_volume {n d : ℕ} (hd : 0<d) (s : Set (MatrixCoordinates n d))
    (hs : matrixVolumeEntropy s ≠ ⊥) : volume s ≠ 0 := by
  intro h
  apply hs
  rw [matrixVolumeEntropy,h,ENNReal.log_zero,EReal.coe_mul_bot_of_pos (by positivity),EReal.bot_add]
 theorem matrixVolumeEntropy_coe {n d : ℕ} (s : Set (MatrixCoordinates n d))
    (hs : volume s ≠ 0) (ht : volume s ≠ ⊤) :
    matrixVolumeEntropy s = (((d:ℝ)^2)⁻¹*Real.log (volume s).toReal+(n:ℝ)/2*Real.log d:ℝ) := by
  rw [matrixVolumeEntropy, ENNReal.log_pos_real' (ENNReal.toReal_pos hs ht)]
  simp only [← EReal.coe_mul,← EReal.coe_add]
 theorem exists_strictMono_diagonal (P : ℕ → ℕ → Prop)
    (hP : ∀k L,∃d,L<d ∧ P k d) : ∃D : ℕ → ℕ, StrictMono D ∧ ∀k,P k (D k) := by
  classical
  choose f hf hfP using hP
  let D : ℕ → ℕ := fun k => Nat.rec (f 0 0) (fun k d => f (k+1) d) k
  refine ⟨D,strictMono_nat_of_lt_succ (fun k => hf (k+1) (D k)),?_⟩
  intro k
  cases k with
  | zero => exact hfP 0 0
  | succ k => exact hfP (k+1) (D k)
 variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {M : VonNeumannAlgebra H} (τ : TracialVector M) {n : ℕ} (X : Fin n → H →L[ℂ] H)
 def diagonalMicrostates (R : ℝ) (k d : ℕ) : Set (MatrixCoordinates n d) :=
    microstates τ X R k d ((k+1:ℝ)⁻¹)
 theorem exists_microstate_dimensions {R b : ℝ} (hb : (b:EReal)<chiCutoff τ X R) :
    ∃D : ℕ → ℕ, StrictMono D ∧ (∀k,0<D k) ∧
      ∀k,(b:EReal)< matrixVolumeEntropy (diagonalMicrostates τ X R k (D k)) := by
  have hP (k L : ℕ) : ∃d,L<d ∧ 0<d ∧
      (b:EReal)< matrixVolumeEntropy (diagonalMicrostates τ X R k d) := by
    have he : 0<(k+1:ℝ)⁻¹ := by positivity
    have hl := hb.trans_le (iInf_le_of_le k (iInf_le _ ⟨(k+1:ℝ)⁻¹,he⟩))
    have hfreq := frequently_lt_of_lt_limsup (h := hl)
    obtain ⟨d,hd,hb'⟩ := (frequently_atTop.mp hfreq) L
    exact ⟨d+1,by omega,by omega,by simpa [matrixVolumeEntropy,diagonalMicrostates] using hb'⟩
  obtain ⟨D,hD,h⟩ := exists_strictMono_diagonal (fun k d => 0<d ∧
    (b:EReal)< matrixVolumeEntropy (diagonalMicrostates τ X R k d)) hP
  exact ⟨D,hD,fun k => (h k).1,fun k => (h k).2⟩
 theorem diagonalMicrostates_moments {D : ℕ → ℕ} {R : ℝ}
    (a : (k:ℕ) → MatrixCoordinates n (D k))
    (ha : ∀k,a k ∈ diagonalMicrostates τ X R k (D k)) (w : List (Fin n)) :
    Tendsto (fun k => matrixMoment (a k) w) atTop (𝓝 (wordMoment τ X w)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun k => norm_nonneg _))
  · filter_upwards [eventually_ge_atTop w.length] with k hk
    exact ((ha k).2 w hk).le
  · simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
 theorem diagonalMicrostates_measurable (R : ℝ) (k d : ℕ) :
    MeasurableSet (diagonalMicrostates τ X R k d) := microstates_measurable τ X R k d _
 theorem diagonalMicrostates_uniform_probability {R b : ℝ} (hR : 0≤R) {D : ℕ → ℕ}
    (hD : ∀k,0<D k) (hb : ∀k,(b:EReal)< matrixVolumeEntropy (diagonalMicrostates τ X R k (D k))) (k : ℕ) :
    IsProbabilityMeasure (cond volume (diagonalMicrostates τ X R k (D k))) := by
  apply cond_isProbabilityMeasure_of_finite
  · exact matrixVolumeEntropy_ne_bot_volume (hD k) _ (ne_bot_of_gt ((EReal.bot_lt_coe b).trans (hb k)))
  · exact ne_of_lt (microstates_volume_lt_top τ X R hR k (D k) _)
end FiniteEntropySeparation

end

end OAI
