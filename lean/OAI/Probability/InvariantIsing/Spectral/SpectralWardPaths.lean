import OAI.Probability.InvariantIsing.Spectral.SpectralReplicaProduct
import OAI.Probability.InvariantIsing.Spectral.SpectralWardLimits
import OAI.Probability.InvariantIsing.Arrays.ReplicaWardPaths

namespace OAI

/-! Limiting spectral Ward tests give the manuscript path equation for
bounded synchronized factors of the actual total-overlap quantile. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing

lemma spectralSpinQuantile_integral {m : ℕ} (Q : ProbabilityMeasure (SpectralArray (m + 1)))
    (hP : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x)
    (hn : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ a, 0 ≤ (x (0,1) a : ℝ))
    (F : ℝ → ℝ) (hF : Measurable F) :
    (∫ x, F (spectralSpinArray x 0 1) ∂(Q : Measure (SpectralArray (m + 1)))) =
      ∫ s, F (spectralSpinQuantilePath Q hP hn s) ∂pathMeasure := by
  have hm : Measurable (fun x : SpectralArray (m + 1) => spectralSpinArray x 0 1) := by
    unfold spectralSpinArray
    fun_prop
  have he := integral_map_of_stronglyMeasurable (μ := (Q : Measure (SpectralArray (m + 1)))) hm hF.stronglyMeasurable
  have hp := integral_map_of_stronglyMeasurable (μ := pathMeasure)
    (spectralSpinQuantilePath Q hP hn).measurable hF.stronglyMeasurable
  rw [spectralSpinQuantilePath_law Q hP hn] at hp
  exact he.symm.trans hp

 theorem spectralPartition_offWardPath {m : ℕ}
    {Q : ProbabilityMeasure (SpectralArray (m + 1))}
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray (m + 1))))
    (hG : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralGram x)
    (q : Fin (m + 1) → ℝ) (hq : ∀ a, 0 ≤ q a)
    (hd : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ i a, (x (i,i) a : ℝ) = q a)
    (hE : ∀ e : ℕ → ℕ, Function.Injective e →
      (Q : Measure (SpectralArray (m + 1))).map (permuteSpectralArray e) = Q)
    (hP : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x)
    (hn : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ a, 0 ≤ (x (0,1) a : ℝ))
    (ρ eig : Fin m → ℝ) (a b : Fin m)
    (hward : ∀ Φ : ℝ → ℝ, Continuous Φ → ∀ C : ℝ, 0 ≤ C → (∀ r, |Φ r| ≤ C) →
      spectralOffWardResidual Q ρ eig a b Φ = 0) :
    ∃ f g : ℝ → ℝ, LipschitzWith 1 f ∧ LipschitzWith 1 g ∧
      (∀ r, f r ∈ Icc (0 : ℝ) 1) ∧ (∀ r, g r ∈ Icc (0 : ℝ) 1) ∧
      (∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ i j, i ≠ j →
        (x (i,j) a.castSucc : ℝ) = f (spectralSpinArray x i j)) ∧
      (∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ i j, i ≠ j →
        (x (i,j) b.castSucc : ℝ) = g (spectralSpinArray x i j)) ∧
      (∀ᵐ s ∂pathMeasure, offWardPath (ρ a) (ρ b) (eig a - eig b) (q a.castSucc) (q b.castSucc)
        (fun u => f (spectralSpinQuantilePath Q hP hn u))
        (fun u => g (spectralSpinQuantilePath Q hP hn u)) s = 0) := by
  obtain ⟨f, g, hf, hg, hfb, hgb, hfa, hga, hprod⟩ :=
    spectralPartition_replicaProductPath hgg hG q hq hd hE hP hn a b
  refine ⟨f, g, hf, hg, hfb, hgb, hfa, hga, ?_⟩
  let p := spectralSpinQuantilePath Q hP hn
  have : IsProbabilityMeasure (scalarOverlapLaw (Q : Measure (SpectralArray (m + 1))) spectralSpinArray) := by
    rw [← spectralSpinQuantilePath_law Q hP hn]
    exact (Measure.isProbabilityMeasure_map_iff p.measurable.aemeasurable).mpr inferInstance
  have haf (r : ℝ) : |f r| ≤ 1 := by rw [abs_of_nonneg (hfb r).1]; exact (hfb r).2
  have hag (r : ℝ) : |g r| ≤ 1 := by rw [abs_of_nonneg (hgb r).1]; exact (hgb r).2
  apply ae_offWardPath_zero_of_tests p (scalarOverlapLaw (Q : Measure (SpectralArray (m + 1))) spectralSpinArray)
    (spectralSpinQuantilePath_law Q hP hn) (ρ a) (ρ b) (eig a - eig b)
    (q a.castSucc) (q b.castSucc) f g hf.continuous hg.continuous zero_le_one zero_le_one haf hag
  intro Φ hΦ C hC hΦB
  have hIa : (∫ x, Φ (spectralSpinArray x 0 1) * (x (0,1) a.castSucc : ℝ) ∂(Q : Measure (SpectralArray (m + 1)))) =
      ∫ s, Φ (p s) * f (p s) ∂pathMeasure := by
    calc
      _ = ∫ x, Φ (spectralSpinArray x 0 1) * f (spectralSpinArray x 0 1) ∂(Q : Measure (SpectralArray (m + 1))) := by
        apply integral_congr_ae
        filter_upwards [hfa] with x hx
        rw [hx 0 1 (by omega)]
      _ = _ := spectralSpinQuantile_integral Q hP hn _ (hΦ.measurable.mul hf.continuous.measurable)
  have hIb : (∫ x, Φ (spectralSpinArray x 0 1) * (x (0,1) b.castSucc : ℝ) ∂(Q : Measure (SpectralArray (m + 1)))) =
      ∫ s, Φ (p s) * g (p s) ∂pathMeasure := by
    calc
      _ = ∫ x, Φ (spectralSpinArray x 0 1) * g (spectralSpinArray x 0 1) ∂(Q : Measure (SpectralArray (m + 1))) := by
        apply integral_congr_ae
        filter_upwards [hga] with x hx
        rw [hx 0 1 (by omega)]
      _ = _ := spectralSpinQuantile_integral Q hP hn _ (hΦ.measurable.mul hg.continuous.measurable)
  have hIp : (∫ x, Φ (spectralSpinArray x 0 1) *
      ((x (0,0) a.castSucc : ℝ) * (x (0,1) b.castSucc : ℝ) +
        (x (0,1) a.castSucc : ℝ) * (x (1,1) b.castSucc : ℝ) -
        2 * ((x (0,2) a.castSucc : ℝ) * (x (1,2) b.castSucc : ℝ))) ∂(Q : Measure (SpectralArray (m + 1)))) =
      ∫ s, Φ (p s) * replicaProductPath (q a.castSucc) (fun u => f (p u))
        (q b.castSucc) (fun u => g (p u)) s ∂pathMeasure := by
    calc
      _ = ∫ x, Φ (spectralSpinArray x 0 1) *
        (q a.castSucc * (x (0,1) b.castSucc : ℝ) + (x (0,1) a.castSucc : ℝ) * q b.castSucc -
          2 * ((x (0,2) a.castSucc : ℝ) * (x (1,2) b.castSucc : ℝ))) ∂(Q : Measure (SpectralArray (m + 1))) := by
        apply integral_congr_ae
        filter_upwards [hd] with x hx
        rw [hx 0 a.castSucc, hx 1 b.castSucc]
      _ = _ := hprod Φ hΦ.measurable C hC hΦB
  have hw := hward Φ hΦ C hC hΦB
  unfold spectralOffWardResidual at hw
  rw [hIa, hIb, hIp] at hw
  have hfi : Integrable (fun s => f (p s)) pathMeasure :=
    integrable_of_measurable_abs_le (hf.continuous.measurable.comp p.measurable) (fun s => haf (p s))
  have hgi : Integrable (fun s => g (p s)) pathMeasure :=
    integrable_of_measurable_abs_le (hg.continuous.measurable.comp p.measurable) (fun s => hag (p s))
  have hpi : Integrable (replicaProductPath (q a.castSucc) (fun u => f (p u))
      (q b.castSucc) (fun u => g (p u))) pathMeasure := by
    have hi := intervalIntegrable_replicaProductPath (fun u => f (p u)) (fun u => g (p u))
      (hf.continuous.measurable.comp p.measurable) (hg.continuous.measurable.comp p.measurable)
      zero_le_one (fun u => haf (p u)) (fun u => hag (p u)) (q a.castSucc) (q b.castSucc) 0 1
    exact hi.1.mono_set (fun _ hu => ⟨hu.1, hu.2.le⟩)
  have hΦm : AEStronglyMeasurable (fun s => Φ (p s)) pathMeasure :=
    (hΦ.measurable.comp p.measurable).aestronglyMeasurable
  have hΦbound : ∀ᵐ s ∂pathMeasure, ‖Φ (p s)‖ ≤ C :=
    ae_of_all _ fun s => by simpa only [Real.norm_eq_abs] using hΦB (p s)
  have hif := hfi.bdd_mul hΦm hΦbound
  have hig := hgi.bdd_mul hΦm hΦbound
  have hip := hpi.bdd_mul hΦm hΦbound
  have he : (fun s => Φ (p s) * offWardPath (ρ a) (ρ b) (eig a - eig b)
      (q a.castSucc) (q b.castSucc) (fun u => f (p u)) (fun u => g (p u)) s) =
      fun s => ρ a * (Φ (p s) * g (p s)) - ρ b * (Φ (p s) * f (p s)) +
        (eig a - eig b) * (Φ (p s) * replicaProductPath (q a.castSucc) (fun u => f (p u))
          (q b.castSucc) (fun u => g (p u)) s) := by
    funext s
    unfold offWardPath
    ring
  have hsum : (∫ s, ρ a * (Φ (p s) * g (p s)) - ρ b * (Φ (p s) * f (p s)) +
      (eig a - eig b) * (Φ (p s) * replicaProductPath (q a.castSucc) (fun u => f (p u))
        (q b.castSucc) (fun u => g (p u)) s) ∂pathMeasure) =
      (∫ s, ρ a * (Φ (p s) * g (p s)) - ρ b * (Φ (p s) * f (p s)) ∂pathMeasure) +
      ∫ s, (eig a - eig b) * (Φ (p s) * replicaProductPath (q a.castSucc) (fun u => f (p u))
        (q b.castSucc) (fun u => g (p u)) s) ∂pathMeasure :=
    integral_add ((hig.const_mul (ρ a)).sub (hif.const_mul (ρ b))) (hip.const_mul (eig a - eig b))
  rw [he, hsum, integral_sub (hig.const_mul (ρ a)) (hif.const_mul (ρ b))]
  simp only [integral_const_mul]
  exact hw

end InvariantIsing

end

end OAI
