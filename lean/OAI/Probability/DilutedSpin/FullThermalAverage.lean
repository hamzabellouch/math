import OAI.Probability.DilutedSpin.FullSelectedThermal
import OAI.Probability.DilutedSpin.TripleMarginal

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}

 
theorem full_selected_thermal_average
    (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν] (r s : ℝ≥0)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    {t a b c : ℝ} (ht : |t| ≤ 1/4) (hab : a < b) (hc : 0 < c)
    (hm : ∀ j, c ≤ m j) (hI : Icc a b ⊆ Icc (-(1:ℝ)/4) (1/4)) :
    (∫ u in a..b, ∫ z, fullSelectedThermal T Q m base sel fixed D E t z u
      ∂fullRootLaw ξ μ ν r s)^2 ≤ (b-a)*(4+4*(b-a))/c*(s:ℝ) := by
  let F := fullSelectedThermal T Q m base sel fixed D E t
  let P := fullRootLaw ξ μ ν r s
  let J := volume.restrict (Ioc a b)
  have hFm : Measurable (fun z : FullRootState Y X I M × ℝ => F z.1 z.2) :=
    measurable_fullSelectedThermal T Q m base sel fixed D E t hb
  have hdom : Integrable (fun z : FullRootState Y X I M => 4*(z.2.2.1:ℝ)) P :=
    ((fullRoot_count_memLp ξ μ ν r s).integrable (by norm_num)).const_mul 4
  have hprod : Integrable (fun z : FullRootState Y X I M × ℝ => F z.1 z.2) (P.prod J) := by
    apply (hdom.comp_fst J).mono' hFm.aestronglyMeasurable
    filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := P) (ν := J)).ae (ae_restrict_mem measurableSet_Ioc)] with z hz
    rw [Real.norm_eq_abs,abs_of_nonneg (fullSelectedThermal_nonneg T Q m base sel fixed D E t z.1 z.2)]
    exact fullSelectedThermal_bound T Q m base sel fixed D E t hD hE ht
      (abs_le.mpr ⟨by linarith [(hI ⟨hz.1.le,hz.2⟩).1],(hI ⟨hz.1.le,hz.2⟩).2⟩) z.1
  have hswap : (∫ u in a..b, ∫ z, F z u ∂P) = ∫ z, (∫ u in a..b, F z u) ∂P := by
    apply intervalIntegral_integral_swap
    rw [uIoc_of_le hab.le]
    change Integrable (fun z : ℝ × FullRootState Y X I M => F z.2 z.1) (J.prod P)
    exact hprod.swap
  rw [show (∫ u in a..b, ∫ z, fullSelectedThermal T Q m base sel fixed D E t z u
    ∂fullRootLaw ξ μ ν r s) = _ from hswap]
  apply fullRoot_average_sq ξ μ ν r s
  · simp_rw [intervalIntegral.integral_of_le hab.le]
    exact hFm.stronglyMeasurable.integral_prod_right'.measurable
  · intro z
    exact fullSelectedThermal_integral_sq T Q m base sel fixed D E t hD hE ht hab hc hm hI z

end DilutedSpinGlass.HeterogeneousMarks
end

end

section
section
namespace DilutedSpinGlass.KernelTower
variable {Ω : Type} [Fintype Ω] {N : ℕ}

/-- The squared spatial covariance density under the conditional continuation
law after a prefix of length d. This version allows the fixed physical height. -/
noncomputable def prefixEnergyAt : (n : ℕ) → KernelTower Ω n → ℕ →
    (FinitePath Ω n → Fin N → ℝ) → ℝ
  | 0, T, _, X => (law 0 T).covarianceEnergy X
  | n+1, T, 0, X => (law (n+1) T).covarianceEnergy X
  | n+1, T, d+1, X => T.1.expect (fun z => prefixEnergyAt n (T.2 z) d (fun y => X (z,y)))

lemma prefixEnergyAt_nonneg (n : ℕ) (T : KernelTower Ω n) (d : ℕ)
    (X : FinitePath Ω n → Fin N → ℝ) : 0 ≤ prefixEnergyAt n T d X := by
  induction n generalizing d with
  | zero => unfold prefixEnergyAt FiniteLaw.covarianceEnergy; positivity
  | succ n ih =>
    cases d with
    | zero => unfold prefixEnergyAt FiniteLaw.covarianceEnergy; positivity
    | succ d => exact T.1.expect_nonneg (fun z => ih (T.2 z) d (fun y => X (z,y)))

lemma prefixEnergyAt_eq (h d : ℕ) (T : KernelTower Ω (h+1+d))
    (X : FinitePath Ω (h+1+d) → Fin N → ℝ) :
    prefixEnergyAt (h+1+d) T d X = prefixCovarianceEnergy h d T X := by
  induction d with
  | zero => rfl
  | succ d ih => exact T.1.expect_congr (fun z => ih (T.2 z) (fun y => X (z,y)))

lemma prefix_three_copy_bound_at (n : ℕ) (T : KernelTower Ω n) (d : ℕ) (hd : d < n)
    (X : FinitePath Ω n → Fin N → ℝ) :
    2*prefixEnergyAt n T d X ≤ tripleExpectAt n T d
      (fun x y z => (FiniteLaw.dot (X x) (X y)-FiniteLaw.dot (X x) (X z))^2) := by
  induction n generalizing d with
  | zero => omega
  | succ n ih =>
    cases d with
    | zero =>
      change 2*(law (n+1) T).covarianceEnergy X ≤ _
      have he : 2*(law (n+1) T).covarianceEnergy X =
          (2/(N:ℝ)^2)*(∑ i, ∑ j, (law (n+1) T).covariance (fun x => X x i) (fun x => X x j)^2) := by
        unfold FiniteLaw.covarianceEnergy
        ring
      rw [he]
      exact (law (n+1) T).three_copy_bound X
    | succ d =>
      change 2*T.1.expect _ ≤ T.1.expect _
      rw [← FiniteLaw.expect_mul_left]
      exact T.1.expect_mono (fun z => ih (T.2 z) d (by omega) (fun y => X (z,y)))

end DilutedSpinGlass.KernelTower
end

end

end OAI
