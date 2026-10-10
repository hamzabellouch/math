import OAI.Probability.FreeIsing.Ising.GaussianPosterior
import OAI.Probability.FreeIsing.Spins.Flip

namespace OAI

noncomputable section

namespace Problem367

private lemma spinSign_global_flip (s : IsingSpin) :
    spinSign s.flip = -spinSign s := by
  cases s <;> norm_num [IsingSpin.flip, spinSign]

theorem finiteIsingEnergy_flipConfig {d : ℕ} (beta : ℝ)
    (D : Finset (TreeVertex d)) (eta : D → IsingSpin) :
    finiteIsingEnergy beta D (flipConfig eta) = finiteIsingEnergy beta D eta := by
  classical
  unfold finiteIsingEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro e he
  have hm := Finset.mem_product.mp (Finset.mem_filter.mp he).1
  have hsign (v : TreeVertex d) (hv : v ∈ D) :
      spinSign (extendFiniteSpin D (flipConfig eta) v) =
        -spinSign (extendFiniteSpin D eta v) := by
    simp only [extendFiniteSpin, dite_eq_left hv, flipConfig_apply, spinSign_global_flip]
  rw [hsign e.1 hm.1, hsign e.2 hm.2, neg_mul_neg]

theorem finiteIsingPosterior_zero_of_odd {d : ℕ} (beta : ℝ)
    (D : Finset (TreeVertex d)) (q : (D → IsingSpin) → ℝ)
    (hq : ∀ eta, q (flipConfig eta) = -q eta) :
    FinitePosterior.fieldMean (finiteIsingEnergy beta D)
      (fun (eta : D → IsingSpin) v => spinSign (eta v)) q (fun _ => 0) = 0 := by
  classical
  have hsum := (flipConfigMeasurableEquiv D).toEquiv.sum_comp
    (fun eta : D → IsingSpin => q eta * Real.exp (finiteIsingEnergy beta D eta))
  change (∑ eta : D → IsingSpin, q (flipConfig eta) *
    Real.exp (finiteIsingEnergy beta D (flipConfig eta))) =
      ∑ eta : D → IsingSpin, q eta * Real.exp (finiteIsingEnergy beta D eta) at hsum
  simp only [hq, finiteIsingEnergy_flipConfig, neg_mul, Finset.sum_neg_distrib] at hsum
  have hzero : (∑ eta : D → IsingSpin,
      q eta * Real.exp (finiteIsingEnergy beta D eta)) = 0 := by linarith
  simp only [FinitePosterior.fieldMean, FinitePosterior.fieldEnergy,
    zero_mul, Finset.sum_const_zero, add_zero, hzero, zero_div]

theorem finiteIsingPosterior_spin_zero {d : ℕ} (beta : ℝ)
    (D : Finset (TreeVertex d)) (v : D) :
    FinitePosterior.fieldMean (finiteIsingEnergy beta D)
      (fun (eta : D → IsingSpin) w => spinSign (eta w))
      (fun eta => spinSign (eta v)) (fun _ => 0) = 0 := by
  apply finiteIsingPosterior_zero_of_odd
  intro eta
  exact spinSign_global_flip (eta v)

end Problem367

end

end OAI
