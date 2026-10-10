import OAI.Probability.RadialTransition.MacroUpper

namespace OAI

noncomputable section


open Function MeasureTheory Set Filter

open scoped ContDiff BigOperators ENNReal NNReal

namespace RadialTransition

def kernelInterior (m q : ℕ) (R : ℝ) : Finset (GridIndex m) :=
  Finset.univ \ boundaryGrid m (cellMargin (R/q+1)).toNat

lemma macroKernelLower_total {q m : ℕ} (hq : 0 < q) {R : ℝ} (hR : (q:ℝ)/4 ≤ R) :
    (kernelInterior m q R).card*(1-kernelRowError q R)/((q:ℝ)/4)^3 ≤
      ∑ i : GridIndex m, ∑ j : GridIndex m, if i = j then 0 else macroKernelLower q R (gridEmbed i) (gridEmbed j) := by
  classical
  have hq0 : (0:ℝ) < q := by exact_mod_cast hq
  let row (i : GridIndex m) := ∑ j : GridIndex m, if i = j then 0 else macroKernelLower q R (gridEmbed i) (gridEmbed j)
  calc
    _ = ∑ i ∈ kernelInterior m q R, (1-kernelRowError q R)/((q:ℝ)/4)^3 := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ ∑ i ∈ kernelInterior m q R, row i := by
      apply Finset.sum_le_sum
      intro i hi
      apply (div_le_iff₀ (by positivity : 0 < ((q:ℝ)/4)^3)).mpr
      rw [mul_comm]
      exact macroKernelLower_row hq hR i (Finset.mem_sdiff.mp hi).2
    _ ≤ ∑ i, row i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro i hi hnot
      exact Finset.sum_nonneg (fun j _ => by split_ifs; rfl; exact macroKernelLower_nonneg _ _ _ _)

lemma macro_attraction_lower {q m n : ℕ} (hq : 0 < q) {R : ℝ} (hR : (q:ℝ)/4 ≤ R)
    (x : ∀ i : GridIndex m, ParticleState (macroRegion q (gridEmbed i))) (hx : ∀ i, particleCount (x i) = n) :
    (kernelInterior m q R).card*(1-kernelRowError q R)*(n:ℝ)^2/(2*((q:ℝ)/4)^3) ≤
      pairCellEnergy (fun i j (y : macroRegion q (gridEmbed i)) (z : macroRegion q (gridEmbed j)) => scaledBump R ((y:Position)-(z:Position))) x := by
  classical
  have hq0 : (0:ℝ) < q := by exact_mod_cast hq
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hR
  have hh := pairCellEnergy_lower_cross
    (fun i j (y : macroRegion q (gridEmbed i)) (z : macroRegion q (gridEmbed j)) => scaledBump R ((y:Position)-(z:Position)))
    (fun i j => macroKernelLower q R (gridEmbed i) (gridEmbed j))
    (fun i a b => scaledBump_nonneg hR0 _) (fun i j a b => (macroKernel_pair_bounds hq hR0 a.property b.property).1) x
  simp only [hx] at hh
  have he (i j : GridIndex m) : (if i = j then (0:ℝ) else macroKernelLower q R (gridEmbed i) (gridEmbed j)*(n:ℝ)*n) =
      (n:ℝ)^2*(if i = j then 0 else macroKernelLower q R (gridEmbed i) (gridEmbed j)) := by split_ifs <;> ring
  simp_rw [he, ← Finset.mul_sum] at hh
  have ht := mul_le_mul_of_nonneg_left (macroKernelLower_total (m := m) hq hR) (sq_nonneg (n:ℝ))
  calc
    _ = (1/2:ℝ)*((n:ℝ)^2*((kernelInterior m q R).card*(1-kernelRowError q R)/((q:ℝ)/4)^3)) := by ring
    _ ≤ _ := by linarith

abbrev MacroState (m q : ℕ) := ∀ i : GridIndex m, ParticleState (macroRegion q (gridEmbed i))

def macroKacEnergy (φ : Potential) (m q : ℕ) (R lam : ℝ) (x : MacroState m q) : ℝ :=
  (∑ i, pairWithin (fun (y z : macroRegion q (gridEmbed i)) => radialPair φ y z) (x i)) -
    lam*pairCellEnergy (fun i j (y : macroRegion q (gridEmbed i)) (z : macroRegion q (gridEmbed j)) => scaledBump R ((y:Position)-(z:Position))) x

lemma measurable_macroKacEnergy {φ : Potential} (hφ : Continuous φ) (m q : ℕ) (R lam : ℝ) :
    Measurable (macroKacEnergy φ m q R lam) := by
  apply Measurable.sub
  · apply Finset.measurable_sum
    intro i hi
    exact (measurable_pairWithin _ (continuous_radialPair_comp hφ continuous_subtype_val continuous_subtype_val).measurable).comp (measurable_pi_apply i)
  · apply measurable_const.mul
    apply measurable_pairCellEnergy
    intro i j
    exact ((continuous_scaledBump R).comp ((continuous_subtype_val.comp continuous_fst).sub (continuous_subtype_val.comp continuous_snd))).measurable

lemma macroKacEnergy_lower {φ : Potential} {q m : ℕ} (hq : 0 < q) {R lam : ℝ}
    (hR : (q:ℝ)/4 ≤ R) (hlam : 0 ≤ lam) (x : MacroState m q) :
    (∑ i : GridIndex m, (pairWithin (fun (y z : macroRegion q (gridEmbed i)) => radialPair φ y z) (x i) -
      lam*(1+10000*(bumpLip:ℝ)*q/R)/(2*((q:ℝ)/4)^3)*(particleCount (x i):ℝ)^2)) ≤
      macroKacEnergy φ m q R lam x := by
  have hh := mul_le_mul_of_nonneg_left (macro_attraction_upper hq hR x) hlam
  unfold macroKacEnergy
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simpa only [mul_div_assoc, mul_assoc] using sub_le_sub_left hh (∑ i : GridIndex m, pairWithin (fun (y z : macroRegion q (gridEmbed i)) => radialPair φ y z) (x i))

end RadialTransition

end

end OAI
