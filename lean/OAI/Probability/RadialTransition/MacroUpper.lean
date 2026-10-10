import OAI.Probability.RadialTransition.InteriorGrid

namespace OAI

universe uI uX uY

noncomputable section


open Function MeasureTheory Set Filter

open scoped BigOperators ENNReal NNReal ContDiff

namespace RadialTransition
section
variable {I : Type uI} [Fintype I] [DecidableEq I] {X : I → Type uX}

lemma pairWithin_nonneg {Y : Type uY} (v : Y → Y → ℝ) (hv : ∀ x y, 0 ≤ v x y) (s : ParticleState Y) :
    0 ≤ pairWithin v s := by
  unfold pairWithin
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => by split_ifs <;> simp_all)))

lemma pairCellEnergy_upper (v : ∀ i j, X i → X j → ℝ) (K : I → I → ℝ) (M : ℝ)
    (hK : ∀ i j, 0 ≤ K i j) (hKs : ∀ i j, K i j = K j i)
    (hrow : ∀ i, ∑ j, K i j ≤ M)
    (hv : ∀ i j x y, |v i j x y| ≤ K i j) (x : ∀ i, ParticleState (X i)) :
    pairCellEnergy v x ≤ M/2*∑ i, (particleCount (x i):ℝ)^2 := by
  have hh := (le_abs_self (pairCellEnergy v x)).trans (pairCellEnergy_abs_bound v K hK hv x)
  dsimp only [cellN] at hh
  have hr := symmetric_row_quadratic K (fun i => (particleCount (x i):ℝ)) M hK hKs hrow
  linarith

lemma pairCellEnergy_lower_cross (v : ∀ i j, X i → X j → ℝ) (K : I → I → ℝ)
    (hn : ∀ i a b, 0 ≤ v i i a b) (hv : ∀ i j a b, K i j ≤ v i j a b)
    (x : ∀ i, ParticleState (X i)) :
    (1/2:ℝ)*∑ i, ∑ j, (if i = j then 0 else K i j*(particleCount (x i):ℝ)*(particleCount (x j):ℝ)) ≤
      pairCellEnergy v x := by
  have hc := Finset.sum_le_sum (s := Finset.univ) (fun (i:I) _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun (j:I) _ => show
      (if i = j then 0 else K i j*(particleCount (x i):ℝ)*(particleCount (x j):ℝ)) ≤
      (if i = j then 0 else pairBetween (v i j) (x i) (x j)) from by
        split_ifs
        · rfl
        · simpa only [neg_neg] using pairBetween_lower (v i j) (J := -K i j) (fun a b => by simpa using hv i j a b) (x i) (x j)))
  have hd : 0 ≤ ∑ i, pairWithin (v i i) (x i) :=
    Finset.sum_nonneg (fun i _ => pairWithin_nonneg _ (hn i) _)
  unfold pairCellEnergy cellHamiltonian
  linarith

lemma pairCellEnergy_smul (a : ℝ) (v : ∀ i j, X i → X j → ℝ) (x : ∀ i, ParticleState (X i)) :
    pairCellEnergy (fun i j x y => a*v i j x y) x = a*pairCellEnergy v x := by
  unfold pairCellEnergy cellHamiltonian pairWithin pairBetween
  have hh (i : I) (k l : Fin (x i).1) :
    (if k = l then (0:ℝ) else a*v i i ((x i).2 k) ((x i).2 l)) =
      a*(if k = l then 0 else v i i ((x i).2 k) ((x i).2 l)) := by split_ifs <;> simp
  simp_rw [hh, ← Finset.mul_sum]
  have hj (i j:I) : (if i = j then (0:ℝ) else a*∑ k, ∑ l, v i j ((x i).2 k) ((x j).2 l)) =
      a*(if i = j then 0 else ∑ k, ∑ l, v i j ((x i).2 k) ((x j).2 l)) := by split_ifs <;> simp
  simp_rw [hj, ← Finset.mul_sum]
  ring

end

lemma macro_attraction_upper {q m : ℕ} (hq : 0 < q) {R : ℝ} (hR : (q:ℝ)/4 ≤ R)
    (x : ∀ i : GridIndex m, ParticleState (macroRegion q (gridEmbed i))) :
    pairCellEnergy (fun i j (y : macroRegion q (gridEmbed i)) (z : macroRegion q (gridEmbed j)) => scaledBump R ((y:Position)-(z:Position))) x ≤
    (1+10000*(bumpLip:ℝ)*q/R)/(2*((q:ℝ)/4)^3)*∑ i, (particleCount (x i):ℝ)^2 := by
  have hq0 : (0:ℝ) < q := by exact_mod_cast hq
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hR
  have he : (1+10000*(bumpLip:ℝ)*q/R)/(2*((q:ℝ)/4)^3) =
      ((1+10000*(bumpLip:ℝ)*q/R)/((q:ℝ)/4)^3)/2 := by ring
  rw [he]
  apply pairCellEnergy_upper _ (fun i j => macroKernelUpper q R (gridEmbed i) (gridEmbed j))
  · exact fun _ _ => macroKernelUpper_nonneg hR0 _ _
  · exact fun _ _ => macroKernelUpper_symm _ _ _ _
  · intro i
    apply (le_div_iff₀ (by positivity : 0 < ((q:ℝ)/4)^3)).mpr
    rw [mul_comm]
    exact macroKernelUpper_row hq hR _
  · intro i j y z
    rw [abs_of_nonneg (scaledBump_nonneg hR0 _)]
    exact (macroKernel_pair_bounds hq hR0 y.property z.property).2

end RadialTransition

end

end OAI
