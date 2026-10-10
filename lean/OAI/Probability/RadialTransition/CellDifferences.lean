import OAI.Probability.RadialTransition.CroppedCells

namespace OAI

universe uX uY uI

noncomputable section


open Function MeasureTheory Set Filter

open scoped ContDiff NNReal BigOperators ENNReal

namespace RadialTransition

lemma if_zero_sub (p : Prop) [Decidable p] (a b : ℝ) :
    (if p then 0 else a-b) = (if p then 0 else a) - (if p then 0 else b) := by
  split_ifs <;> simp

lemma pairWithin_sub {X : Type uX} (v w : X → X → ℝ) (s : ParticleState X) :
    pairWithin (fun x y => v x y-w x y) s = pairWithin v s - pairWithin w s := by
  classical
  unfold pairWithin
  simp_rw [if_zero_sub]
  simp_rw [Finset.sum_sub_distrib]
  ring

lemma pairBetween_sub {X : Type uX} {Y : Type uY} (v w : X → Y → ℝ) (s : ParticleState X) (t : ParticleState Y) :
    pairBetween (fun x y => v x y-w x y) s t = pairBetween v s t - pairBetween w s t := by
  unfold pairBetween
  simp_rw [Finset.sum_sub_distrib]

lemma pairWithin_abs_bound {X : Type uX} (v : X → X → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hv : ∀ x y, |v x y| ≤ K) (s : ParticleState X) :
    |pairWithin v s| ≤ (1/2:ℝ) * (K * particleCount s * particleCount s) := by
  classical
  unfold pairWithin
  rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    |∑ i : Fin s.1, ∑ j : Fin s.1, if i = j then 0 else v (s.2 i) (s.2 j)| ≤
        ∑ i : Fin s.1, ∑ j : Fin s.1, |if i = j then 0 else v (s.2 i) (s.2 j)| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ i : Fin s.1, ∑ j : Fin s.1, K := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      split_ifs
      · simpa only [abs_zero] using hK
      · exact hv _ _
    _ = _ := by simp [particleCount]; ring

lemma pairBetween_abs_bound {X : Type uX} {Y : Type uY} (v : X → Y → ℝ) {K : ℝ}
    (hv : ∀ x y, |v x y| ≤ K) (s : ParticleState X) (t : ParticleState Y) :
    |pairBetween v s t| ≤ K * particleCount s * particleCount t := by
  unfold pairBetween
  calc
    |∑ i : Fin s.1, ∑ j : Fin t.1, v (s.2 i) (t.2 j)| ≤
        ∑ i : Fin s.1, ∑ j : Fin t.1, |v (s.2 i) (t.2 j)| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ i : Fin s.1, ∑ j : Fin t.1, K :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hv _ _))
    _ = _ := by simp [particleCount]; ring

lemma double_sum_diagonal {I : Type uI} [Fintype I] [DecidableEq I] (a : I → I → ℝ) :
    (∑ i, ∑ j, a i j) = ∑ i, a i i + ∑ i, ∑ j, if i = j then 0 else a i j := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  conv_lhs =>
    arg 2; ext j
    rw [show a i j = (if i = j then a i j else 0) + (if i = j then 0 else a i j) by split_ifs <;> simp]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

section CellDifferences
variable {I : Type uI} [Fintype I] [DecidableEq I] {X : I → Type uX}

lemma pairCellEnergy_sub (v w : ∀ i j, X i → X j → ℝ) (x : ∀ i, ParticleState (X i)) :
    pairCellEnergy (fun i j a b => v i j a b-w i j a b) x = pairCellEnergy v x-pairCellEnergy w x := by
  unfold pairCellEnergy cellHamiltonian
  simp_rw [pairWithin_sub, pairBetween_sub, if_zero_sub, Finset.sum_sub_distrib]
  ring

lemma pairCellEnergy_abs_bound (v : ∀ i j, X i → X j → ℝ) (K : I → I → ℝ)
    (hK : ∀ i j, 0 ≤ K i j) (hv : ∀ i j a b, |v i j a b| ≤ K i j)
    (x : ∀ i, ParticleState (X i)) :
    |pairCellEnergy v x| ≤ (1/2:ℝ) * ∑ i, ∑ j, K i j * cellN i x * cellN j x := by
  let a i j := K i j * cellN i x * cellN j x
  have hi : (∑ i, |pairWithin (v i i) (x i)|) ≤ (1/2:ℝ) * ∑ i, a i i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => pairWithin_abs_bound _ (hK i i) (hv i i) (x i))
  have hc : (∑ i, ∑ j, |if i = j then 0 else pairBetween (v i j) (x i) (x j)|) ≤
      ∑ i, ∑ j, if i = j then 0 else a i j := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    split_ifs
    · simp
    · exact pairBetween_abs_bound _ (hv i j) _ _
  unfold pairCellEnergy cellHamiltonian
  calc
    _ ≤ |∑ i, pairWithin (v i i) (x i)| +
        |(1/2:ℝ) * ∑ i, ∑ j, if i = j then 0 else pairBetween (v i j) (x i) (x j)| := abs_add_le _ _
    _ ≤ (∑ i, |pairWithin (v i i) (x i)|) + (1/2:ℝ) *
        ∑ i, ∑ j, |if i = j then 0 else pairBetween (v i j) (x i) (x j)| := by
      rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
      apply add_le_add (Finset.abs_sum_le_sum_abs _ _)
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ (1/2:ℝ) * ∑ i, a i i + (1/2:ℝ) * ∑ i, ∑ j, if i = j then 0 else a i j :=
      add_le_add hi (mul_le_mul_of_nonneg_left hc (by norm_num))
    _ = _ := by rw [← mul_add, ← double_sum_diagonal]

lemma pairCellEnergy_abs_difference (v w : ∀ i j, X i → X j → ℝ) (K : I → I → ℝ)
    (hK : ∀ i j, 0 ≤ K i j) (hv : ∀ i j a b, |v i j a b-w i j a b| ≤ K i j)
    (x : ∀ i, ParticleState (X i)) :
    |pairCellEnergy v x-pairCellEnergy w x| ≤ (1/2:ℝ) * ∑ i, ∑ j, K i j * cellN i x * cellN j x := by
  rw [← pairCellEnergy_sub]
  exact pairCellEnergy_abs_bound _ K hK hv x

end CellDifferences
section PhysicalControl
variable {I : Type uI} [Fintype I] [DecidableEq I] {X : I → Type uX}

lemma pairCell_quadratic_bound
    (pos : ∀ i, X i → Position) (hdiam : ∀ i x y, dist (pos i x) (pos i y) ≤ 1)
    {t : ℝ} (ht : 0 ≤ t) (v : ∀ i j, X i → X j → ℝ)
    (J : I → I → ℝ) (hJ : ∀ i j, 0 ≤ J i j) (hJsym : ∀ i j, J i j = J j i)
    (hrow : ∀ i, ∑ j, J i j ≤ t^2/8)
    (hintra : ∀ i x y, corePotential t (nndist (pos i x) (pos i y)) - J i i ≤ v i i x y)
    (hcross : ∀ i j x y, -J i j ≤ v i j x y) (x : ∀ i, ParticleState (X i)) :
    (t^2/8)/2 * ∑ i, (cellN i x)^2 - (t^2/2) * ∑ i, cellN i x ≤ pairCellEnergy v x := by
  apply cellHamiltonian_stable (fun i => pairWithin (v i i)) (fun i j => pairBetween (v i j))
    (fun _ s => particleCount s) (fun _ _ => Nat.cast_nonneg _) J hJ hJsym (by positivity) hrow
  · intro i s
    exact pairWithin_core ht (hJ i i) (pos i) (hdiam i) (v i i) (hintra i) s
  · intro i j s r
    exact pairBetween_lower (v i j) (hcross i j) s r

variable [∀ i, TopologicalSpace (X i)] [∀ i, MeasurableSpace (X i)]
    [∀ i, BorelSpace (X i)] [∀ i, SecondCountableTopology (X i)]

omit [DecidableEq I] in
lemma cell_boltzmann_integrable (ν : ∀ i, Measure (X i)) [∀ i, IsFiniteMeasure (ν i)]
    (z : ℝ) {D B : ℝ} (hD : 0 ≤ D) {E : (∀ i, ParticleState (X i)) → ℝ}
    (hE : Measurable E)
    (hstable : ∀ x, D/2 * ∑ i, (cellN i x)^2 - B * ∑ i, cellN i x ≤ E x) :
    Integrable (fun x => Real.exp (-E x)) (Measure.pi (fun i => particleBase (ν i) z)) := by
  simpa only [zero_sub] using integrable_cell_numerator ν z hE measurable_const hstable
    (f := fun _ => 0) (fun x => mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

omit [DecidableEq I] in
lemma cell_exponential_integrable (ν : ∀ i, Measure (X i)) [∀ i, IsFiniteMeasure (ν i)]
    (z : ℝ) {D B : ℝ} (hD : 0 ≤ D) {E : (∀ i, ParticleState (X i)) → ℝ}
    (hE : Measurable E)
    (hstable : ∀ x, D/2 * ∑ i, (cellN i x)^2 - B * ∑ i, cellN i x ≤ E x) (i : I) :
    Integrable (fun x => Real.exp (D/4*(cellN i x)^2))
      (boltzmannMeasure (Measure.pi (fun j => particleBase (ν j) z)) E) := by
  have hp := cell_partition_pos ν z (cell_boltzmann_integrable ν z hD hE hstable)
  apply integrable_boltzmann hE _ hp
  have hbound (x : ∀ j, ParticleState (X j)) : D/4*(cellN i x)^2 ≤ D/2*∑ j, (cellN j x)^2 := by
    have hh := Finset.single_le_sum (s := Finset.univ) (f := fun j => (cellN j x)^2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
    nlinarith [mul_nonneg hD (sq_nonneg (cellN i x)), mul_le_mul_of_nonneg_left hh hD]
  have hi := integrable_cell_numerator ν z hE (measurable_const.mul ((measurable_cellN i).pow_const 2))
    hstable hbound
  convert hi using 1
  ext x
  rw [← Real.exp_add]
  congr 1
  dsimp only [Pi.mul_apply]
  ring

lemma pairCell_second_moment [Nonempty I]
    (ν : ∀ i, Measure (X i)) [∀ i, IsFiniteMeasure (ν i)]
    (pos : ∀ i, X i → Position) (hdiam : ∀ i x y, dist (pos i x) (pos i y) ≤ 1)
    {t β V z : ℝ} (ht : 0 < t) (hβ : 0 < β) (hV : 0 ≤ V)
    (hvol : ∀ i, (ν i univ).toReal ≤ V)
    (v : ∀ i j, X i → X j → ℝ) (hv : ∀ i j, Continuous (Function.uncurry (v i j)))
    (hvsym : ∀ i j x y, v i j x y = v j i y x)
    (J : I → I → ℝ) (hJ : ∀ i j, 0 ≤ J i j) (hJsym : ∀ i j, J i j = J j i)
    (hrow : ∀ i, ∑ j, J i j ≤ (t^2/8)/8)
    (hintra : ∀ i x y, corePotential t (nndist (pos i x) (pos i y)) - J i i ≤ v i i x y)
    (hcross : ∀ i j x y, -J i j ≤ v i j x y) :
    let μ := Measure.pi (fun j => particleBase (ν j) z)
    let E := fun x => β * pairCellEnergy v x
    Integrable (fun x => Real.exp (-E x)) μ ∧ 0 < boltzmannPartition μ E ∧
    ∀ i, Integrable (fun x => (cellN i x)^2) (boltzmannMeasure μ E) ∧
      (∫ x, (cellN i x)^2 ∂boltzmannMeasure μ E) ≤
        Real.exp (16/15 * V * Real.exp (z+β*(t^2/2))) / (β*(t^2/8)/4) := by
  dsimp only
  have hD : 0 < β*(t^2/8) := by positivity
  have hr (i : I) : ∑ j, J i j ≤ t^2/8 := (hrow i).trans (by nlinarith [sq_nonneg t])
  have hE : Measurable (fun x => β * pairCellEnergy v x) :=
    measurable_const.mul (continuous_pairCellEnergy v hv).measurable
  have hstable (x : ∀ i, ParticleState (X i)) :
      (β*(t^2/8))/2 * ∑ i, (cellN i x)^2 - (β*(t^2/2))*∑ i, cellN i x ≤ β*pairCellEnergy v x := by
    have hh := mul_le_mul_of_nonneg_left
      (pairCell_quadratic_bound pos hdiam ht.le v J hJ hJsym hr hintra hcross x) hβ.le
    convert hh using 1; first | rfl | ring
  have hi := cell_boltzmann_integrable ν z hD.le hE hstable
  refine ⟨hi, cell_partition_pos ν z hi, fun i => ?_⟩
  exact secondMoment_of_exponential (measurable_cellN i) (by positivity)
    (cell_exponential_integrable ν z hD.le hE hstable i)
    (pairCell_exponential_moment ν pos hdiam ht hβ hV hvol v hv hvsym J hJ hJsym hrow hintra hcross i)

theorem pairCell_log_perturbation [Nonempty I]
    (ν : ∀ i, Measure (X i)) [∀ i, IsFiniteMeasure (ν i)]
    (pos : ∀ i, X i → Position) (hdiam : ∀ i x y, dist (pos i x) (pos i y) ≤ 1)
    {t β V z : ℝ} (ht : 0 < t) (hβ : 0 < β) (hV : 0 ≤ V)
    (hvol : ∀ i, (ν i univ).toReal ≤ V)
    (v w : ∀ i j, X i → X j → ℝ)
    (hv : ∀ i j, Continuous (Function.uncurry (v i j)))
    (hw : ∀ i j, Continuous (Function.uncurry (w i j)))
    (hvsym : ∀ i j x y, v i j x y = v j i y x)
    (hwsym : ∀ i j x y, w i j x y = w j i y x)
    (J : I → I → ℝ) (hJ : ∀ i j, 0 ≤ J i j) (hJsym : ∀ i j, J i j = J j i)
    (hrow : ∀ i, ∑ j, J i j ≤ (t^2/8)/8)
    (hintrav : ∀ i x y, corePotential t (nndist (pos i x) (pos i y)) - J i i ≤ v i i x y)
    (hcrossv : ∀ i j x y, -J i j ≤ v i j x y)
    (hintraw : ∀ i x y, corePotential t (nndist (pos i x) (pos i y)) - J i i ≤ w i i x y)
    (hcrossw : ∀ i j x y, -J i j ≤ w i j x y)
    (K : I → I → ℝ) (hK : ∀ i j, 0 ≤ K i j)
    (hd : ∀ i j a b, |w i j a b-v i j a b| ≤ K i j) :
    let μ := Measure.pi (fun i => particleBase (ν i) z)
    |Real.log (boltzmannPartition μ (fun x => β*pairCellEnergy v x)) -
      Real.log (boltzmannPartition μ (fun x => β*pairCellEnergy w x))| ≤
      β/2 * (Real.exp (16/15 * V * Real.exp (z+β*(t^2/2))) / (β*(t^2/8)/4)) * ∑ i, ∑ j, K i j := by
  dsimp only
  have hvdata := pairCell_second_moment (z := z) ν pos hdiam ht hβ hV hvol v hv hvsym J hJ hJsym hrow hintrav hcrossv
  have hwdata := pairCell_second_moment (z := z) ν pos hdiam ht hβ hV hvol w hw hwsym J hJ hJsym hrow hintraw hcrossw
  let K' i j := β/2*K i j
  have hd' (x : ∀ i, ParticleState (X i)) :
      |β*pairCellEnergy w x-β*pairCellEnergy v x| ≤ ∑ i, ∑ j, K' i j * cellN i x * cellN j x := by
    rw [← mul_sub, abs_mul, abs_of_pos hβ]
    calc
      _ ≤ β*((1/2:ℝ)*∑ i, ∑ j, K i j*cellN i x*cellN j x) :=
        mul_le_mul_of_nonneg_left (pairCellEnergy_abs_difference w v K hK hd x) hβ.le
      _ = _ := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        dsimp [K']
        ring
  have hh := log_partition_perturbation (E := fun x => β*pairCellEnergy v x) (F := fun x => β*pairCellEnergy w x)
    (measurable_const.mul (continuous_pairCellEnergy v hv).measurable)
    (measurable_const.mul (continuous_pairCellEnergy w hw).measurable)
    hvdata.1 hwdata.1 hvdata.2.1 hwdata.2.1 (cellN (X := X)) measurable_cellN
    K' (fun i j => mul_nonneg (by positivity) (hK i j))
    (fun i => (hvdata.2.2 i).1) (fun i => (hwdata.2.2 i).1)
    (fun i => (hvdata.2.2 i).2) (fun i => (hwdata.2.2 i).2) hd'
  have hs : (∑ i, ∑ j, K' i j) = β/2*(∑ i, ∑ j, K i j) := by
    simp only [K', Finset.mul_sum]
  rw [hs] at hh
  simpa only [Pi.mul_apply, mul_assoc, mul_left_comm, mul_comm] using hh

end PhysicalControl

end RadialTransition

end

end OAI
