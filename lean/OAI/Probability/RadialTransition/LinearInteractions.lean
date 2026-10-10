import OAI.Probability.RadialTransition.BoxPressure

namespace OAI

universe uI uX uY uZ

noncomputable section


open Function MeasureTheory Set Filter

open scoped ContDiff BigOperators ENNReal NNReal

namespace RadialTransition

lemma zero_ite_add (p : Prop) [Decidable p] (a b : ℝ) :
    (if p then 0 else a+b) = (if p then 0 else a)+(if p then 0 else b) := by split_ifs <;> ring

section LinearPair
variable {I : Type uI} [Fintype I] [DecidableEq I] {X : I → Type uX}

lemma pairWithin_add {Y : Type uY} (v w : Y → Y → ℝ) (s : ParticleState Y) :
    pairWithin (fun x y => v x y+w x y) s = pairWithin v s+pairWithin w s := by
  dsimp only [pairWithin]
  simp only [zero_ite_add, Finset.sum_add_distrib, mul_add]

lemma pairBetween_add {Y : Type uY} {Z : Type uZ} (v w : Y → Z → ℝ) (s : ParticleState Y) (t : ParticleState Z) :
    pairBetween (fun x y => v x y+w x y) s t = pairBetween v s t+pairBetween w s t := by
  simp only [pairBetween, Finset.sum_add_distrib]

lemma pairCellEnergy_add (v w : ∀ i j, X i → X j → ℝ) (x : ∀ i, ParticleState (X i)) :
    pairCellEnergy (fun i j a b => v i j a b+w i j a b) x = pairCellEnergy v x+pairCellEnergy w x := by
  dsimp only [pairCellEnergy, cellHamiltonian]
  simp only [pairWithin_add, pairBetween_add, zero_ite_add, Finset.sum_add_distrib, mul_add]
  ring

lemma pairCellEnergy_diagonal (v : ∀ i j, X i → X j → ℝ) (x : ∀ i, ParticleState (X i)) :
    pairCellEnergy (fun i j a b => if i = j then v i j a b else 0) x = ∑ i, pairWithin (v i i) (x i) := by
  unfold pairCellEnergy cellHamiltonian
  simp only [ite_true]
  have hcross (i j : I) : (if i = j then 0 else pairBetween (fun a b => if i = j then v i j a b else 0) (x i) (x j)) = 0 := by
    split_ifs <;> simp only [pairBetween, Finset.sum_const_zero]
  simp only [hcross, Finset.sum_const_zero, mul_zero, add_zero]

end LinearPair

def singleAttraction (R lam : ℝ) : Potential := fun r => -lam*scaledBumpProfile R r

lemma continuous_singleAttraction (R lam : ℝ) : Continuous (singleAttraction R lam) :=
  continuous_const.mul ((continuous_scaledBumpProfile R).comp NNReal.continuous_coe)

lemma radialPair_singleAttraction {R : ℝ} (hR : 0 < R) (lam : ℝ) (x y : Position) :
    radialPair (singleAttraction R lam) x y = -lam*scaledBump R (x-y) := by
  rw [scaledBump_radial hR]
  rfl

lemma deletedPair_macro_energy {φ : Potential} {m q : ℕ} {R : ℝ} (hR : 0 < R) (lam : ℝ) (x : MacroState m q) :
    pairCellEnergy (fun i j : GridIndex m => fun (a : macroRegion q (gridEmbed i)) (b : macroRegion q (gridEmbed j)) =>
      deletedPair (macroOf q) φ (singleAttraction R lam) a b) x = macroKacEnergy φ m q R lam x := by
  classical
  have he : (fun i j : GridIndex m => fun (a : macroRegion q (gridEmbed i)) (b : macroRegion q (gridEmbed j)) =>
      deletedPair (macroOf q) φ (singleAttraction R lam) a b) =
    (fun i j : GridIndex m => fun (a : macroRegion q (gridEmbed i)) (b : macroRegion q (gridEmbed j)) =>
      (if i = j then radialPair φ a b else 0)+(-lam*scaledBump R ((a:Position)-(b:Position)))) := by
    funext i j a b
    have ha : macroOf q (cellOf (a:Position)) = gridEmbed i := a.property
    have hb : macroOf q (cellOf (b:Position)) = gridEmbed j := b.property
    simp only [deletedPair, ha, hb, radialPair_singleAttraction hR, (gridEmbed_injective m).eq_iff]
  rw [he, pairCellEnergy_add, pairCellEnergy_diagonal, pairCellEnergy_smul]
  simp only [macroKacEnergy, neg_mul, sub_eq_add_neg]

lemma deletedPair_macroKac {m q : ℕ} (hq : 0 < q)
    {φ : Potential} (hφ : Continuous φ) {R : ℝ} (hR : 0 < R) (lam β z : ℝ) :
    pairGrand (deletedPair (macroOf q) φ (singleAttraction R lam)) (volume.restrict (halfCube (((m:ℝ)*q)/4))) β z =
    boltzmannPartition (macroMeasure m q z) (fun x => β*macroKacEnergy φ m q R lam x) := by
  let X (i : GridIndex m) := macroRegion q (gridEmbed i)
  let ν (i : GridIndex m) := regionMeasure (X i)
  let : ∀ i, IsFiniteMeasure (ν i) := fun i => regionMeasure_finite (measurableSet_macroRegion _ _)
    (by rw [volume_macroRegion hq]; finiteness)
  have hh := pairGrand_eq_cell (fun i : GridIndex m => ↥(X i)) ν (fun _ => Subtype.val)
    (fun _ => measurable_subtype_coe) (deletedPair (macroOf q) φ (singleAttraction R lam))
    (measurable_deletedPair _ hφ (continuous_singleAttraction R lam)) (deletedPair_symm _ _ _)
    (macroRegion_partition (m := m) hq) β z
  exact hh.trans (congrArg (boltzmannPartition (macroMeasure m q z)) (by
    funext x
    exact congrArg (β*·) (deletedPair_macro_energy hR lam x)))

end RadialTransition

end

end OAI
