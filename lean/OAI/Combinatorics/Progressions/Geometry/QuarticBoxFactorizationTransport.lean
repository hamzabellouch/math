import OAI.Combinatorics.Progressions.Polynomial.QuarticBoxPolynomial

namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem tensorPowerBudget_mono (n : ℕ) {p q : ℝ} (hpq : p ≤ q) :
    tensorPowerBudget n p ≤ tensorPowerBudget n q := by
  unfold tensorPowerBudget
  exact mul_le_mul_of_nonneg_left (by linarith : p + 1 ≤ q + 1) (by positivity)

theorem NativeMultidegreeNilcharacter.tensorPower_mono {σ : Type*} [Fintype σ]
    {bound : σ → ℕ} {p q : ℝ} (W : NativeMultidegreeNilcharacter bound p) (hpq : p ≤ q) (n : ℕ) :
    (W.mono hpq).tensorPower n = (W.tensorPower n).mono (tensorPowerBudget_mono n hpq) := by
  rfl

noncomputable def NativeQuarticBoxFactorization.mono {p p' q q' : ℝ} {N : ℕ} [NeZero N]
    {W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p}
    (R : NativeQuarticBoxFactorization W N q) (hp : p ≤ p') (hq : q ≤ q') :
    NativeQuarticBoxFactorization (W.mono hp) N q' := by
  letI := R.topology
  letI := R.topologicalAdd
  letI := R.continuousSMul
  letI := R.hausdorff
  letI : TopologicalSpace (ℝ ⊗[ℚ] (QuarticBoxFactor → (W.mono hp).L)) := R.topology
  letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] (QuarticBoxFactor → (W.mono hp).L)) := R.topologicalAdd
  letI : ContinuousSMul ℝ (ℝ ⊗[ℚ] (QuarticBoxFactor → (W.mono hp).L)) := R.continuousSMul
  letI : T2Space (ℝ ⊗[ℚ] (QuarticBoxFactor → (W.mono hp).L)) := R.hausdorff
  have hfactor := NilpotentLieFiltration.ControlledSymbolFactorization.mono
    (pi (fun _ : QuarticBoxFactor => W.model)).filtration R.basis R.weight R.adapted R.factorization hq
    (fun _ => by exact_mod_cast NeZero.pos N)
  have hsymbol :
      ((W.mono hp).quarticAntisymmetricBoxNiltest (R.nonnegative.trans hp) R.leftIndex R.rightIndex).symbol
        R.basis R.weight R.adapted =
      (W.quarticAntisymmetricBoxNiltest R.nonnegative R.leftIndex R.rightIndex).symbol
        R.basis R.weight R.adapted := by
    rw [(W.mono hp).quarticAntisymmetricBoxNiltest_symbol
      (R.nonnegative.trans hp) R.leftIndex R.rightIndex R.basis R.weight R.adapted]
    rw [W.quarticAntisymmetricBoxNiltest_symbol
      R.nonnegative R.leftIndex R.rightIndex R.basis R.weight R.adapted]
    have hhom :
        (pi (fun _ : QuarticBoxFactor => (W.mono hp).model)).filtration.realPolynomialSymbolHom
          R.basis R.weight R.adapted (fun _ : QuarticBoxIndex => 1) =
        (pi (fun _ : QuarticBoxFactor => W.model)).filtration.realPolynomialSymbolHom
          R.basis R.weight R.adapted (fun _ : QuarticBoxIndex => 1) := by
      rfl
    rw [hhom, W.quarticAntisymmetricBoxPolynomial_mono hp R.leftIndex R.rightIndex]
    cases W
    rfl
  have htransport := (congrArg (fun symbol =>
    (pi (fun _ : QuarticBoxFactor => W.model)).filtration.ControlledSymbolFactorization
      R.basis R.weight R.adapted (piFrequency W.quarticAntisymmetricBoxFrequencies)
      (fun _ : QuarticBoxIndex => (N : ℝ)) symbol q') hsymbol).mpr hfactor
  exact {
    leftIndex := R.leftIndex
    rightIndex := R.rightIndex
    nonnegative := R.nonnegative.trans hp
    topology := R.topology
    topologicalAdd := R.topologicalAdd
    continuousSMul := R.continuousSMul
    hausdorff := R.hausdorff
    basis := R.basis
    weight := R.weight
    adapted := R.adapted
    height := fun i j => (R.height i j).trans hq
    factorization := htransport }

end Erdos3

end

end OAI
