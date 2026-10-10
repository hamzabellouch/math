import OAI.Combinatorics.Progressions.Polynomial.MixedBoxPolynomial

namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

noncomputable def NativeMixedBoxFactorization.mono {n : ℕ} {p p' q q' : ℝ} {N : ℕ} [NeZero N]
    {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p}
    (R : NativeMixedBoxFactorization W N q) (hp : p ≤ p') (hq : q ≤ q') :
    NativeMixedBoxFactorization (W.mono hp) N q' := by
  letI := R.topology
  letI := R.topologicalAdd
  letI := R.continuousSMul
  letI := R.hausdorff
  letI : TopologicalSpace (ℝ ⊗[ℚ] (MixedBoxFactor n → (W.mono hp).L)) := R.topology
  letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] (MixedBoxFactor n → (W.mono hp).L)) := R.topologicalAdd
  letI : ContinuousSMul ℝ (ℝ ⊗[ℚ] (MixedBoxFactor n → (W.mono hp).L)) := R.continuousSMul
  letI : T2Space (ℝ ⊗[ℚ] (MixedBoxFactor n → (W.mono hp).L)) := R.hausdorff
  have hfactor := NilpotentLieFiltration.ControlledSymbolFactorization.mono
    (pi (fun _ : MixedBoxFactor n => W.model)).filtration R.basis R.weight R.adapted R.factorization hq
    (fun _ => by exact_mod_cast NeZero.pos N)
  have hsymbol :
      ((W.mono hp).mixedAntisymmetricBoxNiltest (R.nonnegative.trans hp) R.leftIndex R.rightIndex).symbol
        R.basis R.weight R.adapted =
      (W.mixedAntisymmetricBoxNiltest R.nonnegative R.leftIndex R.rightIndex).symbol
        R.basis R.weight R.adapted := by
    rw [(W.mono hp).mixedAntisymmetricBoxNiltest_symbol
      (R.nonnegative.trans hp) R.leftIndex R.rightIndex R.basis R.weight R.adapted]
    rw [W.mixedAntisymmetricBoxNiltest_symbol
      R.nonnegative R.leftIndex R.rightIndex R.basis R.weight R.adapted]
    have hhom :
        (pi (fun _ : MixedBoxFactor n => (W.mono hp).model)).filtration.realPolynomialSymbolHom
          R.basis R.weight R.adapted (fun _ : MixedBoxIndex n => 1) =
        (pi (fun _ : MixedBoxFactor n => W.model)).filtration.realPolynomialSymbolHom
          R.basis R.weight R.adapted (fun _ : MixedBoxIndex n => 1) := by
      rfl
    rw [hhom, W.mixedAntisymmetricBoxPolynomial_mono hp R.leftIndex R.rightIndex]
    cases W
    rfl
  have htransport := (congrArg (fun symbol =>
    (pi (fun _ : MixedBoxFactor n => W.model)).filtration.ControlledSymbolFactorization
      R.basis R.weight R.adapted (piFrequency W.mixedAntisymmetricBoxFrequencies)
      (fun _ : MixedBoxIndex n => (N : ℝ)) symbol q') hsymbol).mpr hfactor
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
