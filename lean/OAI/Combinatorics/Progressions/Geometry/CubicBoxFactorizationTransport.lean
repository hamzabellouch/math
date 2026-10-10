import OAI.Combinatorics.Progressions.Polynomial.CubicBoxPolynomial

namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

noncomputable def NativeCubicBoxFactorization.mono {p p' q q' : ℝ} {N : ℕ} [NeZero N]
    {V : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p}
    (R : NativeCubicBoxFactorization V N q) (hp : p ≤ p') (hq : q ≤ q') :
    NativeCubicBoxFactorization (V.mono hp) N q' := by
  letI := R.topology
  letI := R.topologicalAdd
  letI := R.continuousSMul
  letI := R.hausdorff
  letI : TopologicalSpace (ℝ ⊗[ℚ] ((Fin 8 × Fin 4) → (V.mono hp).L)) := R.topology
  letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] ((Fin 8 × Fin 4) → (V.mono hp).L)) := R.topologicalAdd
  letI : ContinuousSMul ℝ (ℝ ⊗[ℚ] ((Fin 8 × Fin 4) → (V.mono hp).L)) := R.continuousSMul
  letI : T2Space (ℝ ⊗[ℚ] ((Fin 8 × Fin 4) → (V.mono hp).L)) := R.hausdorff
  have hfactor := NilpotentLieFiltration.ControlledSymbolFactorization.mono
    (pi (fun _ : Fin 8 × Fin 4 => V.model)).filtration R.basis R.weight R.adapted R.factorization hq
    (fun _ => by exact_mod_cast NeZero.pos N)
  have hsymbol :
      ((V.mono hp).cubicAntisymmetricBoxNiltest (R.nonnegative.trans hp) R.leftIndex R.rightIndex
        (-(if R.branch then (N : ℤ) else 0))).symbol R.basis R.weight R.adapted =
      (V.cubicAntisymmetricBoxNiltest R.nonnegative R.leftIndex R.rightIndex
        (-(if R.branch then (N : ℤ) else 0))).symbol R.basis R.weight R.adapted := by
    exact congrArg
      ((pi (fun _ : Fin 8 × Fin 4 => V.model)).filtration.realPolynomialSymbolHom
        R.basis R.weight R.adapted (fun _ : Fin 6 => 1))
      (V.cubicAntisymmetricBoxPolynomial_mono hp R.leftIndex R.rightIndex
        (-(if R.branch then (N : ℤ) else 0)))
  have htransport := (congrArg (fun symbol =>
    (pi (fun _ : Fin 8 × Fin 4 => V.model)).filtration.ControlledSymbolFactorization
      R.basis R.weight R.adapted (piFrequency V.cubicAntisymmetricBoxFrequencies)
      (fun _ : Fin 6 => (N : ℝ)) symbol q') hsymbol).mpr hfactor
  exact {
    leftIndex := R.leftIndex
    rightIndex := R.rightIndex
    branch := R.branch
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
