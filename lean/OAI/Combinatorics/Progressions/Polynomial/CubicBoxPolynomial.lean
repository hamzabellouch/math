import OAI.Combinatorics.Progressions.Geometry.CubicBoxStepDrop

namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

variable {p q : ℝ} (V : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p)

theorem cubicAntisymmetricBoxFactors_orbit_mono (hpq : p ≤ q)
    (i j : Fin V.outputDim × Fin V.outputDim) (shift : ℤ) (a : Fin 8 × Fin 4) :
    ((V.mono hpq).cubicAntisymmetricBoxFactors i j shift a).orbit =
      (V.cubicAntisymmetricBoxFactors i j shift a).orbit := by
  rcases a with ⟨c, k⟩
  unfold cubicAntisymmetricBoxFactors
  split_ifs <;> fin_cases k <;> rfl

noncomputable def cubicAntisymmetricBoxPolynomial
    (i j : Fin V.outputDim × Fin V.outputDim) (shift : ℤ) :
    ((pi (fun _ : Fin 8 × Fin 4 => V.model)).filtration.realification.adaptedPolynomialFiltration
      (fun _ : Fin 6 => 1)).Group :=
  let o := NilpotentLieFiltration.piRealOrbit (fun _ : Fin 8 × Fin 4 => V.model.filtration)
    (fun a => (V.cubicAntisymmetricBoxFactors i j shift a).orbit)
  ⟨⟨o.log, o.property⟩⟩

theorem cubicAntisymmetricBoxPolynomial_mono (hpq : p ≤ q)
    (i j : Fin V.outputDim × Fin V.outputDim) (shift : ℤ) :
    (V.mono hpq).cubicAntisymmetricBoxPolynomial i j shift =
      V.cubicAntisymmetricBoxPolynomial i j shift := by
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  apply congrArg (fun o : (pi (fun _ : Fin 8 × Fin 4 => V.model)).filtration.realification.PolynomialOrbit
    (fun _ : Fin 6 => 1) => o.log)
  apply congrArg (NilpotentLieFiltration.piRealOrbit (fun _ : Fin 8 × Fin 4 => V.model.filtration))
  funext a
  exact V.cubicAntisymmetricBoxFactors_orbit_mono hpq i j shift a

variable [TopologicalSpace (ℝ ⊗[ℚ] ((Fin 8 × Fin 4) → V.L))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] ((Fin 8 × Fin 4) → V.L))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] ((Fin 8 × Fin 4) → V.L))]
  [T2Space (ℝ ⊗[ℚ] ((Fin 8 × Fin 4) → V.L))]

theorem cubicAntisymmetricBoxPolynomial_eq_test (hp : 0 ≤ p)
    (i j : Fin V.outputDim × Fin V.outputDim) (shift : ℤ) :
    V.cubicAntisymmetricBoxPolynomial i j shift =
      ⟨⟨(V.cubicAntisymmetricBoxNiltest hp i j shift).orbit.log,
        (V.cubicAntisymmetricBoxNiltest hp i j shift).orbit.property⟩⟩ := rfl

theorem cubicAntisymmetricBoxNiltest_symbol (hp : 0 ≤ p)
    (i j : Fin V.outputDim × Fin V.outputDim) (shift : ℤ)
    {ι : Type*} (b : Module.Basis ι ℚ ((Fin 8 × Fin 4) → V.L)) (ω : ι → ℕ)
    (hF : ∀ k, (pi (fun _ : Fin 8 × Fin 4 => V.model)).filtration.layer k =
      Submodule.span ℚ (b '' {a | k ≤ ω a})) :
    (V.cubicAntisymmetricBoxNiltest hp i j shift).symbol b ω hF =
      (pi (fun _ : Fin 8 × Fin 4 => V.model)).filtration.realPolynomialSymbolHom b ω hF
        (fun _ : Fin 6 => 1) (V.cubicAntisymmetricBoxPolynomial i j shift) := rfl

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
