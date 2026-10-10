import OAI.Combinatorics.Progressions.Geometry.MixedBoxStepDrop

namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

variable {n : ℕ} {p q : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p)

theorem mixedAntisymmetricBoxFactors_orbit_mono (hpq : p ≤ q)
    (i j : Fin W.outputDim) (a : MixedBoxFactor n) :
    ((W.mono hpq).mixedAntisymmetricBoxFactors i j a).orbit =
      (W.mixedAntisymmetricBoxFactors i j a).orbit := by
  rcases a with ⟨c, k⟩
  unfold mixedAntisymmetricBoxFactors
  split_ifs <;> fin_cases k <;> rfl

noncomputable def mixedAntisymmetricBoxPolynomial (i j : Fin W.outputDim) :
    ((pi (fun _ : MixedBoxFactor n => W.model)).filtration.realification.adaptedPolynomialFiltration
      (fun _ : MixedBoxIndex n => 1)).Group :=
  let o := NilpotentLieFiltration.piRealOrbit (fun _ : MixedBoxFactor n => W.model.filtration)
    (fun a => (W.mixedAntisymmetricBoxFactors i j a).orbit)
  ⟨⟨o.log, o.property⟩⟩

theorem mixedAntisymmetricBoxPolynomial_mono (hpq : p ≤ q) (i j : Fin W.outputDim) :
    (W.mono hpq).mixedAntisymmetricBoxPolynomial i j = W.mixedAntisymmetricBoxPolynomial i j := by
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  apply congrArg (fun o : (pi (fun _ : MixedBoxFactor n => W.model)).filtration.realification.PolynomialOrbit
    (fun _ : MixedBoxIndex n => 1) => o.log)
  apply congrArg (NilpotentLieFiltration.piRealOrbit (fun _ : MixedBoxFactor n => W.model.filtration))
  funext a
  exact W.mixedAntisymmetricBoxFactors_orbit_mono hpq i j a

variable [TopologicalSpace (ℝ ⊗[ℚ] (MixedBoxFactor n → W.L))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (MixedBoxFactor n → W.L))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (MixedBoxFactor n → W.L))]
  [T2Space (ℝ ⊗[ℚ] (MixedBoxFactor n → W.L))]

theorem mixedAntisymmetricBoxPolynomial_eq_test (hp : 0 ≤ p) (i j : Fin W.outputDim) :
    W.mixedAntisymmetricBoxPolynomial i j =
      ⟨⟨(W.mixedAntisymmetricBoxNiltest hp i j).orbit.log,
        (W.mixedAntisymmetricBoxNiltest hp i j).orbit.property⟩⟩ := rfl

theorem mixedAntisymmetricBoxNiltest_symbol (hp : 0 ≤ p) (i j : Fin W.outputDim)
    {ι : Type*} (b : Module.Basis ι ℚ (MixedBoxFactor n → W.L)) (ω : ι → ℕ)
    (hF : ∀ k, (pi (fun _ : MixedBoxFactor n => W.model)).filtration.layer k =
      Submodule.span ℚ (b '' {a | k ≤ ω a})) :
    (W.mixedAntisymmetricBoxNiltest hp i j).symbol b ω hF =
      (pi (fun _ : MixedBoxFactor n => W.model)).filtration.realPolynomialSymbolHom b ω hF
        (fun _ : MixedBoxIndex n => 1) (W.mixedAntisymmetricBoxPolynomial i j) := rfl

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
