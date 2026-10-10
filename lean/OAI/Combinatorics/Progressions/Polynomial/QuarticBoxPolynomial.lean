import OAI.Combinatorics.Progressions.Geometry.QuarticBoxStepDrop

namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

variable {p q : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)

theorem quarticAntisymmetricBoxFactors_orbit_mono (hpq : p ≤ q)
    (i j : Fin W.outputDim) (a : QuarticBoxFactor) :
    ((W.mono hpq).quarticAntisymmetricBoxFactors i j a).orbit =
      (W.quarticAntisymmetricBoxFactors i j a).orbit := by
  rcases a with ⟨c, k⟩
  unfold quarticAntisymmetricBoxFactors
  split_ifs <;> fin_cases k <;> rfl

noncomputable def quarticAntisymmetricBoxPolynomial (i j : Fin W.outputDim) :
    ((pi (fun _ : QuarticBoxFactor => W.model)).filtration.realification.adaptedPolynomialFiltration
      (fun _ : QuarticBoxIndex => 1)).Group :=
  let o := NilpotentLieFiltration.piRealOrbit (fun _ : QuarticBoxFactor => W.model.filtration)
    (fun a => (W.quarticAntisymmetricBoxFactors i j a).orbit)
  ⟨⟨o.log, o.property⟩⟩

theorem quarticAntisymmetricBoxPolynomial_mono (hpq : p ≤ q) (i j : Fin W.outputDim) :
    (W.mono hpq).quarticAntisymmetricBoxPolynomial i j = W.quarticAntisymmetricBoxPolynomial i j := by
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  apply congrArg (fun o : (pi (fun _ : QuarticBoxFactor => W.model)).filtration.realification.PolynomialOrbit
    (fun _ : QuarticBoxIndex => 1) => o.log)
  apply congrArg (NilpotentLieFiltration.piRealOrbit (fun _ : QuarticBoxFactor => W.model.filtration))
  funext a
  exact W.quarticAntisymmetricBoxFactors_orbit_mono hpq i j a

variable [TopologicalSpace (ℝ ⊗[ℚ] (QuarticBoxFactor → W.L))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (QuarticBoxFactor → W.L))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (QuarticBoxFactor → W.L))]
  [T2Space (ℝ ⊗[ℚ] (QuarticBoxFactor → W.L))]

theorem quarticAntisymmetricBoxPolynomial_eq_test (hp : 0 ≤ p) (i j : Fin W.outputDim) :
    W.quarticAntisymmetricBoxPolynomial i j =
      ⟨⟨(W.quarticAntisymmetricBoxNiltest hp i j).orbit.log,
        (W.quarticAntisymmetricBoxNiltest hp i j).orbit.property⟩⟩ := rfl

theorem quarticAntisymmetricBoxNiltest_symbol (hp : 0 ≤ p) (i j : Fin W.outputDim)
    {ι : Type*} (b : Module.Basis ι ℚ (QuarticBoxFactor → W.L)) (ω : ι → ℕ)
    (hF : ∀ k, (pi (fun _ : QuarticBoxFactor => W.model)).filtration.layer k =
      Submodule.span ℚ (b '' {a | k ≤ ω a})) :
    (W.quarticAntisymmetricBoxNiltest hp i j).symbol b ω hF =
      (pi (fun _ : QuarticBoxFactor => W.model)).filtration.realPolynomialSymbolHom b ω hF
        (fun _ : QuarticBoxIndex => 1) (W.quarticAntisymmetricBoxPolynomial i j) := rfl

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
