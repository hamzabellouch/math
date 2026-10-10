import OAI.Combinatorics.Progressions.Lattices.JointAffineL1Parameter

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem jointAffineJetDensity_principalTuple_l1 {Q Z K D α : Type*}
    [Fintype Q] [DecidableEq Q] [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
    (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
    {I J N : Q → Type*} [∀ q, Fintype (I q)] [∀ q, Fintype (J q)] [∀ q, Fintype (N q)]
    (s : ∀ q, I q ↪ J q) (A : ∀ q, (I q → ℝ) ≃L[ℝ] (I q → ℝ))
    (F : ∀ q, (UnselectedColumn (s q) → ℝ) →L[ℝ] (I q → ℝ))
    (e : ∀ q, N q → K →₀ ℕ) (input : K → Option α → Z ⊕ JointBlockParameter B h α)
    (z : Z → ℝ) (hz : ∀ j, |z j| ≤ 1) (rows : ∀ q, I q → Finset α)
    (degree : Q → ℕ) (hd : ∀ q n, (e q n).sum (fun _ k => k) ≤ degree q)
    (c w : ∀ q, J q ⊕ N q → ℝ) (hw : ∀ q j, 0 < w q j) (δ R : Q → ℝ≥0)
    (hδ : ∀ q, 0 < δ q) (hwidth : ∀ q j, (δ q : ℝ) ≤ w q (.inl j))
    (hsupport : ∀ q j, |c q j| + w q j ≤ R q)
    (L M : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j)
    (m : PrincipalTupleIndex B h → Option α → ℕ) (r : ∀ j i, ZMod (m j i))
    (hm : ∀ j i, 0 < m j i) (hmM : ∀ j i, m j i ≤ M j)
    (hsize : ∀ j, (Fintype.card α+1)*M j ≤ L j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant α * ((M j : ℝ)/L j) < volume.real (scalarCubeDomain α)) :
    let ρ := jointAffineJetDensity s A F e input z rows c w
    let Lip := ∑ q, affineJetL1Cost (JointBlockParameter B h α) α (J q) (N q)
      (A q) (degree q) (δ q) (R q)
    let Δ := fun v => (FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights α (L j) (M j) (hL j)
      (m j) (r j) (hm j) (hmM j) (hsize j))).mean
        (fun y => ρ (fun t => (y ⟨t.1, t.2.1, t.2.2.1⟩ t.2.2.2 : ℝ) / L ⟨t.1, t.2.1, t.2.2.1⟩) v) -
      ∫ x, ρ x v ∂jointBooleanSource h
    Integrable Δ (Measure.pi (fun _ => volume)) ∧
      (∫ v, |Δ v| ∂Measure.pi (fun _ => volume)) ≤
        (2 * scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α) + Lip) *
          ∑ j, (M j : ℝ)/L j := by
  dsimp only
  apply principalTuple_density_l1_of_l1_regular B h L M hL m r hm hmM hsize hsmall
    (Measure.pi (fun _ => volume)) (jointAffineJetDensity s A F e input z rows c w)
  · exact jointAffineJetDensity_measurable_comp
      (Ω := (JointBlockParameter B h α → ℝ) × (∀ q, I q → ℝ)) s A F e input rows c w hw R hsupport
      (fun _ => z) (fun _ => measurable_const) (fun p => p.1)
      (fun j => (measurable_pi_apply j).comp measurable_fst) (fun p => p.2)
      (fun q i => (measurable_pi_apply i).comp ((measurable_pi_apply q).comp measurable_snd))
  · intro x _
    have hp := jointAffineJetDensity_probability_data s A F e input z rows c w hw R hsupport x
    exact ⟨hp.2.1, hp.1, hp.2.2⟩
  · exact jointAffineJetDensity_l1_regular s A F e input z hz rows degree hd c w hw δ R hδ hwidth hsupport

end Erdos3

end

end OAI
