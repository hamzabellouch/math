import OAI.MeasureTheory.Falconer.Recursion.PolicyBranchCoefficients
import OAI.MeasureTheory.Falconer.Fourier.PolicyJetChildren

namespace OAI

/-! # The direct angular branch on actual successor states -/

namespace Falconer
open Set MeasureTheory
open scoped SchwartzMap
open PlanarFalconer (PolicyDescriptor descriptorAnchor)

namespace PolicyJetData
variable {m : ℕ}

noncomputable def directWeight (P : PolicyJetData m) (p : ℕ) (lam σ ε : ℝ) : ℝ :=
  ((2:ℝ)^P.N)^(-2*(profileExcess (d := m+3) P.profile P.N p-
    profileExcess (d := m+3) P.profile P.N P.a)+
    PlanarFalconer.height (profileExcess (d := m+3) P.profile P.N) P.a p+
    4000*(dimensionalBranchReserve (m+3) lam σ+σ)+ε)

end PolicyJetData

theorem exists_policy_direct_recurrence
    (hpublished : PublishedGnomonicSurface) (m K : ℕ)
    {lam σ ε : ℝ} (hlam : 0 ≤ lam) (hσ : 0 < σ) (hε : 0 < ε)
    {J : ℕ} (hJ : 0 < J) (T : ℝ)
    (φ : 𝓢(ℝ,ℂ)) (Ψ : ℝ → ℝ)
    (hφ : ∀ u, φ u = (Ψ u : ℂ)) (hΨ : Measurable Ψ)
    (hpos : ∀ u, 0 ≤ Ψ u) (hzero : ∀ u ≤ 0, Ψ u = 0)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ u, Ψ u ≤ W)
    (hsupp : ∀ u, Ψ u ≠ 0 → u ∈ Ioo (1/4:ℝ) 4) (minOrder : ℕ) :
    ∃ (L : ℕ) (Z : ℝ) (N₀ : ℕ), minOrder ≤ L ∧ 1 ≤ Z ∧
      ∀ (P : PolicyJetData m), P.lam = lam → P.σ = σ → P.J = J → P.Z = Z →
      N₀ ≤ P.N → P.i+1 ≤ P.J → ∀ d : PolicyDescriptor,
      ∀ hd : PlanarFalconer.DirectPolicyWitness P.policy P.N P.q P.a₀ P.t₀ P.a P.t P.σ d,
      ∀ M : ℝ, 0 ≤ M →
      (∀ row, ∀ hrow : row ∈
        (P.Q.descendant P.X).occupiedPaths P.ρ (descriptorAnchor d-P.a) ×ˢ
          (P.Q.descendant P.Y).occupiedPaths P.ρ (descriptorAnchor d-P.a),
        P.directWeight (descriptorAnchor d) lam σ ε *
          (P.child (descriptorAnchor d) hd.anchor_gt.le row hrow).envelope K L Ψ ≤ M) →
      P.envelope K L Ψ ≤ M+((2:ℝ)^P.N)^(-T) := by
  obtain ⟨L,Z,Ngraph,hL,hZ,hgraph⟩ := exists_policy_graph_step hpublished m K hσ hJ T
    φ Ψ hφ hΨ hpos hzero hW hΨW hsupp minOrder
  obtain ⟨Ncoeff,hcoeff⟩ := eventual_policy_graph_coefficient m K hlam hσ.le hε
  refine ⟨L,Z,max Ngraph Ncoeff,hL,hZ,?_⟩
  intro P hLam hσP hJP hZP hN hi d hd M hM hchildren
  let w := P.directWeight (descriptorAnchor d) lam σ ε
  have hw : 0 < w := by dsimp [w,PolicyJetData.directWeight]; positivity
  have hchild : P.graphChild K L (descriptorAnchor d) Ψ ≤ M/w := by
    apply P.graphChild_le K L (descriptorAnchor d) hd.anchor_gt.le Ψ (div_nonneg hM hw.le)
    intro row hrow
    apply (le_div_iff₀ hw).mpr
    simpa only [w,mul_comm] using hchildren row hrow
  have hweighted : w*P.graphChild K L (descriptorAnchor d) Ψ ≤ M := by
    simpa only [mul_comm] using (le_div_iff₀ hw).mp hchild
  have hcost := hcoeff P hLam hσP ((le_max_right _ _).trans hN) (descriptorAnchor d)
  have hchild0 : 0 ≤ P.graphChild K L (descriptorAnchor d) Ψ :=
    childJetStateMaximum_nonneg (m+1) K L 1 _ P.Q P.ρ _ P.N P.σ P.J P.i P.masks P.Z
      P.X P.Y (descriptorAnchor d-P.a) _ (descriptorAnchor d) P.t Ψ
  have hg := hgraph P hσP hJP hZP ((le_max_left _ _).trans hN) hi d hd
  calc
    _ ≤ P.graphCoefficient (descriptorAnchor d)*
        (((descriptorJetBound (m+3) K)^K)^2*((descriptorJetBound (m+3) K)^K)^2*
          P.graphChild K L (descriptorAnchor d) Ψ)+((2:ℝ)^P.N)^(-T) := hg
    _ = (P.graphCoefficient (descriptorAnchor d)*
        (((descriptorJetBound (m+3) K)^K)^2*((descriptorJetBound (m+3) K)^K)^2))*
          P.graphChild K L (descriptorAnchor d) Ψ+((2:ℝ)^P.N)^(-T) := by ring
    _ ≤ w*P.graphChild K L (descriptorAnchor d) Ψ+((2:ℝ)^P.N)^(-T) :=
      add_le_add (mul_le_mul_of_nonneg_right hcost hchild0) le_rfl
    _ ≤ _ := add_le_add hweighted le_rfl

end Falconer

end OAI
