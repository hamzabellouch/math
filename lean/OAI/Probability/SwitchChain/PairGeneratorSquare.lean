import OAI.Probability.SwitchChain.PairPoincare
import OAI.Probability.SwitchChain.PairAggregation

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.PairResampling

attribute [local instance] Classical.propDecidable

def tripleGenerator (n : Nat) (d : Fin n → Nat) (T : Finset (Fin n)) :
    StateSpace n d →L[ℝ] StateSpace n d :=
  ∑ a ∈ T.powersetCard 2, fluctuation n d a

theorem tripleGenerator_apply {n : Nat} {d : Fin n → Nat}
    (T : Finset (Fin n)) (f : StateSpace n d) :
    tripleGenerator n d T f = ∑ a ∈ T.powersetCard 2, fluctuation n d a f := by
  simp [tripleGenerator]

theorem inner_tripleGenerator {n : Nat} {d : Fin n → Nat}
    (T : Finset (Fin n)) (f : StateSpace n d) :
    ⟪f, tripleGenerator n d T f⟫ =
      ∑ a ∈ T.powersetCard 2, ‖fluctuation n d a f‖ ^ 2 := by
  simp only [tripleGenerator_apply, inner_sum, inner_fluctuation]

theorem generator_square_of_local {n : Nat} {d : Fin n → Nat}
    (hn : 3 ≤ n) (f : StateSpace n d)
    (htriple : ∀ T : Finset (Fin n), T.card = 3 →
      ⟪f, tripleGenerator n d T f⟫ ≤
        ⟪tripleGenerator n d T f, tripleGenerator n d T f⟫)
    (hdisjoint : 0 ≤ ∑ a ∈ pairs n, ∑ b ∈ pairs n,
      if Disjoint a b then ⟪fluctuation n d a f, fluctuation n d b f⟫ else 0) :
    ⟪f, generator n d f⟫ ≤ ⟪generator n d f, generator n d f⟫ := by
  rw [inner_generator]
  simp only [generator_apply]
  simp only [sum_inner]
  simp only [inner_sum]
  apply PairAggregation.global_of_local (Finset.univ : Finset (Fin n)) (by simpa using hn)
    (fun a => ‖fluctuation n d a f‖ ^ 2)
    (fun a b => ⟪fluctuation n d a f, fluctuation n d b f⟫)
  · intro a ha
    exact real_inner_self_eq_norm_sq _
  · intro T hT
    have hcard := (Finset.mem_powersetCard.mp hT).2
    have h := htriple T hcard
    rw [inner_tripleGenerator] at h
    simp only [tripleGenerator_apply] at h
    simp only [sum_inner] at h
    simp only [inner_sum] at h
    exact h
  · exact hdisjoint

end Problem315.PairResampling

namespace Problem315

attribute [local instance] Classical.propDecidable

theorem spectralGap_of_local_pair_bounds (n : Nat) (d : Fin n → Nat)
    (hn : 4 ≤ n) (hgraphical : Graphical n d)
    (htriple : ∀ (f : PairResampling.StateSpace n d) (T : Finset (Fin n)),
      T.card = 3 →
      ⟪f, PairResampling.tripleGenerator n d T f⟫ ≤
        ⟪PairResampling.tripleGenerator n d T f, PairResampling.tripleGenerator n d T f⟫)
    (hdisjoint : ∀ f : PairResampling.StateSpace n d,
      0 ≤ ∑ a ∈ PairResampling.pairs n, ∑ b ∈ PairResampling.pairs n,
        if Disjoint a b then
          ⟪PairResampling.fluctuation n d a f, PairResampling.fluctuation n d b f⟫ else 0)
    (hcomparison : ∀ f : PairResampling.StateSpace n d,
      uniformInner n d (fun G => f G) (fun G => PairResampling.generator n d f G) ≤
        (24 * (n : ℝ) ^ 2 * (n.choose 4 : ℝ)) *
          dirichletEnergy n d (fun G => f G)) :
    hasSpectralGapAtLeast n d ((1 : ℝ) / (24 * (n : ℝ) ^ 2 * (n.choose 4 : ℝ))) := by
  apply PairResampling.spectralGap_of_square_and_comparison hn hgraphical
  · intro f
    exact PairResampling.generator_square_of_local (by omega) f (htriple f) (hdisjoint f)
  · intro f
    rw [PairResampling.state_inner]
    exact hcomparison (WithLp.toLp 2 f)

end Problem315

end

end OAI
