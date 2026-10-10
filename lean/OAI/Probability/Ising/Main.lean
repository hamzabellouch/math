import OAI.Probability.Ising.Contraction
import OAI.Probability.Ising.Influence

namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing

noncomputable section

/-- The oriented pair matrix is precisely the original edge-list interaction;
parallel edges are summed, with no ghost and no change to the field. -/
def dssMatrix {n m : ℕ} (G : FiniteGraph n m) (u v : Fin n) : ℝ :=
  ∑ e, if G.left e = u then if G.right e = v then G.coupling e else 0 else 0

lemma dssMatrix_nonneg {n m : ℕ} (G : FiniteGraph n m) (u v : Fin n) :
    0 ≤ dssMatrix G u v := by
  apply Finset.sum_nonneg
  intro e _
  split_ifs <;> first | exact G.coupling_nonneg e | exact le_rfl

lemma dss_hamiltonian_eq {n m : ℕ} (G : FiniteGraph n m) (h : Fin n → ℝ)
    (σ : Spins n) : DSS.hamiltonian (dssMatrix G) h σ = energy G h σ := by
  unfold DSS.hamiltonian energy dssMatrix
  change ((∑ u, ∑ v, (∑ e, if G.left e = u then if G.right e = v then
    G.coupling e else 0 else 0) * spin (σ u) * spin (σ v)) + _) = _
  congr 1
  simp only [Finset.sum_mul]
  calc
    _ = ∑ u, ∑ e, ∑ v, (if G.left e = u then if G.right e = v then
        G.coupling e else 0 else 0) * spin (σ u) * spin (σ v) := by
      apply Finset.sum_congr rfl
      intro u _
      exact Finset.sum_comm
    _ = ∑ e, ∑ u, ∑ v, (if G.left e = u then if G.right e = v then
        G.coupling e else 0 else 0) * spin (σ u) * spin (σ v) := Finset.sum_comm
    _ = _ := by simp [ite_mul, Finset.sum_ite_irrel]

lemma dss_mass_eq {n m : ℕ} (G : FiniteGraph n m) (h : Fin n → ℝ)
    (σ : Spins n) : DSS.mass (dssMatrix G) h σ = weight G h σ := by
  rw [DSS.mass, weight, dss_hamiltonian_eq]

lemma dss_average_eq {n m : ℕ} (G : FiniteGraph n m) (h : Fin n → ℝ)
    (f : Spins n → ℝ) : DSS.average (dssMatrix G) h f = expectation G h f := by
  simp only [DSS.average, DSS.part, dss_mass_eq, expectation]
  congr!

/-- The arbitrary-field covariance bound for the finite edge-list Gibbs law, including equal sites. -/
theorem arbitraryFieldCovarianceBound : ArbitraryFieldCovarianceBound := by
  intro n m G h u v
  have H := DSS.covariance_le_zero_field (dssMatrix G) (dssMatrix_nonneg G) h u v
  simp only [DSS.correlation, DSS.mean, dss_average_eq] at H
  convert H using 1 <;> congr!

theorem effectiveCouplingBound : EffectiveCouplingBound :=
  covarianceBound_iff_effectiveCouplingBound.mp arbitraryFieldCovarianceBound

lemma extremeLogOdds_le_zero {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (I J F : Finset (Fin n))
    (hIJ : Disjoint I J) (hIF : Disjoint I F) (hJF : Disjoint J F)
    (i j : KeptVertex F) (hi : i.val ∈ I) (hj : j.val ∈ J) (τ : Spins n) :
    extremeLogOdds G h I J F τ ≤ 4 * Real.artanh (qZero G I J F i j) := by
  rw [extremeLogOdds_eq_actualCoupling G h I J F hIJ hIF hJF i j hi hj τ,
    artanh_qZero_eq_actualCoupling G I J F hIJ i j hi hj]
  exact mul_le_mul_of_nonneg_left
    (effectiveCouplingBound _ _ (actualComparisonGraph G I J F)
      (actualComparisonField G h I J F τ) _ _
      (actualTerminal_ne G I J F hIJ i j hi hj)) (by norm_num)

/-- Finite-graph comparison for arbitrary probability mixtures on both sides. Dirac mixtures recover the conditional laws. -/
theorem finite_graph_comparison {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (I J F : Finset (Fin n))
    (hIJ : Disjoint I J) (hIF : Disjoint I F) (hJF : Disjoint J F)
    (i j : KeptVertex F) (hi : i.val ∈ I) (hj : j.val ∈ J)
    (a τ : Spins n) (mix mix' : Spins n → ℝ)
    (hmix : ∀ b, 0 ≤ mix b) (hmix' : ∀ b, 0 ≤ mix' b)
    (hmixsum : ∑ b, mix b = 1) (hmix'sum : ∑ b, mix' b = 1) :
    Real.exp (-4 * Real.artanh (qZero G I J F i j)) ≤
        mixtureProb G h I J F a τ mix / mixtureProb G h I J F a τ mix' ∧
      mixtureProb G h I J F a τ mix / mixtureProb G h I J F a τ mix' ≤
        Real.exp (4 * Real.artanh (qZero G I J F i j)) := by
  have H := mixture_ratio_extreme G h I J F hIJ hIF hJF a τ mix mix'
    hmix hmix' hmixsum hmix'sum
  have HB := extremeLogOdds_le_zero G h I J F hIJ hIF hJF i j hi hj τ
  exact ⟨(Real.exp_le_exp.mpr (by linarith)).trans H.1,
    H.2.trans (Real.exp_le_exp.mpr HB)⟩

end

end BufferedIsing

end OAI
