import OAI.Probability.InvariantIsing.Cavity.ConsecutiveWindowMinimumConsistency
import OAI.Probability.InvariantIsing.Cavity.CavityRationalLabelIdentities
import OAI.Probability.InvariantIsing.Cavity.CavityRationalAuxiliary

namespace OAI

/-! Rational spectral proportions provide every physical window needed for constrained block consistency. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators BoundedContinuousFunction
namespace InvariantIsing

theorem consecutive_rational_minimizers_weak_consistency
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandRestrictedFieldPairInput)
    {m n : ℕ} (hm : 2 ≤ m) (hn : 0<n) (s : Fin m → ℕ)
    (hs : ∀ a, 0<s a) (hsum : ∑ a, s a=n)
    (Cset : Finset (Spin n)) (hCset : Cset.Nonempty)
    (μ : (M : ℕ) → Measure (Orthogonal M)) [∀ M, IsProbabilityMeasure (μ M)]
    [∀ M, (μ M).IsMulRightInvariant]
    (lam : Fin m → ℝ) (amax : Fin m) (hmax : ∀ a, lam a≤lam amax)
    (u : (r : ℕ) → Fin (cavityRationalSize n (m*n-n) r) → ℝ) (v : ℕ → Fin m → ℝ)
    (hu : ∀ r j, u r j∈Set.Icc (1 : ℝ) 2) (hv : ∀ r a, v r a∈Set.Icc (1 : ℝ) 2)
    (hmin : ∀ r u' v', (∀ j, u' j∈Set.Icc (1 : ℝ) 2) → (∀ a, v' a∈Set.Icc (1 : ℝ) 2) →
      let M := cavityRationalSize n (m*n-n) r
      let g := cavityRationalLabel (by omega : 0 < m) s hsum M
      priorPerturbationObjective (cavityOrientedBaseLaw (by
        have := cavityRationalSize_ge_three n (m*n-n) r hn; omega) (μ M))
        (restrictedZeroTreePrior (consecutiveBlockConstraint n (r+(m*n-n+n+3)) Cset)
          (consecutiveBlockConstraint_nonempty Cset hCset))
        (fun i => lam (g i)) (fun _ => 0) (cavitySpectralGroup g) 1 (fun _ => 0) (u r) (v r) ≤
      priorPerturbationObjective (cavityOrientedBaseLaw (by
        have := cavityRationalSize_ge_three n (m*n-n) r hn; omega) (μ M))
        (restrictedZeroTreePrior (consecutiveBlockConstraint n (r+(m*n-n+n+3)) Cset)
          (consecutiveBlockConstraint_nonempty Cset hCset))
        (fun i => lam (g i)) (fun _ => 0) (cavitySpectralGroup g) 1 (fun _ => 0) u' v') :
    ∃ p : OverlapPath, ∀ Φ : ℝ →ᵇ ℝ,
      Tendsto (fun r => ∫ t, Φ (cavityStrictUniformPath p r t) *
        (restrictedBlockOverlapPath hn Cset hCset (cavityStrictUniformField
          (fun a => (s a : ℝ)/n) lam (cavityRationalMass_positive s hs hn)
          (cavityRationalMass_sum s hsum hn) p r) t-cavityStrictUniformPath p r t) ∂pathMeasure)
        atTop (𝓝 0) := by
  let d := m*n-n
  let q := d+n+3
  let N := fun r => (r+q)*n
  let ρ := fun j => (s j : ℝ)/n
  have hm0 : 0 < m := by omega
  have hρ j : 0 < ρ j := cavityRationalMass_positive s hs hn j
  have hρsum : ∑ j, ρ j=1 := cavityRationalMass_sum s hsum hn
  obtain ⟨hd,es,a₀,B₀,hcounts,hB₀,hperp⟩ := cavity_rational_auxiliary_geometry hm hn s hs hsum
  let k := cavityRationalRetained n d s
  let e : (r : ℕ) → (((a : Fin m) × Fin (k r a)) ⊕ Fin d) ≃ Fin (N r) :=
    cavityRationalBaseEquiv s hs hsum a₀ hcounts
  let gf := cavityRationalFullGroup s hsum d
  let l := fun r j => cavityOrderedStart (cavityRationalCount s q (r+1)) j
  let w := fun r j => l r j+cavityRationalCount s q (r+1) j
  have hN r : 3 ≤ N r := cavityRationalSize_ge_three n d r hn
  have hNl : Tendsto N atTop atTop := cavityRationalDimension_tendsto n q hn
  have hk r j : d ≤ k r j := cavityRationalRetained_ge s hs r j
  have hdim r j : cavityBaseGroupDimension (k r) a₀ j=cavityRationalCount s q r j :=
    cavityRationalBase_dimension s hs hsum a₀ hcounts r j
  have hgroups r j : 0 < cavityBaseGroupDimension (k r) a₀ j := by
    rw [hdim]
    exact cavityRationalCount_positive s hs (by omega) r j
  have hdims j : Tendsto (fun r => cavityBaseGroupDimension (k r) a₀ j) atTop atTop := by
    simpa only [hdim] using cavityRationalCount_tendsto s hs q j
  have hmass r j : (cavityBaseGroupDimension (k r) a₀ j : ℝ)/N r=ρ j := by
    rw [hdim]
    exact cavityRationalCount_ratio s hn (by omega) r j
  have hmasslim : Tendsto (fun r j => (cavityBaseGroupDimension (k r) a₀ j : ℝ)/N r) atTop (𝓝 ρ) := by
    simpa only [hmass] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => ρ) atTop (𝓝 ρ))
  have hc : 0 < (1:ℝ)/n := div_pos zero_lt_one (by exact_mod_cast hn)
  have hfrac r j : (1:ℝ)/n ≤ (cavityBaseGroupDimension (k r) a₀ j : ℝ)/N r := by
    rw [hmass]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hs j) (Nat.cast_nonneg n)
  have hwindow r j i : gf r i=j ↔ l r j ≤ i.val ∧ i.val < w r j :=
    cavityOrderedGroup_window _ _ j i
  have hln r j : l r j+n ≤ w r j :=
    cavityRationalFullWindow_size s hs (by omega) r j
  have hw r j : w r j ≤ N r+n :=
    cavityOrderedStart_add_le (cavityRationalCount s q (r+1))
      (cavityRationalFull_sum s hsum q r) j (cavityRationalCount_positive s hs (by omega) (r+1) j)
  have hl j : Tendsto (fun r => (l r j : ℝ)/(N r+n)) atTop
      (𝓝 ((cavityOrderedStart s j : ℝ)/n)) := by
    apply (tendsto_const_nhds : Tendsto (fun _ : ℕ =>
      (cavityOrderedStart s j : ℝ)/n) atTop (𝓝 _)).congr
    intro r
    symm
    simpa only [l, N, cavityRationalSize, Nat.cast_add] using
      cavityRationalFullStart_ratio (q := q) s hn (by omega) r j
  have hwlim j : Tendsto (fun r => (w r j : ℝ)/(N r+n)) atTop
      (𝓝 ((cavityOrderedStart s j+s j : ℝ)/n)) := by
    apply (tendsto_const_nhds : Tendsto (fun _ : ℕ =>
      (cavityOrderedStart s j+s j : ℝ)/n) atTop (𝓝 _)).congr
    intro r
    symm
    simpa only [w, l, N, cavityRationalSize, Nat.cast_add] using
      cavityRationalFullEnd_ratio (q := q) s hn (by omega) r j
  have hK r : 2≤r+q := by dsimp only [q]; omega
  let θ : Measure (LabeledTree 0) := labeledCascadeLaw 0 (fun _ => 1)
  let : ∀ r, IsProbabilityMeasure (μ (N r+n)) := fun _ => inferInstance
  let : ∀ r, (μ (N r+n)).IsMulRightInvariant := fun _ => inferInstance
  let : ∀ r, IsProbabilityMeasure (μ (N r)) := fun _ => inferInstance
  let : ∀ r, (μ (N r)).IsMulRightInvariant := fun _ => inferInstance
  exact consecutive_window_minimizers_weak_consistency hhaar hgauss hpub (fun r => r+q) hK Cset hCset
    (fun r => (show 0<(r+q)*n from by
      simpa only [N, cavityRationalSize, q, d] using
        (lt_of_lt_of_le (by norm_num : 0<3) (hN r)))) hNl hN gf k
    (cavityRationalRetainedEquiv s hs hsum d) e es B₀ a₀ hk
    (fun r a => μ (cavityBaseGroupDimension (k r) a₀ a)) l w hwindow hln hw
    (fun r => μ (N r+n)) (fun r => μ (N r)) (fun _ => θ) lam v hv u hu (by
      intro r u' v' hu' hv'
      have hh := hmin r u' v' hu' hv'
      have heq (i : Fin (N r)) :
          ((cavityBaseGroupEquiv (k r) (e r) a₀).symm i).1=
            cavityRationalLabel hm0 s hsum (N r) i :=
        cavityRationalBase_canonical_label hm0 s hs hsum hn a₀ hcounts r i
      simp_rw [heq]
      exact hh)
    hd hn hB₀ ρ hρ hρsum (fun a => (cavityOrderedStart s a : ℝ)/n)
    (fun a => (cavityOrderedStart s a+s a : ℝ)/n)
    (funext fun a => (cavityRationalMass_difference s a).symm)
    (cavityRationalFullEnd_tendsto s hs q) (cavityRationalFullStart_alternative s q)
    (fun a => by simpa only [N, cavityRationalSize, Nat.cast_add, q, d] using hl a)
    (fun a => by simpa only [N, cavityRationalSize, Nat.cast_add, q, d] using hwlim a)
    hperp hgroups hdims hc hfrac hmasslim amax hmax

end InvariantIsing

end

end OAI
