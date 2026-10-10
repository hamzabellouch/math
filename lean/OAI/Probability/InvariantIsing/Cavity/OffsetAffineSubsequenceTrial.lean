import OAI.Probability.InvariantIsing.Cavity.OffsetAffineIncrement
import OAI.Probability.InvariantIsing.Cavity.OffsetWindowTrialWitness

namespace OAI

/-! The rational physical trial construction along any increasing selection of dimensions. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators BoundedContinuousFunction
namespace InvariantIsing

theorem offset_affine_subsequence_trial_witness
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandRestrictedFieldPairInput)
    {m n : ℕ} (hm : 2 ≤ m) (hn : 0<n) (s c : Fin m → ℕ)
    (hs : ∀ a, 0<s a) (hsum : ∑ a, s a=n)
    (R : Finset (Spin (∑ a, c a))) (hR : R.Nonempty)
    (Cset : Finset (Spin n)) (hCset : Cset.Nonempty)
    (μ : (M : ℕ) → Measure (Orthogonal M)) [∀ M, IsProbabilityMeasure (μ M)]
    [∀ M, (μ M).IsMulRightInvariant]
    (lam : Fin m → ℝ) (amax : Fin m) (hmax : ∀ a, lam a≤lam amax)
    (ι : ℕ → ℕ) (hι : StrictMono ι)
    (u : (r : ℕ) → Fin (cavityPrefixAffineSize n (m*n-n+n+3) c r) → ℝ) (v : ℕ → Fin m → ℝ)
    (hu : ∀ r j, u r j∈Set.Icc (1 : ℝ) 2) (hv : ∀ r a, v r a∈Set.Icc (1 : ℝ) 2)
    (hmin : ∀ r u' v', (∀ j, u' j∈Set.Icc (1 : ℝ) 2) → (∀ a, v' a∈Set.Icc (1 : ℝ) 2) →
      let M := cavityPrefixAffineSize n (m*n-n+n+3) c r
      let g := cavityAffineLabel (by omega : 0 < m) s c hsum M
      priorPerturbationObjective (cavityOrientedBaseLaw (by
        have hh := cavityRationalSize_ge_three n (m*n-n) r hn
        exact lt_of_lt_of_le (by norm_num : 0<3)
          (hh.trans (Nat.le_add_left _ (∑ a, c a)))) (μ M))
        (restrictedZeroTreePrior (offsetBlockConstraint (r+(m*n-n+n+3)) R Cset)
          (offsetBlockConstraint_nonempty R hR Cset hCset))
        (fun i => lam (g i)) (fun _ => 0) (cavitySpectralGroup g) 1 (fun _ => 0) (u r) (v r) ≤
      priorPerturbationObjective (cavityOrientedBaseLaw (by
        have hh := cavityRationalSize_ge_three n (m*n-n) r hn
        exact lt_of_lt_of_le (by norm_num : 0<3)
          (hh.trans (Nat.le_add_left _ (∑ a, c a)))) (μ M))
        (restrictedZeroTreePrior (offsetBlockConstraint (r+(m*n-n+n+3)) R Cset)
          (offsetBlockConstraint_nonempty R hR Cset hCset))
        (fun i => lam (g i)) (fun _ => 0) (cavitySpectralGroup g) 1 (fun _ => 0) u' v') :
    ∃ (p : OverlapPath) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ Φ : ℝ →ᵇ ℝ,
      Tendsto (fun r => ∫ t, Φ (cavityStrictUniformPath p r t) *
        (restrictedBlockOverlapPath hn Cset hCset (cavityStrictUniformField
          (fun a => (s a : ℝ)/n) lam (cavityRationalMass_positive s hs hn)
          (cavityRationalMass_sum s hsum hn) p r) t-cavityStrictUniformPath p r t) ∂pathMeasure)
        atTop (𝓝 0)) ∧
      ∀ ε > 0, ∀ᶠ r in atTop,
        constrainedBlockValue Cset (cavityStrictUniformField
          (fun a => (s a : ℝ)/n) lam (cavityRationalMass_positive s hs hn)
          (cavityRationalMass_sum s hsum hn) p r)+
        fieldPairing (cavityStrictUniformPath p r) (cavityStrictUniformField
          (fun a => (s a : ℝ)/n) lam (cavityRationalMass_positive s hs hn)
          (cavityRationalMass_sum s hsum hn) p r)/2+
        spectralFunctional (finiteR (fun a => (s a : ℝ)/n) lam
          (cavityRationalMass_positive s hs hn) (cavityRationalMass_sum s hsum hn))
          (cavityStrictUniformPath p r)-
        (n : ℝ)⁻¹*(affineRestrictedIncrement hm hn s c hsum R hR Cset hCset μ lam u v (ι (φ r))+
          (Real.log Cset.card-n*Real.log 2)) < ε := by
  let d := m*n-n
  let q := d+n+3
  let N := fun r => (∑ a, c a)+(ι r+q)*n
  let ρ := fun j => (s j : ℝ)/n
  have hm0 : 0 < m := by omega
  have hρ j : 0 < ρ j := cavityRationalMass_positive s hs hn j
  have hρsum : ∑ j, ρ j=1 := cavityRationalMass_sum s hsum hn
  obtain ⟨hd,es,a₀,B₀,hcounts,hB₀,hperp⟩ := cavity_rational_auxiliary_geometry hm hn s hs hsum
  let k := fun r => cavityAffineRetained n d s c (ι r)
  let e : (r : ℕ) → (((a : Fin m) × Fin (k r a)) ⊕ Fin d) ≃ Fin (N r) :=
    fun r => cavityPrefixAffineBaseEquiv s c hs hsum a₀ hcounts (ι r)
  let gf := fun r => cavityPrefixAffineFullGroup s c hsum d (ι r)
  let l := fun r j => cavityOrderedStart (cavityAffineCount s c q (ι r+1)) j
  let w := fun r j => l r j+cavityAffineCount s c q (ι r+1) j
  have hN r : 3 ≤ N r := (cavityRationalSize_ge_three n d (ι r) hn).trans (Nat.le_add_left _ _)
  have hNl : Tendsto N atTop atTop := tendsto_atTop_mono (fun _ => Nat.le_add_left _ _)
    ((cavityRationalDimension_tendsto n q hn).comp hι.tendsto_atTop)
  have hk r j : d ≤ k r j := cavityAffineRetained_ge s c hs (ι r) j
  have hdim r j : cavityBaseGroupDimension (k r) a₀ j=cavityAffineCount s c q (ι r) j :=
    cavityAffineBase_dimension s c hs hsum a₀ hcounts (ι r) j
  have hgroups r j : 0 < cavityBaseGroupDimension (k r) a₀ j := by
    rw [hdim]
    exact (cavityRationalCount_positive s hs (by omega) (ι r) j).trans_le (Nat.le_add_right _ _)
  have hdims j : Tendsto (fun r => cavityBaseGroupDimension (k r) a₀ j) atTop atTop := by
    simpa only [hdim, Function.comp_def] using (cavityAffineCount_tendsto s c hs q j).comp hι.tendsto_atTop
  have hmasslim : Tendsto (fun r j => (cavityBaseGroupDimension (k r) a₀ j : ℝ)/N r) atTop (𝓝 ρ) := by
    apply tendsto_pi_nhds.mpr
    intro j
    have hh := (cavityAffineCount_ratio s c hn (q := q) (by omega) j).comp hι.tendsto_atTop
    simpa only [hdim, N, cavityAffineSize, Nat.add_comm, Function.comp_def] using hh
  have hc : 0 < (1:ℝ)/(n+∑ a, c a : ℕ) := by
    apply div_pos zero_lt_one
    exact_mod_cast (show 0 < n+∑ a, c a by omega)
  have hfrac r j : (1:ℝ)/(n+∑ a, c a : ℕ) ≤ (cavityBaseGroupDimension (k r) a₀ j : ℝ)/N r := by
    rw [hdim]
    simpa only [N, cavityAffineSize, Nat.add_comm] using
      cavityAffineMass_lower s c hs hn (q := q) (by omega) (ι r) j
  have hwindow r j i : gf r i=j ↔ l r j ≤ i.val ∧ i.val < w r j :=
    cavityOrderedGroup_window _ _ j i
  have hln r j : l r j+n ≤ w r j :=
    cavityAffineFullWindow_size s c hs (by omega) (ι r) j
  have hw r j : w r j ≤ N r+n :=
    cavityOrderedStart_add_le (cavityAffineCount s c q (ι r+1))
      (cavityPrefixAffineFull_sum s c hsum q (ι r)) j ((cavityRationalCount_positive s hs (by omega) (ι r+1) j).trans_le (Nat.le_add_right _ _))
  have hl j : Tendsto (fun r => (l r j : ℝ)/(N r+n)) atTop
      (𝓝 ((cavityOrderedStart s j : ℝ)/n)) := by
    simpa only [l, N, cavityAffineSize, Function.comp_def, Nat.add_comm] using
      (cavityAffineFullStart_ratio s c hn (q := q) (by omega) j).comp hι.tendsto_atTop
  have hwlim j : Tendsto (fun r => (w r j : ℝ)/(N r+n)) atTop
      (𝓝 ((cavityOrderedStart s j+s j : ℝ)/n)) := by
    simpa only [w, l, N, cavityAffineSize, Function.comp_def, Nat.add_comm, Nat.cast_add, add_comm] using
      (cavityAffineFullEnd_ratio s c hn (q := q) (by omega) j).comp hι.tendsto_atTop
  have hK r : 2≤ι r+q := by dsimp only [q]; omega
  let θ : Measure (LabeledTree 0) := labeledCascadeLaw 0 (fun _ => 1)
  let : ∀ r, IsProbabilityMeasure (μ (N r+n)) := fun _ => inferInstance
  let : ∀ r, (μ (N r+n)).IsMulRightInvariant := fun _ => inferInstance
  let : ∀ r, IsProbabilityMeasure (μ (N r)) := fun _ => inferInstance
  let : ∀ r, (μ (N r)).IsMulRightInvariant := fun _ => inferInstance
  have HH := offset_window_minimum_trial_witness hhaar hgauss hpub (fun r => ι r+q) hK
    ((tendsto_add_atTop_nat q).comp hι.tendsto_atTop) R hR Cset hCset
    (fun r => (show 0<(∑ a, c a)+(ι r+q)*n from by
      simpa only [N, cavityPrefixAffineSize, q, d] using
        (lt_of_lt_of_le (by norm_num : 0<3) (hN r)))) hNl hN gf k
    (fun r => cavityPrefixAffineRetainedEquiv s c hs hsum d (ι r)) e es B₀ a₀ hk
    (fun r a => μ (cavityBaseGroupDimension (k r) a₀ a)) l w hwindow hln hw
    (fun r => μ (N r+n)) (fun r => μ (N r)) (fun _ => θ) lam (fun r => v (ι r)) (fun r => hv (ι r))
    (fun r => u (ι r)) (fun r => hu (ι r)) (by
      intro r u' v' hu' hv'
      have hh := hmin (ι r) u' v' hu' hv'
      have heq (i : Fin (N r)) :
          ((cavityBaseGroupEquiv (k r) (e r) a₀).symm i).1=
            cavityAffineLabel hm0 s c hsum (N r) i :=
        cavityPrefixAffineBase_canonical_label hm0 s c hs hsum hn a₀ hcounts (ι r) i
      simp_rw [heq]
      exact hh)
    hd hn hB₀ ρ hρ hρsum (fun a => (cavityOrderedStart s a : ℝ)/n)
    (fun a => (cavityOrderedStart s a+s a : ℝ)/n)
    (funext fun a => (cavityRationalMass_difference s a).symm)
    (fun a => (cavityAffineEnd_tendsto s c hs q a).comp
      ((tendsto_add_atTop_nat 1).comp hι.tendsto_atTop))
    (fun a => (cavityAffineStart_alternative s c hs q a).imp
      (fun ha r => ha (ι r+1))
      (fun ha => ha.comp ((tendsto_add_atTop_nat 1).comp hι.tendsto_atTop)))
    (fun a => by simpa only [N, cavityPrefixAffineSize, Nat.cast_add, q, d] using hl a)
    (fun a => by simpa only [N, cavityPrefixAffineSize, Nat.cast_add, q, d] using hwlim a)
    hperp hgroups hdims hc hfrac hmasslim amax hmax s
    (cavityRationalCount_le_total s hsum) hcounts (fun a => by dsimp only [ρ]; field_simp)
  obtain ⟨p,φ,hφ,hself,htrial⟩ := HH
  refine ⟨p,φ,hφ,hself,?_⟩
  intro ε hε
  filter_upwards [htrial ε hε] with r hr
  have hf : gf (φ r)=cavityAffineLabel hm0 s c hsum (N (φ r)+n) :=
    cavityPrefixAffineFullGroup_eq hm0 s c hsum hn d (ι (φ r))
  have hb' (i : Fin (N (φ r))) :
      Sum.elim (fun w => w.1) a₀ ((e (φ r)).symm i)=cavityAffineLabel hm0 s c hsum (N (φ r)) i :=
    cavityPrefixAffineBase_label hm0 s c hs hsum hn a₀ hcounts (ι (φ r)) i
  have hp : cavityBaseGroup (k (φ r)) (e (φ r)) a₀=
      cavitySpectralGroup (cavityAffineLabel hm0 s c hsum (N (φ r))) :=
    cavityPrefixAffineBase_partition hm0 s c hs hsum hn a₀ hcounts (ι (φ r))
  have heig : (fun i => lam (Sum.elim (fun w => w.1) a₀ ((e (φ r)).symm i))) =
      (fun i => lam (cavityAffineLabel hm0 s c hsum (N (φ r)) i)) :=
    funext fun i => congrArg lam (hb' i)
  rw [hf,hp,heig] at hr
  exact hr

end InvariantIsing

end

end OAI
