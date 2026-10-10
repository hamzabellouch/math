import OAI.Probability.InvariantIsing.Cavity.CavityRationalLabelIdentities
import OAI.Probability.InvariantIsing.Cavity.CavityRationalAuxiliary
import OAI.Probability.InvariantIsing.Cavity.CavityWindowMinimumLower

namespace OAI

/-! The rational finite-spectrum cavity increment bound with all finite
window, axis and limiting-complement geometry constructed explicitly. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators

namespace InvariantIsing

theorem cavity_rational_minimum_lower
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandFieldPairInput)
    {m n : ℕ} (hm : 2 ≤ m) (hn : 0 < n) (s : Fin m → ℕ)
    (hs : ∀ a, 0 < s a) (hsum : ∑ a, s a=n)
    (depth : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents depth b)
    (μ : (N : ℕ) → Measure (Orthogonal N)) [∀ N, IsProbabilityMeasure (μ N)]
    [∀ N, (μ N).IsMulRightInvariant]
    (lam : Fin m → ℝ) (a : Fin m) (ha : ∀ j, lam j ≤ lam a) (R : Rotation n)
    (u : (r : ℕ) → Fin (cavityRationalSize n (m*n-n) r) → ℝ) (v : ℕ → Fin m → ℝ)
    (hu : ∀ r j, u r j ∈ Set.Icc (1 : ℝ) 2) (hv : ∀ r j, v r j ∈ Set.Icc (1 : ℝ) 2)
    (hmin : ∀ r u' v', (∀ j, u' j ∈ Set.Icc (1 : ℝ) 2) →
      (∀ j, v' j ∈ Set.Icc (1 : ℝ) 2) →
      let N := cavityRationalSize n (m*n-n) r
      let g := cavityRationalLabel (by omega : 0 < m) s hsum N
      tensorPerturbationObjective (cavityOrientedBaseLaw (by
        have := cavityRationalSize_ge_three n (m*n-n) r hn; omega) (μ N))
        (fun i => lam (g i)) (fun _ => 0) (cavitySpectralGroup g) 1 depth b
        (fun _ => 0) (u r) (v r) ≤
      tensorPerturbationObjective (cavityOrientedBaseLaw (by
        have := cavityRationalSize_ge_three n (m*n-n) r hn; omega) (μ N))
        (fun i => lam (g i)) (fun _ => 0) (cavitySpectralGroup g) 1 depth b
        (fun _ => 0) u' v') :
    let N := cavityRationalSize n (m*n-n)
    let g := fun M => cavityRationalLabel (by omega : 0 < m) s hsum M
    let θ : Measure (LabeledTree depth) := labeledCascadeLaw depth b
    let Δ := fun r =>
      (∫ z, cavityRotationLogMean z.2
        (diagonalPerturbedEigenvalues (fun i => lam (g (N r+n) i)) (cavitySpectralGroup (g (N r+n))) (v r) 1)
        (cavitySpectralGroup (g (N r+n))) (cavityBaseAmplitude (u r)) z.1 ∂(μ (N r+n)).prod θ) -
      ∫ z, cavityRotationLogMean z.2
        (diagonalPerturbedEigenvalues (fun i => lam (g (N r) i)) (cavitySpectralGroup (g (N r))) (v r) 1)
        (cavitySpectralGroup (g (N r))) (cavityBaseAmplitude (u r)) z.1 ∂(μ (N r)).prod θ
    ∀ ε > 0, ∀ᶠ r in atTop,
      (variationalFunctional (finiteR (fun j => (s j : ℝ)/n) lam
        (cavityRationalMass_positive s hs hn) (cavityRationalMass_sum s hsum hn))).toReal-
        (n : ℝ)⁻¹*Δ r < ε := by
  intro N g θ Δ
  let d := m*n-n
  let q := d+n+3
  let ρ := fun j => (s j : ℝ)/n
  have hm0 : 0 < m := by omega
  have hρ j : 0 < ρ j := cavityRationalMass_positive s hs hn j
  have hρsum : ∑ j, ρ j=1 := cavityRationalMass_sum s hsum hn
  obtain ⟨hd,es,a₀,B₀,hcounts,hB₀,hperp⟩ := cavity_rational_auxiliary_geometry hm hn s hs hsum
  let k := cavityRationalRetained n d s
  let e := cavityRationalBaseEquiv s hs hsum a₀ hcounts
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
  have HH := cavity_window_minimum_variational_lower hhaar hgauss hpub N depth b hb hN hNl
    gf k (cavityRationalRetainedEquiv s hs hsum d) e es B₀ a₀ hk
    (fun r j => μ (cavityBaseGroupDimension (k r) a₀ j)) l w hwindow hln hw
    (fun r => μ (N r+n)) (fun r => μ (N r)) lam v hv u hu (by
      intro r u' v' hu' hv'
      have hh := hmin r u' v' hu' hv'
      have heq (i : Fin (N r)) :
          ((cavityBaseGroupEquiv (k r) (e r) a₀).symm i).1=
            cavityRationalLabel hm0 s hsum (N r) i :=
        cavityRationalBase_canonical_label hm0 s hs hsum hn a₀ hcounts r i
      simp_rw [heq]
      exact hh)
    hd hn hB₀
    ρ hρ hρsum (fun j => (cavityOrderedStart s j : ℝ)/n)
    (fun j => (cavityOrderedStart s j+s j : ℝ)/n)
    (funext fun j => (cavityRationalMass_difference s j).symm)
    (cavityRationalFullEnd_tendsto s hs q) (cavityRationalFullStart_alternative s q)
    hl hwlim hperp hgroups hdims hc hfrac hmasslim a ha s
    (cavityRationalCount_le_total s hsum) hcounts (fun _ => by dsimp only [ρ]; field_simp) R
  intro ε hε
  filter_upwards [HH ε hε] with r hr
  have hf : gf r=g (N r+n) := cavityRationalFullGroup_eq hm0 s hsum hn d r
  have hb' (i : Fin (N r)) : Sum.elim (fun w => w.1) a₀ ((e r).symm i)=g (N r) i :=
    cavityRationalBase_label hm0 s hs hsum hn a₀ hcounts r i
  have hp : cavityBaseGroup (k r) (e r) a₀=cavitySpectralGroup (g (N r)) :=
    cavityRationalBase_partition hm0 s hs hsum hn a₀ hcounts r
  have heig : (fun i => lam (Sum.elim (fun w => w.1) a₀ ((e r).symm i))) =
      (fun i => lam (g (N r) i)) := funext fun i => congrArg lam (hb' i)
  rw [hf,hp] at hr
  rw [heig] at hr
  exact hr

end InvariantIsing

end

end OAI
