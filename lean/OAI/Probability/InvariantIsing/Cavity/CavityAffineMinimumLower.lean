import OAI.Probability.InvariantIsing.Cavity.CavityAffineFamily
import OAI.Probability.InvariantIsing.Cavity.CavityAffineWindows
import OAI.Probability.InvariantIsing.Cavity.CavityRationalAuxiliary
import OAI.Probability.InvariantIsing.Cavity.CavityWindowMinimumLower

namespace OAI

/-! The fixed-residue rational finite-spectrum cavity increment bound with all finite
window, axis and limiting-complement geometry constructed explicitly. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators

namespace InvariantIsing

theorem cavity_affine_minimum_lower
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandFieldPairInput)
    {m n : ℕ} (hm : 2 ≤ m) (hn : 0 < n) (s c : Fin m → ℕ)
    (hs : ∀ a, 0 < s a) (hsum : ∑ a, s a=n)
    (depth : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents depth b)
    (μ : (N : ℕ) → Measure (Orthogonal N)) [∀ N, IsProbabilityMeasure (μ N)]
    [∀ N, (μ N).IsMulRightInvariant]
    (lam : Fin m → ℝ) (a : Fin m) (ha : ∀ j, lam j ≤ lam a) (R : Rotation n)
    (u : (r : ℕ) → Fin (cavityAffineSize n (m*n-n+n+3) c r) → ℝ) (v : ℕ → Fin m → ℝ)
    (hu : ∀ r j, u r j ∈ Set.Icc (1 : ℝ) 2) (hv : ∀ r j, v r j ∈ Set.Icc (1 : ℝ) 2)
    (hmin : ∀ r u' v', (∀ j, u' j ∈ Set.Icc (1 : ℝ) 2) →
      (∀ j, v' j ∈ Set.Icc (1 : ℝ) 2) →
      let N := cavityAffineSize n (m*n-n+n+3) c r
      let g := cavityAffineLabel (by omega : 0 < m) s c hsum N
      tensorPerturbationObjective (cavityOrientedBaseLaw (by
        have := cavityAffineSize_ge_three n (m*n-n) c r hn; omega) (μ N))
        (fun i => lam (g i)) (fun _ => 0) (cavitySpectralGroup g) 1 depth b
        (fun _ => 0) (u r) (v r) ≤
      tensorPerturbationObjective (cavityOrientedBaseLaw (by
        have := cavityAffineSize_ge_three n (m*n-n) c r hn; omega) (μ N))
        (fun i => lam (g i)) (fun _ => 0) (cavitySpectralGroup g) 1 depth b
        (fun _ => 0) u' v') :
    let N := cavityAffineSize n (m*n-n+n+3) c
    let g := fun M => cavityAffineLabel (by omega : 0 < m) s c hsum M
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
  let k := cavityAffineRetained n d s c
  let e := cavityAffineBaseEquiv s c hs hsum a₀ hcounts
  let gf := cavityAffineFullGroup s c hsum d
  let l := fun r j => cavityOrderedStart (cavityAffineCount s c q (r+1)) j
  let w := fun r j => l r j+cavityAffineCount s c q (r+1) j
  have hN r : 3 ≤ N r := cavityAffineSize_ge_three n d c r hn
  have hNl : Tendsto N atTop atTop := cavityAffineSize_tendsto n q c hn
  have hk r j : d ≤ k r j := cavityAffineRetained_ge s c hs r j
  have hdim r j : cavityBaseGroupDimension (k r) a₀ j=cavityAffineCount s c q r j :=
    cavityAffineBase_dimension s c hs hsum a₀ hcounts r j
  have hgroups r j : 0 < cavityBaseGroupDimension (k r) a₀ j := by
    rw [hdim]
    exact (cavityRationalCount_positive s hs (by omega) r j).trans_le (Nat.le_add_right _ _)
  have hdims j : Tendsto (fun r => cavityBaseGroupDimension (k r) a₀ j) atTop atTop := by
    simpa only [hdim] using cavityAffineCount_tendsto s c hs q j
  have hmasslim : Tendsto (fun r j => (cavityBaseGroupDimension (k r) a₀ j : ℝ)/N r) atTop (𝓝 ρ) := by
    apply tendsto_pi_nhds.mpr
    intro j
    simpa only [hdim] using cavityAffineCount_ratio s c hn (q := q) (by omega) j
  have hc : 0 < (1:ℝ)/(n+∑ a, c a : ℕ) := by
    apply div_pos zero_lt_one
    exact_mod_cast (show 0 < n+∑ a, c a by omega)
  have hfrac r j : (1:ℝ)/(n+∑ a, c a : ℕ) ≤
      (cavityBaseGroupDimension (k r) a₀ j : ℝ)/N r := by
    rw [hdim]
    exact cavityAffineMass_lower s c hs hn (by omega) r j
  have hwindow r j i : gf r i=j ↔ l r j ≤ i.val ∧ i.val < w r j :=
    cavityOrderedGroup_window _ _ j i
  have hln r j : l r j+n ≤ w r j :=
    cavityAffineFullWindow_size s c hs (by omega) r j
  have hw r j : w r j ≤ N r+n :=
    cavityOrderedStart_add_le (cavityAffineCount s c q (r+1))
      (cavityAffineFull_sum s c hsum q r) j ((cavityRationalCount_positive s hs (by omega) (r+1) j).trans_le (Nat.le_add_right _ _))
  have hl j : Tendsto (fun r => (l r j : ℝ)/(N r+n)) atTop
      (𝓝 ((cavityOrderedStart s j : ℝ)/n)) :=
    cavityAffineFullStart_ratio s c hn (by omega) j
  have hwlim j : Tendsto (fun r => (w r j : ℝ)/(N r+n)) atTop
      (𝓝 ((cavityOrderedStart s j+s j : ℝ)/n)) := by
    simpa only [w, l, N, Nat.cast_add] using cavityAffineFullEnd_ratio s c hn (by omega : 0 < q) j
  have HH := cavity_window_minimum_variational_lower hhaar hgauss hpub N depth b hb hN hNl
    gf k (cavityAffineRetainedEquiv s c hs hsum d) e es B₀ a₀ hk
    (fun r j => μ (cavityBaseGroupDimension (k r) a₀ j)) l w hwindow hln hw
    (fun r => μ (N r+n)) (fun r => μ (N r)) lam v hv u hu (by
      intro r u' v' hu' hv'
      have hh := hmin r u' v' hu' hv'
      have heq (i : Fin (N r)) :
          ((cavityBaseGroupEquiv (k r) (e r) a₀).symm i).1=
            cavityAffineLabel hm0 s c hsum (N r) i :=
        cavityAffineBase_canonical_label hm0 s c hs hsum hn a₀ hcounts r i
      simp_rw [heq]
      exact hh)
    hd hn hB₀
    ρ hρ hρsum (fun j => (cavityOrderedStart s j : ℝ)/n)
    (fun j => (cavityOrderedStart s j+s j : ℝ)/n)
    (funext fun j => (cavityRationalMass_difference s j).symm)
    (fun j => (cavityAffineEnd_tendsto s c hs q j).comp (tendsto_add_atTop_nat 1)) (fun j => (cavityAffineStart_alternative s c hs q j).elim
      (fun h => Or.inl (fun r => h (r+1)))
      (fun h => Or.inr (h.comp (tendsto_add_atTop_nat 1))))
    hl hwlim hperp hgroups hdims hc hfrac hmasslim a ha s
    (cavityRationalCount_le_total s hsum) hcounts (fun _ => by dsimp only [ρ]; field_simp) R
  intro ε hε
  filter_upwards [HH ε hε] with r hr
  have hf : gf r=g (N r+n) := cavityAffineFullGroup_eq hm0 s c hsum hn d r
  have hb' (i : Fin (N r)) : Sum.elim (fun w => w.1) a₀ ((e r).symm i)=g (N r) i :=
    cavityAffineBase_label hm0 s c hs hsum hn a₀ hcounts r i
  have hp : cavityBaseGroup (k r) (e r) a₀=cavitySpectralGroup (g (N r)) :=
    cavityAffineBase_partition hm0 s c hs hsum hn a₀ hcounts r
  have heig : (fun i => lam (Sum.elim (fun w => w.1) a₀ ((e r).symm i))) =
      (fun i => lam (g (N r) i)) := funext fun i => congrArg lam (hb' i)
  rw [hf,hp] at hr
  rw [heig] at hr
  exact hr

end InvariantIsing

end

end OAI
