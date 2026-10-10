import OAI.Geometry.SurfaceImmersion.Correction.ChartedCombinedMean

namespace OAI

/-! Value and finite-loss difference bounds for the actual combined mean
of a free mode in an arbitrary permitted phase chart. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData
open PhaseMean RealModes WeightedEstimates
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0}
    (c : PolynomialSolveData P ε G hG φ K τ s)

theorem combined_mean_bounds {Q : Set LowJet} (hQ : IsCompact Q) (hQO : Q ⊆ c.O)
    (q m : ℕ) (B F A N : ℝ) (hB : 1 ≤ B) (hF : 0 ≤ F) (hA : 0 ≤ A) (hN : 0 ≤ N)
    (hτ : 0 < τ) (hs : 0 < (s : ℝ)) (hτs : τ ≤ s) (hs1 : s ≤ 1)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hsmall : τ / s + ε / τ ^ tensorLoss P ≤ 1)
    (hGQ : Set.MapsTo (lowJet G) c.U Q)
    (hGb : WeightedBound c.U s (m + tensorOrder P) B (lowJet G))
    (hφb : ∀ v, WeightedBound c.U s (m + tensorOrder P) F
      (fun x => fderiv ℝ φ x (coordinateVector v)))
    (hn : WeightedBound c.e.target s
      (m + tensorOrder P + 1 + (q + 1) * (tensorOrder P + 1)) N (freeNormal c.realMap)) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ δ : ℝ, 0 < δ →
      ∀ (b d : SupportedField (F := ℝ) c.chartCompact) (z : ℝ), 0 ≤ z →
      supportedWeightedSeminorm c.chartCompact s
        (m + tensorOrder P + 1 + (q + 1) * (tensorOrder P + 1)) b ≤ A →
      supportedWeightedSeminorm c.chartCompact s
        (m + tensorOrder P + 1 + (q + 1) * (tensorOrder P + 1)) d ≤ A →
      supportedWeightedSeminorm c.chartCompact s
        (m + tensorOrder P + 1 + (q + 1) * (tensorOrder P + 1)) (b - d) ≤ A * z →
      WeightedBound Set.univ s m ((τ / s + ε / τ ^ tensorLoss P) * E) (c.combinedMeanField δ q b) ∧
      WeightedBound Set.univ s m ((τ / s + ε / τ ^ tensorLoss P) * (2 * E) * z)
        (fun x => c.combinedMeanField δ q b x - c.combinedMeanField δ q d x) := by
  have ho (k : Fin 3) : order (P k) ≤ tensorOrder P :=
    Finset.le_sup (f := fun i => order (P i)) (Finset.mem_univ k)
  have hi (k : Fin 3) : m + order (P k) + (q + 1) * (tensorOrder P + 1) ≤
      m + tensorOrder P + 1 + (q + 1) * (tensorOrder P + 1) := by have := ho k; omega
  have hm : m + 1 + (q + 1) * (tensorOrder P + 1) ≤
      m + tensorOrder P + 1 + (q + 1) * (tensorOrder P + 1) := by omega
  have hex (k : Fin 3) := c.polynomial_mean_bounds hQ hQO k q m B F A N hB hF hA hN
    hτ hs hτs hs1 hε hε1 hsmall hGQ (hGb.mono_order (Nat.add_le_add_left (ho k) m))
    (fun v => (hφb v).mono_order (Nat.add_le_add_left (ho k) m)) (hn.mono_order (hi k))
  choose E hE he using hex
  let T := tensorChartBudget m (c.J m) (c.J (m + 1))
  let M := normalizedMeanBudget (tensorOrder P) c.C c.D q m N
  have hT : 0 ≤ T := tensorChartBudget_nonneg m (zero_le_one.trans (c.oneLEJ m))
    (zero_le_one.trans (c.oneLEJ (m + 1)))
  have hM : 0 ≤ M := normalizedMeanBudget_nonneg (tensorOrder P) c.C c.D c.nonnegC q m N
  have hsum : 0 ≤ ∑ k, E k := Finset.sum_nonneg (fun k _ => hE k)
  refine ⟨T * M * A ^ 2 + ∑ k, E k, by positivity, ?_⟩
  intro δ hδ b d z hz hb hd hbd
  let η := τ / s + ε / τ ^ tensorLoss P
  have hη : 0 ≤ η := add_nonneg (div_nonneg hτ.le hs.le) (div_nonneg hε (pow_nonneg hτ.le _))
  have hp (k : Fin 3) := he k δ hδ b d z hz
    ((supportedWeightedSeminorm_mono s (hi k) b).trans hb)
    ((supportedWeightedSeminorm_mono s (hi k) d).trans hd)
    ((supportedWeightedSeminorm_mono s (hi k) (b - d)).trans hbd)
  have hle (k : Fin 3) : E k ≤ ∑ j, E j :=
    Finset.single_le_sum (fun j _ => hE j) (Finset.mem_univ k)
  have hpv : WeightedBound Set.univ s m (η * ∑ k, E k) (c.polynomialMeanField δ q b) :=
    WeightedBound.pi isOpen_univ.uniqueDiffOn hs (mul_nonneg hη hsum)
      (contDiffOn_pi.mp (c.polynomialMeanField δ q b).contDiff.contDiffOn)
      (fun k => (hp k).1.mono_const (mul_le_mul_of_nonneg_left (hle k) hη))
  have hpd : WeightedBound Set.univ s m (η * (2 * ∑ k, E k) * z)
      ((c.polynomialMeanField δ q b) - (c.polynomialMeanField δ q d)) := by
    apply WeightedBound.pi isOpen_univ.uniqueDiffOn hs (by positivity)
      (contDiffOn_pi.mp ((c.polynomialMeanField δ q b).contDiff.sub
        (c.polynomialMeanField δ q d).contDiff).contDiffOn)
    intro k
    exact (hp k).2.mono_const (by gcongr; exact hle k)
  have hpvc := weightedBound_comp_isometry planeCoordinateIsometry.symm
    (c.polynomialMeanField δ q b).contDiff hpv
  have hpdc := weightedBound_comp_isometry planeCoordinateIsometry.symm
    ((c.polynomialMeanField δ q b).contDiff.sub (c.polynomialMeanField δ q d).contDiff) hpd
  have hmv := c.metricMeanField_bound hδ hτ hs hτs hs1 hε hsmall q m hA hN (hn.mono_order hm)
    b ((supportedWeightedSeminorm_mono s hm b).trans hb)
  have hmd := c.metricMeanField_difference_bound hδ hτ hs hτs hs1 hε hsmall q m hA hN
    (mul_nonneg hA hz) (hn.mono_order hm) b d
    ((supportedWeightedSeminorm_mono s hm b).trans hb)
    ((supportedWeightedSeminorm_mono s hm d).trans hd)
    ((supportedWeightedSeminorm_mono s hm (b - d)).trans hbd)
  constructor
  · have hh := hmv.add isOpen_univ.uniqueDiffOn s.coe_nonneg
      (c.metricMeanField δ q b).contDiff.contDiffOn
      ((c.polynomialMeanField δ q b).contDiff.comp planeCoordinateIsometry.symm.contDiff).contDiffOn hpvc
    convert hh using 1 <;> first | rfl | (dsimp only [T, M, η]; ring)
  · have hh := hmd.add isOpen_univ.uniqueDiffOn s.coe_nonneg
      ((c.metricMeanField δ q b).contDiff.sub (c.metricMeanField δ q d).contDiff).contDiffOn
      (((c.polynomialMeanField δ q b).contDiff.sub (c.polynomialMeanField δ q d).contDiff).comp
        planeCoordinateIsometry.symm.contDiff).contDiffOn hpdc
    apply (hh.congr (fun x _ => show
      c.combinedMeanField δ q b x - c.combinedMeanField δ q d x = _ by
        change (c.metricMeanField δ q b x + c.polynomialMeanField δ q b (planeCoordinateIsometry.symm x)) -
          (c.metricMeanField δ q d x + c.polynomialMeanField δ q d (planeCoordinateIsometry.symm x)) =
          (c.metricMeanField δ q b x - c.metricMeanField δ q d x) +
          (c.polynomialMeanField δ q b (planeCoordinateIsometry.symm x) -
            c.polynomialMeanField δ q d (planeCoordinateIsometry.symm x))
        abel)).mono_const
    apply le_of_eq
    dsimp only [T, M, η]
    ring

end ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

end

end OAI
