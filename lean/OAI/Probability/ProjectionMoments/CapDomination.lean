import OAI.Probability.ProjectionMoments.WeightedCover

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments

theorem positive_cap_domination :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 32 ≤ d →
      let k := d/16
      let α : ℝ := ((d:ℝ)-1)/2
      ∀ (c : EuclideanSpace ℝ (Fin d)), ‖c‖ = 1 →
      ∀ r : ℝ, 0 < r → r ≤ 2 →
      ∀ K : (Fin k → EuclideanSpace ℝ (Fin d)) × Label k → ℝ≥0∞,
      Measurable K → (∀ z, K z ≤ 1) →
      ∃ D : CapDictionary c r α, ∃ a : D.I → ℝ,
        (∀ i, 0 ≤ a i) ∧ Summable (fun i => a i*(r/D.radius i)^α) ∧
        (∑' i, a i*(r/D.radius i)^α) ≤ Real.exp (C*d)*(capReference K c r).toReal^(1-1/(k:ℝ)) ∧
        (capMeasure c r).withDensity (capKernelValue K) ≤
          Measure.sum (fun i => ENNReal.ofReal (a i) • capMeasure (D.center i) (D.radius i)) ∧
        (Measure.sum (fun i => ENNReal.ofReal (a i) • capMeasure (D.center i) (D.radius i))) Set.univ < ∞ := by
  obtain ⟨C,hC,hdual⟩ := cap_dual_estimate
  refine ⟨C,hC,?_⟩
  intro d hd k α c hc r hr hr2 K hK hK1
  let : NeZero d := ⟨by omega⟩
  have hdR : (32:ℝ) ≤ d := by exact_mod_cast hd
  have hα : 1 ≤ α := by dsimp [α]; linarith
  obtain ⟨D⟩ := exists_capDictionary hc hr hα
  let := D.countable
  let : IsProbabilityMeasure (capMeasure c r) := capMeasure_probability hc hr hr2
  let P : D.I → Measure (EuclideanSpace ℝ (Fin d)) := fun i => capMeasure (D.center i) (D.radius i)
  let (i : D.I) : IsProbabilityMeasure (P i) :=
    capMeasure_probability (D.center_norm i) (D.radius_pos i) ((D.radius_le i).trans hr2)
  let b : D.I → ℝ := fun i => (r/D.radius i)^α
  have hb : ∀ i, 1 ≤ b i := fun i => Real.one_le_rpow
    ((one_le_div (D.radius_pos i)).mpr (D.radius_le i)) (zero_le_one.trans hα)
  let μ := (capMeasure c r).withDensity (capKernelValue K)
  let : IsFiniteMeasure μ := isFiniteMeasure_withDensity (ne_of_lt
    ((lintegral_mono (capKernelValue_le_one hK1)).trans_lt (by simp)))
  let B := Real.exp (C*d)*(capReference K c r).toReal^(1-1/(k:ℝ))
  have hkR : (1:ℝ) < k := by
    have hk : 2 ≤ k := by dsimp [k]; omega
    exact_mod_cast (show 1 < k by omega)
  have hθ : 0 ≤ 1-1/(k:ℝ) := by
    have hpq := Real.HolderConjugate.conjExponent hkR
    rw [one_div,hpq.one_sub_inv]
    exact inv_nonneg.mpr hpq.symm.pos.le
  have hqtop : capReference K c r ≠ ∞ := ne_of_lt ((capReference_le_one hK1 c r).trans_lt (by simp))
  have hB : ENNReal.ofReal B = ENNReal.ofReal (Real.exp (C*d))* (capReference K c r)^(1-1/(k:ℝ)) := by
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hθ,
      ENNReal.ofReal_toReal hqtop]
  have htest : ∀ h : EuclideanSpace ℝ (Fin d) → ℝ≥0∞, Measurable h →
      (∃ H : ℝ≥0, ∀ x, h x ≤ H) →
      (∀ i, ∫⁻ x, h x ∂P i ≤ ENNReal.ofReal (b i)) → ∫⁻ x, h x ∂μ ≤ ENNReal.ofReal B := by
    intro h hh _ hhD
    rw [hB,lintegral_withDensity_eq_lintegral_mul _ (measurable_capKernelValue hK) hh]
    simp only [Pi.mul_apply]
    simpa only [mul_comm] using hdual d hd c hc r hr hr2 D K hK hK1 h hh hhD
  obtain ⟨a,ha,has,hcost,hdom⟩ := Weighted.measure_domination_nonneg μ P hb D.proper
    (show 0 ≤ B by positivity) htest
  refine ⟨D,a,ha,has,hcost,hdom,?_⟩
  rw [Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply,measure_univ,smul_eq_mul,mul_one]
  have has' : Summable a := Summable.of_nonneg_of_le ha
    (fun i => by simpa using mul_le_mul_of_nonneg_left (hb i) (ha i)) has
  rw [← ENNReal.ofReal_tsum_of_nonneg ha has']
  exact ENNReal.ofReal_lt_top

lemma capReference_sum_le_one {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {k : ℕ} {J : Type*} [Fintype J]
    (K : J → (Fin k → E) × Label k → ℝ≥0∞) (hK : ∀ j, Measurable (K j))
    (hKsum : ∀ z, ∑ j, K j z ≤ 1) (c : E) (r : ℝ) : ∑ j, capReference (K j) c r ≤ 1 := by
  classical
  simp only [capReference]
  rw [← lintegral_finsetSum _ (fun j _ => by fun_prop)]
  calc
    _ = ∫⁻ X, ∫⁻ z, ∑ j, K j (X,capReferenceLabel c r X z) ∂unitBallLaw k
        ∂Measure.pi (fun _ => stdGaussian E) := by
      apply lintegral_congr
      intro X
      exact (lintegral_finsetSum _ (fun j _ => by fun_prop)).symm
    _ ≤ ∫⁻ X, ∫⁻ z : Label k, (1 : ℝ≥0∞) ∂unitBallLaw k
        ∂Measure.pi (fun _ : Fin k => stdGaussian E) :=
      lintegral_mono (fun X => lintegral_mono (fun z => hKsum _))
    _ = 1 := by simp

theorem positive_family_cap_domination :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 32 ≤ d →
      let k := d/16
      let α : ℝ := ((d:ℝ)-1)/2
      ∀ (c : EuclideanSpace ℝ (Fin d)), ‖c‖ = 1 →
      ∀ r : ℝ, 0 < r → r ≤ 2 → ∀ N : ℕ,
      ∀ K : Fin N → (Fin k → EuclideanSpace ℝ (Fin d)) × Label k → ℝ≥0∞,
      (∀ j, Measurable (K j)) → (∀ z, ∑ j, K j z ≤ 1) →
      (∑ j, capReference (K j) c r) ≤ 1 ∧
      ∀ j, ∃ D : CapDictionary c r α, ∃ a : D.I → ℝ,
        (∀ i, 0 ≤ a i) ∧ Summable (fun i => a i*(r/D.radius i)^α) ∧
        (∑' i, a i*(r/D.radius i)^α) ≤ Real.exp (C*d)*(capReference (K j) c r).toReal^(1-1/(k:ℝ)) ∧
        (capMeasure c r).withDensity (capKernelValue (K j)) ≤
          Measure.sum (fun i => ENNReal.ofReal (a i) • capMeasure (D.center i) (D.radius i)) ∧
        (Measure.sum (fun i => ENNReal.ofReal (a i) • capMeasure (D.center i) (D.radius i))) Set.univ < ∞ := by
  obtain ⟨C,hC,h⟩ := positive_cap_domination
  refine ⟨C,hC,?_⟩
  intro d hd k α c hc r hr hr2 N K hK hKsum
  refine ⟨capReference_sum_le_one K hK hKsum c r,?_⟩
  intro j
  apply h d hd c hc r hr hr2 (K j) (hK j)
  intro z
  exact (Finset.single_le_sum (fun i _ => bot_le) (Finset.mem_univ j)).trans (hKsum z)

end ProjectionMoments

end

end OAI
