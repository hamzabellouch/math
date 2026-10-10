import OAI.Combinatorics.Progressions.Sampling.PreparedRelativeEndpointForecastBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem exists_preparedFiniteForwardActualPacket_budget
    (depth m A Ccontrol Cchild : ℕ) (stageCountConstant : ℕ → ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (x gainLog stageLog : ℝ),
      0 ≤ x → gainLog ∈ Set.Icc 0 x → stageLog ∈ Set.Icc 0 x →
      ∀ n : ℕ, n ≤ depth → ∀ M nX Jalloc : ℕ,
      ∀ {Pdim pRadius Qstride PF Pchart childLog : ℝ},
      let b := preparedFiniteForwardParameter A stageCountConstant n x
      let w := preparedFiniteForwardWork A stageCountConstant n x
      let u := preparedFiniteForwardModelPrecision A stageCountConstant n x gainLog stageLog
      let cost := (b + Ccontrol) ^ Ccontrol
      let Edata := 2 * u + 4 * w + 12
      allocatedComparisonDimension m
        (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ≤ b →
      ((nX + m * M : ℕ) : ℝ) ≤ b →
      Pdim ∈ Set.Icc 0 b → pRadius ∈ Set.Icc 0 b → Qstride ∈ Set.Icc 0 b →
      PF ∈ Set.Icc 0 b → Pchart ∈ Set.Icc 0 b →
      childLog ∈ Set.Icc 0 ((b + Cchild) ^ Cchild) →
      let period := preparedConcreteSlicedForecastPeriodLog m M nX Jalloc
        Pdim cost pRadius gainLog Qstride Pchart childLog Edata
      let native := preparedConcreteSlicedForecastNativeLog m M nX Jalloc
        Pdim cost pRadius gainLog Qstride PF Pchart childLog Edata
      let mass := preparedConcreteSlicedForecastMassLog m M nX Jalloc
        Pdim cost pRadius gainLog Qstride Pchart childLog Edata
      period ∈ Set.Icc 0 ((x + C) ^ C) ∧
      native ∈ Set.Icc 0 ((x + C) ^ C) ∧
      mass ∈ Set.Icc 0 ((x + C) ^ C) ∧
      ∀ budget : ℝ, 0 ≤ budget →
        actualForecastDataModelRequired budget native mass u w ∈
          Set.Icc 0 (budget + (x + C) ^ C) := by
  obtain ⟨B, _, hstage⟩ := exists_preparedFiniteForwardStage_budget depth A stageCountConstant
  obtain ⟨Cp, _, hlogs⟩ := exists_preparedConcreteSlicedForecastPacketLog_budget m
  let X : Polynomial ℕ := Polynomial.X
  let T : Polynomial ℕ := (X + Polynomial.C B) ^ B
  let R : Polynomial ℕ := 7 * T + (T + Polynomial.C Ccontrol) ^ Ccontrol +
    (T + Polynomial.C Cchild) ^ Cchild + 13
  let Packet : Polynomial ℕ := (R + Polynomial.C Cp) ^ Cp
  let Q : Polynomial ℕ := 4 * Packet + 9 * T + 55
  obtain ⟨C, hC, hpoly⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro x gainLog stageLog hx hg hs n hn M nX Jalloc Pdim pRadius Qstride PF Pchart childLog
    b w u cost Edata hDbase hDmod hPdim hRadius hStride hPF hChart hChild period native mass
  let t : ℝ := (x + B) ^ B
  let costBound : ℝ := (t + Ccontrol) ^ Ccontrol
  let childBound : ℝ := (t + Cchild) ^ Cchild
  let r : ℝ := 7 * t + costBound + childBound + 13
  let packet : ℝ := (r + Cp) ^ Cp
  obtain ⟨hbase, hwork, _, _, _, _, _, hmodel, _⟩ := hstage x gainLog stageLog hx hg hs n hn
  change b ∈ Set.Icc 0 t at hbase
  change w ∈ Set.Icc 0 t at hwork
  change u ∈ Set.Icc 0 t at hmodel
  have ht : 0 ≤ t := hbase.1.trans hbase.2
  have hcostBound : 0 ≤ costBound := by dsimp only [costBound]; positivity
  have hchildBound : 0 ≤ childBound := by dsimp only [childBound]; positivity
  have hr : 0 ≤ r := by dsimp only [r]; positivity
  have htr : t ≤ r := by dsimp only [r]; linarith only [ht, hcostBound, hchildBound]
  have hbr : b ≤ r := hbase.2.trans htr
  have hcostr : costBound ≤ r := by dsimp only [r]; linarith only [ht, hchildBound]
  have hchildr : childBound ≤ r := by dsimp only [r]; linarith only [ht, hcostBound]
  have hEr : 6 * t + 12 ≤ r := by
    dsimp only [r]
    linarith only [ht, hcostBound, hchildBound]
  have hcost0 : 0 ≤ cost := pow_nonneg (add_nonneg hbase.1 (Nat.cast_nonneg _)) _
  have hcost : cost ≤ costBound :=
    pow_le_pow_left₀ (add_nonneg hbase.1 (Nat.cast_nonneg _))
      (add_le_add hbase.2 le_rfl) Ccontrol
  have hchild : childLog ≤ childBound := hChild.2.trans
    (pow_le_pow_left₀ (add_nonneg hbase.1 (Nat.cast_nonneg _))
      (add_le_add hbase.2 le_rfl) Cchild)
  have hE0 : 0 ≤ Edata := by dsimp only [Edata]; linarith only [hmodel.1, hwork.1]
  have hE : Edata ≤ r := by
    apply le_trans _ hEr
    dsimp only [Edata]
    linarith only [hmodel.2, hwork.2]
  have hgain : gainLog ≤ r := hg.2.trans
    ((le_preparedFiniteForwardParameter A stageCountConstant n hx).trans hbr)
  obtain ⟨hperiod, hnative, hmass⟩ := hlogs M nX Jalloc hr
    (hDbase.trans hbr) (hDmod.trans hbr)
    ⟨hPdim.1, hPdim.2.trans hbr⟩ ⟨hcost0, hcost.trans hcostr⟩
    ⟨hRadius.1, hRadius.2.trans hbr⟩ ⟨hg.1, hgain⟩
    ⟨hStride.1, hStride.2.trans hbr⟩ ⟨hPF.1, hPF.2.trans hbr⟩
    ⟨hChart.1, hChart.2.trans hbr⟩ ⟨hChild.1, hchild.trans hchildr⟩ ⟨hE0, hE⟩
  change period ∈ Set.Icc 0 packet at hperiod
  change native ∈ Set.Icc 0 packet at hnative
  change mass ∈ Set.Icc 0 packet at hmass
  have hpacket0 : 0 ≤ packet := hperiod.1.trans hperiod.2
  have hfinal : 4 * packet + 9 * t + 55 ≤ (x + C) ^ C := by
    simpa [Q, Packet, R, T, X, packet, r, t, costBound, childBound,
      Polynomial.eval₂_pow] using hpoly x hx
  have hraise : packet ≤ (x + C) ^ C := by linarith only [hfinal, hpacket0, ht]
  refine ⟨⟨hperiod.1, hperiod.2.trans hraise⟩,
    ⟨hnative.1, hnative.2.trans hraise⟩, ⟨hmass.1, hmass.2.trans hraise⟩, ?_⟩
  intro budget hbudget
  have hrequired := actualForecastDataModelRequired_sum_bound
    hbudget hnative.1 hmass.1 hmodel.1 hwork.1
  exact ⟨hrequired.1, by
    linarith only [hrequired.2, hnative.2, hmass.2, hmodel.2, hwork.2, hfinal]⟩

end Erdos3.VectorPolynomial

end

end OAI
