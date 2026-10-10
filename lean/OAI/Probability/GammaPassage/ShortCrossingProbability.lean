import OAI.Probability.GammaPassage.ShortCrossingGeometry
import OAI.Probability.GammaPassage.BallTravel

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.IntervalTravelBridge Set Filter MeasureTheory
open scoped Topology
variable {shape rate : ℝ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

/-- Origin-to-endpoint local travel from the actual simultaneous ball event. -/
theorem gamma_origin_local_travel (h : GammaEnvironment shape rate P τ)
    (hshape : 0 < shape) (hrate : 0 < rate) (D η δ : ℝ)
    (hD : 0 < D) (hη : 0 < η) (hδ : 0 < δ) :
    ∀ κ > 0, ∀ᶠ s : ℝ in atTop, ∀ q : Vertex, ‖latticeEmbed q‖ ≤ D*s →
      P.real {ω | ¬LocalTravel (gammaMeanNorm h hshape hrate) η δ s 0 q (fun e => τ e ω)} < κ := by
  let _ := h.probability
  intro κ hκ
  filter_upwards [gamma_ball_travel h hshape hrate D η δ hD hη hδ κ hκ,
    eventually_ge_atTop (0 : ℝ)] with s hb hs
  intro q hq
  have hb0 := hb 0
  simp only [shiftEdge, zero_add, Prod.eta] at hb0
  refine (measureReal_mono (μ := P) (show
    {ω | ¬LocalTravel (gammaMeanNorm h hshape hrate) η δ s 0 q (fun e => τ e ω)} ⊆
    {ω | ¬BallTravel (gammaMeanNorm h hshape hrate) D η δ s (fun e => τ e ω)} from ?_)).trans_lt hb0
  intro ω hω hball
  apply hω
  apply hball 0 q ?_ hq
  simpa only [latticeEmbed_zero, norm_zero] using mul_nonneg hD.le hs

/-- Bounded longitudinal scales use an explicit horizontal path. -/
theorem gamma_bounded_crossing_failure (h : GammaEnvironment shape rate P τ) (hshape : 0 < shape) (hrate : 0 < rate)
    (b m K s N : ℝ) (n : ℤ) (hb : |b| ≤ 1) (hm : 0 ≤ m)
    (hn : 0 ≤ n) (hnN : (n : ℝ) ≤ N) (hns : (n : ℝ) ≤ 8*s) :
    P.real {ω | (fun e => τ e ω) ∉ crossingEvent b m K s n 0} ≤
      Real.exp (-(rate/2)*(K*s-coordinateAllowance shape rate*N)) := by
  let _ := h.probability
  have hallow := coordinateAllowance_pos hshape hrate
  have hsub : {ω | (fun e => τ e ω) ∉ crossingEvent b m K s n 0} ⊆
      {ω | coordinateAllowance shape rate*(n.natAbs : ℝ)+(K*s-coordinateAllowance shape rate*N) ≤ pathCost (fun e => τ e ω) 0 (horizontal n)} := by
    intro ω hbad
    have hc : m*n+K*s ≤ pathCost (fun e => τ e ω) 0 (horizontal n) := by
      by_contra hh
      apply hbad
      refine ⟨0,horizontal n,⟨rfl,?_⟩,?_,lt_of_not_ge hh⟩
      · simp [displacement_horizontal]
      · intro i hi
        exact (mem_rareFastVertices ..).mpr (horizontal_in_crossingRegion b s n hb hn hns i hi)
    have ha : (n.natAbs : ℝ)=(n : ℝ) := by
      have hi : (n.natAbs : ℤ)=n := by omega
      exact (by simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℝ)) hi)
    have hn' : (0 : ℝ) ≤ n := by exact_mod_cast hn
    change coordinateAllowance shape rate*(n.natAbs : ℝ)+(K*s-coordinateAllowance shape rate*N) ≤ pathCost (fun e => τ e ω) 0 (horizontal n)
    rw [ha]
    nlinarith
  exact (measureReal_mono hsub).trans (h.costly_horizontal_excess_probability_real hshape hrate 0 n (K*s-coordinateAllowance shape rate*N))

/-- This is the joint short-crossing limit in gr:characteristic-lengths,
expressed as uniform convergence of the failure probabilities. -/
theorem gamma_short_crossing_failure (h : GammaEnvironment shape rate P τ)
    (hshape : 0 < shape) (hrate : 0 < rate)
    (b K C : ℝ) (hb : |b| ≤ 1) (hK : 0 < K) (hC : 0 < C) :
    ∀ κ > 0, ∀ᶠ s : ℝ in atTop, ∀ n : ℤ, 1 ≤ n → (n : ℝ) ≤ C*s →
      P.real {ω | (fun e => τ e ω) ∉ crossingEvent b ((gammaMeanNorm h hshape hrate) (direction b)) K s n 0} < κ := by
  let _ := h.probability
  let η := K/(4*C)
  let δ := min (1/4) (1/(2*C))
  have hη : 0 < η := by dsimp [η]; positivity
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1/4 := min_le_left _ _
  have hδC : δ*C ≤ 1/2 := by
    have hh := min_le_right (1/4 : ℝ) (1/(2*C))
    have he : δ ≤ (1/2)/C := by
      have heq : (1 : ℝ)/(2*C)=(1/2)/C := by ring
      rw [← heq]
      exact hh
    exact (le_div_iff₀ hC).mp he
  intro κ hκ
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    (gamma_origin_local_travel h hshape hrate 3 η δ (by norm_num) hη hδ κ hκ)
  have htail : ∀ᶠ s : ℝ in atTop, Real.exp (-(rate/2)*(K*s-coordinateAllowance shape rate*N)) < κ := by
    filter_upwards [eventually_ge_atTop ((coordinateAllowance shape rate*N+2*(1-Real.log κ)/rate)/K)] with s hs
    have hh := (div_le_iff₀ hK).mp hs
    rw [← Real.exp_log hκ]
    apply Real.exp_lt_exp.mpr
    have hm := mul_le_mul_of_nonneg_left hh hrate.le
    have hid : rate*(2*(1-Real.log κ)/rate)=2*(1-Real.log κ) := by
      field_simp [hrate.ne']
    nlinarith
  filter_upwards [eventually_ge_atTop (1 : ℝ),eventually_ge_atTop N,
    eventually_ge_atTop ((4*(gammaMeanNorm h hshape hrate) transverseUnit+1)/K),htail] with s hs hsN hsNorm htail
  intro n hn hns
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  by_cases hnN : N ≤ (n : ℝ)
  · have hlt := hN n hnN (sourceEndpoint b n) (by
      simpa only [sub_zero] using sourceEndpoint_distance b n hb hn)
    have hsub : {ω | (fun e => τ e ω) ∉ crossingEvent b ((gammaMeanNorm h hshape hrate) (direction b)) K s n 0} ⊆
        {ω | ¬LocalTravel (gammaMeanNorm h hshape hrate) η δ n 0 (sourceEndpoint b n) (fun e => τ e ω)} := by
      intro ω hbad hgood
      obtain ⟨ds,hd,hcost,hin⟩ := hgood
      apply hbad
      refine ⟨0,ds,⟨rfl,?_⟩,?_,?_⟩
      · simpa [sourceEndpoint] using congrArg Prod.fst hd
      · intro i hi
        exact (mem_rareFastVertices ..).mpr
          (sourceEndpoint_tube_containment b C δ s n hb hs hn hns hδ.le hδ1 hδC (hin i hi))
      · have hNormBound := sourceEndpoint_norm_cost (gammaMeanNorm h hshape hrate) (gammaMeanNorm_laws h hshape hrate) b n (by omega)
        have hηn : η*(n : ℝ) ≤ K*s/4 := by
          dsimp [η]
          calc
            _ ≤ K/(4*C)*(C*s) := mul_le_mul_of_nonneg_left hns hη.le
            _ = _ := by field_simp
        have hh := (div_le_iff₀ hK).mp hsNorm
        simp only [sub_zero] at hcost
        change pathCost (fun e => τ e ω) 0 ds < (gammaMeanNorm h hshape hrate) (direction b)*n+K*s
        linarith [(gammaMeanNorm_laws h hshape hrate).nonneg transverseUnit]
    exact (measureReal_mono hsub).trans_lt hlt
  · exact (gamma_bounded_crossing_failure h hshape hrate b ((gammaMeanNorm h hshape hrate) (direction b)) K s N n hb ((gammaMeanNorm_laws h hshape hrate).nonneg _)
      (by omega) (le_of_not_ge hnN) (by linarith)).trans_lt htail

/-- Equivalent success-probability formulation from eq:gr-short-crossings. -/
theorem gamma_short_crossing_probability (h : GammaEnvironment shape rate P τ)
    (hshape : 0 < shape) (hrate : 0 < rate)
    (b K C : ℝ) (hb : |b| ≤ 1) (hK : 0 < K) (hC : 0 < C) :
    ∀ q < 1, ∀ᶠ s : ℝ in atTop, ∀ n : ℤ, 1 ≤ n → (n : ℝ) ≤ C*s →
      q < P.real {ω | (fun e => τ e ω) ∈ crossingEvent b ((gammaMeanNorm h hshape hrate) (direction b)) K s n 0} := by
  let _ := h.probability
  intro q hq
  filter_upwards [gamma_short_crossing_failure h hshape hrate b K C hb hK hC (1-q) (by linarith)] with s hs
  intro n hn hns
  have hh := hs n hn hns
  have hc := measureReal_compl (μ := P) ((measurableSet_crossingEvent b ((gammaMeanNorm h hshape hrate) (direction b)) K s n 0).preimage
    (Measurable.of_eval h.measurable))
  change P.real {ω | (fun e => τ e ω) ∉ crossingEvent b ((gammaMeanNorm h hshape hrate) (direction b)) K s n 0} = _ at hc
  rw [hc] at hh
  simpa [Set.preimage] using hh

end GammaFPP.CrossingBridge

end OAI
