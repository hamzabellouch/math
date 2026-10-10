import OAI.Probability.FirstPassage.ShortCrossingGeometry

namespace OAI

namespace PlanarFPP
open Set Filter MeasureTheory
open scoped Topology
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem exponential_bounded_crossing_failure (h : ExponentialEnvironment P τ)
    (b m K s N : ℝ) (n : ℤ) (hb : |b| ≤ 1) (hm : 0 ≤ m)
    (hn : 0 ≤ n) (hnN : (n : ℝ) ≤ N) (hns : (n : ℝ) ≤ 8*s) :
    P.real {ω | (fun e => τ e ω) ∉ crossingEvent b m K s n 0} ≤
      Real.exp (-(K*s-4*N)/2) := by
  let _ := h.probability
  have hsub : {ω | (fun e => τ e ω) ∉ crossingEvent b m K s n 0} ⊆
      {ω | 4*(n.natAbs : ℝ)+(K*s-4*N) ≤ pathCost (fun e => τ e ω) 0 (horizontal n)} := by
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
    change 4*(n.natAbs : ℝ)+(K*s-4*N) ≤ pathCost (fun e => τ e ω) 0 (horizontal n)
    rw [ha]
    nlinarith
  exact (measureReal_mono hsub).trans (costly_horizontal_excess_probability_real h 0 n (K*s-4*N))

theorem exponential_short_crossing_failure (h : ExponentialEnvironment P τ)
    (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (ht : IsTimeConstant P τ μ)
    (b K C : ℝ) (hb : |b| ≤ 1) (hK : 0 < K) (hC : 0 < C) :
    ∀ κ > 0, ∀ᶠ s : ℝ in atTop, ∀ n : ℤ, 1 ≤ n → (n : ℝ) ≤ C*s →
      P.real {ω | (fun e => τ e ω) ∉ crossingEvent b (μ (direction b)) K s n 0} < κ := by
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
    (exponential_local_travel h μ hμ ht 3 η δ (by norm_num) hη hδ κ hκ)
  have htail : ∀ᶠ s : ℝ in atTop, Real.exp (-(K*s-4*N)/2) < κ := by
    filter_upwards [eventually_ge_atTop ((4*N-2*Real.log κ+2)/K)] with s hs
    have hh := (div_le_iff₀ hK).mp hs
    rw [← Real.exp_log hκ]
    apply Real.exp_lt_exp.mpr
    linarith
  filter_upwards [eventually_ge_atTop (1 : ℝ),eventually_ge_atTop N,
    eventually_ge_atTop ((4*μ transverseUnit+1)/K),htail] with s hs hsN hsμ htail
  intro n hn hns
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  by_cases hnN : N ≤ (n : ℝ)
  · have hlt := hN n hnN 0 (sourceEndpoint b n) (by
      simpa only [sub_zero] using sourceEndpoint_distance b n hb hn)
    have hsub : {ω | (fun e => τ e ω) ∉ crossingEvent b (μ (direction b)) K s n 0} ⊆
        {ω | ¬LocalTravel μ η δ n 0 (sourceEndpoint b n) (fun e => τ e ω)} := by
      intro ω hbad hgood
      obtain ⟨ds,hd,hcost,hin⟩ := hgood
      apply hbad
      refine ⟨0,ds,⟨rfl,?_⟩,?_,?_⟩
      · simpa [sourceEndpoint] using congrArg Prod.fst hd
      · intro i hi
        exact (mem_rareFastVertices ..).mpr
          (sourceEndpoint_tube_containment b C δ s n hb hs hn hns hδ.le hδ1 hδC (hin i hi))
      · have hμbound := sourceEndpoint_norm_cost μ hμ b n (by omega)
        have hηn : η*(n : ℝ) ≤ K*s/4 := by
          dsimp [η]
          calc
            _ ≤ K/(4*C)*(C*s) := mul_le_mul_of_nonneg_left hns hη.le
            _ = _ := by field_simp
        have hh := (div_le_iff₀ hK).mp hsμ
        simp only [sub_zero] at hcost
        change pathCost (fun e => τ e ω) 0 ds < μ (direction b)*n+K*s
        linarith [hμ.nonneg transverseUnit]
    exact (measureReal_mono hsub).trans_lt hlt
  · exact (exponential_bounded_crossing_failure h b (μ (direction b)) K s N n hb (hμ.nonneg _)
      (by omega) (le_of_not_ge hnN) (by linarith)).trans_lt htail

theorem exponential_short_crossing_probability (h : ExponentialEnvironment P τ)
    (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (ht : IsTimeConstant P τ μ)
    (b K C : ℝ) (hb : |b| ≤ 1) (hK : 0 < K) (hC : 0 < C) :
    ∀ q < 1, ∀ᶠ s : ℝ in atTop, ∀ n : ℤ, 1 ≤ n → (n : ℝ) ≤ C*s →
      q < P.real {ω | (fun e => τ e ω) ∈ crossingEvent b (μ (direction b)) K s n 0} := by
  let _ := h.probability
  intro q hq
  filter_upwards [exponential_short_crossing_failure h μ hμ ht b K C hb hK hC (1-q) (by linarith)] with s hs
  intro n hn hns
  have hh := hs n hn hns
  have hc := measureReal_compl (μ := P) ((measurableSet_crossingEvent b (μ (direction b)) K s n 0).preimage
    (Measurable.of_eval h.measurable))
  change P.real {ω | (fun e => τ e ω) ∉ crossingEvent b (μ (direction b)) K s n 0} = _ at hc
  rw [hc] at hh
  simpa [Set.preimage] using hh

end PlanarFPP

end OAI
