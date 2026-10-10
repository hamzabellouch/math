import OAI.Probability.FirstPassage.EndpointProbability
import OAI.Probability.FirstPassage.EndpointAsymptotics

namespace OAI

namespace PlanarFPP
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem exponential_arbitraryEndpoint_tendsto_of_grids {ι : Type*} {l : Filter ι}
    (henv : ExponentialEnvironment P τ)
    (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (ht : IsTimeConstant P τ μ)
    (b K A R ε q₀ : ℝ) (hb : |b| ≤ 1) (hK : 0 ≤ K)
    (hA : 0 < A) (hR : 0 < R) (hε : 0 < ε) (hq : 0 < q₀) (plus : Bool)
    (k m : ι → ℕ) (hk : Tendsto k l atTop)
    (hratio : Tendsto (fun i => (2 : ℝ)^(m i)/(2 : ℝ)^(k i)) l atTop)
    (hm : ∀ᶠ i in l, m i ≤ 3*k i)
    (hgrid : ∀ J : ℕ, 1 ≤ J → ∀ᶠ i in l,
      P.real {ω | (fun e => τ e ω) ∉ gridConnectionsEvent b (μ (direction b)) K A R (k i) (m i) J} ≤
        gridFailureTail (gridIndexConstant A R) q₀ J) :
    Tendsto (fun i => P.real {ω | (fun e => τ e ω) ∈ arbitraryEndpointEvent b (μ (direction b))
      (extremeSlope μ b plus) A R ε (k i) (m i)}) l (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall (fun _ => ha.trans_le measureReal_nonneg)
  · intro δ hδ
    have htE : Tendsto (fun J => 32*(K+200)*endpointErrorTail J) atTop (𝓝 0) := by
      simpa using endpointErrorTail_tendsto.const_mul (32*(K+200))
    have htG := gridFailureTail_tendsto (gridIndexConstant A R) q₀ hq
    obtain ⟨J,hJE,hJG,hJ⟩ := ((htE.eventually (gt_mem_nhds (by linarith : 0 < ε/4))).and
      ((htG.eventually (gt_mem_nhds (by linarith : 0 < δ/2))).and (eventually_ge_atTop 1))).exists
    let M : ℝ := (coarsePairIndices A J).card
    have hM : 0 ≤ M := by positivity
    let κ : ℝ := δ/(2*(M+1))
    have hκ : 0 < κ := by dsimp [κ]; positivity
    have hκM : M*κ < δ/2 := by
      have hh : κ*(2*(M+1))=δ := by dsimp [κ]; field_simp
      nlinarith
    obtain ⟨S,D,_hS,_hD,hprob⟩ := exponential_arbitraryEndpoint_probability_bound henv μ hμ ht
      b K A R ε hb hK (norm_direction_pos μ hμ b) hA hR hε plus J hJ κ hκ
    have hs := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp hk
    have hd := endpoint_mesh_ratio_tendsto k m hratio J
    let C := 2*R*|extremeSlope μ b plus| /(μ (direction b))
    filter_upwards [endpoint_levels_eventually k m hk hratio hm J,
      endpoint_error_eventually k hk K (extremeSlope μ b plus) ε hε J hJE.le,
      hs.eventually (eventually_ge_atTop S),hd.eventually (eventually_ge_atTop D),
      hd.eventually (eventually_ge_atTop C),hgrid J hJ] with i hlev herr hsi hdi hci hgi
    have hs0 : (0 : ℝ) < 2^(k i) := by positivity
    have hp := hprob (k i) (m i) hlev.1 hlev.2 hsi ((le_div_iff₀ hs0).mp hdi) herr
      ((le_div_iff₀ hs0).mp hci)
    have hsmall : P.real {ω | (fun e => τ e ω) ∉
        gridConnectionsEvent b (μ (direction b)) K A R (k i) (m i) J} < δ/2 := hgi.trans_lt hJG
    change M*κ < δ/2 at hκM
    change _ ≤ _+M*κ at hp
    linarith

end PlanarFPP

end OAI
