import OAI.Probability.FirstPassage.EndpointLimit
import OAI.Probability.FirstPassage.ActualTimeConstant

namespace OAI

namespace PlanarFPP
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem exponential_arbitraryEndpoint_record_scales (henv : ExponentialEnvironment P τ)
    (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (ht : IsTimeConstant P τ μ)
    (b q₀ : ℝ) (hb : |b| ≤ 1) (hq : 0 < q₀) (hq1 : q₀ < 1) :
    ∃ k₀ : ℕ, ∃ k : ℕ → ℕ, Tendsto k atTop atTop ∧
      (∀ n, n < k n ∧ k₀ ≤ k n ∧
        ∀ j, j ≤ k n-k₀ → (1/16 : ℝ)^j*(characteristicLength P τ μ b q₀ (k n) : ℝ) ≤
          (characteristicLength P τ μ b q₀ (k n-j) : ℝ)) ∧
      ∀ A R ε : ℝ, 0 < A → 0 < R → 0 < ε → ∀ plus : Bool,
        Tendsto (fun n => P.real {ω | (fun e => τ e ω) ∈ arbitraryEndpointEvent b (μ (direction b))
          (extremeSlope μ b plus) A R ε (k n) (characteristicExponent P τ μ b q₀ (k n))}) atTop (𝓝 0) := by
  obtain ⟨k₀,hscales⟩ := exponential_simultaneous_grid_scales henv μ hμ ht b q₀ hb hq hq1
  choose k hk hk₀ hrec hgrid using hscales
  have hkt : Tendsto k atTop atTop := by
    apply tendsto_atTop.2
    intro N
    filter_upwards [eventually_ge_atTop N] with n hn
    exact hn.trans (hk n).le
  refine ⟨k₀,k,hkt,fun n => ⟨hk n,hk₀ n,hrec n⟩,?_⟩
  intro A R ε hA hR hε plus
  have hratio : Tendsto (fun n => (2 : ℝ)^(characteristicExponent P τ μ b q₀ (k n))/(2 : ℝ)^(k n)) atTop atTop := by
    convert (exponential_characteristic_lengths_ratio henv μ hμ ht b q₀ hb hq hq1).comp hkt using 1
    ext n
    simp [characteristicLength]
  have hm : ∀ᶠ n : ℕ in atTop, characteristicExponent P τ μ b q₀ (k n) ≤ 3*k n := by
    filter_upwards [hkt.eventually (exponential_characteristic_lengths_exist henv μ hμ ht b q₀ hb hq)] with n hn
    exact hn.1
  exact exponential_arbitraryEndpoint_tendsto_of_grids henv μ hμ ht b (sourceCrossingK μ b) A R ε q₀
    hb (by unfold sourceCrossingK; positivity) hA hR hε hq plus k
    (fun n => characteristicExponent P τ μ b q₀ (k n)) hkt hratio hm
    (fun J hJ => Eventually.of_forall (fun n => hgrid n A R hA hR J hJ))

theorem actual_arbitraryEndpoint_record_scales (henv : ExponentialEnvironment P τ)
    (b q₀ : ℝ) (hb : |b| ≤ 1) (hq : 0 < q₀) (hq1 : q₀ < 1) :
    ∃ k₀ : ℕ, ∃ k : ℕ → ℕ, Tendsto k atTop atTop ∧
      (∀ n, n < k n ∧ k₀ ≤ k n ∧
        ∀ j, j ≤ k n-k₀ → (1/16 : ℝ)^j*(characteristicLength P τ actualSourceTimeConstant b q₀ (k n) : ℝ) ≤
          (characteristicLength P τ actualSourceTimeConstant b q₀ (k n-j) : ℝ)) ∧
      ∀ A R ε : ℝ, 0 < A → 0 < R → 0 < ε → ∀ plus : Bool,
        Tendsto (fun n => P.real {ω | (fun e => τ e ω) ∈ arbitraryEndpointEvent b (actualSourceTimeConstant (direction b))
          (extremeSlope actualSourceTimeConstant b plus) A R ε (k n)
          (characteristicExponent P τ actualSourceTimeConstant b q₀ (k n))}) atTop (𝓝 0) :=
  exponential_arbitraryEndpoint_record_scales henv actualSourceTimeConstant actualSourceTimeConstant_norm
    (actualSourceTimeConstant_isTimeConstant henv) b q₀ hb hq hq1

end PlanarFPP

end OAI
