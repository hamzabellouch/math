import OAI.Probability.GammaPassage.GridEvents
import OAI.Probability.GammaPassage.GridTail

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.IntervalTravelBridge Set Finset MeasureTheory ProbabilityTheory Filter
open scoped Topology

variable {shape rate : ℝ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

/-- Simultaneous finite-grid probability bound from subcharacteristic
crossing bounds. -/
theorem gridConnectionsEvent_failure_bound (henv : GammaEnvironment shape rate P τ)
    (hs : 0 < shape) (hr : 0 < rate)
    (b m₀ K A R q₀ : ℝ) (hA : 0 < A) (hR : 0 < R) (hq : 0 < q₀) (hq1 : q₀ ≤ 1)
    (k m J : ℕ) (hJ : 1 ≤ J) (hlast : gridLastLevel m ≤ k)
    (htrial : ∀ j, J ≤ j → j ≤ gridLastLevel m →
      q₀ ≤ P.real {ω | (fun e => τ e ω) ∈ crossingEvent b m₀ K (gridWidth k j) (gridMesh m j) 0}) :
    P.real {ω | (fun e => τ e ω) ∉ gridConnectionsEvent shape rate b m₀ K A R k m J} ≤
      Grid.gridFailureTail shape (gridIndexConstant A R) q₀ J := by
  let _ := henv.probability
  let N := gridLastLevel m+1-J
  let S (n : ℕ) := gridTestIndices A R ((2 : ℝ)^m) ((2 : ℝ)^k) (gridMesh m (n+J)) (gridWidth k (n+J))
  let Bad (n : ℕ) (ih : ℤ×ℤ) : Set Ω := {ω | (fun e => τ e ω) ∉ gridBinGood shape rate b m₀ K
    (gridMesh m (n+J)*ih.1) ih.2 (gridWidth k (n+J)) (gridMesh m (n+J)) (n+J)}
  let AllBad : Set Ω := ⋃ n ∈ Finset.range N, ⋃ ih ∈ S n, Bad n ih
  have hsub : ∀ᵐ ω ∂P, (fun e => τ e ω) ∉ gridConnectionsEvent shape rate b m₀ K A R k m J → ω ∈ AllBad := by
    filter_upwards [henv.ae_positive] with ω hω hb
    have ht : ¬(fun e => τ e ω) ∈ gridTestsEvent shape rate b m₀ K A R k m J := by
      intro ht
      exact hb ⟨fun e => (hω e).le,ht⟩
    simp only [gridTestsEvent,Set.mem_ofPred_eq,not_forall] at ht
    obtain ⟨n,hn,ih,hih,hbad⟩ := ht
    exact mem_iUnion₂.mpr ⟨n,hn,mem_iUnion₂.mpr ⟨ih,hih,hbad⟩⟩
  have hprob : P.real {ω | (fun e => τ e ω) ∉ gridConnectionsEvent shape rate b m₀ K A R k m J} ≤ P.real AllBad :=
    ENNReal.toReal_mono (measure_ne_top P _) (measure_mono_ae hsub)
  have hC : 0 ≤ gridIndexConstant A R := (gridIndexConstant_pos A R hA hR).le
  have hlevel (n : ℕ) (hn : n ∈ Finset.range N) :
      P.real (⋃ ih ∈ S n, Bad n ih) ≤ gridIndexConstant A R*Grid.gridFailureSeries shape q₀ (n+J) := by
    have hn' : n+J ≤ gridLastLevel m := by have hh := Finset.mem_range.mp hn; dsimp [N] at hh; omega
    have hjk : n+J ≤ k := hn'.trans hlast
    let d := (1-q₀)^((n+J)^2)+2*Real.exp (-(Grid.verticalExponent shape)*((n+J : ℕ) : ℝ)^2*(gridWidth k (n+J)))
    have hd : 0 ≤ d := by dsimp [d]; positivity
    have hb (ih : ℤ×ℤ) : P.real (Bad n ih) ≤ d :=
      gridBinGood_failure_bound henv hs hr b m₀ K q₀ _ _ _ _ (n+J) (by omega)
        (gridWidth_pos k (n+J)) (htrial (n+J) (by omega) hn')
    calc
      _ ≤ ∑ ih ∈ S n,P.real (Bad n ih) := measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _ih ∈ S n,d := Finset.sum_le_sum (fun ih _ => hb ih)
      _ = ((S n).card : ℝ)*d := by simp
      _ ≤ (gridIndexConstant A R*(2 : ℝ)^(5*(n+J)))*d :=
        mul_le_mul_of_nonneg_right (gridTestIndices_level_card A R hA hR k m (n+J) hjk) hd
      _ ≤ gridIndexConstant A R*Grid.gridFailureSeries shape q₀ (n+J) := by
        rw [mul_assoc]
        apply mul_le_mul_of_nonneg_left _ hC
        exact Grid.grid_level_failure_le_series shape hs q₀ hq.le hq1 (n+J)
          (gridWidth k (n+J)) (by exact_mod_cast gridWidth_pos k (n+J))
  calc
    _ ≤ P.real AllBad := hprob
    _ ≤ ∑ n ∈ Finset.range N,P.real (⋃ ih ∈ S n, Bad n ih) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ n ∈ Finset.range N,gridIndexConstant A R*Grid.gridFailureSeries shape q₀ (n+J) :=
      Finset.sum_le_sum hlevel
    _ = gridIndexConstant A R*(∑ n ∈ Finset.range N,Grid.gridFailureSeries shape q₀ (n+J)) := by rw [Finset.mul_sum]
    _ ≤ gridIndexConstant A R*(∑' n : ℕ,Grid.gridFailureSeries shape q₀ (n+J)) := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact (Grid.summable_gridFailureSeries shape hs q₀ hq).comp_injective (fun _ _ h => Nat.add_right_cancel h)
        |>.sum_le_tsum (Finset.range N) (fun _ _ => Grid.gridFailureSeries_nonneg shape hs q₀ _)
    _ = _ := rfl

/-- Lemma `gr:grid-tools` for characteristic lengths satisfying the
record-scale comparison. -/
theorem gamma_grid_connections (henv : GammaEnvironment shape rate P τ)
    (hs : 0 < shape) (hr : 0 < rate)
    (b q₀ A R : ℝ) (hb : |b| ≤ 1) (hq : 0 < q₀) (hq1 : q₀ < 1) (hA : 0 < A) (hR : 0 < R)
    (J : ℕ) (hJ : 1 ≤ J) :
    ∀ᶠ k : ℕ in atTop,
      (∀ j, j ≤ gridLastLevel (characteristicExponent P τ shape rate (gammaMeanNorm henv hs hr) b q₀ k) →
        (1/16 : ℝ)^j*(characteristicLength P τ shape rate (gammaMeanNorm henv hs hr) b q₀ k : ℝ) ≤
          (characteristicLength P τ shape rate (gammaMeanNorm henv hs hr) b q₀ (k-j) : ℝ)) →
      P.real {ω | (fun e => τ e ω) ∉ gridConnectionsEvent shape rate b ((gammaMeanNorm henv hs hr) (direction b))
        (sourceCrossingK shape rate (gammaMeanNorm henv hs hr) b) A R k (characteristicExponent P τ shape rate (gammaMeanNorm henv hs hr) b q₀ k) J} ≤
        Grid.gridFailureTail shape (gridIndexConstant A R) q₀ J := by
  filter_upwards [eventually_ge_atTop 2,
    gamma_characteristic_lengths_exist henv hs hr b q₀ hb hq,
    gamma_grid_trial_probabilities henv hs hr b q₀ hb hq hq1] with k hk hex hp
  intro hrec
  apply gridConnectionsEvent_failure_bound henv hs hr b ((gammaMeanNorm henv hs hr) (direction b)) (sourceCrossingK shape rate (gammaMeanNorm henv hs hr) b)
    A R q₀ hA hR hq hq1.le k (characteristicExponent P τ shape rate (gammaMeanNorm henv hs hr) b q₀ k) J hJ
  · unfold gridLastLevel
    omega
  · intro j _ hj
    exact (hp j hj (hrec j hj)).le

/-- Arbitrarily large characteristic record scales carry simultaneous grid
bounds, independently of the box parameters and initial level. -/
theorem gamma_simultaneous_grid_scales (henv : GammaEnvironment shape rate P τ)
    (hs : 0 < shape) (hr : 0 < rate)
    (b q₀ : ℝ) (hb : |b| ≤ 1) (hq : 0 < q₀) (hq1 : q₀ < 1) :
    ∃ k₀ : ℕ, ∀ N : ℕ, ∃ k : ℕ, N < k ∧ k₀ ≤ k ∧
      (∀ j, j ≤ k-k₀ → (1/16 : ℝ)^j*(characteristicLength P τ shape rate (gammaMeanNorm henv hs hr) b q₀ k : ℝ) ≤
        (characteristicLength P τ shape rate (gammaMeanNorm henv hs hr) b q₀ (k-j) : ℝ)) ∧
      ∀ A R : ℝ, 0 < A → 0 < R → ∀ J : ℕ, 1 ≤ J →
        P.real {ω | (fun e => τ e ω) ∉ gridConnectionsEvent shape rate b ((gammaMeanNorm henv hs hr) (direction b))
          (sourceCrossingK shape rate (gammaMeanNorm henv hs hr) b) A R k (characteristicExponent P τ shape rate (gammaMeanNorm henv hs hr) b q₀ k) J} ≤
          Grid.gridFailureTail shape (gridIndexConstant A R) q₀ J := by
  obtain ⟨k₀,hrec⟩ := gamma_characteristic_record_scales henv hs hr b q₀ hb hq
  have he := (gamma_characteristic_lengths_exist henv hs hr b q₀ hb hq).and
    (gamma_grid_trial_probabilities henv hs hr b q₀ hb hq hq1)
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp he
  refine ⟨k₀,?_⟩
  intro N
  obtain ⟨k,hk,hkk₀,hkr⟩ := hrec (max N (max N₀ (4*k₀+4)))
  have hkN : N < k := (le_max_left _ _).trans_lt hk
  have hkN₀ : N₀ ≤ k := by omega
  have hklarge : 4*k₀+4 ≤ k := by omega
  obtain ⟨hex,hp⟩ := hN₀ k hkN₀
  have hlast : gridLastLevel (characteristicExponent P τ shape rate (gammaMeanNorm henv hs hr) b q₀ k) ≤ k-k₀ := by
    unfold gridLastLevel
    omega
  refine ⟨k,hkN,hkk₀,hkr,?_⟩
  intro A R hA hR J hJ
  apply gridConnectionsEvent_failure_bound henv hs hr b ((gammaMeanNorm henv hs hr) (direction b)) (sourceCrossingK shape rate (gammaMeanNorm henv hs hr) b)
    A R q₀ hA hR hq hq1.le k (characteristicExponent P τ shape rate (gammaMeanNorm henv hs hr) b q₀ k) J hJ
    (hlast.trans (Nat.sub_le _ _))
  intro j _ hj
  exact (hp j hj (hkr j (hj.trans hlast))).le

end GammaFPP.CrossingBridge

end OAI
