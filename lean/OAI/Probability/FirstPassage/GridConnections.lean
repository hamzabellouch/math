import OAI.Probability.FirstPassage.GridCounting
import OAI.Probability.FirstPassage.GridTail

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory ProbabilityTheory Filter
open scoped Topology

noncomputable def gridTestsEvent (b m₀ K A R : ℝ) (k m J : ℕ) : Set (Edge → ℝ) :=
  {weights | ∀ n ∈ Finset.range (gridLastLevel m+1-J),
    ∀ ih ∈ gridTestIndices A R ((2 : ℝ)^m) ((2 : ℝ)^k) (gridMesh m (n+J)) (gridWidth k (n+J)),
      weights ∈ gridBinGood b m₀ K ((gridMesh m (n+J))*ih.1) ih.2
        (gridWidth k (n+J)) (gridMesh m (n+J)) (n+J)}

noncomputable def gridConnectionsEvent (b m₀ K A R : ℝ) (k m J : ℕ) : Set (Edge → ℝ) :=
  {weights | (∀ e, 0 ≤ weights e) ∧ weights ∈ gridTestsEvent b m₀ K A R k m J}

lemma measurableSet_gridConnectionsEvent (b m₀ K A R : ℝ) (k m J : ℕ) :
    MeasurableSet (gridConnectionsEvent b m₀ K A R k m J) := by
  have hp : MeasurableSet {weights : Edge → ℝ | ∀ e, 0 ≤ weights e} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun e => measurableSet_le measurable_const (measurable_pi_apply e))
  have ht : MeasurableSet (gridTestsEvent b m₀ K A R k m J) := by
    simp only [gridTestsEvent,Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro n
    apply MeasurableSet.iInter
    intro _
    apply MeasurableSet.iInter
    intro ih
    exact MeasurableSet.iInter (fun _ => measurableSet_gridBinGood ..)
  exact hp.inter ht

theorem gridConnectionsEvent_paths (weights : Edge → ℝ)
    (b m₀ K A R : ℝ) (hK : 0 ≤ K) (k m J : ℕ) (hJ : 1 ≤ J)
    (hg : weights ∈ gridConnectionsEvent b m₀ K A R k m J)
    (j : ℕ) (hj : J ≤ j ∧ j ≤ gridLastLevel m) (i : ℤ)
    (hi : -(A+4)*(2 : ℝ)^m ≤ ((gridMesh m j*i : ℤ) : ℝ) ∧
      ((gridMesh m j*i+gridMesh m j : ℤ) : ℝ) ≤ (A+4)*(2 : ℝ)^m)
    (r₀ : ℝ) (hr : |r₀| ≤ R*(2 : ℝ)^k)
    (p q : Vertex)
    (hp : p.1=gridMesh m j*i ∧ |transverse b p-r₀| ≤ 1)
    (hq : q.1=gridMesh m j*i+gridMesh m j ∧ |transverse b q-r₀| ≤ 1) :
    ∃ ds, p+displacement ds=q ∧
      pathCost weights p ds ≤ m₀*(gridMesh m j)+(K+200)*(j : ℝ)^2*(gridWidth k j) ∧
      PathIn p ds {z | gridMesh m j*i-gridMesh m j ≤ z.1 ∧
        z.1 ≤ gridMesh m j*i+2*gridMesh m j ∧
        |transverse b z-r₀| ≤ (K+200)*(j : ℝ)^2*(gridWidth k j)} := by
  have hn : j-J ∈ Finset.range (gridLastLevel m+1-J) := by rw [Finset.mem_range]; omega
  have he : j-J+J=j := by omega
  have htest := hg.2 (j-J) hn
  rw [he] at htest
  have hpos := gridMesh_pos m j
  have hpos' : (0 : ℝ) < gridMesh m j := by exact_mod_cast hpos
  have hi' : -(A+4)*(2 : ℝ)^m ≤ ((gridMesh m j*i : ℤ) : ℝ) ∧
      ((gridMesh m j*i : ℤ) : ℝ) ≤ (A+4)*(2 : ℝ)^m := by
    refine ⟨hi.1,?_⟩
    have hh := hi.2
    push_cast at hh ⊢
    linarith
  have hm := grid_interval_index_mem A R ((2 : ℝ)^m) ((2 : ℝ)^k)
    (gridMesh m j) (gridWidth k j) hpos (gridWidth_pos k j) i r₀ hi' hr
  exact gridBinGood_connection weights hg.1 b m₀ K hK _ _ _ _ hpos.le j
    (by omega) (gridWidth_pos k j) (htest _ hm) r₀
    (grid_bin_floor (gridWidth k j) (gridWidth_pos k j) r₀) p q hp hq

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem gridConnectionsEvent_failure_bound (henv : ExponentialEnvironment P τ)
    (b m₀ K A R q₀ : ℝ) (hA : 0 < A) (hR : 0 < R) (hq : 0 < q₀) (hq1 : q₀ ≤ 1)
    (k m J : ℕ) (hJ : 1 ≤ J) (hlast : gridLastLevel m ≤ k)
    (htrial : ∀ j, J ≤ j → j ≤ gridLastLevel m →
      q₀ ≤ P.real {ω | (fun e => τ e ω) ∈ crossingEvent b m₀ K (gridWidth k j) (gridMesh m j) 0}) :
    P.real {ω | (fun e => τ e ω) ∉ gridConnectionsEvent b m₀ K A R k m J} ≤
      gridFailureTail (gridIndexConstant A R) q₀ J := by
  let _ := henv.probability
  let N := gridLastLevel m+1-J
  let S (n : ℕ) := gridTestIndices A R ((2 : ℝ)^m) ((2 : ℝ)^k) (gridMesh m (n+J)) (gridWidth k (n+J))
  let Bad (n : ℕ) (ih : ℤ×ℤ) : Set Ω := {ω | (fun e => τ e ω) ∉ gridBinGood b m₀ K
    (gridMesh m (n+J)*ih.1) ih.2 (gridWidth k (n+J)) (gridMesh m (n+J)) (n+J)}
  let AllBad : Set Ω := ⋃ n ∈ Finset.range N, ⋃ ih ∈ S n, Bad n ih
  have hsub : ∀ᵐ ω ∂P, (fun e => τ e ω) ∉ gridConnectionsEvent b m₀ K A R k m J → ω ∈ AllBad := by
    filter_upwards [henv.ae_positive] with ω hω hb
    have ht : ¬(fun e => τ e ω) ∈ gridTestsEvent b m₀ K A R k m J := by
      intro ht
      exact hb ⟨fun e => (hω e).le,ht⟩
    simp only [gridTestsEvent,Set.mem_ofPred_eq,not_forall] at ht
    obtain ⟨n,hn,ih,hih,hbad⟩ := ht
    exact mem_iUnion₂.mpr ⟨n,hn,mem_iUnion₂.mpr ⟨ih,hih,hbad⟩⟩
  have hprob : P.real {ω | (fun e => τ e ω) ∉ gridConnectionsEvent b m₀ K A R k m J} ≤ P.real AllBad :=
    ENNReal.toReal_mono (measure_ne_top P _) (measure_mono_ae hsub)
  have hC : 0 ≤ gridIndexConstant A R := (gridIndexConstant_pos A R hA hR).le
  have hlevel (n : ℕ) (hn : n ∈ Finset.range N) :
      P.real (⋃ ih ∈ S n, Bad n ih) ≤ gridIndexConstant A R*gridFailureSeries q₀ (n+J) := by
    have hn' : n+J ≤ gridLastLevel m := by have hh := Finset.mem_range.mp hn; dsimp [N] at hh; omega
    have hjk : n+J ≤ k := hn'.trans hlast
    let d := (1-q₀)^((n+J)^2)+2*Real.exp (-gridVerticalExponent*((n+J : ℕ) : ℝ)^2*(gridWidth k (n+J)))
    have hd : 0 ≤ d := by dsimp [d]; positivity
    have hb (ih : ℤ×ℤ) : P.real (Bad n ih) ≤ d :=
      gridBinGood_failure_bound henv b m₀ K q₀ _ _ _ _ (n+J) (by omega)
        (gridWidth_pos k (n+J)) (htrial (n+J) (by omega) hn')
    calc
      _ ≤ ∑ ih ∈ S n,P.real (Bad n ih) := measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _ih ∈ S n,d := Finset.sum_le_sum (fun ih _ => hb ih)
      _ = ((S n).card : ℝ)*d := by simp
      _ ≤ (gridIndexConstant A R*(2 : ℝ)^(5*(n+J)))*d :=
        mul_le_mul_of_nonneg_right (gridTestIndices_level_card A R hA hR k m (n+J) hjk) hd
      _ ≤ gridIndexConstant A R*gridFailureSeries q₀ (n+J) := by
        rw [mul_assoc]
        apply mul_le_mul_of_nonneg_left _ hC
        exact grid_level_failure_le_series q₀ hq.le hq1 (n+J)
          (gridWidth k (n+J)) (by exact_mod_cast gridWidth_pos k (n+J))
  calc
    _ ≤ P.real AllBad := hprob
    _ ≤ ∑ n ∈ Finset.range N,P.real (⋃ ih ∈ S n, Bad n ih) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ n ∈ Finset.range N,gridIndexConstant A R*gridFailureSeries q₀ (n+J) :=
      Finset.sum_le_sum hlevel
    _ = gridIndexConstant A R*(∑ n ∈ Finset.range N,gridFailureSeries q₀ (n+J)) := by rw [Finset.mul_sum]
    _ ≤ gridIndexConstant A R*(∑' n : ℕ,gridFailureSeries q₀ (n+J)) := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact (summable_gridFailureSeries q₀ hq).comp_injective (fun _ _ h => Nat.add_right_cancel h)
        |>.sum_le_tsum (Finset.range N) (fun _ _ => gridFailureSeries_nonneg q₀ _)
    _ = _ := rfl

theorem exponential_grid_connections (henv : ExponentialEnvironment P τ)
    (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (ht : IsTimeConstant P τ μ)
    (b q₀ A R : ℝ) (hb : |b| ≤ 1) (hq : 0 < q₀) (hq1 : q₀ < 1) (hA : 0 < A) (hR : 0 < R)
    (J : ℕ) (hJ : 1 ≤ J) :
    ∀ᶠ k : ℕ in atTop,
      (∀ j, j ≤ gridLastLevel (characteristicExponent P τ μ b q₀ k) →
        (1/16 : ℝ)^j*(characteristicLength P τ μ b q₀ k : ℝ) ≤
          (characteristicLength P τ μ b q₀ (k-j) : ℝ)) →
      P.real {ω | (fun e => τ e ω) ∉ gridConnectionsEvent b (μ (direction b))
        (sourceCrossingK μ b) A R k (characteristicExponent P τ μ b q₀ k) J} ≤
        gridFailureTail (gridIndexConstant A R) q₀ J := by
  filter_upwards [eventually_ge_atTop 2,
    exponential_characteristic_lengths_exist henv μ hμ ht b q₀ hb hq,
    actual_grid_trial_probabilities henv μ hμ ht b q₀ hb hq hq1] with k hk hex hp
  intro hrec
  apply gridConnectionsEvent_failure_bound henv b (μ (direction b)) (sourceCrossingK μ b)
    A R q₀ hA hR hq hq1.le k (characteristicExponent P τ μ b q₀ k) J hJ
  · unfold gridLastLevel
    omega
  · intro j _ hj
    exact (hp j hj (hrec j hj)).le

theorem exponential_simultaneous_grid_scales (henv : ExponentialEnvironment P τ)
    (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (ht : IsTimeConstant P τ μ)
    (b q₀ : ℝ) (hb : |b| ≤ 1) (hq : 0 < q₀) (hq1 : q₀ < 1) :
    ∃ k₀ : ℕ, ∀ N : ℕ, ∃ k : ℕ, N < k ∧ k₀ ≤ k ∧
      (∀ j, j ≤ k-k₀ → (1/16 : ℝ)^j*(characteristicLength P τ μ b q₀ k : ℝ) ≤
        (characteristicLength P τ μ b q₀ (k-j) : ℝ)) ∧
      ∀ A R : ℝ, 0 < A → 0 < R → ∀ J : ℕ, 1 ≤ J →
        P.real {ω | (fun e => τ e ω) ∉ gridConnectionsEvent b (μ (direction b))
          (sourceCrossingK μ b) A R k (characteristicExponent P τ μ b q₀ k) J} ≤
          gridFailureTail (gridIndexConstant A R) q₀ J := by
  obtain ⟨k₀,hrec⟩ := exponential_characteristic_record_scales henv μ hμ ht b q₀ hb hq
  have he := (exponential_characteristic_lengths_exist henv μ hμ ht b q₀ hb hq).and
    (actual_grid_trial_probabilities henv μ hμ ht b q₀ hb hq hq1)
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp he
  refine ⟨k₀,?_⟩
  intro N
  obtain ⟨k,hk,hkk₀,hkr⟩ := hrec (max N (max N₀ (4*k₀+4)))
  have hkN : N < k := (le_max_left _ _).trans_lt hk
  have hkN₀ : N₀ ≤ k := by omega
  have hklarge : 4*k₀+4 ≤ k := by omega
  obtain ⟨hex,hp⟩ := hN₀ k hkN₀
  have hlast : gridLastLevel (characteristicExponent P τ μ b q₀ k) ≤ k-k₀ := by
    unfold gridLastLevel
    omega
  refine ⟨k,hkN,hkk₀,hkr,?_⟩
  intro A R hA hR J hJ
  apply gridConnectionsEvent_failure_bound henv b (μ (direction b)) (sourceCrossingK μ b)
    A R q₀ hA hR hq hq1.le k (characteristicExponent P τ μ b q₀ k) J hJ
    (hlast.trans (Nat.sub_le _ _))
  intro j _ hj
  exact (hp j hj (hkr j (hj.trans hlast))).le

end PlanarFPP

end OAI
