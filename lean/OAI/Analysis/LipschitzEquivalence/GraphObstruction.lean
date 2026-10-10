import OAI.Analysis.LipschitzEquivalence.WeakSums

namespace OAI

universe uH uA uB

noncomputable section
namespace LipschitzCounterexample

namespace GraphObstruction
open Filter Topology
open WeakSequences
open scoped ENNReal NNReal
variable {H : Type uH} [NormedAddCommGroup H] [NormedSpace ℝ H]
abbrev unitVector (i : ℕ) : RealL2 := lp.single 2 i 1

@[simp] theorem unitVector_coord (i j : ℕ) : unitVector i j = if j = i then 1 else 0 := by
  simp [unitVector, lp.single_apply, Pi.single_apply]

@[simp] theorem norm_unitVector (i : ℕ) : ‖unitVector i‖ = 1 := by
  simp [unitVector]

theorem unitVector_weakNull : WeakNull unitVector := by
  intro f
  let x := (InnerProductSpace.toDual ℝ RealL2).symm f
  have hx (i : ℕ) : f (unitVector i) = x i := by
    rw [← InnerProductSpace.toDual_symm_apply]
    change inner ℝ x (lp.single 2 i (1 : ℝ)) = x i
    simp [lp.inner_single_right]
  simp_rw [hx]
  have hs : Summable (fun i => ‖x i‖ ^ 2) := by
    simpa using (lp.hasSum_norm (by norm_num : 0 < (2 : ℝ≥0∞).toReal) x).summable
  have ht := hs.tendsto_atTop_zero
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 ht (ε^2) (sq_pos_of_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  have h := hN n hn
  rw [dist_zero_right, Real.norm_of_nonneg (sq_nonneg _)] at h
  rw [dist_zero_right]
  nlinarith [norm_nonneg (x n)]

theorem norm_sum_unitVector_sq (a : ℕ → ℕ) (ha : Function.Injective a) (N : ℕ) :
    ‖∑ j ∈ Finset.range N, unitVector (a j)‖ ^ 2 = (N : ℝ) := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [sum_inner, inner_sum, lp.inner_single_left]
  have hin (j k : ℕ) : inner ℝ (1 : ℝ) (unitVector (a k) (a j)) = if j = k then 1 else 0 := by
    simp [unitVector, lp.single_apply, Pi.single_apply, ha.eq_iff]
  simp only [hin]
  simp
  simpa only [Finset.card_range] using congrArg Finset.card (Finset.filter_eq_self.2 (fun i hi => Finset.mem_range.1 hi))

open NullSequences

omit [NormedSpace ℝ H] in
theorem eventually_trunc_small (y : ℕ → C0 (H := H))
    (hy : ∀ i, Tendsto (fun k => y k i) atTop (𝓝 0)) (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, ‖NullSequences.trunc N (y k)‖ < ε := by
  have h : ∀ᶠ k in atTop, ∀ i ∈ Finset.range N, ‖y k i‖ < ε/2 := by
    apply (Finset.eventually_all _).2
    intro i hi
    simpa only [dist_zero_right] using (hy i).eventually (Metric.ball_mem_nhds _ (half_pos hε))
  filter_upwards [h] with k hk
  apply lt_of_le_of_lt ((NullSequences.norm_le (half_pos hε).le).2 ?_) (half_lt_self hε)
  intro i
  simp only [NullSequences.trunc_apply]
  split_ifs with hi
  · exact (hk i (Finset.mem_range.2 hi)).le
  · simpa using (half_pos hε).le

omit [NormedSpace ℝ H] in
theorem norm_c0_block_le (y : C0 (H := H)) (N M : ℕ) (hNM : N ≤ M) :
    ‖NullSequences.trunc M y - NullSequences.trunc N y‖ ≤ ‖y‖ := by
  apply (NullSequences.norm_le (norm_nonneg _)).2
  intro i
  change ‖NullSequences.trunc M y i - NullSequences.trunc N y i‖ ≤ _
  simp only [NullSequences.trunc_apply]
  by_cases hi : i < N
  · simp [hi, hi.trans_le hNM]
  · by_cases hj : i < M
    · simpa [hi, hj] using norm_apply_le y i
    · simp [hi, hj]

omit [NormedSpace ℝ H] in

theorem norm_sum_blocks_le (y : ℕ → C0 (H := H)) (n : ℕ → ℕ) (hn : StrictMono n)
    (C : ℝ) (hC : 0 ≤ C) (hy : ∀ j, ‖y j‖ ≤ C) (J : ℕ) :
    ‖∑ j ∈ Finset.range J, (NullSequences.trunc (n (j+1)) (y j) -
      NullSequences.trunc (n j) (y j))‖ ≤ C := by
  classical
  apply (NullSequences.norm_le hC).2
  intro i
  rw [NullSequences.sum_apply]
  let z := fun j => NullSequences.trunc (n (j+1)) (y j) - NullSequences.trunc (n j) (y j)
  have hi (j : ℕ) : z j i = if n j ≤ i ∧ i < n (j+1) then y j i else 0 := by
    change NullSequences.trunc (n (j+1)) (y j) i - NullSequences.trunc (n j) (y j) i = _
    simp only [NullSequences.trunc_apply]
    have h := hn (Nat.lt_succ_self j)
    split_ifs <;> simp_all
    all_goals omega
  change ‖∑ j ∈ Finset.range J, z j i‖ ≤ C
  by_cases hex : ∃ j ∈ Finset.range J, n j ≤ i ∧ i < n (j+1)
  · obtain ⟨j, hj, hij⟩ := hex
    rw [Finset.sum_eq_single j]
    · rw [hi, ite_eq_left hij]
      exact (norm_apply_le (y j) i).trans (hy j)
    · intro k hk hkj
      rw [hi, ite_eq_right]
      intro hik
      rcases lt_or_gt_of_ne hkj with hkj | hjk
      · have h := hn.monotone (Nat.succ_le_of_lt hkj)
        change n (k+1) ≤ n j at h
        omega
      · have h := hn.monotone (Nat.succ_le_of_lt hjk)
        change n (j+1) ≤ n k at h
        omega
    · exact fun h => (h hj).elim
  · have hz : ∀ j ∈ Finset.range J, z j i = 0 := by
      intro j hj
      rw [hi, ite_eq_right (fun h => hex ⟨j, hj, h⟩)]
    simpa only [Finset.sum_eq_zero hz, norm_zero] using hC

theorem no_lower_of_coordinate_null (T : RealL2 →L[ℝ] C0 (H := H))
    (hcoord : ∀ i, Tendsto (fun k => T (unitVector k) i) atTop (𝓝 0))
    (b : ℝ) (hb : 0 < b) (hlower : ∀ x, b * ‖x‖ ≤ ‖T x‖) : False := by
  classical
  let y : ℕ → C0 (H := H) := fun k => T (unitVector k)
  have hnorm (k : ℕ) : ‖y k‖ ≤ ‖T‖ := by
    simpa only [y, norm_unitVector, mul_one] using T.le_opNorm (unitVector k)
  have step (j : ℕ) (p : ℕ × ℕ) : ∃ q : ℕ × ℕ, p.1 < q.1 ∧ p.2 < q.2 ∧
      ‖y q.1 - (NullSequences.trunc q.2 (y q.1) - NullSequences.trunc p.2 (y q.1))‖ ≤
        WeightedGraph.weight j := by
    have hw := WeightedGraph.weight_pos j
    obtain ⟨K, hK⟩ := eventually_atTop.1 (eventually_trunc_small y hcoord p.2
      (WeightedGraph.weight j / 2) (half_pos hw))
    let k := max K (p.1+1)
    have hkh : ‖NullSequences.trunc p.2 (y k)‖ < WeightedGraph.weight j/2 :=
      hK k (le_max_left _ _)
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (NullSequences.tendsto_trunc (y k))
      (WeightedGraph.weight j / 2) (half_pos hw)
    let n := max N (p.2+1)
    refine ⟨(k,n), (Nat.lt_succ_self _).trans_le (le_max_right _ _),
      (Nat.lt_succ_self _).trans_le (le_max_right _ _), ?_⟩
    have hkn := hN n (le_max_left _ _)
    rw [dist_eq_norm, norm_sub_rev] at hkn
    have he : y k - (NullSequences.trunc n (y k) - NullSequences.trunc p.2 (y k)) =
        (y k - NullSequences.trunc n (y k)) + NullSequences.trunc p.2 (y k) := by abel
    rw [he]
    exact (norm_add_le _ _).trans (by linarith)
  let next (j : ℕ) (p : ℕ × ℕ) := Classical.choose (step j p)
  let r : ℕ → ℕ × ℕ := fun j => Nat.rec (0,0) next j
  let k := fun j => (r (j+1)).1
  let n := fun j => (r j).2
  have hr (j : ℕ) : (r j).1 < (r (j+1)).1 ∧ n j < n (j+1) ∧
      ‖y (k j) - (NullSequences.trunc (n (j+1)) (y (k j)) -
        NullSequences.trunc (n j) (y (k j)))‖ ≤ WeightedGraph.weight j :=
    Classical.choose_spec (step j (r j))
  have hk : StrictMono k := strictMono_nat_of_lt_succ (fun j => (hr (j+1)).1)
  have hn : StrictMono n := strictMono_nat_of_lt_succ (fun j => (hr j).2.1)
  let z := fun j => NullSequences.trunc (n (j+1)) (y (k j)) - NullSequences.trunc (n j) (y (k j))
  have hbound (J : ℕ) : ‖T (∑ j ∈ Finset.range J, unitVector (k j))‖ ≤ ‖T‖ + 1 := by
    rw [map_sum]
    change ‖∑ j ∈ Finset.range J, y (k j)‖ ≤ _
    have hsplit : (∑ j ∈ Finset.range J, y (k j)) =
        (∑ j ∈ Finset.range J, z j) + ∑ j ∈ Finset.range J, (y (k j) - z j) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      abel
    rw [hsplit]
    apply (norm_add_le _ _).trans
    apply add_le_add
    · exact norm_sum_blocks_le (fun j => y (k j)) n hn ‖T‖ (by positivity) (fun j => hnorm (k j)) J
    · apply (norm_sum_le _ _).trans
      apply le_trans (Finset.sum_le_sum (fun j _ => (hr j).2.2))
      exact WeightedGraph.hasSum_weight.summable.sum_le_tsum _
        (fun _ _ => WeightedGraph.weight_nonneg _) |>.trans_eq WeightedGraph.hasSum_weight.tsum_eq
  obtain ⟨J, hJ⟩ := exists_nat_gt (((‖T‖+1)/b)^2)
  have hlow := hlower (∑ j ∈ Finset.range J, unitVector (k j))
  have hhi := hbound J
  have hnsq := norm_sum_unitVector_sq k hk.injective J
  have hnormle : ‖∑ j ∈ Finset.range J, unitVector (k j)‖ ≤ (‖T‖+1)/b :=
    (le_div_iff₀ hb).2 (by nlinarith)
  have hnonneg : 0 ≤ (‖T‖+1)/b := div_nonneg (by positivity) hb.le
  nlinarith [norm_nonneg (∑ j ∈ Finset.range J, unitVector (k j))]

variable {A : Type uA} {B : Type uB} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

theorem exists_small_unit (T : A →L[ℝ] B) (ε : ℝ)
    (hT : ¬ ∀ x, ε * ‖x‖ ≤ ‖T x‖) : ∃ x, ‖x‖ = 1 ∧ ‖T x‖ < ε := by
  push Not at hT
  obtain ⟨x, hx⟩ := hT
  have hn : 0 < ‖x‖ := norm_pos_iff.2 (by intro h; simp [h] at hx)
  refine ⟨‖x‖⁻¹ • x, ?_, ?_⟩
  · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hn.le), inv_mul_cancel₀ hn.ne']
  · rw [map_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hn.le)]
    apply (inv_mul_lt_iff₀ hn).2
    nlinarith

theorem exists_small_unit_of_coordinate_null (T : RealL2 →L[ℝ] C0 (H := H))
    (hcoord : ∀ i, Tendsto (fun k => T (unitVector k) i) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) : ∃ x, ‖x‖ = 1 ∧ ‖T x‖ < ε :=
  exists_small_unit T ε (no_lower_of_coordinate_null T hcoord ε hε)

def c0singleLI (n : ℕ) : RealL2 →ₗᵢ[ℝ] C0 (H := RealL2) where
  toFun := NullSequences.single n
  map_add' := by
    intro x y
    ext i
    by_cases hi : i = n <;> simp [hi]
  map_smul' := by
    intro c x
    ext i
    by_cases hi : i = n <;> simp [hi]
  norm_map' := NullSequences.norm_single n

def diagonalFun (t : ℕ → RealL2) (ht : ∀ n, ‖t n‖ = 1) (a : ScalarC0) : C0 (H := RealL2) :=
  ofTendsto (fun n => a n • t n) (by
    apply tendsto_zero_iff_norm_tendsto_zero.2
    simpa only [norm_smul, ht, mul_one, norm_zero] using (NullSequences.tendsto_zero a).norm)

def diagonal (t : ℕ → RealL2) (ht : ∀ n, ‖t n‖ = 1) : ScalarC0 →ₗᵢ[ℝ] C0 (H := RealL2) where
  toFun := diagonalFun t ht
  map_add' := by
    intro a b
    apply ZeroAtInftyContinuousMap.ext
    intro n
    exact add_smul (a n) (b n) (t n)
  map_smul' := by
    intro c a
    apply ZeroAtInftyContinuousMap.ext
    intro n
    exact mul_smul c (a n) (t n)
  norm_map' := by
    intro a
    apply le_antisymm
    · apply (NullSequences.norm_le (norm_nonneg a)).2
      intro n
      change ‖a n • t n‖ ≤ ‖a‖
      rw [norm_smul, ht, mul_one]
      exact norm_apply_le a n
    · apply (NullSequences.norm_le (norm_nonneg _)).2
      intro n
      calc
        ‖a n‖ = ‖a n • t n‖ := by rw [norm_smul, ht, mul_one]
        _ ≤ _ := norm_apply_le (diagonalFun t ht a) n

@[simp] theorem diagonal_apply (t : ℕ → RealL2) (ht : ∀ n, ‖t n‖ = 1) (a : ScalarC0) (n : ℕ) :
    diagonal t ht a n = a n • t n := rfl

theorem diagonal_single (t : ℕ → RealL2) (ht : ∀ n, ‖t n‖ = 1) (n : ℕ) (r : ℝ) :
    diagonal t ht (NullSequences.single n r) = r • c0singleLI n (t n) := by
  apply ZeroAtInftyContinuousMap.ext
  intro i
  change (if i = n then r else 0) • t i = r • (if i = n then t n else 0)
  by_cases h : i = n <;> simp [h]

variable [CompleteSpace A] [CompleteSpace H]

def first (Q : A →L[ℝ] H) : WeightedGraph.Space Q →L[ℝ] WeightedGraph.L1 A :=
  (ContinuousLinearMap.fst ℝ (WeightedGraph.L1 A) (WeightedGraph.C0 H)).comp
    (WeightedGraph.inclusion Q).toContinuousLinearMap

omit [CompleteSpace A] [CompleteSpace H] in
theorem graph_norm (Q : A →L[ℝ] H) (s : WeightedGraph.Space Q) :
    ‖s‖ = max ‖first Q s‖ ‖WeightedGraph.output Q s‖ := rfl

omit [CompleteSpace H] in

theorem graph_no_c0L2 (Q : A →L[ℝ] H) (hA : WeakSequentiallyComplete A)
    (hQ : CompletelyContinuous Q) (S : C0 (H := RealL2) →L[ℝ] WeightedGraph.Space Q)
    (b : ℝ) (hb : 0 < b) (hS : ∀ x, b * ‖x‖ ≤ ‖S x‖) : False := by
  classical
  let J := WeightedGraph.output Q
  let T (n : ℕ) : RealL2 →L[ℝ] C0 (H := H) :=
    J.comp (S.comp (c0singleLI n).toContinuousLinearMap)
  have hcoord (n i : ℕ) : Tendsto (fun k => T n (unitVector k) i) atTop (𝓝 0) := by
    have hw := (unitVector_weakNull.map (c0singleLI n).toContinuousLinearMap).map S
    have h := hQ _ (hw.map (WeightedGraph.coordCLM Q i))
    change Tendsto (fun k => Q (WeightedGraph.coord Q (S (c0singleLI n (unitVector k))) i))
      atTop (𝓝 0) at h
    simpa only [WeightedGraph.map_coord, T, J, ContinuousLinearMap.comp_apply,
      LinearIsometry.coe_toContinuousLinearMap] using h
  have hchoose (n : ℕ) : ∃ t : RealL2, ‖t‖ = 1 ∧ ‖T n t‖ < (b/2) * WeightedGraph.weight n :=
    exists_small_unit_of_coordinate_null (T n) (hcoord n) _ (mul_pos (half_pos hb) (WeightedGraph.weight_pos n))
  choose t ht hsmall using hchoose
  let R := (diagonal t ht).toContinuousLinearMap
  let L : ScalarC0 →L[ℝ] C0 (H := H) := J.comp (S.comp R)
  have hsingle (n : ℕ) (r : ℝ) : L (NullSequences.single n r) = r • T n (t n) := by
    change J (S (diagonal t ht (NullSequences.single n r))) = _
    rw [diagonal_single, map_smul, map_smul]
    rfl
  have hL (a : ScalarC0) : ‖L a‖ ≤ (b/2) * ‖a‖ := by
    have htrunc (N : ℕ) : ‖L (NullSequences.trunc N a)‖ ≤ (b/2) * ‖a‖ := by
      rw [NullSequences.trunc, map_sum]
      apply (norm_sum_le _ _).trans
      calc
        ∑ n ∈ Finset.range N, ‖L (NullSequences.single n (a n))‖ ≤
            ∑ n ∈ Finset.range N, ((b/2)*‖a‖) * WeightedGraph.weight n := by
          apply Finset.sum_le_sum
          intro n hn
          rw [hsingle, norm_smul]
          calc
            ‖a n‖ * ‖T n (t n)‖ ≤ ‖a‖ * ((b/2)*WeightedGraph.weight n) :=
              mul_le_mul (norm_apply_le a n) (hsmall n).le (norm_nonneg _) (norm_nonneg _)
            _ = _ := by ring
        _ = ((b/2)*‖a‖) * ∑ n ∈ Finset.range N, WeightedGraph.weight n := by rw [Finset.mul_sum]
        _ ≤ ((b/2)*‖a‖) * 1 := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg (half_pos hb).le (norm_nonneg _))
          exact WeightedGraph.hasSum_weight.summable.sum_le_tsum _
            (fun _ _ => WeightedGraph.weight_nonneg _) |>.trans_eq WeightedGraph.hasSum_weight.tsum_eq
        _ = _ := mul_one _
    exact le_of_tendsto ((L.continuous.tendsto a).comp (NullSequences.tendsto_trunc a)).norm
      (Eventually.of_forall htrunc)
  let F := (first Q).comp (S.comp R)
  apply no_c0_of_wsc (wsc_sumL1 (fun _ => hA)) F b hb
  intro a
  have hs := hS (R a)
  have hr : ‖R a‖ = ‖a‖ := (diagonal t ht).norm_map a
  rw [hr, graph_norm] at hs
  have hsmall' := hL a
  change ‖J (S (R a))‖ ≤ (b/2)*‖a‖ at hsmall'
  change b * ‖a‖ ≤ ‖first Q (S (R a))‖
  rcases le_max_iff.1 hs with hf | hg
  · exact hf
  · have hz : ‖a‖ = 0 := by nlinarith [norm_nonneg a]
    simp [hz]

end GraphObstruction

end LipschitzCounterexample
end

end OAI
