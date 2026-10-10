import OAI.NumberTheory.Jacobsthal.Primes.PrimeInverseBins

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.SourceInverseBinRate

open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeSideSupport
open PrimeGridGeometry PrimeGridKernel PrimeInverseBins DerivativeWeights MarginalProfiles
open SourceMarginalRate ExponentialMesh UniformBudgetRate HorizonMeshSmallness LowStateHorizon

theorem source_inverse_bins : ∃ κ₀ C : ℝ,0 < κ₀ ∧ 0 < C ∧
    ∀ κ : ℝ,0 < κ → κ ≤ κ₀ → ∀ d : ℝ,0 < d → ∃ w₀ : ℝ,1 < w₀ ∧
      ∀ w : ℝ,w₀ ≤ w → ∀ ell B : ℝ,∀ start : Node,
        1 ≤ ell → 0 < B → 2 ≤ Real.log B → Real.log B ≤ d*Real.log w →
        0 < start.gap → start.side = .even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
        let S := (Real.log B)^2
        let N := sourceHorizon S B
        let m := ⌈Real.exp (κ*Real.sqrt (Real.log w))⌉₊
        (∀ j,Valid .odd (point m j) → inverseBin w ell S start m 1 j ≤ ENNReal.ofReal (C*width m)) ∧
        (∀ n,2 ≤ n → n ≤ N → ∀ j,lowerIndex m (sideAfter .even n) ≤ j →
          inverseBin w ell S start m n j ≤ ENNReal.ofReal (C*width m)) := by
  obtain ⟨κ₀,C,hκ₀,hC,hsource⟩ := source_discrete_marginals
  obtain ⟨L,hL,hlocal⟩ := actual_inverse_bin_local
  refine ⟨κ₀,57*C,hκ₀,by positivity,?_⟩
  intro κ hκ hκle d hd
  obtain ⟨wP,hwP,hsource⟩ := hsource κ hκ hκle d hd
  have hevent := (horizon_mesh_smallness (A:=0) (D:=L) (by norm_num) hL.le hκ).and
    (Real.tendsto_log_atTop.eventually (eventually_ge_atTop (d^2)))
  obtain ⟨wAux,hwAux⟩ := eventually_atTop.mp hevent
  refine ⟨max wP wAux,hwP.trans_le (le_max_left _ _),?_⟩
  intro w hw ell B start hell hB hlogB hcomp hr hi h199 h23
  dsimp only
  let S := (Real.log B)^2
  let N := sourceHorizon S B
  let m := ⌈Real.exp (κ*Real.sqrt (Real.log w))⌉₊
  have hs : Valid start.side start.ratio := by rw [hi]; change 198/100 ≤ start.ratio; linarith
  have hwe := hwAux w ((le_max_right _ _).trans hw)
  have hscale := source_scale_bound hwe.2 hlogB hcomp
  have hS0 : 0 ≤ S := sq_nonneg _
  have hS3 : 3 ≤ S := by dsimp [S]; nlinarith
  have hsS : start.ratio ≤ S := by linarith
  have hm : 1 ≤ m := Nat.ceil_pos.mpr (Real.exp_pos _)
  have hmesh : width m = mesh κ w := rfl
  have hsmall := hwe.1 S hS0 hscale.1 0 (by simp)
  have hh : width m ≤ 1 := by rw [hmesh]; linarith [hsmall.1]
  have hE : Real.exp (L*(1+S)^3*width m) ≤ 3 := by
    rw [hmesh]
    exact (Real.exp_le_exp.mpr hsmall.2.2.1).trans Real.exp_one_lt_three.le
  have hprofiles := hsource w ((le_max_left _ _).trans hw) ell B start hell hB hlogB hcomp hr hi h199 h23
  have hwidth := width_nonneg m
  have hE0 := (Real.exp_pos (L*(1+S)^3*width m)).le
  constructor
  · intro j hj
    have hj' : Valid (sideAfter .even 1) (point m j) := hj
    have hmass : mass w ell S start m 1 j ≤
        ENNReal.ofReal (C*width m*weight (sideAfter .even 1) (point m j)*W (point m j)) := by
      simpa only [sideAfter,Side.flip,mul_assoc,mul_comm,mul_left_comm] using hprofiles.2.1 j hj
    have hb := cancel_inverse_bin hE0 hj' (hlocal w ell S hS3 start hs hi hsS m 1 j hj') hmass
    have ht : (1:ℝ)/2 ≤ point m j := by change 95/100 ≤ point m j at hj; linarith
    have hW := W_le_six ht
    have hW0 := (WeightFutureIntegrals.W_pos (by linarith : 0 < point m j)).le
    refine hb.trans (ENNReal.ofReal_le_ofReal ?_)
    calc
      _ ≤ 3*C*width m*6 := mul_le_mul
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hE hC.le) hwidth) hW hW0 (by positivity)
      _ ≤ _ := by nlinarith [mul_nonneg hC.le hwidth]
  · intro n hn hnN j hj
    have hjV := index_valid hm (sideAfter .even n) hj
    have hb := cancel_inverse_bin hE0 hjV (hlocal w ell S hS3 start hs hi hsS m n j hjV)
      (hprofiles.2.2 n hn hnN j hj)
    have hprof := profile_le_nineteen hh (index_regular hm (sideAfter .even n) hj)
    have hp0 := profile_nonneg m (index_regular hm (sideAfter .even n) hj)
    refine hb.trans (ENNReal.ofReal_le_ofReal ?_)
    calc
      _ ≤ 3*C*width m*19 := mul_le_mul
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hE hC.le) hwidth) hprof hp0 (by positivity)
      _ = _ := by ring

end NumberTheoryLean.SourceInverseBinRate

end

section

namespace NumberTheoryLean.SourceAllInverseBins

open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeSideSupport
open PrimeGridGeometry PrimeGridKernel PrimeInverseBins SourceInverseBinRate
open SourceMarginalRate ExponentialMesh LowStateHorizon

variable {w ell S : ℝ} {start : Node}

theorem inverse_bin_zero_first {m j : ℕ} (hm : 1 ≤ m) (hsmall : width m ≤ 1/100)
    (hs : Valid start.side start.ratio) (hi : start.side = .even)
    (hj : ¬Valid .odd (point m j)) : inverseBin w ell S start m 1 j = 0 := by
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_of_ae (pathLaw_side (w:=w) (ell:=ell) (S:=S) hi 1),
    ae_restrict_of_ae (pathLaw_weak hs 1 le_rfl),ae_restrict_mem (bin_measurable m j)] with z hz hweak hbin
  cases z with
  | none => exact False.elim hbin
  | some h =>
    have hv := weak_bin_domain hm hsmall hweak ((mem_bin h m j).mp hbin)
    have he : h.node.side = .odd := hz
    rw [he] at hv
    exact False.elim (hj hv)

theorem inverse_bin_zero_lower {m n j : ℕ} (hm : 1 ≤ m) (hn : 2 ≤ n)
    (hi : start.side = .even) (hj : j < lowerIndex m (sideAfter .even n)) :
    inverseBin w ell S start m n j = 0 := by
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_of_ae (pathLaw_side (w:=w) (ell:=ell) (S:=S) hi n),
    ae_restrict_of_ae (pathLaw_regular (w:=w) (ell:=ell) (S:=S) (start:=start) n hn),
    ae_restrict_mem (bin_measurable m j)] with z hz hreg hbin
  cases z with
  | none => exact False.elim hbin
  | some h =>
    have hv := (regular_bin_domain hm hreg ((mem_bin h m j).mp hbin)).1
    rw [hz] at hv
    omega

theorem source_all_inverse_bins : ∃ κ₀ C : ℝ,0 < κ₀ ∧ 0 < C ∧
    ∀ κ : ℝ,0 < κ → κ ≤ κ₀ → ∀ d : ℝ,0 < d → ∃ w₀ : ℝ,1 < w₀ ∧
      ∀ w : ℝ,w₀ ≤ w → ∀ ell B : ℝ,∀ start : Node,
        1 ≤ ell → 0 < B → 2 ≤ Real.log B → Real.log B ≤ d*Real.log w →
        0 < start.gap → start.side = .even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
        let S := (Real.log B)^2
        let N := sourceHorizon S B
        let m := ⌈Real.exp (κ*Real.sqrt (Real.log w))⌉₊
        ∀ n,1 ≤ n → n ≤ N → ∀ j,inverseBin w ell S start m n j ≤ ENNReal.ofReal (C*width m) := by
  obtain ⟨κ₀,C,hκ₀,hC,hsource⟩ := source_inverse_bins
  refine ⟨κ₀,C,hκ₀,hC,?_⟩
  intro κ hκ hκle d hd
  obtain ⟨wP,hwP,hsource⟩ := hsource κ hκ hκle d hd
  obtain ⟨wAux,hwAux⟩ := eventually_atTop.mp (mesh_eventually_small hκ (by norm_num : (0:ℝ) < 1/100))
  refine ⟨max wP wAux,hwP.trans_le (le_max_left _ _),?_⟩
  intro w hw ell B start hell hB hlogB hcomp hr hi h199 h23
  dsimp only
  let m := ⌈Real.exp (κ*Real.sqrt (Real.log w))⌉₊
  have hm : 1 ≤ m := Nat.ceil_pos.mpr (Real.exp_pos _)
  have hh : width m ≤ 1/100 := hwAux w ((le_max_right _ _).trans hw)
  have hs : Valid start.side start.ratio := by rw [hi]; change 198/100 ≤ start.ratio; linarith
  have hb := hsource w ((le_max_left _ _).trans hw) ell B start hell hB hlogB hcomp hr hi h199 h23
  intro n hn hnN j
  by_cases he : n=1
  · subst n
    by_cases hj : Valid .odd (point m j)
    · exact hb.1 j hj
    · rw [inverse_bin_zero_first hm hh hs hi hj]
      exact zero_le
  · have hn2 : 2 ≤ n := by omega
    by_cases hj : lowerIndex m (sideAfter .even n) ≤ j
    · exact hb.2 n hn2 hnN j hj
    · rw [inverse_bin_zero_lower hm hn2 hi (by omega : j < lowerIndex m (sideAfter .even n))]
      exact zero_le

end NumberTheoryLean.SourceAllInverseBins

end

end Erdos970

end OAI
