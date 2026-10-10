import Mathlib
import OAI.Probability.GaussianInformation.Inverse.ClippedMoments

namespace OAI
open MeasureTheory Metric
open scoped ENNReal
namespace AllScaleInverseVolume
open Set
open scoped Topology NNReal
open InnerProductSpace
open scoped RealInnerProductSpace
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
noncomputable def GreedyEvent {d k : ℕ} (u : Ambient d) : Set (Fin k → Ambient d) :=
  {z | Greedy residualScore (translated u z)}
lemma measurableSet_greedyEvent {d k : ℕ} (u : Ambient d) :
    MeasurableSet (GreedyEvent (k := k) u) := measurableSet_greedy.preimage (measurable_translated u)

lemma lintegral_greedy_clipped_le {d k : ℕ} (hd : 1 ≤ d) (hk : 3 ≤ k)
    (hα : 10*(k:ℝ) ≤ ((d:ℝ)-1)/2) (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (hν : BallBound ν) {ε : ℝ} (hε : 0 < ε) (u : Ambient d) :
    (∫⁻ z,(GreedyEvent u).indicator (fun z => clippedInverse ε (translated u z)) z
      ∂Measure.pi (fun _ : Fin k => ν)) ≤ ENNReal.ofReal (Real.exp (baseExponent d k))*3^k := by
  classical
  calc
    _ ≤ ∫⁻ z,∑' l : Fin k → ℤ,
        (BinEvent ε u l).indicator (fun z => clippedInverse ε (translated u z)) z
        ∂Measure.pi (fun _ : Fin k => ν) := by
      apply lintegral_mono
      intro z
      by_cases hz : z∈GreedyEvent u
      · rw [indicator_of_mem hz]
        obtain ⟨l,hl⟩ := exists_bins hε (translated u z)
        have hzl : z∈BinEvent ε u l := ⟨hz,hl⟩
        have hm := ENNReal.le_tsum (f := fun l : Fin k → ℤ =>
          (BinEvent ε u l).indicator (fun z => clippedInverse ε (translated u z)) z) l
        simpa only [indicator_of_mem hzl] using hm
      · simp only [indicator_of_notMem hz]; exact bot_le
    _ = ∑' l : Fin k → ℤ,∫⁻ z,
        (BinEvent ε u l).indicator (fun z => clippedInverse ε (translated u z)) z
        ∂Measure.pi (fun _ : Fin k => ν) :=
      lintegral_tsum (fun l => (((measurable_clippedInverse ε).comp (measurable_translated u)).indicator
        (measurableSet_binEvent ε u l)).aemeasurable)
    _ ≤ ∑' l : Fin k → ℤ,ENNReal.ofReal (Real.exp (baseExponent d k))*∏ i,integerWeight (l i) :=
      ENNReal.tsum_le_tsum (lintegral_bin_clipped_le hd hk hα ν hν ε u)
    _ = _ := by rw [ENNReal.tsum_mul_left,tsum_prod_integerWeight]

noncomputable def rawInverse {d k : ℕ} (u : Ambient d) (z : Fin k → Ambient d) : ℝ≥0∞ :=
  ((ENNReal.ofReal (Real.sqrt (Matrix.gram ℝ (translated u z)).det))⁻¹)^k

lemma clippedInverse_eq {d k : ℕ} {ε : ℝ} (hε : 0 < ε) (f : Fin k → Ambient d) :
    clippedInverse ε f=((ENNReal.ofReal (∏ i,clippedLength ε f i))⁻¹)^k := by
  have hi : ∀ i,0 < clippedLength ε f i := fun i => hε.trans_le (le_max_right _ _)
  have hprod : 0 < ∏ i,clippedLength ε f i := Finset.prod_pos (fun i _ => hi i)
  unfold clippedInverse
  simp_rw [← ENNReal.ofReal_inv_of_pos (hi _),← ENNReal.ofReal_pow (inv_nonneg.mpr (hi _).le)]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => pow_nonneg (inv_nonneg.mpr (hi i).le) k),Finset.prod_pow,
    Finset.prod_inv_distrib,ENNReal.ofReal_pow (by positivity),ENNReal.ofReal_inv_of_pos hprod]

lemma measurable_rawInverse {d k : ℕ} (u : Ambient d) : Measurable (rawInverse (k := k) u) := by
  have hm : Measurable (fun z : Fin k → Ambient d => ∏ i,‖gramSchmidt ℝ (translated u z) i‖) :=
    Finset.measurable_prod _ (fun i _ => ((measurable_gramSchmidt i).comp (measurable_translated u)).norm)
  change Measurable (fun z : Fin k → Ambient d =>
    ((ENNReal.ofReal (Real.sqrt (Matrix.gram ℝ (translated u z)).det))⁻¹)^k)
  simp_rw [sqrt_gram_det_eq_prod_gramSchmidt]
  exact hm.ennreal_ofReal.inv.pow_const k

lemma tendsto_clippedInverse {d k : ℕ} (u : Ambient d) (z : Fin k → Ambient d) :
    Filter.Tendsto (fun L : ℕ => clippedInverse ((1/2:ℝ)^L) (translated u z)) Filter.atTop
      (nhds (rawInverse u z)) := by
  have hε : ∀ L : ℕ,0 < (1/2:ℝ)^L := fun L => pow_pos (by norm_num) _
  have hzero := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ)<1)
  have hi : ∀ i : Fin k,Filter.Tendsto (fun L : ℕ => clippedLength ((1/2:ℝ)^L) (translated u z) i)
      Filter.atTop (nhds ‖gramSchmidt ℝ (translated u z) i‖) := by
    intro i
    have hh := (tendsto_const_nhds (x := ‖gramSchmidt ℝ (translated u z) i‖)).max hzero
    simpa only [clippedLength,max_eq_left (norm_nonneg _)] using hh
  have hp := tendsto_finsetProd Finset.univ (fun i _ => hi i)
  have hinv := (ENNReal.tendsto_ofReal hp).inv
  have hpow := (ENNReal.continuous_pow k).tendsto _ |>.comp hinv
  simpa only [clippedInverse_eq (hε _),rawInverse,sqrt_gram_det_eq_prod_gramSchmidt,Function.comp_def] using hpow

lemma lintegral_greedy_raw_le {d k : ℕ} (hd : 1 ≤ d) (hk : 3 ≤ k)
    (hα : 10*(k:ℝ) ≤ ((d:ℝ)-1)/2) (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (hν : BallBound ν) (u : Ambient d) :
    (∫⁻ z,(GreedyEvent u).indicator (rawInverse u) z ∂Measure.pi (fun _ : Fin k => ν)) ≤
      ENNReal.ofReal (Real.exp (baseExponent d k))*3^k := by
  let F : ℕ → (Fin k → Ambient d) → ℝ≥0∞ := fun L =>
    (GreedyEvent u).indicator (fun z => clippedInverse ((1/2:ℝ)^L) (translated u z))
  have hF : ∀ L,Measurable (F L) := fun L =>
    ((measurable_clippedInverse _).comp (measurable_translated u)).indicator (measurableSet_greedyEvent u)
  have hlim : ∀ z,Filter.Tendsto (fun L => F L z) Filter.atTop
      (nhds ((GreedyEvent u).indicator (rawInverse u) z)) := by
    intro z
    by_cases hz : z∈GreedyEvent u
    · simpa only [F,indicator_of_mem hz] using tendsto_clippedInverse u z
    · simp only [F,indicator_of_notMem hz]
      exact tendsto_const_nhds
  calc
    _ = ∫⁻ z,Filter.liminf (fun L => F L z) Filter.atTop ∂Measure.pi (fun _ : Fin k => ν) :=
      lintegral_congr (fun z => (hlim z).liminf_eq.symm)
    _ ≤ Filter.liminf (fun L => ∫⁻ z,F L z ∂Measure.pi (fun _ : Fin k => ν)) Filter.atTop :=
      lintegral_liminf_le hF
    _ ≤ _ := Filter.liminf_le_of_frequently_le (Filter.Eventually.frequently (Filter.Eventually.of_forall
      (fun L => lintegral_greedy_clipped_le hd hk hα ν hν (pow_pos (by norm_num : (0:ℝ)<1/2) L) u)))

lemma rawInverse_perm {d k : ℕ} (u : Ambient d) (z : Fin k → Ambient d)
    (π : Equiv.Perm (Fin k)) : rawInverse u (z ∘ π)=rawInverse u z := by
  have hg : Matrix.gram ℝ (translated u (z ∘ π))=
      (Matrix.gram ℝ (translated u z)).submatrix π π := rfl
  unfold rawInverse
  rw [hg,Matrix.det_submatrix_equiv_self]

lemma measurePreserving_permutation {d k : ℕ} (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (π : Equiv.Perm (Fin k)) :
    MeasurePreserving (fun z : Fin k → Ambient d => z ∘ π)
      (Measure.pi (fun _ : Fin k => ν)) (Measure.pi (fun _ : Fin k => ν)) := by
  have hh := MeasurePreserving.symm (MeasurableEquiv.piCongrLeft (fun _ : Fin k => Ambient d) π)
    (measurePreserving_piCongrLeft (fun _ : Fin k => ν) π)
  have he : ((MeasurableEquiv.piCongrLeft (fun _ : Fin k => Ambient d) π).symm :
      (Fin k → Ambient d) → (Fin k → Ambient d))=(fun z => z ∘ π) := by
    funext z i
    rfl
  simpa only [he] using hh

lemma lintegral_raw_le {d k : ℕ} (hd : 1 ≤ d) (hk : 3 ≤ k)
    (hα : 10*(k:ℝ) ≤ ((d:ℝ)-1)/2) (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (hν : BallBound ν) (u : Ambient d) :
    (∫⁻ z,rawInverse u z ∂Measure.pi (fun _ : Fin k => ν)) ≤
      (k.factorial:ℝ≥0∞)*(ENNReal.ofReal (Real.exp (baseExponent d k))*3^k) := by
  classical
  let F : (Fin k → Ambient d) → ℝ≥0∞ := (GreedyEvent u).indicator (rawInverse u)
  have hF : Measurable F := (measurable_rawInverse u).indicator (measurableSet_greedyEvent u)
  calc
    _ ≤ ∫⁻ z,∑ π : Equiv.Perm (Fin k),F (z ∘ π) ∂Measure.pi (fun _ : Fin k => ν) := by
      apply lintegral_mono
      intro z
      obtain ⟨π,hπ⟩ := exists_greedy_gram_order (translated u z)
      have hz : z ∘ π ∈ GreedyEvent u := hπ
      have he : F (z ∘ π)=rawInverse u z := by
        dsimp only [F]
        rw [indicator_of_mem hz,rawInverse_perm]
      rw [← he]
      exact Finset.single_le_sum (f := fun π : Equiv.Perm (Fin k) => F (z ∘ π)) (fun _ _ => bot_le) (Finset.mem_univ π)
    _ = ∑ π : Equiv.Perm (Fin k),∫⁻ z,F (z ∘ π) ∂Measure.pi (fun _ : Fin k => ν) :=
      lintegral_finsetSum _ (fun π _ => (hF.comp (measurePreserving_permutation ν π).measurable))
    _ = ∑ _π : Equiv.Perm (Fin k),∫⁻ z,F z ∂Measure.pi (fun _ : Fin k => ν) := by
      apply Finset.sum_congr rfl
      intro π _
      exact (measurePreserving_permutation ν π).lintegral_comp hF
    _ ≤ ∑ _π : Equiv.Perm (Fin k),ENNReal.ofReal (Real.exp (baseExponent d k))*3^k :=
      Finset.sum_le_sum (fun _ _ => lintegral_greedy_raw_le hd hk hα ν hν u)
    _ = _ := by simp [Fintype.card_perm,nsmul_eq_mul]

lemma inverse_constants {d k : ℕ} (hd : 1 ≤ d) (hk : k ≤ d) :
    (k.factorial:ℝ≥0∞)*(ENNReal.ofReal (Real.exp (baseExponent d k))*3^k) ≤
      ENNReal.ofReal (Real.exp (20*d*k)) := by
  have hd0 : (0:ℝ) ≤ d := Nat.cast_nonneg _
  have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg _
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hkd : (k:ℝ) ≤ d := by exact_mod_cast hk
  have hfact : (k.factorial:ℝ) ≤ Real.exp ((d:ℝ)*k) := by
    calc
      _ ≤ (k:ℝ)^k := by exact_mod_cast Nat.factorial_le_pow k
      _ ≤ (Real.exp (d:ℝ))^k := pow_le_pow_left₀ hk0 (hkd.trans (by linarith [Real.add_one_le_exp (d:ℝ)])) _
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have h3 : (3:ℝ)^k ≤ Real.exp ((2:ℝ)*k) := by
    calc
      _ ≤ (Real.exp 2)^k := pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp (2:ℝ)]) _
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hexp : (d:ℝ)*k+baseExponent d k+2*k ≤ 20*d*k := by
    have hlog5 : Real.log 5 ≤ 5 := (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
    have hlog3 : Real.log 3 ≤ 3 := (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
    have hlog2 : Real.log 2 ≤ 2 := (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
    have ht5 := mul_le_mul_of_nonneg_left hlog5 hk0
    have ht3 := mul_le_mul_of_nonneg_left hlog3 (show 0 ≤ ((d:ℝ)-1)/2 by linarith)
    have ht := mul_le_mul_of_nonneg_left (add_le_add ht5 ht3) hk0
    have ht2 := mul_le_mul_of_nonneg_right hlog2 (sq_nonneg (k:ℝ))
    have hs := mul_le_mul_of_nonneg_right hkd hk0
    have hs1 := mul_le_mul_of_nonneg_right hd1 hk0
    unfold baseExponent
    nlinarith
  have hr : (k.factorial:ℝ)*(Real.exp (baseExponent d k)*3^k) ≤ Real.exp (20*d*k) := by
    calc
      _ ≤ Real.exp ((d:ℝ)*k)*(Real.exp (baseExponent d k)*Real.exp (2*k)) := by
        exact mul_le_mul hfact (mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le) (by positivity) (Real.exp_pos _).le
      _ = Real.exp ((d:ℝ)*k+baseExponent d k+2*k) := by rw [Real.exp_add,Real.exp_add]; ring
      _ ≤ _ := Real.exp_le_exp.mpr hexp
  have hh := ENNReal.ofReal_le_ofReal hr
  simpa only [ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_natCast,
    ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 3), ENNReal.ofReal_ofNat] using hh

end AllScaleInverseVolume

end OAI
