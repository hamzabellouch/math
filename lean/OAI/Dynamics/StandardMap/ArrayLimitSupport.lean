import OAI.Dynamics.StandardMap.RealArrays

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Topology
open scoped ENNReal Topology CompactlySupported Classical
namespace StandardMapEntropy
lemma rescaledDistance_tree (k : ℝ) (hk : 0 ≤ k) (z : Torus) (n : ℕ) (hn : 0<n)
    (v x y w : DyadicTime) :
    min (rescaledDistance k z n v x+rescaledDistance k z n v y-rescaledDistance k z n x y)
      (rescaledDistance k z n v y+rescaledDistance k z n v w-rescaledDistance k z n y w)-
      (rescaledDistance k z n v x+rescaledDistance k z n v w-rescaledDistance k z n x w) ≤ 3/(n:ℝ) := by
  have hh := productDistance_tree k hk z ⌊(n:ℝ)*(v:ℝ)⌋ ⌊(n:ℝ)*(x:ℝ)⌋ ⌊(n:ℝ)*(y:ℝ)⌋ ⌊(n:ℝ)*(w:ℝ)⌋
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  unfold rescaledDistance
  simp_rw [← add_div,← sub_div]
  rw [min_div_div_right hn'.le,← sub_div]
  exact div_le_div_of_nonneg_right (by linarith) hn'.le
lemma integral_nonaffine_scale_zero (k : ℝ) (hk : 0 ≤ k) (p l : ℕ) (ε : ℝ) (hε : 0<ε)
    (g : C_c(NonAffineArray,ℝ))
    (hz : ∀ j∈Finset.range l,∀ z,arrayTestExtend g (sampleArray k hk z (2^(p+j)) (by positivity))=0) :
    (∫ d,g d ∂nonaffinePart (scaleLaw k hk p l ε))=0 := by
  rw [←integral_arrayTestExtend,integral_scaleLaw k hk p l ε hε (fun d => arrayTestExtend g d) (arrayTestExtend g).continuous]
  have hs : (∑ j∈Finset.range l,∫ d,arrayTestExtend g d ∂sampleLaw k hk (2^(p+j)) (by positivity))=0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [integral_sampleLaw _ _ _ _ (fun d => arrayTestExtend g d) (arrayTestExtend g).continuous]
    simp_rw [hz j hj]
    simp
  rw [hs,zero_div]
lemma integral_nonaffine_scale_zero_of_bound (k : ℝ) (hk : 0 ≤ k) (p l : ℕ) (ε : ℝ) (hε : 0<ε)
    (g : C_c(NonAffineArray,ℝ)) (f : DistanceArray → ℝ) (q : ℝ)
    (hg : ∀ d : NonAffineArray, f d.val ≤ q → g d=0)
    (hf : ∀ j∈Finset.range l,∀ z,f (sampleArray k hk z (2^(p+j)) (by positivity)) ≤ q) :
    (∫ d,g d ∂nonaffinePart (scaleLaw k hk p l ε))=0 := by
  apply integral_nonaffine_scale_zero k hk p l ε hε g
  intro j hj z
  let d := sampleArray k hk z (2^(p+j)) (by positivity)
  by_cases hd : d∈affineLocus
  · exact arrayTestExtend_affine g d hd
  · exact (arrayTestExtend_apply g ⟨d,hd⟩).trans (hg ⟨d,hd⟩ (hf j hj z))
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence) (L : S.LimitLaws)
lemma power_lower_tendsto : Tendsto (fun i => (2:ℝ)^(criticalLowerExponent S.offset i)) atTop atTop :=
  (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).comp S.lowerExponent_tendsto
lemma power_terminal_tendsto : Tendsto (fun i => (2:ℝ)^(S.exponent i)) atTop atTop :=
  (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).comp S.exponent_tendsto
lemma sample_constraint_aemulti (f : DistanceArray → ℝ) (hf : Continuous f) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ k : ℝ,∀ hk : 0 ≤ k,∀ z : Torus,∀ n : ℕ,∀ hn : 0<n,
      f (sampleArray k hk z n hn) ≤ C/(n:ℝ)) : ∀ᵐ d ∂L.multi, f d.val ≤ 0 := by
  apply ae_le_zero_of_positive_rational_null
  intro q hq
  have hqR : (0:ℝ)<q := by exact_mod_cast hq
  apply vague_open_null L.filter (fun i => nonaffinePart (S.multiLaw i)) L.multi L.multi_converges
    (isOpen_lt continuous_const (hf.comp continuous_subtype_val))
  intro g hg hz
  have he : ∀ᶠ i in atTop,C/(2:ℝ)^(criticalLowerExponent S.offset i)<q :=
    (tendsto_const_nhds.div_atTop S.power_lower_tendsto).eventually (gt_mem_nhds hqR)
  apply tendsto_const_nhds.congr'
  filter_upwards [L.refines he] with i hi
  symm
  apply integral_nonaffine_scale_zero_of_bound _ _ _ _ _ (S.epsilon_pos i) g f q
  · intro d hd; exact hz d (not_lt.mpr hd)
  · intro j hj z
    exact (hb _ _ z _ (by positivity)).trans ((div_le_div_of_nonneg_left hC (by positivity)
      (by exact_mod_cast pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (Nat.le_add_right (criticalLowerExponent S.offset i) j))).trans hi.le)
lemma sample_constraint_aeterminal (f : DistanceArray → ℝ) (hf : Continuous f) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ k : ℝ,∀ hk : 0 ≤ k,∀ z : Torus,∀ n : ℕ,∀ hn : 0<n,
      f (sampleArray k hk z n hn) ≤ C/(n:ℝ)) : ∀ᵐ d ∂L.terminal, f d.val ≤ 0 := by
  apply ae_le_zero_of_positive_rational_null
  intro q hq
  have hqR : (0:ℝ)<q := by exact_mod_cast hq
  apply vague_open_null L.filter (fun i => nonaffinePart (S.terminalLaw i)) L.terminal L.terminal_converges
    (isOpen_lt continuous_const (hf.comp continuous_subtype_val))
  intro g hg hz
  have he : ∀ᶠ i in atTop,C/(2:ℝ)^(S.exponent i)<q :=
    (tendsto_const_nhds.div_atTop S.power_terminal_tendsto).eventually (gt_mem_nhds hqR)
  apply tendsto_const_nhds.congr'
  filter_upwards [L.refines he] with i hi
  symm
  apply integral_nonaffine_scale_zero_of_bound _ _ _ _ _ (S.epsilon_pos i) g f q
  · intro d hd; exact hz d (not_lt.mpr hd)
  · intro j hj z
    exact (hb _ _ z _ (by positivity)).trans ((div_le_div_of_nonneg_left hC (by positivity)
      (by exact_mod_cast pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (Nat.le_add_right (S.exponent i) j))).trans hi.le)
lemma unit_aemulti : ∀ᵐ d ∂L.multi, UnitArray d.val := by
  have h (s t : DyadicTime) : ∀ᵐ d ∂L.multi,d.val.val s t-|(t:ℝ)-(s:ℝ)| ≤ 0 := by
    apply S.sample_constraint_aemulti L (fun d => d.val s t-|(t:ℝ)-(s:ℝ)|)
      ((continuous_arrayEval s t).sub continuous_const) 1 (by norm_num)
    intro k hk z n hn
    change rescaledDistance k z n s t-|(t:ℝ)-(s:ℝ)| ≤ 1/(n:ℝ)
    linarith [rescaledDistance_bound k hk z n hn s t]
  filter_upwards [ae_all_iff.mpr (fun s => ae_all_iff.mpr (h s))] with d hd
  intro s t
  linarith [hd s t]
lemma unit_aeterminal : ∀ᵐ d ∂L.terminal, UnitArray d.val := by
  have h (s t : DyadicTime) : ∀ᵐ d ∂L.terminal,d.val.val s t-|(t:ℝ)-(s:ℝ)| ≤ 0 := by
    apply S.sample_constraint_aeterminal L (fun d => d.val s t-|(t:ℝ)-(s:ℝ)|)
      ((continuous_arrayEval s t).sub continuous_const) 1 (by norm_num)
    intro k hk z n hn
    change rescaledDistance k z n s t-|(t:ℝ)-(s:ℝ)| ≤ 1/(n:ℝ)
    linarith [rescaledDistance_bound k hk z n hn s t]
  filter_upwards [ae_all_iff.mpr (fun s => ae_all_iff.mpr (h s))] with d hd
  intro s t
  linarith [hd s t]
lemma tree_aemulti : ∀ᵐ d ∂L.multi, TreeArray d.val := by
  have h (v x y z : DyadicTime) : ∀ᵐ d ∂L.multi,
      min (d.val.val v x+d.val.val v y-d.val.val x y) (d.val.val v y+d.val.val v z-d.val.val y z)-
      (d.val.val v x+d.val.val v z-d.val.val x z) ≤ 0 := by
    have hc (a b c : DyadicTime) : Continuous (fun d : DistanceArray => d.val a b+d.val a c-d.val b c) :=
      ((continuous_arrayEval a b).add (continuous_arrayEval a c)).sub (continuous_arrayEval b c)
    exact S.sample_constraint_aemulti L _ (((hc v x y).min (hc v y z)).sub (hc v x z)) 3 (by norm_num)
      (fun k hk q n hn => rescaledDistance_tree k hk q n hn v x y z)
  filter_upwards [ae_all_iff.mpr (fun v => ae_all_iff.mpr (fun x => ae_all_iff.mpr
    (fun y => ae_all_iff.mpr (h v x y))))] with d hd
  intro v x y z
  linarith [hd v x y z]
lemma tree_aeterminal : ∀ᵐ d ∂L.terminal, TreeArray d.val := by
  have h (v x y z : DyadicTime) : ∀ᵐ d ∂L.terminal,
      min (d.val.val v x+d.val.val v y-d.val.val x y) (d.val.val v y+d.val.val v z-d.val.val y z)-
      (d.val.val v x+d.val.val v z-d.val.val x z) ≤ 0 := by
    have hc (a b c : DyadicTime) : Continuous (fun d : DistanceArray => d.val a b+d.val a c-d.val b c) :=
      ((continuous_arrayEval a b).add (continuous_arrayEval a c)).sub (continuous_arrayEval b c)
    exact S.sample_constraint_aeterminal L _ (((hc v x y).min (hc v y z)).sub (hc v x z)) 3 (by norm_num)
      (fun k hk q n hn => rescaledDistance_tree k hk q n hn v x y z)
  filter_upwards [ae_all_iff.mpr (fun v => ae_all_iff.mpr (fun x => ae_all_iff.mpr
    (fun y => ae_all_iff.mpr (h v x y))))] with d hd
  intro v x y z
  linarith [hd v x y z]
end CriticalScaleSequence
end StandardMapEntropy

end OAI
