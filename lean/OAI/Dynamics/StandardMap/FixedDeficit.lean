import OAI.Dynamics.StandardMap.ConeGrowth

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
noncomputable def cosineBad (δ : ℝ) (x : Circle) : ℝ :=
  {x : Circle | |cosine x|≤δ}.indicator (fun _ => 1) x
lemma measurable_cosineBad (δ : ℝ) : Measurable (cosineBad δ) :=
  measurable_const.indicator (isClosed_le continuous_cosine.abs continuous_const).measurableSet
lemma integrable_cosineBad (δ : ℝ) : Integrable (cosineBad δ) volume :=
  (integrable_const _).indicator (isClosed_le continuous_cosine.abs continuous_const).measurableSet
lemma integral_cosineBad (δ : ℝ) : (∫ x,cosineBad δ x ∂volume)=(volume {x : Circle | |cosine x|≤δ}).toReal := by
  unfold cosineBad
  rw [integral_indicator (isClosed_le continuous_cosine.abs continuous_const).measurableSet]
  simp [Measure.real]
lemma circleFst_preserving : MeasurePreserving (Prod.fst : Torus → Circle) area volume :=
  measurePreserving_fst
lemma bad_time_integrable (k δ : ℝ) (i : ℤ) :
    Integrable (fun z => cosineBad δ (torusIter k i z).1) area :=
  (circleFst_preserving.comp (measurePreserving_torusIter k i)).integrable_comp_of_integrable (integrable_cosineBad δ)
lemma bad_time_integral (k δ : ℝ) (i : ℤ) :
    (∫ z,cosineBad δ (torusIter k i z).1 ∂area)=(volume {x : Circle | |cosine x|≤δ}).toReal := by
  calc
    _ = ∫ z,cosineBad δ z.1 ∂area := by
      convert! integral_torusIter k i (fun z => cosineBad δ z.1) using 1
    _ = _ := by rw [area,integral_fun_fst,integral_cosineBad]; simp
lemma potential_large_of_cosine (k δ : ℝ) (hk : 0≤k) (hδ0 : 0<δ) (hδ1 : δ≤1)
    (hM : 12/δ≤growthBase k) (x : Circle) (hx : δ≤|cosine x|) :
    growthBase k*δ/2≤|torusPotential k x| := by
  have hK : 0≤2*Real.pi*k := by positivity
  have ht := abs_sub_abs_le_abs_sub ((2*Real.pi*k)*cosine x) (-2)
  rw [abs_mul,abs_of_nonneg hK] at ht
  have hm := mul_le_mul_of_nonneg_left hx hK
  have hMd : 12≤growthBase k*δ := (div_le_iff₀ hδ0).mp hM
  unfold torusPotential
  have hg : growthBase k=2*Real.pi*k+4 := rfl
  have he : (2*Real.pi*k)*cosine x-(-2)=2+(2*Real.pi*k)*cosine x := by ring
  rw [he] at ht
  norm_num at ht
  nlinarith
lemma shortfall_small_of_cosine (k δ : ℝ) (hk : 0≤k) (hδ0 : 0<δ) (hδ1 : δ≤1)
    (hM : 12/δ≤growthBase k) (n : ℕ) (hn : 0<n) (z : Torus)
    (hgood : ∀ i∈Finset.range n, δ≤|cosine (torusIter k (i:ℤ) z).1|) :
    torusShortfall k z 0 n≤-Real.log (δ/4)/Real.log (growthBase k) := by
  have hMd : 12≤growthBase k*δ := (div_le_iff₀ hδ0).mp hM
  have hMp : 0<growthBase k := by have := growthBase_ge_four k hk; linarith
  have hL : 0<Real.log (growthBase k) := log_growthBase_pos k hk
  have hg := transferProduct_norm_lower_of_coefficients (torusSegmentCoefficient k z 0)
    (growthBase k*δ/2) (by linarith) n (by
      intro i hi hin
      have hidx : (0:ℤ)+(i:ℤ)-1=((i-1:ℕ):ℤ) := by omega
      unfold torusSegmentCoefficient
      rw [hidx]
      exact potential_large_of_cosine k δ hk hδ0 hδ1 hM _ (hgood (i-1) (Finset.mem_range.mpr (by omega))))
  have hlower : (growthBase k*(δ/4))^n≤‖torusSegmentTransfer k z 0 n‖ := by
    apply (pow_le_pow_left₀ (by positivity : 0≤growthBase k*(δ/4)) (by nlinarith : growthBase k*(δ/4)≤growthBase k*δ/2-1) n).trans hg
  have hl := Real.log_le_log (show 0<(growthBase k*(δ/4))^n by positivity) hlower
  rw [Real.log_pow,Real.log_mul hMp.ne' (by positivity : δ/4≠0)] at hl
  have hnpos : (0:ℝ)<n := by exact_mod_cast hn
  unfold torusShortfall
  apply (le_div_iff₀ hL).mpr
  have he : (1-Real.log ‖torusSegmentTransfer k z 0 n‖/((n:ℝ)*Real.log (growthBase k)))*Real.log (growthBase k)=
      Real.log (growthBase k)-Real.log ‖torusSegmentTransfer k z 0 n‖/(n:ℝ) := by field_simp
  rw [he]
  have hnd : Real.log (growthBase k)+Real.log (δ/4)≤Real.log ‖torusSegmentTransfer k z 0 n‖/(n:ℝ) := (le_div_iff₀ hnpos).mpr (by nlinarith [hl])
  nlinarith
lemma fixed_shortfall_pointwise (k δ : ℝ) (hk : 0≤k) (hδ0 : 0<δ) (hδ1 : δ≤1)
    (hM : 12/δ≤growthBase k) (n : ℕ) (hn : 0<n) (z : Torus) :
    torusShortfall k z 0 n≤-Real.log (δ/4)/Real.log (growthBase k)+
      ∑ i∈Finset.range n,cosineBad δ (torusIter k (i:ℤ) z).1 := by
  have h0 (i : ℕ) : 0≤cosineBad δ (torusIter k (i:ℤ) z).1 := by
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  by_cases hg : ∀ i∈Finset.range n, δ≤|cosine (torusIter k (i:ℤ) z).1|
  · exact (shortfall_small_of_cosine k δ hk hδ0 hδ1 hM n hn z hg).trans (le_add_of_nonneg_right (Finset.sum_nonneg (fun i hi => h0 i)))
  · push Not at hg
    obtain ⟨i,hi,hbad⟩ := hg
    have h1 : cosineBad δ (torusIter k (i:ℤ) z).1=1 := by
      simp [cosineBad,le_of_lt hbad]
    have hs := Finset.single_le_sum (fun j _ => h0 j) hi
    rw [h1] at hs
    have hr : 0≤-Real.log (δ/4)/Real.log (growthBase k) :=
      div_nonneg (neg_nonneg.mpr (Real.log_nonpos (by linarith) (by linarith))) (log_growthBase_pos k hk).le
    have hsf := (torusShortfall_mem k hk z 0 n hn).2
    linarith
lemma meanDeficit_eq_integral_shortfall (k : ℝ) (hk : 0≤k) (n : ℕ) :
    meanDeficit k n=∫ z,torusShortfall k z 0 n ∂area := by
  have he (z : Torus) : torusShortfall k z 0 n=1-productDistance k z 0 (n:ℤ)/(n:ℝ) := by
    have hh := productDistance_forward k z 0 n
    simp only [zero_add] at hh
    rw [hh]
    unfold torusShortfall
    ring
  simp_rw [he]
  rw [integral_sub (integrable_const _) ((integrable_productDistance k hk 0 _).div_const _),integral_div]
  simp [meanDeficit]
lemma meanDeficit_fixed_bound (k δ : ℝ) (hk : 0≤k) (hδ0 : 0<δ) (hδ1 : δ≤1)
    (hM : 12/δ≤growthBase k) (n : ℕ) (hn : 0<n) :
    meanDeficit k n≤-Real.log (δ/4)/Real.log (growthBase k)+
      (n:ℝ)*(volume {x : Circle | |cosine x|≤δ}).toReal := by
  rw [meanDeficit_eq_integral_shortfall k hk n]
  have hi : Integrable (fun z => torusShortfall k z 0 n) area :=
    (continuous_torusShortfall k hk 0 n).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hs : Integrable (fun z => ∑ i∈Finset.range n,cosineBad δ (torusIter k (i:ℤ) z).1) area :=
    integrable_finsetSum _ (fun i hi => bad_time_integrable k δ (i:ℤ))
  have hb := integral_mono hi ((integrable_const _).add hs) (fixed_shortfall_pointwise k δ hk hδ0 hδ1 hM n hn)
  have he : (∫ z,-Real.log (δ/4)/Real.log (growthBase k)+∑ i∈Finset.range n,cosineBad δ (torusIter k (i:ℤ) z).1 ∂area)=
      -Real.log (δ/4)/Real.log (growthBase k)+(n:ℝ)*(volume {x : Circle | |cosine x|≤δ}).toReal := by
    rw [integral_add (integrable_const _) hs]
    have he := integral_finsetSum (Finset.range n) (fun (i : ℕ) _ => bad_time_integrable k δ (i:ℤ))
    rw [he]
    simp [bad_time_integral]
  exact he ▸ hb
lemma meanDeficit_fixed_small (n : ℕ) (hn : 0<n) (ε : ℝ) (hε : 0<ε) :
    ∃ M₀ : ℝ, ∀ k : ℝ, 0≤k → M₀≤growthBase k → meanDeficit k n≤ε := by
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  obtain ⟨δ,hδ0,hδ1,hδm⟩ := cosine_small_measure (ε/(2*(n:ℝ))) (by positivity)
  let C := -Real.log (δ/4)
  have hC : 0≤C := neg_nonneg.mpr (Real.log_nonpos (by linarith) (by linarith))
  refine ⟨max (12/δ) (Real.exp (2*C/ε+1)),?_⟩
  intro k hk hM
  have hMd : 12/δ≤growthBase k := (le_max_left _ _).trans hM
  have hMe : Real.exp (2*C/ε+1)≤growthBase k := (le_max_right _ _).trans hM
  have hlog := Real.log_le_log (Real.exp_pos _) hMe
  rw [Real.log_exp] at hlog
  have hr : C/Real.log (growthBase k)≤ε/2 := by
    apply (div_le_iff₀ (log_growthBase_pos k hk)).mpr
    have hm := mul_le_mul_of_nonneg_left hlog (show 0≤ε/2 by positivity)
    have he : (ε/2)*(2*C/ε+1)=C+ε/2 := by field_simp
    rw [he] at hm
    linarith
  have hv := ENNReal.toReal_lt_of_lt_ofReal hδm
  have hnv : (n:ℝ)*(volume {x : Circle | |cosine x|≤δ}).toReal<ε/2 := by
    have hh := (lt_div_iff₀ (show 0<2*(n:ℝ) by positivity)).mp hv
    nlinarith
  have hb := meanDeficit_fixed_bound k δ hk hδ0 hδ1 hMd n hn
  change meanDeficit k n≤C/Real.log (growthBase k)+(n:ℝ)*(volume {x : Circle | |cosine x|≤δ}).toReal at hb
  linarith
end StandardMapEntropy

end OAI
