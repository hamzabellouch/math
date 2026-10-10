import OAI.Combinatorics.HoneycombChords.Interlacing
import OAI.Combinatorics.HoneycombChords.Pollaczek
import OAI.Combinatorics.HoneycombChords.PhysicalFactors

namespace OAI

/-!
# Pollaczek expansions of complete jet families

Formalized from *Critical honeycomb chords with prescribed boundary endpoints*
(OpenAI, September 26, 2026).
-/

section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open MeasureTheory Polynomial
/-- Literal real complete-jet M (N jets at0 and N atL²). -/
noncomputable def twoJetCombination (N : ℕ) (a : Fin (2*N) → ℝ) (x : ℝ) : ℝ :=
  ∑ i,a i*cosineKernelJet (nodalOrder (twoKnotLabels N) i) 0 (twoKnotLabels N i) x
noncomputable def stripSquaredNorm (h : ℝ → ℝ) : ℝ :=
  ∫ p in Set.Ioi (0:ℝ),h (p^2)^2*stripDensity p
/-- Polynomial approximation of complete jets with uniform degree and exponential error. -/
def TwoJetPolynomialApproximation : Prop :=
  ∃ C N₀ : ℕ,0<C ∧ ∀ N : ℕ,N₀ ≤ N → 0<N → ∀ a : Fin (2*N) → ℝ,
    ∃ P : Polynomial ℝ,P.natDegree<C*N ∧
      stripSquaredNorm (fun x=>twoJetCombination N a x-P.eval x) ≤
        Real.exp (-2*(N:ℝ))*stripSquaredNorm (twoJetCombination N a)
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Real Filter Topology MeasureTheory
lemma pollaczek_series_bound_gen {H B : ℝ → ℝ} (hB : ∀ p,0 ≤ B p)
    (hBe : ∀ p,B (-p)=B p) (hH : ∀ p,|H p| ≤ B p) {t : ℝ} (ht : |t| ≤ 1/4) (n : ℕ) (p : ℝ) :
    ‖((pollaczekCoeff p n*H p+pollaczekCoeff (-p) n*H (-p))/Real.cosh (Real.pi*p))*t^n‖ ≤
      (meixnerCoeff |p| n*(1/4)^n)*(2*B p/Real.cosh (Real.pi*p)) := by
  have hq := pollaczekCoeff_abs_le p n
  have hqm := pollaczekCoeff_abs_le (-p) n
  have hh := hH p
  have hhm := hH (-p)
  simp only [abs_neg] at hqm
  rw [hBe] at hhm
  simp only [norm_mul,Real.norm_eq_abs,abs_div,abs_of_pos (Real.cosh_pos _),abs_pow]
  have hb : |pollaczekCoeff p n*H p+pollaczekCoeff (-p) n*H (-p)| ≤
      2*(meixnerCoeff |p| n*(B p)) := by
    calc
      _ ≤ |pollaczekCoeff p n*H p|+|pollaczekCoeff (-p) n*H (-p)| := abs_add_le _ _
      _ ≤ meixnerCoeff |p| n*(B p)+meixnerCoeff |p| n*(B p) := by
        rw [abs_mul,abs_mul]
        exact add_le_add (mul_le_mul hq hh (abs_nonneg _) (meixnerCoeff_nonneg (abs_nonneg p) n))
          (mul_le_mul hqm hhm (abs_nonneg _) (meixnerCoeff_nonneg (abs_nonneg p) n))
      _ = _ := by ring
  calc
    _ ≤ (2*(meixnerCoeff |p| n*(B p))/Real.cosh (Real.pi*p))*(1/4)^n := by
      have hmn := meixnerCoeff_nonneg (abs_nonneg p) n
      have hp := hB p
      gcongr
    _ = _ := by ring
lemma pollaczek_pair_hasSum_gen {H B : ℝ → ℝ} (hHc : Continuous H)
    (hB : ∀ p,0 ≤ B p) (hBe : ∀ p,B (-p)=B p) (hH : ∀ p,|H p| ≤ B p)
    (hBi : IntegrableOn (fun p=>pollaczekMajorant p*B p/Real.cosh (Real.pi*p)) (Set.Ioi 0))
    {t : ℝ} (ht : |t| ≤ 1/4) :
    HasSum (fun n => symmetricSechPair (fun p=>pollaczekCoeff p n) H*t^n)
      (symmetricSechPair (fun p=>pollaczekGenerator p t) H) := by
  let F : ℕ → ℝ → ℝ := fun n p =>
    ((pollaczekCoeff p n*H p+pollaczekCoeff (-p) n*H (-p))/Real.cosh (Real.pi*p))*t^n
  let bound : ℕ → ℝ → ℝ := fun n p =>
    (meixnerCoeff |p| n*(1/4)^n)*(2*B p/Real.cosh (Real.pi*p))
  have hmeas (n : ℕ) : AEStronglyMeasurable (F n) (volume.restrict (Set.Ioi 0)) := by
    apply Continuous.aestronglyMeasurable
    unfold F
    apply Continuous.mul _ continuous_const
    apply Continuous.div _ (by fun_prop) (fun p => (Real.cosh_pos _).ne')
    exact ((pollaczekCoeff_continuous n).mul hHc).add
      (((pollaczekCoeff_continuous n).comp continuous_neg).mul (hHc.comp continuous_neg))
  have hb (n : ℕ) : ∀ᵐ p ∂volume.restrict (Set.Ioi 0), ‖F n p‖ ≤ bound n p :=
    Eventually.of_forall (pollaczek_series_bound_gen hB hBe hH ht n)
  have hsum (p : ℝ) : HasSum (fun n => bound n p)
      (2*(pollaczekMajorant p*B p/Real.cosh (Real.pi*p))) := by
    convert! (meixnerCoeff_hasSum |p| (u:=1/4) (by norm_num)).mul_right
      (2*B p/Real.cosh (Real.pi*p)) using 1
    unfold pollaczekMajorant
    ring
  have hint : Integrable (fun p => ∑' n,bound n p) (volume.restrict (Set.Ioi 0)) := by
    simp_rw [(hsum _).tsum_eq]
    exact hBi.const_mul 2
  have hlim : ∀ᵐ p ∂volume.restrict (Set.Ioi 0),HasSum (fun n=>F n p)
      ((pollaczekGenerator p t*H p+pollaczekGenerator (-p) t*H (-p))/Real.cosh (Real.pi*p)) := by
    apply Eventually.of_forall
    intro p
    convert! ((pollaczekCoeff_hasSum p (t:=t) (by linarith)).mul_right (H p) |>.add
      ((pollaczekCoeff_hasSum (-p) (t:=t) (by linarith)).mul_right (H (-p)))).div_const
        (Real.cosh (Real.pi*p)) using 1
    funext n
    unfold F
    ring
  have hz := hasSum_integral_of_dominated_convergence bound hmeas hb
    (Eventually.of_forall fun p => (hsum p).summable) hint hlim
  simpa only [F,integral_mul_const,symmetricSechPair] using hz


lemma pollaczekMajorant_mul_exp_integrable {a : ℝ}
    (ha : 2*Real.artanh (1/4)+a < Real.pi) :
    IntegrableOn (fun p=>pollaczekMajorant p*Real.exp (a*|p|)/Real.cosh (Real.pi*p)) (Set.Ioi 0) := by
  have hi := (exp_div_cosh_integrable ha).const_mul ((1-(1/4:ℝ)^2)^(-(1:ℝ)/2))
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
  rw [pollaczekMajorant_exp hp.le,abs_of_nonneg hp.le,add_mul,Real.exp_add]
  ring
lemma pollaczekGenerator_exp_bound (p : ℝ) {u : ℝ} (hu : |u|<1) :
    |pollaczekGenerator p u| ≤ Real.exp ((Real.pi/2)*|p|) := by
  rw [pollaczekGenerator,generator_prefactor,abs_mul,abs_of_pos (Real.cos_arctan_pos u),abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ 1*Real.exp ((Real.pi/2)*|p|) := by
      apply mul_le_mul (Real.cos_le_one _) _ (by positivity) (by norm_num)
      apply Real.exp_le_exp.mpr
      calc
        2*p*Real.arctan u ≤ |2*p*Real.arctan u| := le_abs_self _
        _ = 2*|p| *|Real.arctan u| := by rw [abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
        _ ≤ 2*|p| *(Real.pi/4) := mul_le_mul_of_nonneg_left (arctan_quarter_bound hu).le (by positivity)
        _ = _ := by ring
    _ = _ := one_mul _
lemma symmetricSechPair_coeff_generator_full {u : ℝ} (hu : |u| < 1) (n : ℕ) :
    symmetricSechPair (fun p=>pollaczekCoeff p n) (fun p=>pollaczekGenerator p u)=u^n := by
  refine coefficients_unique (a:=fun n => symmetricSechPair (fun p=>pollaczekCoeff p n) (fun p=>pollaczekGenerator p u))
    (b:=fun n=>u^n) (f:=fun t=>1/(1-t*u)) ?_ ?_ n
  · filter_upwards [Metric.ball_mem_nhds (0:ℝ) (by norm_num : (0:ℝ)<1/4)] with t ht
    have ht' : |t| < 1/4 := by simpa [Metric.mem_ball] using ht
    have hs := pollaczek_pair_hasSum_gen (pollaczekGenerator_continuous_p u)
      (B:=fun p=>Real.exp ((Real.pi/2)*|p|)) (fun _=>(Real.exp_pos _).le)
      (fun _=>by rw [abs_neg]) (fun p=>pollaczekGenerator_exp_bound p hu)
      (pollaczekMajorant_mul_exp_integrable (by linarith [quarter_artanh_bounds.2])) ht'.le
    rw [symmetricSechPair_generator (by linarith) hu] at hs
    exact hs
  · filter_upwards [Metric.ball_mem_nhds (0:ℝ) (by norm_num : (0:ℝ)<1)] with t ht
    have ht' : |t| < 1 := by simpa [Metric.mem_ball] using ht
    have hp : ‖t*u‖ < 1 := by rw [Real.norm_eq_abs,abs_mul];nlinarith [abs_nonneg t,abs_nonneg u]
    simpa [mul_pow,mul_comm,one_div] using hasSum_geometric_of_norm_lt_one hp
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Real MeasureTheory Filter
noncomputable def sechPairIntegrand (f g : ℝ → ℝ) (p : ℝ) : ℝ :=
  (f p*g p+f (-p)*g (-p))/Real.cosh (Real.pi*p)
lemma symmetricSechPair_nonneg (f : ℝ → ℝ) : 0 ≤ symmetricSechPair f f := by
  apply integral_nonneg
  intro p
  exact div_nonneg (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)) (Real.cosh_pos _).le
lemma sechPairIntegrand_exp_integrable {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    {C D a b : ℝ} (hC : 0 ≤ C) (hab : a+b<Real.pi)
    (hfB : ∀ p,|f p| ≤ C*Real.exp (a*|p|)) (hgB : ∀ p,|g p| ≤ D*Real.exp (b*|p|)) :
    IntegrableOn (sechPairIntegrand f g) (Set.Ioi 0) := by
  apply ((exp_div_cosh_integrable hab).const_mul (2*C*D)).mono'
  · apply Continuous.aestronglyMeasurable
    unfold sechPairIntegrand
    exact ((hf.mul hg).add ((hf.comp continuous_neg).mul (hg.comp continuous_neg))).div
      (by fun_prop) (fun p=>(Real.cosh_pos _).ne')
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
    rw [Real.norm_eq_abs,sechPairIntegrand,abs_div,abs_of_pos (Real.cosh_pos _)]
    have hp' : 0<p := hp
    have hfp := hfB p
    have hfmp := hfB (-p)
    have hgp := hgB p
    have hgmp := hgB (-p)
    simp only [abs_neg,abs_of_pos hp'] at hfp hfmp hgp hgmp
    calc
      _ ≤ (|f p| *|g p|+|f (-p)| *|g (-p)|)/Real.cosh (Real.pi*p) := by
        gcongr
        simpa only [abs_mul] using abs_add_le (f p*g p) (f (-p)*g (-p))
      _ ≤ ((C*Real.exp (a*p))*(D*Real.exp (b*p))+(C*Real.exp (a*p))*(D*Real.exp (b*p)))/Real.cosh (Real.pi*p) := by
        gcongr
      _ = _ := by rw [add_mul,Real.exp_add];ring
lemma symmetricSechPair_smul_left (f g : ℝ → ℝ) (c : ℝ) :
    symmetricSechPair (fun p=>c*f p) g=c*symmetricSechPair f g := by
  unfold symmetricSechPair
  rw [←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with p
  ring
lemma symmetricSechPair_sum_left {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ) (g : ℝ → ℝ)
    (h : ∀ i∈s,IntegrableOn (sechPairIntegrand (f i) g) (Set.Ioi 0)) :
    symmetricSechPair (fun p=>∑ i∈s,f i p) g=∑ i∈s,symmetricSechPair (f i) g := by
  unfold symmetricSechPair
  simp only [Finset.sum_mul,←Finset.sum_add_distrib,Finset.sum_div]
  exact integral_finsetSum s h
lemma symmetricSechPair_sub_left (f g h : ℝ → ℝ)
    (hf : IntegrableOn (sechPairIntegrand f h) (Set.Ioi 0))
    (hg : IntegrableOn (sechPairIntegrand g h) (Set.Ioi 0)) :
    symmetricSechPair (fun p=>f p-g p) h=symmetricSechPair f h-symmetricSechPair g h := by
  change (∫ p in Set.Ioi (0:ℝ),sechPairIntegrand (fun p=>f p-g p) h p)=
    (∫ p in Set.Ioi (0:ℝ),sechPairIntegrand f h p)-(∫ p in Set.Ioi (0:ℝ),sechPairIntegrand g h p)
  rw [←integral_sub hf hg]
  apply integral_congr_ae
  filter_upwards with p
  unfold sechPairIntegrand
  ring
lemma sechPairIntegrand_smul_left (f g : ℝ → ℝ) (c : ℝ) :
    sechPairIntegrand (fun p=>c*f p) g=fun p=>c*sechPairIntegrand f g p := by
  funext p
  unfold sechPairIntegrand
  ring
lemma sechPairIntegrand_comm (f g : ℝ → ℝ) : sechPairIntegrand f g=sechPairIntegrand g f := by
  funext p
  unfold sechPairIntegrand
  ring
lemma pollaczekCoeff_exp_bound (n : ℕ) (p : ℝ) :
    |pollaczekCoeff p n| ≤ (4^n*(1-(1/4:ℝ)^2)^(-(1:ℝ)/2))*Real.exp (2*Real.artanh (1/4)*|p|) := by
  have he : pollaczekMajorant p=(1-(1/4:ℝ)^2)^(-(1:ℝ)/2)*Real.exp (2*Real.artanh (1/4)*|p|) := by
    rw [pollaczekMajorant,meixnerGenerator_exp (by norm_num)]
    congr 2; ring
  simpa only [he,mul_assoc] using pollaczekCoeff_majorant p n
lemma pollaczekGenerator_exp_bound_sharp (p u : ℝ) :
    |pollaczekGenerator p u| ≤ Real.exp ((2*|Real.arctan u|)*|p|) := by
  rw [pollaczekGenerator,generator_prefactor,abs_mul,abs_of_pos (Real.cos_arctan_pos u),abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ 1*Real.exp ((2*|Real.arctan u|)*|p|) := by
      apply mul_le_mul (Real.cos_le_one _) _ (by positivity) (by norm_num)
      apply Real.exp_le_exp.mpr
      calc
        2*p*Real.arctan u ≤ |2*p*Real.arctan u| := le_abs_self _
        _ = _ := by rw [abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)];ring
    _ = _ := one_mul _
lemma pollaczekCoeff_pair_integrable (n m : ℕ) :
    IntegrableOn (sechPairIntegrand (fun p=>pollaczekCoeff p n) (fun p=>pollaczekCoeff p m)) (Set.Ioi 0) :=
  sechPairIntegrand_exp_integrable (pollaczekCoeff_continuous n) (pollaczekCoeff_continuous m)
    (by positivity) (by linarith [quarter_artanh_bounds.2])
    (pollaczekCoeff_exp_bound n) (pollaczekCoeff_exp_bound m)
lemma pollaczekCoeff_generator_integrable (n : ℕ) {u : ℝ} (hu : |u|<1) :
    IntegrableOn (sechPairIntegrand (fun p=>pollaczekCoeff p n) (fun p=>pollaczekGenerator p u)) (Set.Ioi 0) := by
  apply sechPairIntegrand_exp_integrable (pollaczekCoeff_continuous n) (pollaczekGenerator_continuous_p u)
    (C:=4^n*(1-(1/4:ℝ)^2)^(-(1:ℝ)/2)) (D:=1) (a:=2*Real.artanh (1/4)) (b:=2*|Real.arctan u|)
    (by positivity) (by linarith [quarter_artanh_bounds.2,arctan_quarter_bound hu])
    (pollaczekCoeff_exp_bound n)
  intro p
  simpa only [one_mul] using pollaczekGenerator_exp_bound_sharp p u
lemma pollaczekGenerator_pair_integrable {t u : ℝ} (ht : |t|<1) (hu : |u|<1) :
    IntegrableOn (sechPairIntegrand (fun p=>pollaczekGenerator p t) (fun p=>pollaczekGenerator p u)) (Set.Ioi 0) := by
  apply sechPairIntegrand_exp_integrable (pollaczekGenerator_continuous_p t) (pollaczekGenerator_continuous_p u)
    (C:=1) (D:=1) (a:=2*|Real.arctan t|) (b:=2*|Real.arctan u|)
    (by norm_num) (by linarith [arctan_quarter_bound ht,arctan_quarter_bound hu])
  · intro p;simpa only [one_mul] using pollaczekGenerator_exp_bound_sharp p t
  · intro p;simpa only [one_mul] using pollaczekGenerator_exp_bound_sharp p u
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Real MeasureTheory Polynomial Finset Filter Topology
noncomputable def kernelJetTruncation (r : ℕ) (b : ℝ) (K : ℕ) : Polynomial ℝ :=
  ∑ k∈range K,Polynomial.C ((k.choose r:ℝ)*b^(k-r)/((2*k).factorial:ℝ))*X^k
lemma kernelJetTruncation_eval (r K : ℕ) (b x : ℝ) :
    (kernelJetTruncation r b K).eval x=∑ k∈range K,kernelJetTerm r 0 b x k := by
  simp only [kernelJetTruncation,eval_finsetSum,eval_mul,eval_C,eval_pow,eval_X,
    kernelJetTerm,polynomialJet_X_pow,Nat.choose_zero_right,Nat.cast_one,one_mul,Nat.sub_zero]
  apply sum_congr rfl
  intro k _
  ring
lemma kernelJetTruncation_bounds (r K : ℕ) {b x : ℝ} (hb : 0≤b) (hx : 0≤x) :
    0≤(kernelJetTruncation r b K).eval x ∧ (kernelJetTruncation r b K).eval x≤cosineKernelJet r 0 b x := by
  have hnon (k : ℕ) : 0≤kernelJetTerm r 0 b x k := by
    simp only [kernelJetTerm,polynomialJet_X_pow]
    positivity
  rw [kernelJetTruncation_eval]
  exact ⟨sum_nonneg (fun k _=>hnon k),(kernelJetTerm_summable r 0 b x).sum_le_tsum (range K) (fun k _=>hnon k)⟩
lemma kernelJetTruncation_tendsto (r : ℕ) (b x : ℝ) :
    Tendsto (fun K=>(kernelJetTruncation r b K).eval x) atTop (𝓝 (cosineKernelJet r 0 b x)) := by
  simp only [kernelJetTruncation_eval]
  exact (kernelJetTerm_summable r 0 b x).hasSum.tendsto_sum_nat
lemma kernelJetSech_square_integrable {b δ : ℝ} (hb : 0≤b) (hd : 0<δ)
    (hlim : Real.sqrt (b+δ)<Real.pi/2) (r : ℕ) :
    IntegrableOn (fun p=>(cosineKernelJet r 0 b (p^2))^2/Real.cosh (Real.pi*p)) (Set.Ioi 0) := by
  apply ((exp_div_cosh_integrable (show 2*Real.sqrt (b+δ)<Real.pi by linarith)).const_mul ((δ^(-(r:ℤ)))^2)).mono'
  · apply Continuous.aestronglyMeasurable
    have hc : Continuous (fun x=>cosineKernelJet r 0 b x) := continuous_iff_continuousAt.mpr
      (fun x=>(cosineKernelJet_hasDerivAt_right r 0 b x).continuousAt)
    exact ((hc.comp (continuous_id.pow 2)).pow 2).div (by fun_prop) (fun p=>(Real.cosh_pos _).ne')
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    have hh := cosineKernelJet_exp_bound hb hd r (le_of_lt hp)
    have he : (δ^(-(r:ℤ))*Real.exp (Real.sqrt (b+δ)*p))^2=
        (δ^(-(r:ℤ)))^2*Real.exp ((2*Real.sqrt (b+δ))*p) := by
      rw [mul_pow,←Real.exp_nat_mul]
      congr 2; ring
    rw [←mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (Real.cosh_pos _).le
    calc
      _ = |cosineKernelJet r 0 b (p^2)|^2 := (sq_abs _).symm
      _ ≤ (δ^(-(r:ℤ))*Real.exp (Real.sqrt (b+δ)*p))^2 := by gcongr
      _ = _ := he
lemma kernelJetTruncation_L2_tendsto {b δ : ℝ} (hb : 0≤b) (hd : 0<δ)
    (hlim : Real.sqrt (b+δ)<Real.pi/2) (r : ℕ) :
    Tendsto (fun K=>∫ p in Set.Ioi (0:ℝ),
      (cosineKernelJet r 0 b (p^2)-(kernelJetTruncation r b K).eval (p^2))^2/Real.cosh (Real.pi*p)) atTop (𝓝 0) := by
  have hc : Continuous (fun x=>cosineKernelJet r 0 b x) := continuous_iff_continuousAt.mpr
    (fun x=>(cosineKernelJet_hasDerivAt_right r 0 b x).continuousAt)
  have hh := tendsto_integral_of_dominated_convergence (μ:=volume.restrict (Set.Ioi (0:ℝ)))
    (fun p=>(cosineKernelJet r 0 b (p^2))^2/Real.cosh (Real.pi*p))
    (F:=fun K p=>(cosineKernelJet r 0 b (p^2)-(kernelJetTruncation r b K).eval (p^2))^2/Real.cosh (Real.pi*p))
    (f:=fun _=>0)
  convert! hh ?_ (kernelJetSech_square_integrable hb hd hlim r) ?_ ?_ using 1 <;> try simp only [integral_zero]
  · intro K
    apply Continuous.aestronglyMeasurable
    exact (((hc.comp (continuous_id.pow 2)).sub ((kernelJetTruncation r b K).continuous.comp (continuous_id.pow 2))).pow 2).div
      (by fun_prop) (fun p=>(Real.cosh_pos _).ne')
  · intro K
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    apply div_le_div_of_nonneg_right _ (Real.cosh_pos _).le
    obtain ⟨hl,hu⟩ := kernelJetTruncation_bounds r K hb (sq_nonneg p)
    have hj:=cosineKernelJet_nonneg hb (sq_nonneg p) r 0
    nlinarith
  · filter_upwards with p
    convert! ((tendsto_const_nhds.sub (kernelJetTruncation_tendsto r b (p^2))).pow 2).div_const (Real.cosh (Real.pi*p)) using 1; simp
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Real MeasureTheory Filter Finset
noncomputable def pollaczekFinite (s : Finset ℕ) (a : ℕ → ℝ) (p : ℝ) : ℝ :=
  ∑ n∈s,a n*pollaczekCoeff p n
lemma sechPairIntegrand_pollaczekFinite (s : Finset ℕ) (a : ℕ → ℝ) (f : ℝ → ℝ) :
    sechPairIntegrand (pollaczekFinite s a) f=
      fun p=>∑ n∈s,a n*sechPairIntegrand (fun p=>pollaczekCoeff p n) f p := by
  funext p
  simp only [sechPairIntegrand,pollaczekFinite,sum_mul,←sum_add_distrib,sum_div]
  apply sum_congr rfl
  intro n _
  ring
lemma sechPairIntegrand_pollaczekFinite_integrable (s : Finset ℕ) (a : ℕ → ℝ) (f : ℝ → ℝ)
    (h : ∀ n∈s,IntegrableOn (sechPairIntegrand (fun p=>pollaczekCoeff p n) f) (Set.Ioi 0)) :
    IntegrableOn (sechPairIntegrand (pollaczekFinite s a) f) (Set.Ioi 0) := by
  rw [sechPairIntegrand_pollaczekFinite]
  exact integrable_finsetSum s (fun n hn=>(h n hn).const_mul (a n))
lemma symmetricSechPair_pollaczekFinite (s : Finset ℕ) (a : ℕ → ℝ) (f : ℝ → ℝ)
    (h : ∀ n∈s,IntegrableOn (sechPairIntegrand (fun p=>pollaczekCoeff p n) f) (Set.Ioi 0)) :
    symmetricSechPair (pollaczekFinite s a) f=∑ n∈s,a n*symmetricSechPair (fun p=>pollaczekCoeff p n) f := by
  change (∫ p in Set.Ioi (0:ℝ),sechPairIntegrand (pollaczekFinite s a) f p)=_
  rw [sechPairIntegrand_pollaczekFinite,integral_finsetSum s (fun n hn=>(h n hn).const_mul (a n))]
  simp only [integral_const_mul,symmetricSechPair,sechPairIntegrand]
lemma pollaczekFinite_coeff (s : Finset ℕ) (a : ℕ → ℝ) (n : ℕ) :
    symmetricSechPair (pollaczekFinite s a) (fun p=>pollaczekCoeff p n)=if n∈s then a n else 0 := by
  rw [symmetricSechPair_pollaczekFinite s a _ (fun _ _=>pollaczekCoeff_pair_integrable _ n)]
  simp only [symmetricSechPair_orthogonal,mul_ite,mul_one,mul_zero]
  simp
lemma pollaczekFinite_pair_integrable (s t : Finset ℕ) (a b : ℕ → ℝ) :
    IntegrableOn (sechPairIntegrand (pollaczekFinite s a) (pollaczekFinite t b)) (Set.Ioi 0) := by
  apply sechPairIntegrand_pollaczekFinite_integrable
  intro n _
  rw [sechPairIntegrand_comm]
  exact sechPairIntegrand_pollaczekFinite_integrable t b _ (fun _ _=>pollaczekCoeff_pair_integrable _ n)
lemma pollaczekFinite_norm (s : Finset ℕ) (a : ℕ → ℝ) :
    symmetricSechPair (pollaczekFinite s a) (pollaczekFinite s a)=∑ n∈s,(a n)^2 := by
  rw [symmetricSechPair_pollaczekFinite]
  · apply sum_congr rfl
    intro n hn
    rw [symmetricSechPair_comm,pollaczekFinite_coeff,ite_eq_left hn,pow_two]
  · intro n _
    rw [sechPairIntegrand_comm]
    exact sechPairIntegrand_pollaczekFinite_integrable s a _ (fun _ _=>pollaczekCoeff_pair_integrable _ n)
lemma sechPairIntegrand_sub_left (f g h : ℝ → ℝ) :
    sechPairIntegrand (fun p=>f p-g p) h=fun p=>sechPairIntegrand f h p-sechPairIntegrand g h p := by
  funext p
  unfold sechPairIntegrand
  ring
lemma symmetricSechPair_difference_norm (f g : ℝ → ℝ)
    (hff : IntegrableOn (sechPairIntegrand f f) (Set.Ioi 0))
    (hgg : IntegrableOn (sechPairIntegrand g g) (Set.Ioi 0))
    (hfg : IntegrableOn (sechPairIntegrand f g) (Set.Ioi 0)) :
    symmetricSechPair (fun p=>f p-g p) (fun p=>f p-g p)=
      symmetricSechPair f f-2*symmetricSechPair f g+symmetricSechPair g g := by
  have hgf : IntegrableOn (sechPairIntegrand g f) (Set.Ioi 0) := by rw [sechPairIntegrand_comm];exact hfg
  rw [symmetricSechPair_sub_left]
  · rw [symmetricSechPair_comm f (fun p=>f p-g p),symmetricSechPair_sub_left _ _ _ hff hgf,
      symmetricSechPair_comm g (fun p=>f p-g p),symmetricSechPair_sub_left _ _ _ hfg hgg,symmetricSechPair_comm g f]
    ring
  · rw [sechPairIntegrand_comm,sechPairIntegrand_sub_left]
    exact hff.sub hgf
  · rw [sechPairIntegrand_comm,sechPairIntegrand_sub_left]
    exact hfg.sub hgg
lemma pollaczek_projection_squared_error (s : Finset ℕ) (f : ℝ → ℝ)
    (hff : IntegrableOn (sechPairIntegrand f f) (Set.Ioi 0))
    (hf : ∀ n∈s,IntegrableOn (sechPairIntegrand (fun p=>pollaczekCoeff p n) f) (Set.Ioi 0)) :
    let a := fun n=>symmetricSechPair (fun p=>pollaczekCoeff p n) f
    symmetricSechPair (fun p=>f p-pollaczekFinite s a p) (fun p=>f p-pollaczekFinite s a p)=
      symmetricSechPair f f-∑ n∈s,(a n)^2 := by
  intro a
  rw [symmetricSechPair_difference_norm f _ hff (pollaczekFinite_pair_integrable _ _ _ _)
    (by rw [sechPairIntegrand_comm];exact sechPairIntegrand_pollaczekFinite_integrable s a f hf),
    pollaczekFinite_norm,symmetricSechPair_comm f (pollaczekFinite s a),symmetricSechPair_pollaczekFinite s a f hf]
  change symmetricSechPair f f-2*(∑ n∈s,a n*a n)+(∑ n∈s,(a n)^2)=_
  simp only [←pow_two]
  ring
lemma pollaczek_bessel (s : Finset ℕ) (f : ℝ → ℝ)
    (hff : IntegrableOn (sechPairIntegrand f f) (Set.Ioi 0))
    (hf : ∀ n∈s,IntegrableOn (sechPairIntegrand (fun p=>pollaczekCoeff p n) f) (Set.Ioi 0)) :
    (∑ n∈s,(symmetricSechPair (fun p=>pollaczekCoeff p n) f)^2) ≤ symmetricSechPair f f := by
  have h:=symmetricSechPair_nonneg (fun p=>f p-pollaczekFinite s (fun n=>symmetricSechPair (fun p=>pollaczekCoeff p n) f) p)
  rw [pollaczek_projection_squared_error s f hff hf] at h
  linarith
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Real MeasureTheory Polynomial Finset
noncomputable def evenPollaczekFinite (K : ℕ) (a : Fin K → ℝ) (p : ℝ) : ℝ :=
  ∑ j,a j*pollaczekCoeff p (2*j)
lemma evenPollaczekFinite_polynomial (K : ℕ) (a : Fin K → ℝ) (p : ℝ) :
    evenPollaczekFinite K a p=(∑ j,a j • evenPoly (-1) j).eval (p^2) := by
  simp only [evenPollaczekFinite,eval_finsetSum,eval_smul,smul_eq_mul]
  apply sum_congr rfl
  intro i _
  rw [←(pollaczekCoeff_evenOdd p i).1]
lemma polynomial_evenPollaczekFinite (P : Polynomial ℝ) {n : ℕ} (hn : P.natDegree≤n) :
    ∃ a : Fin (n+1) → ℝ,(fun p=>P.eval (p^2))=evenPollaczekFinite (n+1) a := by
  obtain ⟨a,ha⟩:=polynomial_eq_pollaczek_sum P hn
  refine ⟨a,funext (fun p=>?_)⟩
  rw [evenPollaczekFinite_polynomial,ha]
lemma sechPairIntegrand_evenFinite (K : ℕ) (a : Fin K → ℝ) (f : ℝ → ℝ) :
    sechPairIntegrand (evenPollaczekFinite K a) f=
      fun p=>∑ j,a j*sechPairIntegrand (fun p=>pollaczekCoeff p (2*j)) f p := by
  funext p
  simp only [sechPairIntegrand,evenPollaczekFinite,sum_mul,←sum_add_distrib,sum_div]
  apply sum_congr rfl
  intro j _
  ring
lemma evenFinite_pair_integrable (K : ℕ) (a : Fin K → ℝ) (f : ℝ → ℝ)
    (hf : ∀ j:Fin K,IntegrableOn (sechPairIntegrand (fun p=>pollaczekCoeff p (2*j)) f) (Set.Ioi 0)) :
    IntegrableOn (sechPairIntegrand (evenPollaczekFinite K a) f) (Set.Ioi 0) := by
  rw [sechPairIntegrand_evenFinite]
  exact integrable_finsetSum _ (fun j _=>(hf j).const_mul _)
lemma evenFinite_pair (K : ℕ) (a : Fin K → ℝ) (f : ℝ → ℝ)
    (hf : ∀ j:Fin K,IntegrableOn (sechPairIntegrand (fun p=>pollaczekCoeff p (2*j)) f) (Set.Ioi 0)) :
    symmetricSechPair (evenPollaczekFinite K a) f=
      ∑ j,a j*symmetricSechPair (fun p=>pollaczekCoeff p (2*j)) f := by
  change (∫ p in Set.Ioi (0:ℝ),sechPairIntegrand (evenPollaczekFinite K a) f p)=_
  rw [sechPairIntegrand_evenFinite,integral_finsetSum univ (fun j _=>(hf j).const_mul (a j))]
  simp only [integral_const_mul,symmetricSechPair,sechPairIntegrand]
lemma evenFinite_coeff (K : ℕ) (a : Fin K → ℝ) (j : Fin K) :
    symmetricSechPair (evenPollaczekFinite K a) (fun p=>pollaczekCoeff p (2*j))=a j := by
  rw [evenFinite_pair K a _ (fun i=>pollaczekCoeff_pair_integrable _ _)]
  simp only [symmetricSechPair_orthogonal]
  have he (i : Fin K) : (2*(i:ℕ)=2*j)↔i=j := by constructor <;> intro h <;> omega
  simp only [he,mul_ite,mul_one,mul_zero]
  simp
lemma evenFinite_square_integrable (K : ℕ) (a : Fin K → ℝ) :
    IntegrableOn (sechPairIntegrand (evenPollaczekFinite K a) (evenPollaczekFinite K a)) (Set.Ioi 0) := by
  apply evenFinite_pair_integrable
  intro j
  rw [sechPairIntegrand_comm]
  exact evenFinite_pair_integrable K a _ (fun _=>pollaczekCoeff_pair_integrable _ _)
lemma evenFinite_norm (K : ℕ) (a : Fin K → ℝ) :
    symmetricSechPair (evenPollaczekFinite K a) (evenPollaczekFinite K a)=∑ j,(a j)^2 := by
  rw [evenFinite_pair K a _ (fun j=>by
    rw [sechPairIntegrand_comm];exact evenFinite_pair_integrable K a _ (fun _=>pollaczekCoeff_pair_integrable _ _))]
  apply sum_congr rfl
  intro j _
  rw [symmetricSechPair_comm,evenFinite_coeff,pow_two]
lemma even_projection_error (K : ℕ) (f : ℝ → ℝ)
    (hff : IntegrableOn (sechPairIntegrand f f) (Set.Ioi 0))
    (hf : ∀ j:Fin K,IntegrableOn (sechPairIntegrand (fun p=>pollaczekCoeff p (2*j)) f) (Set.Ioi 0))
    (a : Fin K → ℝ) :
    symmetricSechPair (fun p=>f p-evenPollaczekFinite K a p) (fun p=>f p-evenPollaczekFinite K a p)=
      symmetricSechPair f f-2*(∑ j,a j*symmetricSechPair (fun p=>pollaczekCoeff p (2*j)) f)+∑ j,(a j)^2 := by
  rw [symmetricSechPair_difference_norm f _ hff (evenFinite_square_integrable K a)
    (by rw [sechPairIntegrand_comm];exact evenFinite_pair_integrable K a f hf),
    evenFinite_norm,symmetricSechPair_comm f (evenPollaczekFinite K a),evenFinite_pair K a f hf]
lemma even_projection_minimal (K : ℕ) (f : ℝ → ℝ)
    (hff : IntegrableOn (sechPairIntegrand f f) (Set.Ioi 0))
    (hf : ∀ j:Fin K,IntegrableOn (sechPairIntegrand (fun p=>pollaczekCoeff p (2*j)) f) (Set.Ioi 0))
    (a : Fin K → ℝ) :
    symmetricSechPair f f-∑ j:Fin K,(symmetricSechPair (fun p=>pollaczekCoeff p (2*j)) f)^2 ≤
      symmetricSechPair (fun p=>f p-evenPollaczekFinite K a p) (fun p=>f p-evenPollaczekFinite K a p) := by
  rw [even_projection_error K f hff hf a]
  have h:=sum_nonneg (s:=univ) (fun (j:Fin K) _=>sq_nonneg (a j-symmetricSechPair (fun p=>pollaczekCoeff p (2*j)) f))
  simp only [sub_sq,sum_add_distrib,sum_sub_distrib,mul_assoc,←mul_sum] at h
  linarith
lemma even_projection_bessel (K : ℕ) (f : ℝ → ℝ)
    (hff : IntegrableOn (sechPairIntegrand f f) (Set.Ioi 0))
    (hf : ∀ j:Fin K,IntegrableOn (sechPairIntegrand (fun p=>pollaczekCoeff p (2*j)) f) (Set.Ioi 0)) :
    0 ≤ symmetricSechPair f f-∑ j:Fin K,(symmetricSechPair (fun p=>pollaczekCoeff p (2*j)) f)^2 := by
  have h:=symmetricSechPair_nonneg (fun p=>f p-evenPollaczekFinite K
    (fun j=>symmetricSechPair (fun p=>pollaczekCoeff p (2*j)) f) p)
  rw [even_projection_error K f hff hf] at h
  simp only [←pow_two] at h
  linarith
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Real MeasureTheory Polynomial Finset Filter Topology
lemma kernelJetTruncation_degree (r n : ℕ) (b : ℝ) :
    (kernelJetTruncation r b (n+1)).natDegree≤n := by
  apply natDegree_sum_le_of_forall_le
  intro k hk
  exact ((natDegree_C_mul_le _ _).trans (show (X^k:Polynomial ℝ).natDegree≤k by simp)).trans (by have:=mem_range.mp hk;omega)
lemma kernelJetSech_pair_integrable {b δ : ℝ} (hb : 0≤b) (hd : 0<δ)
    (hlim : Real.sqrt (b+δ)<Real.pi/2) (r n : ℕ) :
    IntegrableOn (sechPairIntegrand (fun p=>pollaczekCoeff p n) (fun p=>cosineKernelJet r 0 b (p^2))) (Set.Ioi 0) := by
  have hc : Continuous (fun p=>cosineKernelJet r 0 b (p^2)) :=
    (continuous_iff_continuousAt.mpr (fun x=>(cosineKernelJet_hasDerivAt_right r 0 b x).continuousAt)).comp
      (continuous_id.pow 2)
  apply sechPairIntegrand_exp_integrable (pollaczekCoeff_continuous n) hc
    (C:=4^n*(1-(1/4:ℝ)^2)^(-(1:ℝ)/2)) (D:=δ^(-(r:ℤ)))
    (a:=2*Real.artanh (1/4)) (b:=Real.sqrt (b+δ)) (by positivity)
    (by linarith [quarter_artanh_bounds.2]) (pollaczekCoeff_exp_bound n)
  intro p
  simpa only [sq_abs] using cosineKernelJet_exp_bound hb hd r (abs_nonneg p)
lemma evenSech_squaredNorm (f : ℝ → ℝ) :
    symmetricSechPair (fun p=>f (p^2)) (fun p=>f (p^2))=
      2*(∫ p in Set.Ioi (0:ℝ),(f (p^2))^2/Real.cosh (Real.pi*p)) := by
  unfold symmetricSechPair
  rw [←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with p
  simp only [neg_sq]
  ring
lemma kernelJetSech_norm_integrable {b δ : ℝ} (hb : 0≤b) (hd : 0<δ)
    (hlim : Real.sqrt (b+δ)<Real.pi/2) (r : ℕ) :
    IntegrableOn (sechPairIntegrand (fun p=>cosineKernelJet r 0 b (p^2)) (fun p=>cosineKernelJet r 0 b (p^2))) (Set.Ioi 0) := by
  have he : sechPairIntegrand (fun p=>cosineKernelJet r 0 b (p^2)) (fun p=>cosineKernelJet r 0 b (p^2))=
      fun p=>2*((cosineKernelJet r 0 b (p^2))^2/Real.cosh (Real.pi*p)) := by
    funext p
    simp only [sechPairIntegrand,neg_sq]
    ring
  rw [he]
  exact (kernelJetSech_square_integrable hb hd hlim r).const_mul 2
lemma kernelJetSech_parseval_residual {b δ : ℝ} (hb : 0≤b) (hd : 0<δ)
    (hlim : Real.sqrt (b+δ)<Real.pi/2) (r : ℕ) :
    Tendsto (fun n=>symmetricSechPair (fun p=>cosineKernelJet r 0 b (p^2)) (fun p=>cosineKernelJet r 0 b (p^2))-
      ∑ j:Fin (n+1),(symmetricSechPair (fun p=>pollaczekCoeff p (2*j)) (fun p=>cosineKernelJet r 0 b (p^2)))^2)
      atTop (𝓝 0) := by
  let f:=fun p=>cosineKernelJet r 0 b (p^2)
  apply squeeze_zero (g:=fun n=>2*(∫ p in Set.Ioi (0:ℝ),
      (cosineKernelJet r 0 b (p^2)-(kernelJetTruncation r b (n+1)).eval (p^2))^2/Real.cosh (Real.pi*p))) (fun n=>even_projection_bessel (n+1) f (kernelJetSech_norm_integrable hb hd hlim r)
    (fun j=>kernelJetSech_pair_integrable hb hd hlim r (2*j)))
  · intro n
    obtain ⟨a,ha⟩:=polynomial_evenPollaczekFinite (kernelJetTruncation r b (n+1)) (kernelJetTruncation_degree r n b)
    have hh:=even_projection_minimal (n+1) f (kernelJetSech_norm_integrable hb hd hlim r)
      (fun j=>kernelJetSech_pair_integrable hb hd hlim r (2*j)) a
    rw [←ha] at hh
    change _ ≤ symmetricSechPair (fun p=>(fun x=>cosineKernelJet r 0 b x-(kernelJetTruncation r b (n+1)).eval x) (p^2))
      (fun p=>(fun x=>cosineKernelJet r 0 b x-(kernelJetTruncation r b (n+1)).eval x) (p^2)) at hh
    rw [evenSech_squaredNorm (fun x=>cosineKernelJet r 0 b x-(kernelJetTruncation r b (n+1)).eval x)] at hh
    exact hh
  · have hh:=((kernelJetTruncation_L2_tendsto hb hd hlim r).comp (tendsto_add_atTop_nat 1)).const_mul 2
    simpa only [Function.comp_apply,mul_zero] using hh
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Real MeasureTheory Polynomial Finset Filter Topology
noncomputable def finiteJetCombination (M : ℕ) (a b : Fin M → ℝ) (r : Fin M → ℕ) (x : ℝ) : ℝ :=
  ∑ i,a i*cosineKernelJet (r i) 0 (b i) x
noncomputable def finiteJetTruncation (M K : ℕ) (a b : Fin M → ℝ) (r : Fin M → ℕ) : Polynomial ℝ :=
  ∑ i,a i • kernelJetTruncation (r i) (b i) K
lemma finiteJetTruncation_eval (M K : ℕ) (a b : Fin M → ℝ) (r : Fin M → ℕ) (x : ℝ) :
    (finiteJetTruncation M K a b r).eval x=∑ i,a i*(kernelJetTruncation (r i) (b i) K).eval x := by
  simp only [finiteJetTruncation,eval_finsetSum,eval_smul,smul_eq_mul]
lemma finiteJetTruncation_degree (M n : ℕ) (a b : Fin M → ℝ) (r : Fin M → ℕ) :
    (finiteJetTruncation M (n+1) a b r).natDegree≤n := by
  apply natDegree_sum_le_of_forall_le
  intro i _
  rw [Polynomial.smul_eq_C_mul]
  exact (natDegree_C_mul_le _ _).trans (kernelJetTruncation_degree (r i) n (b i))
lemma finiteJetCombination_continuous (M : ℕ) (a b : Fin M → ℝ) (r : Fin M → ℕ) :
    Continuous (finiteJetCombination M a b r) := by
  apply continuous_finsetSum
  intro i _
  exact (continuous_iff_continuousAt.mpr (fun x=>(cosineKernelJet_hasDerivAt_right (r i) 0 (b i) x).continuousAt)).const_mul _
lemma finiteJetTruncation_error_bound (M K : ℕ) (a b : Fin M → ℝ) (r : Fin M → ℕ)
    (hb : ∀ i,0≤b i) {x : ℝ} (hx : 0≤x) :
    (finiteJetCombination M a b r x-(finiteJetTruncation M K a b r).eval x)^2 ≤
      (∑ i,(a i)^2)*(∑ i,(cosineKernelJet (r i) 0 (b i) x)^2) := by
  rw [finiteJetTruncation_eval,finiteJetCombination,←sum_sub_distrib]
  simp only [←mul_sub]
  apply (sum_mul_sq_le_sq_mul_sq univ a (fun i=>cosineKernelJet (r i) 0 (b i) x-(kernelJetTruncation (r i) (b i) K).eval x)).trans
  apply mul_le_mul_of_nonneg_left _ (sum_nonneg (fun i _=>sq_nonneg _))
  apply sum_le_sum
  intro i _
  obtain ⟨hl,hu⟩:=kernelJetTruncation_bounds (r i) K (hb i) hx
  have hJ:=cosineKernelJet_nonneg (hb i) hx (r i) 0
  nlinarith
lemma finiteJetTruncation_L2_tendsto (M : ℕ) (a b δ : Fin M → ℝ) (r : Fin M → ℕ)
    (hb : ∀ i,0≤b i) (hd : ∀ i,0<δ i) (hlim : ∀ i,Real.sqrt (b i+δ i)<Real.pi/2) :
    Tendsto (fun K=>∫ p in Set.Ioi (0:ℝ),
      (finiteJetCombination M a b r (p^2)-(finiteJetTruncation M K a b r).eval (p^2))^2/Real.cosh (Real.pi*p)) atTop (𝓝 0) := by
  let B:=fun p=>(∑ i,(a i)^2)*(∑ i,(cosineKernelJet (r i) 0 (b i) (p^2))^2/Real.cosh (Real.pi*p))
  have hB : IntegrableOn B (Set.Ioi 0) :=
    (integrable_finsetSum univ (fun i _=>kernelJetSech_square_integrable (hb i) (hd i) (hlim i) (r i))).const_mul _
  have hh:=tendsto_integral_of_dominated_convergence (μ:=volume.restrict (Set.Ioi (0:ℝ))) B
    (F:=fun K p=>(finiteJetCombination M a b r (p^2)-(finiteJetTruncation M K a b r).eval (p^2))^2/Real.cosh (Real.pi*p))
    (f:=fun _=>0)
  convert! hh ?_ hB ?_ ?_ using 1 <;> try simp only [integral_zero]
  · intro K
    apply Continuous.aestronglyMeasurable
    exact ((((finiteJetCombination_continuous M a b r).comp (continuous_id.pow 2)).sub
      ((finiteJetTruncation M K a b r).continuous.comp (continuous_id.pow 2))).pow 2).div (by fun_prop) (fun p=>(Real.cosh_pos _).ne')
  · intro K
    filter_upwards with p
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    change _≤(∑ i,(a i)^2)*(∑ i,(cosineKernelJet (r i) 0 (b i) (p^2))^2/_)
    rw [←sum_div,←mul_div_assoc]
    exact div_le_div_of_nonneg_right (finiteJetTruncation_error_bound M K a b r hb (sq_nonneg p)) (Real.cosh_pos _).le
  · filter_upwards with p
    have ht : Tendsto (fun K=>(finiteJetTruncation M K a b r).eval (p^2)) atTop (𝓝 (finiteJetCombination M a b r (p^2))) := by
      simp only [finiteJetTruncation_eval,finiteJetCombination]
      exact tendsto_finsetSum univ (fun i _=>(kernelJetTruncation_tendsto (r i) (b i) (p^2)).const_mul (a i))
    convert! ((tendsto_const_nhds.sub ht).pow 2).div_const (Real.cosh (Real.pi*p)) using 1; simp
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Real MeasureTheory Polynomial Finset Filter Topology
lemma finiteJetSech_pair_integrable (M : ℕ) (a b δ : Fin M → ℝ) (r : Fin M → ℕ)
    (hb : ∀ i,0≤b i) (hd : ∀ i,0<δ i) (hlim : ∀ i,Real.sqrt (b i+δ i)<Real.pi/2) (n : ℕ) :
    IntegrableOn (sechPairIntegrand (fun p=>pollaczekCoeff p n) (fun p=>finiteJetCombination M a b r (p^2))) (Set.Ioi 0) := by
  have he : sechPairIntegrand (fun p=>pollaczekCoeff p n) (fun p=>finiteJetCombination M a b r (p^2))=
      fun p=>∑ i,a i*sechPairIntegrand (fun p=>pollaczekCoeff p n) (fun p=>cosineKernelJet (r i) 0 (b i) (p^2)) p := by
    funext p
    simp only [sechPairIntegrand,finiteJetCombination,mul_sum,←sum_add_distrib,sum_div]
    apply sum_congr rfl
    intro i _
    ring
  rw [he]
  exact integrable_finsetSum univ (fun i _=>(kernelJetSech_pair_integrable (hb i) (hd i) (hlim i) (r i) n).const_mul _)
lemma finiteJetSech_norm_integrable (M : ℕ) (a b δ : Fin M → ℝ) (r : Fin M → ℕ)
    (hb : ∀ i,0≤b i) (hd : ∀ i,0<δ i) (hlim : ∀ i,Real.sqrt (b i+δ i)<Real.pi/2) :
    IntegrableOn (sechPairIntegrand (fun p=>finiteJetCombination M a b r (p^2)) (fun p=>finiteJetCombination M a b r (p^2))) (Set.Ioi 0) := by
  let B:=fun p=>2*(∑ i,(a i)^2)*(∑ i,(cosineKernelJet (r i) 0 (b i) (p^2))^2/Real.cosh (Real.pi*p))
  have hB : IntegrableOn B (Set.Ioi 0) :=
    (integrable_finsetSum univ (fun i _=>kernelJetSech_square_integrable (hb i) (hd i) (hlim i) (r i))).const_mul _
  refine hB.mono' ?_ ?_
  · apply Continuous.aestronglyMeasurable
    have hc:Continuous (fun p=>finiteJetCombination M a b r (p^2)):=
      (finiteJetCombination_continuous M a b r).comp (continuous_id.pow 2)
    exact ((hc.mul hc).add ((hc.comp continuous_neg).mul (hc.comp continuous_neg))).div
      (by fun_prop) (fun p=>(Real.cosh_pos _).ne')
  · filter_upwards with p
    have hh:=finiteJetTruncation_error_bound M 0 a b r hb (sq_nonneg p)
    simp only [finiteJetTruncation,kernelJetTruncation,sum_range_zero,smul_zero,sum_const_zero,eval_zero,sub_zero] at hh
    simp only [sechPairIntegrand,neg_sq,Real.norm_eq_abs]
    rw [abs_of_nonneg (div_nonneg (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)) (Real.cosh_pos _).le)]
    dsimp [B]
    rw [←sum_div,←mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (Real.cosh_pos _).le
    nlinarith
lemma finiteJetSech_parseval_residual (M : ℕ) (a b δ : Fin M → ℝ) (r : Fin M → ℕ)
    (hb : ∀ i,0≤b i) (hd : ∀ i,0<δ i) (hlim : ∀ i,Real.sqrt (b i+δ i)<Real.pi/2) :
    Tendsto (fun n=>symmetricSechPair (fun p=>finiteJetCombination M a b r (p^2)) (fun p=>finiteJetCombination M a b r (p^2))-
      ∑ j:Fin (n+1),(symmetricSechPair (fun p=>pollaczekCoeff p (2*j)) (fun p=>finiteJetCombination M a b r (p^2)))^2)
      atTop (𝓝 0) := by
  let f:=fun p=>finiteJetCombination M a b r (p^2)
  have hff:=finiteJetSech_norm_integrable M a b δ r hb hd hlim
  have hf:=finiteJetSech_pair_integrable M a b δ r hb hd hlim
  apply squeeze_zero (g:=fun n=>2*(∫ p in Set.Ioi (0:ℝ),
      (finiteJetCombination M a b r (p^2)-(finiteJetTruncation M (n+1) a b r).eval (p^2))^2/Real.cosh (Real.pi*p)))
    (fun n=>even_projection_bessel (n+1) f hff (fun j=>hf (2*j)))
  · intro n
    obtain ⟨c,hc⟩:=polynomial_evenPollaczekFinite (finiteJetTruncation M (n+1) a b r) (finiteJetTruncation_degree M n a b r)
    have hh:=even_projection_minimal (n+1) f hff (fun j=>hf (2*j)) c
    rw [←hc] at hh
    change _ ≤ symmetricSechPair (fun p=>(fun x=>finiteJetCombination M a b r x-(finiteJetTruncation M (n+1) a b r).eval x) (p^2))
      (fun p=>(fun x=>finiteJetCombination M a b r x-(finiteJetTruncation M (n+1) a b r).eval x) (p^2)) at hh
    rw [evenSech_squaredNorm (fun x=>finiteJetCombination M a b r x-(finiteJetTruncation M (n+1) a b r).eval x)] at hh
    exact hh
  · have hh:=((finiteJetTruncation_L2_tendsto M a b δ r hb hd hlim).comp (tendsto_add_atTop_nat 1)).const_mul 2
    simpa only [Function.comp_apply,mul_zero] using hh
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Polynomial
noncomputable def jetCoshPolynomial (m : ℝ) : ℕ → Polynomial ℝ
  | 0 => 1
  | 1 => 0
  | r+2 => Polynomial.C ((4*m^2*((r:ℝ)+1)*((r:ℝ)+2))⁻¹)*
      (X^2*jetCoshPolynomial m r-Polynomial.C (2*((r:ℝ)+1)*(2*(r:ℝ)+1))*jetCoshPolynomial m (r+1))
noncomputable def jetSinhPolynomial (m : ℝ) : ℕ → Polynomial ℝ
  | 0 => 0
  | 1 => Polynomial.C ((2*m)⁻¹)*X
  | r+2 => Polynomial.C ((4*m^2*((r:ℝ)+1)*((r:ℝ)+2))⁻¹)*
      (X^2*jetSinhPolynomial m r-Polynomial.C (2*((r:ℝ)+1)*(2*(r:ℝ)+1))*jetSinhPolynomial m (r+1))
lemma jetPolynomial_degrees (m : ℝ) (r : ℕ) :
    (jetCoshPolynomial m r).natDegree≤r ∧ (jetSinhPolynomial m r).natDegree≤r := by
  induction r using Nat.twoStepInduction with
  | zero => simp [jetCoshPolynomial,jetSinhPolynomial]
  | one =>
    constructor
    · simp [jetCoshPolynomial]
    · exact (natDegree_C_mul_le _ _).trans (by simp)
  | more r ih ih' =>
    constructor
    · rw [jetCoshPolynomial]
      apply (natDegree_C_mul_le _ _).trans
      apply (natDegree_sub_le _ _).trans
      apply max_le
      · apply natDegree_mul_le.trans
        have hh := Nat.add_le_add (show (X^2:Polynomial ℝ).natDegree≤2 by simp) ih.1
        omega
      · exact ((natDegree_C_mul_le _ _).trans ih'.1).trans (by omega)
    · rw [jetSinhPolynomial]
      apply (natDegree_C_mul_le _ _).trans
      apply (natDegree_sub_le _ _).trans
      apply max_le
      · apply natDegree_mul_le.trans
        have hh := Nat.add_le_add (show (X^2:Polynomial ℝ).natDegree≤2 by simp) ih.2
        omega
      · exact ((natDegree_C_mul_le _ _).trans ih'.2).trans (by omega)
lemma cosineKernelJet_polynomials {m : ℝ} (hm : m≠0) (r : ℕ) (p : ℝ) :
    cosineKernelJet r 0 (m^2) (p^2)=
      (jetCoshPolynomial m r).eval p*Real.cosh (m*p)+(jetSinhPolynomial m r).eval p*Real.sinh (m*p) := by
  induction r using Nat.twoStepInduction with
  | zero => simp [jetCoshPolynomial,jetSinhPolynomial,cosineKernelJet_square_cosh]
  | one =>
    simp only [jetCoshPolynomial,jetSinhPolynomial,eval_zero,eval_mul,eval_C,eval_X,zero_mul,zero_add]
    have hd := cosineKernelJet_first_square m p
    field_simp [hm]
    nlinarith only [hd]
  | more r ih ih' =>
    rw [jetCoshPolynomial,jetSinhPolynomial]
    simp only [eval_mul,eval_C,eval_sub,eval_pow,eval_X]
    have hd := cosineKernelJet_ode r (sq_pos_of_ne_zero hm) p
    rw [ih,ih'] at hd
    have hden : 4*m^2*((r:ℝ)+1)*((r:ℝ)+2)≠0 := by positivity
    field_simp [hm]
    nlinarith only [hd]
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Real MeasureTheory
noncomputable def generatorMoment (u : ℝ) (k : ℕ) (p : ℝ) : ℝ := p^k*pollaczekGenerator p u
lemma generatorMoment_continuous (u : ℝ) (k : ℕ) : Continuous (generatorMoment u k) :=
  (continuous_id.pow k).mul (pollaczekGenerator_continuous_p u)
lemma power_exp_bound {δ : ℝ} (hδ : 0<δ) (k : ℕ) (p : ℝ) :
    |p|^k ≤ ((k.factorial:ℝ)/δ^k)*Real.exp (δ*|p|) := by
  have h := Real.pow_div_factorial_le_exp (δ*|p|) (by positivity) k
  rw [div_le_iff₀ (by positivity : (0:ℝ)<(k.factorial:ℝ)),mul_pow] at h
  rw [div_mul_eq_mul_div,le_div_iff₀ (pow_pos hδ k)]
  nlinarith only [h]
lemma generatorMoment_bound {δ : ℝ} (hδ : 0<δ) (u : ℝ) (k : ℕ) (p : ℝ) :
    |generatorMoment u k p| ≤ ((k.factorial:ℝ)/δ^k)*Real.exp ((δ+2*|Real.arctan u|)*|p|) := by
  rw [generatorMoment,abs_mul,abs_pow]
  calc
    _ ≤ ((k.factorial:ℝ)/δ^k)*Real.exp (δ*|p|)*Real.exp ((2*|Real.arctan u|)*|p|) :=
      mul_le_mul (power_exp_bound hδ k p) (pollaczekGenerator_exp_bound_sharp p u) (abs_nonneg _) (by positivity)
    _ = _ := by rw [add_mul,Real.exp_add];ring
lemma generatorMoment_pair_integrable {t u : ℝ} (ht : |t|<1) (hu : |u|<1) (k j : ℕ) :
    IntegrableOn (sechPairIntegrand (generatorMoment t k) (generatorMoment u j)) (Set.Ioi 0) := by
  let δ := (Real.pi-(2*|Real.arctan t|+2*|Real.arctan u|))/4
  have hδ : 0<δ := by dsimp [δ];linarith [arctan_quarter_bound ht,arctan_quarter_bound hu]
  exact sechPairIntegrand_exp_integrable (generatorMoment_continuous t k) (generatorMoment_continuous u j)
    (by positivity) (by dsimp [δ];linarith [arctan_quarter_bound ht,arctan_quarter_bound hu])
    (generatorMoment_bound hδ t k) (generatorMoment_bound hδ u j)
lemma pollaczekCoeff_moment_integrable {u : ℝ} (hu : |u|<1) (n k : ℕ) :
    IntegrableOn (sechPairIntegrand (fun p=>pollaczekCoeff p n) (generatorMoment u k)) (Set.Ioi 0) := by
  let δ := (Real.pi-(2*Real.artanh (1/4)+2*|Real.arctan u|))/2
  have hδ : 0<δ := by dsimp [δ];linarith [quarter_artanh_bounds.2,arctan_quarter_bound hu]
  exact sechPairIntegrand_exp_integrable (pollaczekCoeff_continuous n) (generatorMoment_continuous u k)
    (by positivity) (by dsimp [δ];linarith [quarter_artanh_bounds.2,arctan_quarter_bound hu])
    (pollaczekCoeff_exp_bound n) (generatorMoment_bound hδ u k)
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Real MeasureTheory Polynomial
noncomputable def generatorMomentCoefficient (u : ℝ) (k n : ℕ) : ℝ :=
  symmetricSechPair (fun p=>pollaczekCoeff p n) (generatorMoment u k)
lemma generatorMomentCoefficient_zero {u : ℝ} (hu : |u|<1) (n : ℕ) :
    generatorMomentCoefficient u 0 n=u^n := by
  change symmetricSechPair (fun p=>pollaczekCoeff p n) (fun p=>p^0*pollaczekGenerator p u)=_
  simpa only [pow_zero,one_mul] using symmetricSechPair_coeff_generator_full hu n
lemma pollaczek_coeff_recurrence (n : ℕ) (p : ℝ) :
    2*p*pollaczekCoeff p (n+1)=(n+2:ℝ)*pollaczekCoeff p (n+2)+(n+1:ℝ)*pollaczekCoeff p n := by
  rw [pollaczekCoeff]
  have hn : (n:ℝ)+2≠0 := by positivity
  field_simp
  ring
lemma generatorMomentCoefficient_succ {u : ℝ} (hu : |u|<1) (k n : ℕ) :
    generatorMomentCoefficient u (k+1) (n+1)=
      (((n:ℝ)+2)*generatorMomentCoefficient u k (n+2)+((n:ℝ)+1)*generatorMomentCoefficient u k n)/2 := by
  have he : sechPairIntegrand (fun p=>pollaczekCoeff p (n+1)) (generatorMoment u (k+1))=
      fun p=>(((n:ℝ)+2)/2)*sechPairIntegrand (fun p=>pollaczekCoeff p (n+2)) (generatorMoment u k) p+
        (((n:ℝ)+1)/2)*sechPairIntegrand (fun p=>pollaczekCoeff p n) (generatorMoment u k) p := by
    funext p
    unfold sechPairIntegrand generatorMoment
    rw [pow_succ,pow_succ]
    linear_combination (p^k*pollaczekGenerator p u)/(2*Real.cosh (Real.pi*p))*pollaczek_coeff_recurrence n p+
      ((-p)^k*pollaczekGenerator (-p) u)/(2*Real.cosh (Real.pi*p))*pollaczek_coeff_recurrence n (-p)
  change (∫ p in Set.Ioi (0:ℝ),sechPairIntegrand (fun p=>pollaczekCoeff p (n+1)) (generatorMoment u (k+1)) p)=_
  rw [he,integral_add ((pollaczekCoeff_moment_integrable hu (n+2) k).const_mul _)
    ((pollaczekCoeff_moment_integrable hu n k).const_mul _),integral_const_mul,integral_const_mul]
  change (((n:ℝ)+2)/2)*generatorMomentCoefficient u k (n+2)+(((n:ℝ)+1)/2)*generatorMomentCoefficient u k n=_
  ring
noncomputable def generatorMomentPolynomial (u : ℝ) : ℕ → Polynomial ℝ
  | 0 => 1
  | k+1 => Polynomial.C (1/2)*(Polynomial.C u*(X+1)*(generatorMomentPolynomial u k).comp (X+1)+
      Polynomial.C u⁻¹*X*(generatorMomentPolynomial u k).comp (X-1))
lemma generatorMomentPolynomial_degree (u : ℝ) (k : ℕ) : (generatorMomentPolynomial u k).natDegree ≤ k := by
  induction k with
  | zero => simp [generatorMomentPolynomial]
  | succ k ih =>
    rw [generatorMomentPolynomial]
    apply (natDegree_C_mul_le _ _).trans
    apply natDegree_add_le_of_degree_le
    · apply natDegree_mul_le.trans
      have hcomp : ((generatorMomentPolynomial u k).comp (X+1)).natDegree ≤ k := by
        have h := (natDegree_comp_le (p:=generatorMomentPolynomial u k) (q:=(X+1)))
        simpa using h.trans (Nat.mul_le_mul ih (show (X+1:Polynomial ℝ).natDegree ≤ 1 by simpa only [← C_1] using (natDegree_X_add_C (1:ℝ)).le))
      apply (Nat.add_le_add ((natDegree_C_mul_le _ _).trans (show (X+1:Polynomial ℝ).natDegree≤1 by simpa only [← C_1] using (natDegree_X_add_C (1:ℝ)).le)) hcomp).trans
      omega
    · apply natDegree_mul_le.trans
      have hcomp : ((generatorMomentPolynomial u k).comp (X-1)).natDegree ≤ k := by
        have h := (natDegree_comp_le (p:=generatorMomentPolynomial u k) (q:=(X-1)))
        simpa using h.trans (Nat.mul_le_mul ih (show (X-1:Polynomial ℝ).natDegree ≤ 1 by simpa only [← C_1] using (natDegree_X_sub_C (1:ℝ)).le))
      apply (Nat.add_le_add ((natDegree_C_mul_le _ _).trans (show (X:Polynomial ℝ).natDegree≤1 by simp)) hcomp).trans
      omega
lemma generatorMomentCoefficient_polynomial {u : ℝ} (hu : |u|<1) (hu0 : u≠0) (k n : ℕ) (hkn : k≤n) :
    generatorMomentCoefficient u k n=u^n*(generatorMomentPolynomial u k).eval (n:ℝ) := by
  induction k generalizing n with
  | zero => simp only [generatorMomentCoefficient_zero hu,generatorMomentPolynomial,eval_one,mul_one]
  | succ k ih =>
    obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n≠0 by omega)
    rw [generatorMomentCoefficient_succ hu,ih (n+2) (by omega),ih n (by omega),generatorMomentPolynomial]
    simp only [eval_mul,eval_C,eval_add,eval_sub,eval_X,eval_one,eval_comp,Nat.cast_succ]
    rw [show (n:ℝ)+1+1=(n:ℝ)+2 by ring,show (n:ℝ)+1-1=(n:ℝ) by ring,pow_succ,pow_succ]
    field_simp [hu0]
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Real Polynomial MeasureTheory Finset
noncomputable def generatorPolynomial (u : ℝ) (P : Polynomial ℝ) (p : ℝ) : ℝ := P.eval p*pollaczekGenerator p u
lemma generatorPolynomial_sum (u : ℝ) (P : Polynomial ℝ) :
    generatorPolynomial u P=fun p=>∑ k∈range (P.natDegree+1),P.coeff k*generatorMoment u k p := by
  funext p
  have h:=congrArg (fun Q:Polynomial ℝ=>Q.eval p) P.as_sum_range_C_mul_X_pow
  simp only [eval_finsetSum,eval_mul,eval_C,eval_pow,eval_X] at h
  simp only [generatorPolynomial,generatorMoment,h,sum_mul]
  apply sum_congr rfl
  intro k _
  ring
lemma generatorPolynomial_pair_integrable {u : ℝ} (hu : |u|<1) (P : Polynomial ℝ) (n : ℕ) :
    IntegrableOn (sechPairIntegrand (generatorPolynomial u P) (fun p=>pollaczekCoeff p n)) (Set.Ioi 0) := by
  rw [generatorPolynomial_sum]
  have he : sechPairIntegrand (fun p=>∑ k∈range (P.natDegree+1),P.coeff k*generatorMoment u k p) (fun p=>pollaczekCoeff p n)=
      fun p=>∑ k∈range (P.natDegree+1),P.coeff k*sechPairIntegrand (generatorMoment u k) (fun p=>pollaczekCoeff p n) p := by
    funext p
    simp only [sechPairIntegrand,sum_mul,←sum_add_distrib,sum_div]
    apply sum_congr rfl
    intro k _
    ring
  rw [he]
  apply integrable_finsetSum
  intro k _
  rw [sechPairIntegrand_comm]
  exact (pollaczekCoeff_moment_integrable hu n k).const_mul _
noncomputable def generatorPolynomialCoefficient (u : ℝ) (P : Polynomial ℝ) : Polynomial ℝ :=
  ∑ k∈range (P.natDegree+1),Polynomial.C (P.coeff k)*generatorMomentPolynomial u k
lemma generatorPolynomialCoefficient_degree (u : ℝ) (P : Polynomial ℝ) :
    (generatorPolynomialCoefficient u P).natDegree≤P.natDegree := by
  apply natDegree_sum_le_of_forall_le
  intro k hk
  exact ((natDegree_C_mul_le _ _).trans (generatorMomentPolynomial_degree u k)).trans (by simpa using mem_range.mp hk)
lemma generatorPolynomial_coefficient {u : ℝ} (hu : |u|<1) (hu0 : u≠0) (P : Polynomial ℝ) (n : ℕ) (hn : P.natDegree≤n) :
    symmetricSechPair (fun p=>pollaczekCoeff p n) (generatorPolynomial u P)=
      u^n*(generatorPolynomialCoefficient u P).eval (n:ℝ) := by
  rw [symmetricSechPair_comm,generatorPolynomial_sum]
  rw [symmetricSechPair_sum_left]
  · simp only [symmetricSechPair_smul_left]
    simp only [generatorPolynomialCoefficient,eval_finsetSum,eval_mul,eval_C,mul_sum]
    apply sum_congr rfl
    intro k hk
    rw [symmetricSechPair_comm]
    change P.coeff k*generatorMomentCoefficient u k n=_
    rw [generatorMomentCoefficient_polynomial hu hu0 k n (by have :=mem_range.mp hk;omega)]
    ring
  · intro k _
    rw [sechPairIntegrand_smul_left,sechPairIntegrand_comm]
    exact (pollaczekCoeff_moment_integrable hu n k).const_mul _
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Real Polynomial MeasureTheory
lemma generator_even_sum (u p : ℝ) :
    pollaczekGenerator p u+pollaczekGenerator p (-u)=
      2*Real.cos (Real.arctan u)*Real.cosh ((2*Real.arctan u)*p) := by
  simp only [pollaczekGenerator,generator_prefactor,Real.arctan_neg,Real.cos_neg,Real.cosh_eq]
  rw [show 2*p*(-Real.arctan u)=-(2*Real.arctan u*p) by ring,show 2*p*Real.arctan u=2*Real.arctan u*p by ring]
  ring
lemma generator_odd_sum (u p : ℝ) :
    pollaczekGenerator p u-pollaczekGenerator p (-u)=
      2*Real.cos (Real.arctan u)*Real.sinh ((2*Real.arctan u)*p) := by
  simp only [pollaczekGenerator,generator_prefactor,Real.arctan_neg,Real.cos_neg,Real.sinh_eq]
  rw [show 2*p*(-Real.arctan u)=-(2*Real.arctan u*p) by ring,show 2*p*Real.arctan u=2*Real.arctan u*p by ring]
  ring
lemma cosineKernelJet_generator_polynomials {u : ℝ} (hu : u≠0) (r : ℕ) :
    ∃ A B : Polynomial ℝ,A.natDegree≤r ∧ B.natDegree≤r ∧
      (fun p=>cosineKernelJet r 0 ((2*Real.arctan u)^2) (p^2))=
        fun p=>generatorPolynomial u A p+generatorPolynomial (-u) B p := by
  let m:=2*Real.arctan u
  let c:=2*Real.cos (Real.arctan u)
  have hm : m≠0 := mul_ne_zero (by norm_num) (Real.arctan_eq_zero_iff.not.mpr hu)
  have hc : c≠0 := by dsimp [c];positivity
  let A:=Polynomial.C c⁻¹*(jetCoshPolynomial m r+jetSinhPolynomial m r)
  let B:=Polynomial.C c⁻¹*(jetCoshPolynomial m r-jetSinhPolynomial m r)
  refine ⟨A,B,?_,?_,?_⟩
  · exact (natDegree_C_mul_le _ _).trans (natDegree_add_le_of_degree_le (jetPolynomial_degrees m r).1 (jetPolynomial_degrees m r).2)
  · exact (natDegree_C_mul_le _ _).trans ((natDegree_sub_le _ _).trans (max_le (jetPolynomial_degrees m r).1 (jetPolynomial_degrees m r).2))
  · funext p
    rw [cosineKernelJet_polynomials hm]
    simp only [generatorPolynomial,A,B,eval_mul,eval_C,eval_add,eval_sub]
    have he:=generator_even_sum u p
    have ho:=generator_odd_sum u p
    change pollaczekGenerator p u+pollaczekGenerator p (-u)=c*Real.cosh (m*p) at he
    change pollaczekGenerator p u-pollaczekGenerator p (-u)=c*Real.sinh (m*p) at ho
    field_simp
    linear_combination -((jetCoshPolynomial m r).eval p)*he-((jetSinhPolynomial m r).eval p)*ho
lemma symmetricSechPair_add_right (f g h : ℝ → ℝ)
    (hg : IntegrableOn (sechPairIntegrand f g) (Set.Ioi 0))
    (hh : IntegrableOn (sechPairIntegrand f h) (Set.Ioi 0)) :
    symmetricSechPair f (fun p=>g p+h p)=symmetricSechPair f g+symmetricSechPair f h := by
  change (∫ p in Set.Ioi (0:ℝ),sechPairIntegrand f (fun p=>g p+h p) p)=
    (∫ p in Set.Ioi (0:ℝ),sechPairIntegrand f g p)+(∫ p in Set.Ioi (0:ℝ),sechPairIntegrand f h p)
  rw [←integral_add hg hh]
  apply integral_congr_ae
  filter_upwards with p
  unfold sechPairIntegrand
  ring
lemma cosineKernelJet_evenCoefficient {u : ℝ} (hu : |u|<1) (hu0 : u≠0) (r : ℕ) :
    ∃ P : Polynomial ℝ,P.natDegree≤r ∧ ∀ j : ℕ,r≤2*j →
      symmetricSechPair (fun p=>pollaczekCoeff p (2*j))
        (fun p=>cosineKernelJet r 0 ((2*Real.arctan u)^2) (p^2))=(u^2)^j*P.eval (j:ℝ) := by
  obtain ⟨A,B,hA,hB,he⟩:=cosineKernelJet_generator_polynomials hu0 r
  let P:=(generatorPolynomialCoefficient u A+generatorPolynomialCoefficient (-u) B).comp (Polynomial.C 2*X)
  refine ⟨P,?_,?_⟩
  · apply natDegree_comp_le.trans
    have hdeg : (generatorPolynomialCoefficient u A+generatorPolynomialCoefficient (-u) B).natDegree≤r :=
      natDegree_add_le_of_degree_le ((generatorPolynomialCoefficient_degree u A).trans hA)
        ((generatorPolynomialCoefficient_degree (-u) B).trans hB)
    have hlinear : (Polynomial.C 2*X:Polynomial ℝ).natDegree≤1 := (natDegree_C_mul_le _ _).trans (by simp)
    simpa using Nat.mul_le_mul hdeg hlinear
  · intro j hj
    rw [he,symmetricSechPair_add_right]
    · rw [generatorPolynomial_coefficient hu hu0 A (2*j) (hA.trans hj),
        generatorPolynomial_coefficient (by simpa using hu) (neg_ne_zero.mpr hu0) B (2*j) (hB.trans hj)]
      simp only [P,eval_comp,eval_add,eval_mul,eval_C,eval_X,Nat.cast_mul,Nat.cast_ofNat,
        pow_mul,neg_sq]
      ring
    · rw [sechPairIntegrand_comm];exact generatorPolynomial_pair_integrable hu A (2*j)
    · rw [sechPairIntegrand_comm];exact generatorPolynomial_pair_integrable (by simpa using hu) B (2*j)
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Real Polynomial MeasureTheory Finset
lemma polynomialSech_pair_integrable (P : Polynomial ℝ) (n : ℕ) :
    IntegrableOn (sechPairIntegrand (fun p=>P.eval (p^2)) (fun p=>pollaczekCoeff p n)) (Set.Ioi 0) := by
  obtain ⟨a,ha⟩:=polynomial_evenPollaczekFinite P (le_refl P.natDegree)
  rw [ha]
  exact evenFinite_pair_integrable _ a _ (fun _=>pollaczekCoeff_pair_integrable _ _)
lemma polynomialSech_coefficient_zero (P : Polynomial ℝ) (j : ℕ) (hj : P.natDegree<j) :
    symmetricSechPair (fun p=>pollaczekCoeff p (2*j)) (fun p=>P.eval (p^2))=0 := by
  obtain ⟨a,ha⟩:=polynomial_evenPollaczekFinite P (le_refl P.natDegree)
  rw [ha,symmetricSechPair_comm,evenFinite_pair _ a _ (fun _=>pollaczekCoeff_pair_integrable _ _)]
  apply sum_eq_zero
  intro i _
  rw [symmetricSechPair_orthogonal,ite_eq_right (by have:=i.isLt;omega),mul_zero]
lemma kernelJet_zeroLabel_polynomial (r : ℕ) :
    (fun p=>cosineKernelJet r 0 0 (p^2))=
      fun p=>(Polynomial.C ((2*r).factorial:ℝ)⁻¹*X^r).eval (p^2) := by
  funext p
  simp only [cosineKernelJet_at_zero,eval_mul,eval_C,eval_pow,eval_X]
  ring
lemma kernelJet_zeroLabel_coefficient (r j : ℕ) (hr : r<j) :
    symmetricSechPair (fun p=>pollaczekCoeff p (2*j)) (fun p=>cosineKernelJet r 0 0 (p^2))=0 := by
  rw [kernelJet_zeroLabel_polynomial]
  apply polynomialSech_coefficient_zero
  exact lt_of_le_of_lt ((natDegree_C_mul_le _ _).trans (by simp)) hr
lemma kernelJet_zeroLabel_pair_integrable (r n : ℕ) :
    IntegrableOn (sechPairIntegrand (fun p=>cosineKernelJet r 0 0 (p^2)) (fun p=>pollaczekCoeff p n)) (Set.Ioi 0) := by
  rw [kernelJet_zeroLabel_polynomial]
  exact polynomialSech_pair_integrable _ _
lemma kernelJet_arctan_pair_integrable {u : ℝ} (hu : |u|<1) (hu0 : u≠0) (r n : ℕ) :
    IntegrableOn (sechPairIntegrand (fun p=>cosineKernelJet r 0 ((2*Real.arctan u)^2) (p^2))
      (fun p=>pollaczekCoeff p n)) (Set.Ioi 0) := by
  obtain ⟨A,B,_,_,he⟩:=cosineKernelJet_generator_polynomials hu0 r
  rw [he]
  have he' : sechPairIntegrand (fun p=>generatorPolynomial u A p+generatorPolynomial (-u) B p)
      (fun p=>pollaczekCoeff p n)=
      fun p=>sechPairIntegrand (generatorPolynomial u A) (fun p=>pollaczekCoeff p n) p+
        sechPairIntegrand (generatorPolynomial (-u) B) (fun p=>pollaczekCoeff p n) p := by
    funext p
    unfold sechPairIntegrand
    ring
  rw [he']
  exact (generatorPolynomial_pair_integrable hu A n).add (generatorPolynomial_pair_integrable (by simpa using hu) B n)
noncomputable def completeJetCombination (N : ℕ) (b : ℝ) (a c : Fin N → ℝ) (p : ℝ) : ℝ :=
  (∑ i,a i*cosineKernelJet i 0 0 (p^2))+(∑ i,c i*cosineKernelJet i 0 b (p^2))
lemma completeJetCombination_coefficient {u : ℝ} (hu : |u|<1) (hu0 : u≠0)
    (N : ℕ) (hN : 0<N) (a c : Fin N → ℝ) :
    ∃ P : Polynomial ℝ,P.natDegree<N ∧ ∀ j : ℕ,N≤j →
      symmetricSechPair (fun p=>pollaczekCoeff p (2*j)) (completeJetCombination N ((2*Real.arctan u)^2) a c)=
        (u^2)^j*P.eval (j:ℝ) := by
  choose P hP using fun i:Fin N=>cosineKernelJet_evenCoefficient hu hu0 i
  refine ⟨∑ i,Polynomial.C (c i)*P i,?_,?_⟩
  · apply lt_of_le_of_lt (b:=N-1)
    · apply natDegree_sum_le_of_forall_le
      intro i _
      exact ((natDegree_C_mul_le _ _).trans (hP i).1).trans (by have:=i.isLt;omega)
    · omega
  · intro j hj
    let Q:=fun p=>pollaczekCoeff p (2*j)
    have hzero (i : Fin N) : IntegrableOn (sechPairIntegrand (fun p=>a i*cosineKernelJet i 0 0 (p^2)) Q) (Set.Ioi 0) := by
      rw [sechPairIntegrand_smul_left]
      exact (kernelJet_zeroLabel_pair_integrable i (2*j)).const_mul (a i)
    have hpos (i : Fin N) : IntegrableOn (sechPairIntegrand (fun p=>c i*cosineKernelJet i 0 ((2*Real.arctan u)^2) (p^2)) Q) (Set.Ioi 0) := by
      rw [sechPairIntegrand_smul_left]
      exact (kernelJet_arctan_pair_integrable hu hu0 i (2*j)).const_mul (c i)
    have hs (f : Fin N→ℝ→ℝ) : sechPairIntegrand (fun p=>∑ i,f i p) Q=fun p=>∑ i,sechPairIntegrand (f i) Q p := by
      funext p
      simp only [sechPairIntegrand,sum_mul,←sum_add_distrib,sum_div]
    have h0 : IntegrableOn (sechPairIntegrand Q (fun p=>∑ i,a i*cosineKernelJet i 0 0 (p^2))) (Set.Ioi 0) := by
      rw [sechPairIntegrand_comm,hs]
      exact integrable_finsetSum univ (fun i _=>hzero i)
    have h1 : IntegrableOn (sechPairIntegrand Q (fun p=>∑ i,c i*cosineKernelJet i 0 ((2*Real.arctan u)^2) (p^2))) (Set.Ioi 0) := by
      rw [sechPairIntegrand_comm,hs]
      exact integrable_finsetSum univ (fun i _=>hpos i)
    change symmetricSechPair Q (fun p=>(∑ i,a i*cosineKernelJet i 0 0 (p^2))+
      (∑ i,c i*cosineKernelJet i 0 ((2*Real.arctan u)^2) (p^2)))=_
    rw [symmetricSechPair_add_right Q _ _ h0 h1,symmetricSechPair_comm Q (fun p=>∑ i,a i*cosineKernelJet i 0 0 (p^2)),
      symmetricSechPair_sum_left _ _ Q (fun i _=>hzero i),symmetricSechPair_comm Q (fun p=>∑ i,c i*cosineKernelJet i 0 ((2*Real.arctan u)^2) (p^2)),
      symmetricSechPair_sum_left _ _ Q (fun i _=>hpos i)]
    simp only [symmetricSechPair_smul_left]
    have hz : ∑ i:Fin N,a i*symmetricSechPair (fun p=>cosineKernelJet i 0 0 (p^2)) Q=0 := by
      apply sum_eq_zero
      intro i _
      rw [symmetricSechPair_comm,kernelJet_zeroLabel_coefficient i j (by have:=i.isLt;omega),mul_zero]
    rw [hz,zero_add]
    simp only [eval_finsetSum,eval_mul,eval_C,mul_sum]
    apply sum_congr rfl
    intro i _
    rw [symmetricSechPair_comm,(hP i).2 j (by have:=i.isLt;omega)]
    ring
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Real MeasureTheory Polynomial Finset Filter Topology
lemma completeJetCombination_finite (N : ℕ) (b : ℝ) (a c : Fin N → ℝ) :
    completeJetCombination N b a c=fun p=>finiteJetCombination (N+N) (Fin.addCases a c)
      (Fin.addCases (fun _=>(0:ℝ)) (fun _=>b)) (Fin.addCases Fin.val Fin.val) (p^2) := by
  funext p
  simp only [finiteJetCombination,Fin.sum_univ_add,Fin.addCases_left,Fin.addCases_right,completeJetCombination]
lemma completeJetSech_bounds {b δ : ℝ} (hb : 0≤b) (hlim : Real.sqrt (b+δ)<Real.pi/2)
    (N : ℕ) :
    (∀ i:Fin (N+N),(0:ℝ)≤Fin.addCases (fun _=>(0:ℝ)) (fun _=>b) i) ∧
    (∀ i:Fin (N+N),Real.sqrt (Fin.addCases (fun _=>(0:ℝ)) (fun _=>b) i+δ)<Real.pi/2) := by
  constructor
  · intro i
    refine Fin.addCases (fun j=>?_) (fun j=>?_) i <;> simp only [Fin.addCases_left,Fin.addCases_right]
    · exact le_refl _
    · exact hb
  · intro i
    refine Fin.addCases (fun j=>?_) (fun j=>?_) i <;> simp only [Fin.addCases_left,Fin.addCases_right]
    · exact lt_of_le_of_lt (Real.sqrt_le_sqrt (by linarith)) hlim
    · exact hlim
lemma completeJetSech_norm_integrable {b δ : ℝ} (hb : 0≤b) (hd : 0<δ) (hlim : Real.sqrt (b+δ)<Real.pi/2)
    (N : ℕ) (a c : Fin N → ℝ) :
    IntegrableOn (sechPairIntegrand (completeJetCombination N b a c) (completeJetCombination N b a c)) (Set.Ioi 0) := by
  rw [completeJetCombination_finite]
  obtain ⟨hb',hl'⟩:=completeJetSech_bounds hb hlim N
  exact finiteJetSech_norm_integrable _ _ _ (fun _=>δ) _ hb' (fun _=>hd) hl'
lemma completeJetSech_pair_integrable {b δ : ℝ} (hb : 0≤b) (hd : 0<δ) (hlim : Real.sqrt (b+δ)<Real.pi/2)
    (N : ℕ) (a c : Fin N → ℝ) (n : ℕ) :
    IntegrableOn (sechPairIntegrand (fun p=>pollaczekCoeff p n) (completeJetCombination N b a c)) (Set.Ioi 0) := by
  rw [completeJetCombination_finite]
  obtain ⟨hb',hl'⟩:=completeJetSech_bounds hb hlim N
  exact finiteJetSech_pair_integrable _ _ _ (fun _=>δ) _ hb' (fun _=>hd) hl' n
lemma completeJetSech_parseval_residual {b δ : ℝ} (hb : 0≤b) (hd : 0<δ) (hlim : Real.sqrt (b+δ)<Real.pi/2)
    (N : ℕ) (a c : Fin N → ℝ) :
    Tendsto (fun n=>symmetricSechPair (completeJetCombination N b a c) (completeJetCombination N b a c)-
      ∑ j:Fin (n+1),(symmetricSechPair (fun p=>pollaczekCoeff p (2*j)) (completeJetCombination N b a c))^2)
      atTop (𝓝 0) := by
  rw [completeJetCombination_finite]
  obtain ⟨hb',hl'⟩:=completeJetSech_bounds hb hlim N
  exact finiteJetSech_parseval_residual _ _ _ (fun _=>δ) _ hb' (fun _=>hd) hl'
lemma label_margin_exists {b : ℝ} (hb : b<(Real.pi/2)^2) :
    ∃ δ : ℝ,0<δ ∧ Real.sqrt (b+δ)<Real.pi/2 := by
  refine ⟨((Real.pi/2)^2-b)/2,by linarith,?_⟩
  apply (Real.sqrt_lt' (by positivity)).mpr
  linarith
lemma arctan_label_margin {u : ℝ} (hu : |u|<1) :
    ∃ δ : ℝ,0<δ ∧ Real.sqrt ((2*Real.arctan u)^2+δ)<Real.pi/2 := by
  apply label_margin_exists
  have hu1 : -1<u ∧ u<1 := abs_lt.mp hu
  have hupper:=Real.arctan_strictMono hu1.2
  have hlower:=Real.arctan_strictMono hu1.1
  rw [Real.arctan_one] at hupper
  rw [Real.arctan_neg,Real.arctan_one] at hlower
  nlinarith [Real.pi_pos]
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Real MeasureTheory Polynomial Finset Filter Topology
lemma evenProjection_coefficient_le_one (f : ℝ → ℝ)
    (hff : IntegrableOn (sechPairIntegrand f f) (Set.Ioi 0))
    (hf : ∀ j:ℕ,IntegrableOn (sechPairIntegrand (fun p=>pollaczekCoeff p (2*j)) f) (Set.Ioi 0))
    (hnorm : symmetricSechPair f f≤1) (j : ℕ) :
    |symmetricSechPair (fun p=>pollaczekCoeff p (2*j)) f|≤1 := by
  have hB:=even_projection_bessel (j+1) f hff (fun i=>hf i)
  have hs:=single_le_sum (s:=univ) (f:=fun i:Fin (j+1)=>(symmetricSechPair (fun p=>pollaczekCoeff p (2*i)) f)^2)
    (fun i _=>sq_nonneg _) (mem_univ (⟨j,by omega⟩:Fin (j+1)))
  simp only at hs
  rw [abs_le]
  constructor <;> nlinarith
lemma evenProjection_hasSum (f : ℝ → ℝ)
    (hres : Tendsto (fun n=>symmetricSechPair f f-
      ∑ j:Fin (n+1),(symmetricSechPair (fun p=>pollaczekCoeff p (2*j)) f)^2) atTop (𝓝 0)) :
    HasSum (fun j=>(symmetricSechPair (fun p=>pollaczekCoeff p (2*j)) f)^2) (symmetricSechPair f f) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun j=>sq_nonneg _) _).mpr
  apply (Filter.tendsto_add_atTop_iff_nat 1).mp
  have hh:=(tendsto_const_nhds (x:=symmetricSechPair f f)).sub hres
  have hs (n:ℕ) : (∑ j:Fin n,(symmetricSechPair (fun p=>pollaczekCoeff p (2*j)) f)^2)=
      ∑ j∈range n,(symmetricSechPair (fun p=>pollaczekCoeff p (2*j)) f)^2 :=
    Fin.sum_univ_eq_sum_range (fun j=>(symmetricSechPair (fun p=>pollaczekCoeff p (2*j)) f)^2) n
  simpa only [sub_sub_cancel,sub_zero,hs] using hh
lemma evenProjection_exponential_error (f : ℝ → ℝ)
    (hff : IntegrableOn (sechPairIntegrand f f) (Set.Ioi 0))
    (hf : ∀ j:ℕ,IntegrableOn (sechPairIntegrand (fun p=>pollaczekCoeff p (2*j)) f) (Set.Ioi 0))
    (hres : Tendsto (fun n=>symmetricSechPair f f-
      ∑ j:Fin (n+1),(symmetricSechPair (fun p=>pollaczekCoeff p (2*j)) f)^2) atTop (𝓝 0))
    {γ : ℝ} (hγ : 0<γ) (K : ℕ)
    (htail : ∀ j:ℕ,K≤j → |symmetricSechPair (fun p=>pollaczekCoeff p (2*j)) f|≤Real.exp (-γ*(j:ℝ))) :
    symmetricSechPair (fun p=>f p-evenPollaczekFinite K (fun j=>symmetricSechPair (fun p=>pollaczekCoeff p (2*j)) f) p)
      (fun p=>f p-evenPollaczekFinite K (fun j=>symmetricSechPair (fun p=>pollaczekCoeff p (2*j)) f) p) ≤
      Real.exp (-2*γ*(K:ℝ))/(1-Real.exp (-2*γ)) := by
  have hsum:=evenProjection_hasSum f hres
  have ht:=(hasSum_nat_add_iff' K).mpr hsum
  rw [even_projection_error K f hff (fun j=>hf j)]
  simp only [←pow_two]
  have he : symmetricSechPair f f-2*(∑ j:Fin K,(symmetricSechPair (fun p=>pollaczekCoeff p (2*j)) f)^2)+
      ∑ j:Fin K,(symmetricSechPair (fun p=>pollaczekCoeff p (2*j)) f)^2=
      ∑' j:ℕ,(symmetricSechPair (fun p=>pollaczekCoeff p (2*(j+K))) f)^2 := by
    have hs : (∑ j:Fin K,(symmetricSechPair (fun p=>pollaczekCoeff p (2*j)) f)^2)=
        ∑ j∈range K,(symmetricSechPair (fun p=>pollaczekCoeff p (2*j)) f)^2 :=
      Fin.sum_univ_eq_sum_range (fun j=>(symmetricSechPair (fun p=>pollaczekCoeff p (2*j)) f)^2) K
    rw [ht.tsum_eq,hs]
    ring
  rw [he]
  have hex : Real.exp (-2*γ)<1 := by rw [Real.exp_lt_one_iff];linarith
  have hgeo:=summable_geometric_of_lt_one (Real.exp_pos (-2*γ)).le hex
  have hbound (j : ℕ) : (symmetricSechPair (fun p=>pollaczekCoeff p (2*(j+K))) f)^2 ≤
      Real.exp (-2*γ*(K:ℝ))*(Real.exp (-2*γ))^j := by
    calc
      _ ≤ (Real.exp (-γ*((j+K:ℕ):ℝ)))^2 := by
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (htail (j+K) (by omega)) 2
      _ = _ := by
        rw [←Real.exp_nat_mul,←Real.exp_nat_mul,←Real.exp_add]
        congr 1
        push_cast
        ring
  calc
    _ ≤ ∑' j:ℕ,Real.exp (-2*γ*(K:ℝ))*(Real.exp (-2*γ))^j :=
      Summable.tsum_le_tsum hbound ht.summable (hgeo.mul_left _)
    _ = _ := by rw [tsum_mul_left,tsum_geometric_of_lt_one (Real.exp_pos _).le hex,div_eq_mul_inv]
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end

end OAI
