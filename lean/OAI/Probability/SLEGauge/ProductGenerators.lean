import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.RadialFactors

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
open scoped Topology
open Set
open MeasureTheory Filter
open scoped NNReal Topology
open MeasureTheory Filter Set Metric Function ODE
open MeasureTheory ProbabilityTheory Filter Set
open Filter
open Filter Set
namespace ExactSLECalculus
variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma normalized_product_generator (s : Finset ι) (f : ι → E → ℝ) (x A e : E)
    (hf : ∀ i ∈ s, ContDiffAt ℝ 2 (f i) x) (hp : ∀ i ∈ s, f i x ≠ 0) :
    N (fun y => ∏ i ∈ s, f i y) e x / (∏ i ∈ s, f i x) = ∑ i ∈ s, N (f i) e x / f i x ∧
    L (fun y => ∏ i ∈ s, f i y) A e x / (∏ i ∈ s, f i x) =
      (∑ i ∈ s, L (f i) A e x / f i x) +
      ((∑ i ∈ s, N (f i) e x / f i x)^2 - ∑ i ∈ s, (N (f i) e x / f i x)^2)/2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hfi := hf i (Finset.mem_insert_self _ _)
    have hfs : ∀ j∈s, ContDiffAt ℝ 2 (f j) x := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have hpi := hp i (Finset.mem_insert_self _ _)
    have hps : ∀ j∈s, f j x ≠ 0 := fun j hj => hp j (Finset.mem_insert_of_mem hj)
    have hs := contDiffAt_prod hfs
    have hnz : (∏ j∈s, f j x) ≠ 0 := Finset.prod_ne_zero_iff.mpr hps
    obtain ⟨ihN,ihL⟩ := ih hfs hps
    simp only [Finset.prod_insert hi,Finset.sum_insert hi]
    rw [N_mul (hfi.differentiableAt (by norm_num)) (hs.differentiableAt (by norm_num)),L_mul hfi hs]
    constructor
    · calc
        _ = N (f i) e x / f i x + N (fun y => ∏j∈s,f j y) e x / (∏j∈s,f j x) := by field_simp; ring
        _ = _ := by rw [ihN]
    · have he : (f i x * L (fun y => ∏j∈s,f j y) A e x +
          (∏j∈s,f j x)*L (f i) A e x + N (f i) e x*N (fun y => ∏j∈s,f j y) e x) /
          (f i x*(∏j∈s,f j x)) =
          L (f i) A e x/f i x + L (fun y => ∏j∈s,f j y) A e x/(∏j∈s,f j x) +
          (N (f i) e x/f i x)*(N (fun y => ∏j∈s,f j y) e x/(∏j∈s,f j x)) := by field_simp; ring
      rw [he,ihN,ihL]
      ring
end ExactSLECalculus

namespace ExactSLECalculus
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
lemma N_comp_clm (c : E →L[ℝ] F) {f : F → ℝ} {x e : E}
    (hf : DifferentiableAt ℝ f (c x)) :
    N (f ∘ c) e x = N f (c e) (c x) := by
  rw [N,(hf.hasFDerivAt.comp x c.hasFDerivAt).fderiv]
  rfl
lemma L_comp_clm (c : E →L[ℝ] F) {f : F → ℝ} {x A e : E}
    (hf : ContDiffAt ℝ 2 f (c x)) :
    L (f ∘ c) A e x = L f (c A) (c e) (c x) := by
  have hfd := hf.differentiableAt (by norm_num)
  have heq : N (f ∘ c) e =ᶠ[𝓝 x] (N f (c e) ∘ c) := by
    filter_upwards [c.continuous.continuousAt.preimage_mem_nhds (hf.eventually (by norm_num))] with y hy
    change ContDiffAt ℝ 2 f (c y) at hy
    exact N_comp_clm c (hy.differentiableAt (by norm_num))
  unfold L
  rw [N,heq.fderiv_eq,((N_differentiableAt (e := c e) hf).hasFDerivAt.comp x c.hasFDerivAt).fderiv,
    (hfd.hasFDerivAt.comp x c.hasFDerivAt).fderiv]
  rfl
end ExactSLECalculus

namespace ExactSLEFiniteTilt
lemma pair_noise_form {a δ₁ δ₂ D₁ D₂ V₁ V₂ : ℝ}
    (hδ₁ : 0<δ₁) (hδ₂ : 0<δ₂) (hD₁ : 0≤D₁) (hD₂ : 0≤D₂)
    (hV₁ : 0<V₁) (hV₂ : 0<V₂) :
    ((regP a+regQ a)*3^(regEta a)*δ₁^(-1-regEta a)*D₁^(regEta a)*V₁)*
      ((regP a+regQ a)*3^(regEta a)*δ₂^(-1-regEta a)*D₂^(regEta a)*V₂) =
    regC2 a*(δ₁*δ₂)^(-1-regEta a)*(D₁*V₁^2)^(regEta a)*(D₂*V₂^2)^(regEta a)*
      (V₁*V₂)^(1-2*regEta a) := by
  have hv₁ : V₁^(2*regEta a)*V₁^(1-2*regEta a)=V₁ := by
    rw [←Real.rpow_add hV₁,show 2*regEta a+(1-2*regEta a)=1 by ring,Real.rpow_one]
  have hv₂ : V₂^(2*regEta a)*V₂^(1-2*regEta a)=V₂ := by
    rw [←Real.rpow_add hV₂,show 2*regEta a+(1-2*regEta a)=1 by ring,Real.rpow_one]
  have h3 : (3:ℝ)^(2*regEta a)=3^(regEta a)*3^(regEta a) := by
    rw [show 2*regEta a=regEta a+regEta a by ring,Real.rpow_add (by norm_num : (0:ℝ)<3)]
  symm
  rw [regC2,Real.mul_rpow hδ₁.le hδ₂.le,Real.mul_rpow hD₁ (sq_nonneg V₁),
    Real.mul_rpow hD₂ (sq_nonneg V₂),Real.mul_rpow hV₁.le hV₂.le,
    ←Real.rpow_natCast_mul hV₁.le 2 (regEta a),←Real.rpow_natCast_mul hV₂.le 2 (regEta a),h3]
  calc
    _ = ((regP a+regQ a)*3^(regEta a)*δ₁^(-1-regEta a)*D₁^(regEta a))*
        ((regP a+regQ a)*3^(regEta a)*δ₂^(-1-regEta a)*D₂^(regEta a))*
        (V₁^(2*regEta a)*V₁^(1-2*regEta a))*(V₂^(2*regEta a)*V₂^(1-2*regEta a)) := by ring_nf
    _ = _ := by rw [hv₁,hv₂]; ring
end ExactSLEFiniteTilt
namespace ExactSLEGreen
open ExactSLECalculus ExactSLEFiniteTilt
lemma actual_noise_pair {a ε cap₁ cap₂ σ₁ σ₂ off₁ off₂ : ℝ}
    (ha : 1/4<a) (hε : 0<ε) (v₁ v₂ : State) (hY₁ : 0<Y v₁) (hY₂ : 0<Y v₂)
    (hδ₁ : physicalDelta a cap₁ σ₁ off₁ v₁≤1) (hδ₂ : physicalDelta a cap₂ σ₂ off₂ v₂≤1)
    (hσ₁ : |σ₁|≤regBeta a) (hσ₂ : |σ₂|≤regBeta a) :
    (N (physicalRegularized a cap₁ σ₁ off₁) noise v₁/physicalRegularized a cap₁ σ₁ off₁ v₁)*
      (N (physicalRegularized a cap₂ σ₂ off₂) noise v₂/physicalRegularized a cap₂ σ₂ off₂ v₂) ≤
    ε*(regD a (physicalDelta a cap₁ σ₁ off₁ v₁) (physicalTheta v₁)*(physicalV v₁)^2 +
      regD a (physicalDelta a cap₂ σ₂ off₂ v₂) (physicalTheta v₂)*(physicalV v₂)^2) +
    regYoungC a ε*(physicalDelta a cap₁ σ₁ off₁ v₁*physicalDelta a cap₂ σ₂ off₂ v₂)^(-regM a)*
      physicalV v₁*physicalV v₂ := by
  have hf₁ := actual_regularized_factor ha v₁ hY₁ hδ₁ hσ₁
  have hf₂ := actual_regularized_factor ha v₂ hY₂ hδ₂ hσ₂
  have hdp₁ : 0<physicalDelta a cap₁ σ₁ off₁ v₁ := Real.exp_pos _
  have hdp₂ : 0<physicalDelta a cap₂ σ₂ off₂ v₂ := Real.exp_pos _
  have hV₁ : 0<physicalV v₁ := div_pos hY₁ (Q_pos hY₁)
  have hV₂ : 0<physicalV v₂ := div_pos hY₂ (Q_pos hY₂)
  have hs₁ := physicalTheta_mem v₁
  have hs₂ := physicalTheta_mem v₂
  have hD₁ : 0≤regD a (physicalDelta a cap₁ σ₁ off₁ v₁) (physicalTheta v₁) := by
    dsimp only [regD]
    exact mul_nonneg (div_nonneg hdp₁.le ((regFactor_bounds ha hdp₁ hδ₁
      (Real.sin_pos_of_pos_of_lt_pi hs₁.1 hs₁.2)).1.le)) (Real.rpow_nonneg (Real.sin_pos_of_pos_of_lt_pi hs₁.1 hs₁.2).le _)
  have hD₂ : 0≤regD a (physicalDelta a cap₂ σ₂ off₂ v₂) (physicalTheta v₂) := by
    dsimp only [regD]
    exact mul_nonneg (div_nonneg hdp₂.le ((regFactor_bounds ha hdp₂ hδ₂
      (Real.sin_pos_of_pos_of_lt_pi hs₂.1 hs₂.2)).1.le)) (Real.rpow_nonneg (Real.sin_pos_of_pos_of_lt_pi hs₂.1 hs₂.2).le _)
  have hb₁ := hf₁.2.2
  have hb₂ := hf₂.2.2
  have hn₁ : 0≤|N (physicalRegularized a cap₁ σ₁ off₁) noise v₁| /
      physicalRegularized a cap₁ σ₁ off₁ v₁ := div_nonneg (abs_nonneg _) hf₁.1.le
  have hn₂ : 0≤|N (physicalRegularized a cap₂ σ₂ off₂) noise v₂| /
      physicalRegularized a cap₂ σ₂ off₂ v₂ := div_nonneg (abs_nonneg _) hf₂.1.le
  have hp := mul_le_mul hb₁ hb₂ hn₂ (hn₁.trans hb₁)
  have habs := le_abs_self ((N (physicalRegularized a cap₁ σ₁ off₁) noise v₁ /
      physicalRegularized a cap₁ σ₁ off₁ v₁)*(N (physicalRegularized a cap₂ σ₂ off₂) noise v₂ /
      physicalRegularized a cap₂ σ₂ off₂ v₂))
  rw [abs_mul,abs_div,abs_div,abs_of_pos hf₁.1,abs_of_pos hf₂.1] at habs
  apply (habs.trans hp).trans
  rw [pair_noise_form hdp₁ hdp₂ hD₁ hD₂ hV₁ hV₂]
  exact regularized_pair_absorption ha hε hdp₁ hdp₂ hD₁ hD₂ hV₁.le hV₂.le
end ExactSLEGreen

namespace ExactSLECalculus
variable {ι : Type*} [DecidableEq ι]
lemma sum_square_off_diagonal (s : Finset ι) (b : ι → ℝ) :
    (∑i∈s,b i)^2-(∑i∈s,(b i)^2) = ∑i∈s,∑j∈s.erase i,b i*b j := by
  have h : ∑i∈s,∑j∈s.erase i,b i*b j = ∑i∈s, ((∑j∈s,b i*b j)-b i*b i) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact Finset.sum_erase_eq_sub hi
  rw [h,Finset.sum_sub_distrib,←Finset.sum_mul_sum]
  simp only [pow_two]
lemma sum_pair_endpoints (s : Finset ι) (X : ι → ℝ) :
    (∑i∈s,∑j∈s.erase i,(X i+X j)) = 2*((s.card:ℝ)-1)*(∑i∈s,X i) := by
  have h : (∑i∈s,∑j∈s.erase i,(X i+X j)) =
      ∑i∈s,((∑j∈s,(X i+X j))-(X i+X i)) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact Finset.sum_erase_eq_sub hi
  rw [h]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul]
  rw [←Finset.mul_sum]
  ring

lemma sum_generator_absorption (s : Finset ι) (l b X R : ι → ℝ) (Y : ι → ι → ℝ)
    (c C ε : ℝ) (hX : ∀i∈s,0≤X i) (hsize : ε*((s.card:ℝ)-1)≤c)
    (hl : ∀i∈s,l i≤R i-c*X i)
    (hb : ∀i∈s,∀j∈s.erase i,b i*b j ≤ ε*(X i+X j)+C*Y i j) :
    (∑i∈s,l i)+((∑i∈s,b i)^2-∑i∈s,(b i)^2)/2 ≤
      (∑i∈s,R i)+C/2*(∑i∈s,∑j∈s.erase i,Y i j) := by
  have hl' := Finset.sum_le_sum hl
  have hb' : (∑i∈s,∑j∈s.erase i,b i*b j) ≤
      ∑i∈s,∑j∈s.erase i,(ε*(X i+X j)+C*Y i j) := by
    apply Finset.sum_le_sum
    intro i hi
    exact Finset.sum_le_sum (hb i hi)
  have he : (∑i∈s,∑j∈s.erase i,(ε*(X i+X j)+C*Y i j)) =
      ε*(∑i∈s,∑j∈s.erase i,(X i+X j))+C*(∑i∈s,∑j∈s.erase i,Y i j) := by
    simp only [Finset.sum_add_distrib,←Finset.mul_sum]
  rw [he,sum_pair_endpoints s X] at hb'
  simp only [Finset.sum_sub_distrib,←Finset.mul_sum] at hl'
  have hx : 0≤∑i∈s,X i := Finset.sum_nonneg hX
  have hsize' := mul_le_mul_of_nonneg_right hsize hx
  rw [sum_square_off_diagonal]
  nlinarith only [hl',hb',hsize']
end ExactSLECalculus

namespace ExactSLEGreen
open ExactSLECalculus ExactSLEFiniteTilt
noncomputable def multiDrift {m : ℕ} (a : ℝ) (v : Fin m → State) : Fin m → State :=
  fun i => physicalDrift a (v i)
def multiNoise (m : ℕ) : Fin m → State := fun _ => noise
noncomputable def regularizedProduct {m : ℕ} (s : Finset (Fin m))
    (a : ℝ) (cap σ off : Fin m → ℝ) (v : Fin m → State) : ℝ :=
  ∏i∈s, physicalRegularized a (cap i) (σ i) (off i) (v i)
 
theorem regularized_product_drift {m : ℕ} (s : Finset (Fin m)) {a ε : ℝ}
    (ha : 1/4<a) (hε : 0<ε) (hsize : ε*((s.card:ℝ)-1)≤regK a/2)
    (cap σ off : Fin m → ℝ) (v : Fin m → State)
    (hY : ∀ i∈s, 0<Y (v i))
    (hδ : ∀ i∈s, physicalDelta a (cap i) (σ i) (off i) (v i)≤1)
    (hσ : ∀ i∈s, |σ i|≤regBeta a) :
    0<regularizedProduct s a cap σ off v ∧
    L (regularizedProduct s a cap σ off) (multiDrift a v) (multiNoise m) v /
      regularizedProduct s a cap σ off v ≤
      regC a*(∑i∈s,physicalDelta a (cap i) (σ i) (off i) (v i)*(physicalV (v i))^2) +
      regYoungC a ε/2*(∑i∈s,∑j∈s.erase i,
        (physicalDelta a (cap i) (σ i) (off i) (v i)*
          physicalDelta a (cap j) (σ j) (off j) (v j))^(-regM a)*
          physicalV (v i)*physicalV (v j)) := by

  classical
  let F : Fin m → (Fin m → State) → ℝ :=
    fun i w => physicalRegularized a (cap i) (σ i) (off i) (w i)
  have hF (i) (hi : i∈s) : ContDiffAt ℝ 2 (F i) v := by
    exact (physicalRegularized_smooth a (cap i) (σ i) (off i) (v i) (hY i hi)).comp v
      (ContinuousLinearMap.proj i : (Fin m → State) →L[ℝ] State).contDiff.contDiffAt
  have hpos (i) (hi : i∈s) : 0<F i v :=
    (actual_regularized_factor ha (v i) (hY i hi) (hδ i hi) (hσ i hi)).1
  have hL (i) (hi : i∈s) : L (F i) (multiDrift a v) (multiNoise m) v =
      L (physicalRegularized a (cap i) (σ i) (off i)) (physicalDrift a (v i)) noise (v i) := by
    exact L_comp_clm (ContinuousLinearMap.proj i : (Fin m → State) →L[ℝ] State)
      (physicalRegularized_smooth a (cap i) (σ i) (off i) (v i) (hY i hi))
  have hN (i) (hi : i∈s) : N (F i) (multiNoise m) v =
      N (physicalRegularized a (cap i) (σ i) (off i)) noise (v i) := by
    exact N_comp_clm (ContinuousLinearMap.proj i : (Fin m → State) →L[ℝ] State)
      ((physicalRegularized_smooth a (cap i) (σ i) (off i) (v i) (hY i hi)).differentiableAt (by norm_num))
  have hD (i) (hi : i∈s) :
      0≤regD a (physicalDelta a (cap i) (σ i) (off i) (v i)) (physicalTheta (v i)) := by
    have hθ := physicalTheta_mem (v i)
    have hsin := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
    have hd : 0<physicalDelta a (cap i) (σ i) (off i) (v i) := Real.exp_pos _
    dsimp only [regD]
    exact mul_nonneg (div_nonneg hd.le (regFactor_bounds ha hd (hδ i hi) hsin).1.le)
      (Real.rpow_nonneg hsin.le _)
  constructor
  · exact Finset.prod_pos hpos
  · change L (fun w => ∏i∈s,F i w) (multiDrift a v) (multiNoise m) v / (∏i∈s,F i v) ≤ _
    rw [(normalized_product_generator s F v (multiDrift a v) (multiNoise m) hF
      (fun i hi => (hpos i hi).ne')).2]
    have habs := sum_generator_absorption s
      (fun i => L (F i) (multiDrift a v) (multiNoise m) v / F i v)
      (fun i => N (F i) (multiNoise m) v / F i v)
      (fun i => regD a (physicalDelta a (cap i) (σ i) (off i) (v i)) (physicalTheta (v i))*(physicalV (v i))^2)
      (fun i => regC a*physicalDelta a (cap i) (σ i) (off i) (v i)*(physicalV (v i))^2)
      (fun i j => (physicalDelta a (cap i) (σ i) (off i) (v i)*
        physicalDelta a (cap j) (σ j) (off j) (v j))^(-regM a)*physicalV (v i)*physicalV (v j))
      (regK a/2) (regYoungC a ε) ε
      (fun i hi => mul_nonneg (hD i hi) (sq_nonneg _)) hsize
    refine le_trans (habs ?_ ?_) ?_
    · intro i hi
      rw [hL i hi]
      have h := (actual_regularized_factor ha (v i) (hY i hi) (hδ i hi) (hσ i hi)).2.1
      convert h using 1
      ring
    · intro i hi j hj
      have hjs := Finset.mem_of_mem_erase hj
      rw [hN i hi,hN j hjs]
      have h := actual_noise_pair ha hε (v i) (v j) (hY i hi) (hY j hjs)
        (hδ i hi) (hδ j hjs) (hσ i hi) (hσ j hjs)
      convert h using 1
      ring
    · apply le_of_eq
      congr 1
      simp only [mul_assoc,Finset.mul_sum]

end ExactSLEGreen

namespace ExactSLEGreen
open ExactSLECalculus ExactSLEFiniteTilt ExactSLEGenerator
abbrev RegimeState (m : ℕ) := (Fin m → State) × ℝ
noncomputable def regimeDiscount {m : ℕ} (s : Finset (Fin m))
    (a ε : ℝ) (cap σ off : Fin m → ℝ) (v : Fin m → State) : ℝ :=
  regC a*(∑i∈s,physicalDelta a (cap i) (σ i) (off i) (v i)*(physicalV (v i))^2) +
  regYoungC a ε/2*(∑i∈s,∑j∈s.erase i,
    (physicalDelta a (cap i) (σ i) (off i) (v i)*
      physicalDelta a (cap j) (σ j) (off j) (v j))^(-regM a)*
      physicalV (v i)*physicalV (v j))
noncomputable def discountedProduct {m : ℕ} (s : Finset (Fin m))
    (a : ℝ) (cap σ off : Fin m → ℝ) (v : RegimeState m) : ℝ :=
  Real.exp (-v.2)*regularizedProduct s a cap σ off v.1
end ExactSLEGreen

namespace ExactSLECalculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma discounted_generator {f : E → ℝ} {x A e : E} (r k : ℝ)
    (hf : ContDiffAt ℝ 2 f x) :
    L (fun y : E×ℝ => Real.exp (-y.2)*f y.1) (A,k) (e,0) (x,r) =
      Real.exp (-r)*(L f A e x-k*f x) := by
  let g : E×ℝ → ℝ := fun y => Real.exp (-y.2)
  have hd (y : E×ℝ) : HasFDerivAt g
      (Real.exp (-y.2) • (-ContinuousLinearMap.snd ℝ E ℝ)) y := by
    exact (hasFDerivAt_snd (𝕜 := ℝ) (p := y)).neg.exp
  have hn (y : E×ℝ) : N g (e,0) y = 0 := by
    rw [N,(hd y).fderiv]
    simp
  have hl : L g (A,k) (e,0) (x,r) = -Real.exp (-r)*k := by
    simp only [L,show N g (e,0) = (fun _ => 0) from funext hn,N_const,mul_zero,zero_add]
    rw [(hd (x,r)).fderiv]
    simp
  have hgs : ContDiffAt ℝ 2 g (x,r) := contDiffAt_snd.neg.exp
  have hfs : ContDiffAt ℝ 2 (fun y : E×ℝ => f y.1) (x,r) := hf.comp (x,r) contDiffAt_fst
  rw [L_mul hgs hfs]
  change g (x,r)*L (f ∘ ContinuousLinearMap.fst ℝ E ℝ) (A,k) (e,0) (x,r)+
    f x*L g (A,k) (e,0) (x,r)+N g (e,0) (x,r)*N (fun y : E×ℝ => f y.1) (e,0) (x,r) = _
  rw [L_comp_clm _ hf,hl,hn]
  dsimp [g]
  ring
end ExactSLECalculus

namespace ExactSLEGreen
open ExactSLECalculus ExactSLEFiniteTilt ExactSLEGenerator Metric
lemma physicalRegularized_smooth_infty (a cap σ off : ℝ) (v : State) (hv : 0<Y v) :
    ContDiffAt ℝ (↑(⊤ : ℕ∞)) (physicalRegularized a cap σ off) v := by
  have hu : ContDiffAt ℝ (↑(⊤ : ℕ∞)) (physicalClock a cap) v :=
    ((contDiffAt_const.add J.contDiff.contDiffAt).sub
      (Y.contDiff.contDiffAt.log hv.ne')).div_const (2*a)
  have ht : ContDiffAt ℝ (↑(⊤ : ℕ∞)) physicalTheta v :=
    contDiffAt_const.sub ((X.contDiff.contDiffAt.div Y.contDiff.contDiffAt hv.ne').arctan)
  have hp := physicalTheta_mem v
  have hs : Real.sin (physicalTheta v) ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hp.1 hp.2).ne'
  exact (((contDiffAt_const.mul hu).exp.div_const 3).mul
    ((ht.sin.rpow_const_of_ne hs).add
      (((contDiffAt_const.add (contDiffAt_const.mul hu)).exp).mul
        (contDiffAt_const.add (ht.sin.rpow_const_of_ne hs)))))
lemma regularizedProduct_smooth_infty {m : ℕ} (s : Finset (Fin m))
    (a : ℝ) (cap σ off : Fin m → ℝ) (v : Fin m → State)
    (hY : ∀ i∈s, 0<Y (v i)) :
    ContDiffAt ℝ (↑(⊤ : ℕ∞)) (regularizedProduct s a cap σ off) v := by
  apply contDiffAt_prod
  intro i hi
  exact (physicalRegularized_smooth_infty a (cap i) (σ i) (off i) (v i) (hY i hi)).comp v
    (ContinuousLinearMap.proj i : (Fin m → State) →L[ℝ] State).contDiff.contDiffAt
lemma regularizedProduct_generator_agrees {m : ℕ} (s : Finset (Fin m)) {a : ℝ}
    (ha : 1/4<a) (cap σ off : Fin m → ℝ) (v B : Fin m → State)
    (hY : ∀ i∈s, 0<Y (v i))
    (hδ : ∀ i∈s, physicalDelta a (cap i) (σ i) (off i) (v i)≤1)
    (hσ : ∀ i∈s, |σ i|≤regBeta a)
    (hB : ∀ i∈s, B i=physicalDrift a (v i)) :
    L (regularizedProduct s a cap σ off) B (multiNoise m) v =
      L (regularizedProduct s a cap σ off) (multiDrift a v) (multiNoise m) v := by
  let F : Fin m → (Fin m → State) → ℝ := fun i w => physicalRegularized a (cap i) (σ i) (off i) (w i)
  have hF (i) (hi : i∈s) : ContDiffAt ℝ 2 (F i) v :=
    (physicalRegularized_smooth a (cap i) (σ i) (off i) (v i) (hY i hi)).comp v
      (ContinuousLinearMap.proj i : (Fin m → State) →L[ℝ] State).contDiff.contDiffAt
  have hpos (i) (hi : i∈s) : F i v≠0 :=
    (actual_regularized_factor ha (v i) (hY i hi) (hδ i hi) (hσ i hi)).1.ne'
  have hP : regularizedProduct s a cap σ off v≠0 := Finset.prod_ne_zero_iff.mpr hpos
  apply (div_left_inj' hP).mp
  change L (fun w => ∏ i ∈ s, F i w) B (multiNoise m) v / (∏ i ∈ s, F i v) =
    L (fun w => ∏ i ∈ s, F i w) (multiDrift a v) (multiNoise m) v / (∏ i ∈ s, F i v)
  rw [(normalized_product_generator s F v B (multiNoise m) hF hpos).2,
      (normalized_product_generator s F v (multiDrift a v) (multiNoise m) hF hpos).2]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  have hf := physicalRegularized_smooth a (cap i) (σ i) (off i) (v i) (hY i hi)
  change L (physicalRegularized a (cap i) (σ i) (off i) ∘ (ContinuousLinearMap.proj i : (Fin m → State) →L[ℝ] State)) B _ v = _
  rw [L_comp_clm (ContinuousLinearMap.proj i : (Fin m → State) →L[ℝ] State) hf]
  change _ = L (physicalRegularized a (cap i) (σ i) (off i) ∘ (ContinuousLinearMap.proj i : (Fin m → State) →L[ℝ] State)) (multiDrift a v) _ v
  rw [L_comp_clm (ContinuousLinearMap.proj i : (Fin m → State) →L[ℝ] State) hf]
  change L _ (B i) noise (v i) = L _ (physicalDrift a (v i)) noise (v i)
  rw [hB i hi]
lemma discountedProduct_nonpos {m : ℕ} (s : Finset (Fin m)) {a ε : ℝ}
    (ha : 1/4<a) (hε : 0<ε) (hsize : ε*((s.card:ℝ)-1)≤regK a/2)
    (cap σ off : Fin m → ℝ) (v B : RegimeState m)
    (hY : ∀ i∈s, 0<Y (v.1 i))
    (hδ : ∀ i∈s, physicalDelta a (cap i) (σ i) (off i) (v.1 i)≤1)
    (hσ : ∀ i∈s, |σ i|≤regBeta a)
    (hB : B.2=regimeDiscount s a ε cap σ off v.1 ∧
      ∀ i∈s, B.1 i=physicalDrift a (v.1 i)) :
    L (discountedProduct s a cap σ off) B (multiNoise m,0) v ≤ 0 := by
  have hf : ContDiffAt ℝ 2 (regularizedProduct s a cap σ off) v.1 :=
    (regularizedProduct_smooth_infty s a cap σ off v.1 hY).of_le (by exact WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  change L (fun y : RegimeState m => Real.exp (-y.2)*regularizedProduct s a cap σ off y.1)
    (B.1,B.2) (multiNoise m,0) (v.1,v.2) ≤ 0
  rw [discounted_generator _ _ hf,regularizedProduct_generator_agrees s ha cap σ off v.1 B.1 hY hδ hσ hB.2,hB.1]
  have h := regularized_product_drift s ha hε hsize cap σ off v.1 hY hδ hσ
  apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
  exact sub_nonpos.mpr ((div_le_iff₀ h.1).mp h.2)

noncomputable def regularizedHeightTurn (η : ℝ) (v : State) : ℝ :=
  Real.smoothTransition (4*Y v/η-1)
lemma regularizedHeightTurn_smooth (η : ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (regularizedHeightTurn η) :=
  Real.smoothTransition.contDiff.comp (((contDiff_const.mul Y.contDiff).div_const η).sub contDiff_const)
lemma regularizedHeightTurn_zero {η : ℝ} (hη : 0<η) (v : State) (hv : Y v≤η/4) :
    regularizedHeightTurn η v=0 := by
  apply Real.smoothTransition.zero_of_nonpos
  rw [sub_nonpos,div_le_iff₀ hη]
  linarith
lemma regularizedHeightTurn_one {η : ℝ} (hη : 0<η) (v : State) (hv : η/2≤Y v) :
    regularizedHeightTurn η v=1 := by
  apply Real.smoothTransition.one_of_one_le
  rw [le_sub_iff_add_le,le_div_iff₀ hη]
  linarith
lemma height_regularized_smooth (a η cap σ off : ℝ) (hη : 0<η) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun v => regularizedHeightTurn η v*physicalRegularized a cap σ off v) := by
  rw [contDiff_iff_contDiffAt]
  intro v
  by_cases hv : 0<Y v
  · exact (regularizedHeightTurn_smooth η).contDiffAt.mul (physicalRegularized_smooth_infty a cap σ off v hv)
  · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    have hv' : Y v<η/4 := lt_of_le_of_lt (le_of_not_gt hv) (by positivity)
    filter_upwards [Y.continuous.continuousAt.preimage_mem_nhds (Iio_mem_nhds hv')] with w hw
    simp only [regularizedHeightTurn_zero hη w hw.le,zero_mul]

def regimeBump (m : ℕ) (N : ℝ≥0) : ContDiffBump (0 : RegimeState m) where
  rIn := N+1
  rOut := N+2
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith
noncomputable def regimeCutoff {m : ℕ} (s : Finset (Fin m))
    (a η : ℝ) (N : ℝ≥0) (cap σ off : Fin m → ℝ) (v : RegimeState m) : ℝ :=
  regimeBump m N v * (Real.exp (-v.2)*∏i∈s,
    regularizedHeightTurn η (v.1 i)*physicalRegularized a (cap i) (σ i) (off i) (v.1 i))
lemma regimeCutoff_smooth {m : ℕ} (s : Finset (Fin m)) (a η : ℝ) (hη : 0<η)
    (N : ℝ≥0) (cap σ off : Fin m → ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (regimeCutoff s a η N cap σ off) := by
  apply (regimeBump m N).contDiff.mul
  apply contDiff_snd.neg.exp.mul
  apply contDiff_prod
  intro i hi
  exact (height_regularized_smooth a η (cap i) (σ i) (off i) hη).comp
    (((ContinuousLinearMap.proj i : (Fin m → State) →L[ℝ] State).contDiff).comp contDiff_fst)
lemma regimeCutoff_compact {m : ℕ} (s : Finset (Fin m)) (a η : ℝ)
    (N : ℝ≥0) (cap σ off : Fin m → ℝ) :
    HasCompactSupport (regimeCutoff s a η N cap σ off) :=
  (regimeBump m N).hasCompactSupport.mul_right
lemma regimeCutoff_eq_near {m : ℕ} (s : Finset (Fin m)) (a η : ℝ) (hη : 0<η)
    (N : ℝ≥0) (cap σ off : Fin m → ℝ) (v : RegimeState m) (hv : ‖v‖≤N)
    (hY : ∀ i∈s, η≤Y (v.1 i)) :
    regimeCutoff s a η N cap σ off =ᶠ[𝓝 v] discountedProduct s a cap σ off := by
  have hb : v∈ball (0 : RegimeState m) (regimeBump m N).rIn := by
    simp only [mem_ball,dist_zero_right,regimeBump]
    linarith
  have hturn : ∀ i∈s, ∀ᶠ w in 𝓝 v, regularizedHeightTurn η (w.1 i)=1 := by
    intro i hi
    have hy : η/2<Y (v.1 i) := lt_of_lt_of_le (by linarith) (hY i hi)
    have hc : Continuous (fun w : RegimeState m => Y (w.1 i)) :=
      Y.continuous.comp ((continuous_apply i).comp continuous_fst)
    filter_upwards [hc.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hy)] with w hw
    exact regularizedHeightTurn_one hη (w.1 i) hw.le
  filter_upwards [(regimeBump m N).eventuallyEq_one_of_mem_ball hb,
    (Filter.eventually_all_finset s).mpr hturn] with w hw htw
  simp only [regimeCutoff,hw,Pi.one_apply,one_mul,discountedProduct,regularizedProduct]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [htw i hi,one_mul]
end ExactSLEGreen
end

end OAI
