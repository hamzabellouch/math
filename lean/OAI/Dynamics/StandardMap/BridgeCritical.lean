import OAI.Dynamics.StandardMap.LimitCancellation

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology CompactlySupported Classical
namespace StandardMapEntropy
namespace CriticalScaleSequence
lemma aligned_observation_bound (S : CriticalScaleSequence) {R : ℕ}
    (p : ℕ) (s t : Fin R → DyadicTime) (a : Fin R → ℤ) (m : Fin R → ℕ) (hm : ∀j,0< m j)
    (hs : ∀j,((2^p:ℕ):ℝ)*(s j:ℝ)=(a j:ℝ))
    (ht : ∀j,((2^p:ℕ):ℝ)*(t j:ℝ)=(a j:ℝ)+(m j:ℝ))
    (F : (Fin R → ℝ) → ℝ) (L : NNReal) (hF : LipschitzWith L F) (hFz : F 0=0) :
    ∃ C : ℝ,0≤ C ∧ ∀i l,p+l≤ S.exponent i →
      (∫d,arrayObservation s t F d ∂sampleLaw (S.parameter i) (S.positive i).le (2^(p+l)) (by positivity))≤ C*S.epsilon i := by
  obtain ⟨C,hC,hb⟩ := S.observation_scaled_bound p a m hm F L hF hFz
  refine ⟨C,hC,?_⟩
  intro i l hl
  rw [integral_observable_sample _ (S.positive i).le _ (by positivity) s t (fun j => a j*2^l) (fun j => m j*2^l)
    (fun j => Nat.mul_pos (hm j) (by positivity)) (fun j => aligned_scale p l (s j) (a j) (hs j))
    (fun j => aligned_scale_end p l (t j) (a j) (m j) (ht j)) F hF.continuous]
  exact hb i l hl
lemma bridge_grid_mean_bounds (S : CriticalScaleSequence) {Rw Rh : ℕ} (B : BridgeGrid Rw Rh)
    (Fw : (Fin Rw → ℝ) → ℝ) (Fh : (Fin Rh → ℝ) → ℝ) (L : NNReal)
    (hFw : LipschitzWith L Fw) (hFh : LipschitzWith L Fh) (hFwz : Fw 0=0) (hFhz : Fh 0=0) :
    ∃ C : ℝ,0≤ C ∧ ∀i l,B.p+l≤ S.exponent i →
      (∫d,arrayObservation B.sw B.tw Fw d ∂sampleLaw (S.parameter i) (S.positive i).le (2^(B.p+l)) (by positivity))≤ C*S.epsilon i ∧
      (∫d,arrayObservation B.sh B.th Fh d ∂sampleLaw (S.parameter i) (S.positive i).le (2^(B.p+l)) (by positivity))≤ C*S.epsilon i := by
  obtain ⟨Cw,hCw,hw⟩ := S.aligned_observation_bound B.p B.sw B.tw (fun j => B.aw j+B.b) B.nw B.pw B.hsw B.htw Fw L hFw hFwz
  obtain ⟨Ch,hCh,hh⟩ := S.aligned_observation_bound B.p B.sh B.th (fun j => B.ah j+B.b) B.nh B.ph B.hsh B.hth Fh L hFh hFhz
  refine ⟨max Cw Ch,hCw.trans (le_max_left _ _),?_⟩
  intro i l hl
  exact ⟨(hw i l hl).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (S.epsilon_pos i).le),
    (hh i l hl).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (S.epsilon_pos i).le)⟩
lemma bridge_integral_tendsto (S : CriticalScaleSequence) {Rw Rh : ℕ} (B : BridgeGrid Rw Rh)
    (p len : ℕ → ℕ) (hp : Tendsto p atTop atTop)
    (hpl : ∀i j,j<len i → p i+j≤ S.exponent i)
    (Fw : (Fin Rw → ℝ) → ℝ) (Fh : (Fin Rh → ℝ) → ℝ) (L : NNReal)
    (hFw : LipschitzWith L Fw) (hFh : LipschitzWith L Fh) (hFwz : Fw 0=0) (hFhz : Fh 0=0)
    (hW0 : ∀d,0≤ arrayObservation B.sw B.tw Fw d) (hH0 : ∀d,0≤ arrayObservation B.sh B.th Fh d)
    (T : ℝ) (hT : ∀ᶠ i in atTop,
      (∫d,arrayObservation B.sw B.tw Fw d ∂scaleLaw (S.parameter i) (S.positive i).le (p i) (len i) (S.epsilon i))≤ T ∨
      (∫d,arrayObservation B.sh B.th Fh d ∂scaleLaw (S.parameter i) (S.positive i).le (p i) (len i) (S.epsilon i))≤ T)
    (η : ℝ) (hη : 0<η) (F : DistanceArray → ℝ) (hF : Continuous F) (hF0 : ∀d,0≤ F d)
    (D : ℝ) (hD : 0≤ D) (hFW : ∀d,F d≤ D*arrayObservation B.sw B.tw Fw d)
    (hzero : ∀d,¬((999/1000:ℝ)*((B.v:ℝ)-(B.u:ℝ))< d.val B.u B.v ∧ η< arrayObservation B.sh B.th Fh d) → F d=0) :
    Tendsto (fun i => ∫d,F d ∂scaleLaw (S.parameter i) (S.positive i).le (p i) (len i) (S.epsilon i)) atTop (𝓝 0) := by
  obtain ⟨C,hC,hmeans⟩ := S.bridge_grid_mean_bounds B Fw Fh L hFw hFh hFwz hFhz
  have hlo : Tendsto (fun i => p i-B.p) atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro n
    filter_upwards [hp.eventually_ge_atTop (n+B.p)] with i hi
    omega
  have hn : Tendsto (fun i => ((B.N*2^(p i-B.p):ℕ):ℝ)) atTop atTop := by
    have hpow : Tendsto (fun i => (2:ℝ)^(p i-B.p)) atTop atTop := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).comp hlo
    simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using hpow.const_mul_atTop (show (0:ℝ)<B.N by exact_mod_cast (show 0<B.N from by have := B.large; omega))
  have hinv : Tendsto (fun i => 1/((B.N*2^(p i-B.p):ℕ):ℝ)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hn
  have hdelta : ∀ᶠ i in atTop,1/((B.N*2^(p i-B.p):ℕ):ℝ)<η/2 := hinv.eventually_lt_const (by linarith)
  have hc := S.parameter_tendsto.eventually eventually_bridgeScalarControl
  have hs := S.parameter_tendsto.eventually (eventually_bridge_observation_scalars (L:ℝ))
  have hM := (tendsto_growthBase.comp S.parameter_tendsto).eventually_ge_atTop ((2:ℝ)^10)
  apply squeeze_zero' (Eventually.of_forall (fun i => integral_nonneg hF0))
  · filter_upwards [hp.eventually_ge_atTop B.p,hdelta,hc,hs,hM,hT] with i hi hdi hci hsi hMi hTi
    have he : B.p+(p i-B.p)=p i := Nat.add_sub_of_le hi
    have hb := B.scale_bound (S.parameter i) hci (p i-B.p) (len i) (S.epsilon i) (S.epsilon_pos i)
      Fw Fh L hFw hFh hW0 hH0 hsi.1 hsi.2 hMi η hη hdi F hF D hD hFW hzero C T hC
      (fun j hj => by simpa only [←Nat.add_assoc,he] using (hmeans i (p i-B.p+j) (by have := hpl i j hj; omega)).1)
      (fun j hj => by simpa only [←Nat.add_assoc,he] using (hmeans i (p i-B.p+j) (by have := hpl i j hj; omega)).2)
      (by simpa only [he] using hTi)
    simpa only [he] using hb
  · have ht := (S.epsilon_tendsto.const_mul T).add (hinv.const_mul 2)
    have hh := ht.const_mul ((D*bridgeRealConstant/(η/2))*C)
    convert! hh using 1 <;> simp only [mul_zero,add_zero,mul_one_div]
end CriticalScaleSequence
end StandardMapEntropy

end OAI
