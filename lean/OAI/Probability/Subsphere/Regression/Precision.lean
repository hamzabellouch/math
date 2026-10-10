import Mathlib
import OAI.Probability.Subsphere.Regression.Streaming

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace SubsphereRegression
open scoped Topology
open InnerProductSpace
open scoped Pointwise
section StreamTransfer
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma measurePreserving_pi_prefix (ν : Measure E) [IsProbabilityMeasure ν]
    {t T : ℕ} (ht : t ≤ T) :
    MeasurePreserving (fun x : Fin T → E => fun i : Fin t => x (Fin.castLE ht i))
      (Measure.pi (fun _ => ν)) (Measure.pi (fun _ => ν)) := by
  refine ⟨by fun_prop, ?_⟩
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (by fun_prop)]
  exact lintegral_pi_prefix ν ht f hf

lemma sphere_sample_observation_quasi [Nontrivial E] (hd : 3 ≤ Module.finrank ℝ E)
    {T : ℕ} (i : Fin T) :
    Measure.QuasiMeasurePreserving
      (fun z : (Metric.sphere (0 : E) 1) × (Fin T → E) => (z.2 i, ⟪z.1.val,z.2 i⟫))
      ((sphereLaw (E := E)).prod (Measure.pi (fun _ => stdGaussian E)))
      ((stdGaussian E).prod volume) := by
  exact (sphere_observation_quasi hd).comp
    ((MeasurePreserving.id (sphereLaw (E := E))).prod
      (measurePreserving_eval (fun _ : Fin T => stdGaussian E) i)).quasiMeasurePreserving

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] in
lemma streamRoute_congr {J : Type*} (δ δ' : ℕ → J → (E × ℝ) → J)
    (n k : ℕ) (j : J) (A : Fin k → E) (b : Fin k → ℝ)
    (h : ∀ t j i, δ t j (A i,b i) = δ' t j (A i,b i)) :
    streamRoute δ n k j (A,b) = streamRoute δ' n k j (A,b) := by
  induction k generalizing n j with
  | zero => rfl
  | succ k ih =>
    rw [streamRoute, streamRoute, h]
    exact ih (n+1) _ (Fin.tail A) (Fin.tail b) (fun t j i => h t j i.succ)

lemma prefix_route_cap_bound [Nontrivial E]
    {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J] [Nonempty J]
    {δ : ℕ → J → (E × ℝ) → J} (hδ : ∀ n j, Measurable (δ n j)) (y : J → E)
    {ε : ℝ} (hε : 0 < ε) {a q : ℕ} (ha : 2*a ≤ Module.finrank ℝ E - 1)
    (hq : 2 ≤ q) (hqa : 2*q ≤ a) {k T : ℕ} (hk : k ≤ T) (j : J) :
    ((sphereLaw (E := E)).prod (Measure.pi (fun _ : Fin T => stdGaussian E)))
      {z | dist z.1.val (y (streamRoute δ 0 k j
        ((fun i => z.2 (Fin.castLE hk i)),fun i => ⟪z.1.val,z.2 (Fin.castLE hk i)⟫))) ≤ ε} ≤
      (ENNReal.ofReal ((3 : ℝ)*4^Module.finrank ℝ E) * ENNReal.ofReal (ε^a)) *
        streamFactor (E := E) (J := J) q ^ (T/q+1) := by
  have hp := (MeasurePreserving.id (sphereLaw (E := E))).prod
    (measurePreserving_pi_prefix (stdGaussian E) hk)
  have hs : MeasurableSet
      {z : (Metric.sphere (0 : E) 1) × (Fin k → E) |
        dist z.1.val (y (streamRoute δ 0 k j (z.2,fun i => ⟪z.1.val,z.2 i⟫))) ≤ ε} := by
    apply measurableSet_le _ measurable_const
    exact (measurable_subtype_coe.comp measurable_fst).dist
      ((measurable_of_finite y).comp ((measurable_streamRoute hδ 0 k j).comp (by fun_prop)))
  apply (le_of_eq (hp.measure_preimage hs.nullMeasurableSet)).trans
  apply (route_cap_bound hδ y hε ha hq hqa k j).trans
  apply mul_le_mul' le_rfl
  exact pow_le_pow_right₀ (one_le_streamFactor (by omega : 0 < q))
    (Nat.add_le_add_right (Nat.div_le_div_right hk) 1)

end StreamTransfer

namespace Learner

lemma frozen_success_bound {d M T : ℕ} {Ω : Type u} (L : Learner d M T Ω)
    (ω : Ω) (hd : 3 ≤ d)
    (htrans : ∀ t j, AEMeasurable (fun obs => (L.transition t ω j obs).2) (observationReference d))
    {ε : ℝ} (hε : 0 < ε) {a q : ℕ} (ha : 2*a ≤ d-1) (hq : 2 ≤ q) (hqa : 2*q ≤ a) :
    ((uniformSphere d).prod (sampleLaw d T))
      {z | angularError z.1 (L.estimate z.1 ω z.2) ≤ ε} ≤
      (T+1 : ℝ≥0∞) * (ENNReal.ofReal ((3 : ℝ)*4^d) * ENNReal.ofReal (ε^a)) *
        streamFactor (E := Vector d) (J := State M) q ^ (T/q+1) := by
  classical
  let : NeZero d := ⟨by omega⟩
  let δ : ℕ → State M → (Vector d × ℝ) → State M := fun t j => (htrans t j).mk _
  have hδ (t : ℕ) (j : State M) : Measurable (δ t j) := (htrans t j).measurable_mk
  let μ := (uniformSphere d).prod (sampleLaw d T)
  have hgood : ∀ᵐ z ∂μ, ∀ t j (i : Fin T),
      (L.transition t ω j (z.2 i,⟪z.1.val,z.2 i⟫)).2 = δ t j (z.2 i,⟪z.1.val,z.2 i⟫) := by
    simp only [ae_all_iff]
    intro t j i
    exact (sphere_sample_observation_quasi (by simpa using hd) i).ae (htrans t j).ae_eq_mk
  let S : Fin (T+1) → Set (UnitSphere d × Samples d T) := fun t =>
    {z | dist z.1.val (L.output t ω (streamRoute δ 0 t (L.initialChoice ω).2
      ((fun i => z.2 (Fin.castLE (by omega) i)),fun i => ⟪z.1.val,z.2 (Fin.castLE (by omega) i)⟫))).val ≤ ε}
  have hmono : {z : UnitSphere d × Samples d T | angularError z.1 (L.estimate z.1 ω z.2) ≤ ε}
      ≤ᵐ[μ] ⋃ t, S t := by
    filter_upwards [hgood] with z hz
    intro hs
    rcases L.terminal_forced_witness z.1 ω z.2 with ⟨t,ht,he⟩
    have hf : L.forcedRun z.1 ω z.2 t = streamRoute δ 0 t (L.initialChoice ω).2
        ((fun i => z.2 (Fin.castLE ht i)),fun i => ⟪z.1.val,z.2 (Fin.castLE ht i)⟫) := by
      rw [L.forcedRun_eq_route z.1 ω z.2 ht]
      exact streamRoute_congr _ _ 0 t _ _ _ (fun n j i => hz n j (Fin.castLE ht i))
    have hc : dist z.1.val (L.estimate z.1 ω z.2).val ≤ ε := by
      apply le_trans _ hs
      simpa only [angularError, dist_comm] using chord_le_arccos (L.estimate z.1 ω z.2) z.1
    refine Set.mem_iUnion.mpr ⟨⟨t,by omega⟩, ?_⟩
    change dist z.1.val (L.output t ω _) ≤ ε
    simpa only [estimate, he, hf] using hc
  let B : ℝ≥0∞ := (ENNReal.ofReal ((3 : ℝ)*4^d) * ENNReal.ofReal (ε^a)) *
    streamFactor (E := Vector d) (J := State M) q ^ (T/q+1)
  have hb (t : Fin (T+1)) : μ (S t) ≤ B := by
    simpa only [B, μ, S, uniformSphere, sphereLaw, sampleLaw, finrank_euclideanSpace_fin] using
      prefix_route_cap_bound hδ (fun j => (L.output t ω j).val) hε
        (by simpa using ha) hq hqa (by omega : (t : ℕ) ≤ T) (L.initialChoice ω).2
  calc
    _ ≤ μ (⋃ t, S t) := measure_mono_ae hmono
    _ ≤ ∑' t, μ (S t) := measure_iUnion_le S
    _ ≤ ∑' _ : Fin (T+1), B := ENNReal.tsum_le_tsum hb
    _ = _ := by simp [B, tsum_fintype, nsmul_eq_mul, mul_assoc]

lemma streaming_success_bound {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (hL : L.Admissible ρ) (hd : 3 ≤ d) {ε : ℝ} (hε : 0 < ε)
    {a q : ℕ} (ha : 2*a ≤ d-1) (hq : 2 ≤ q) (hqa : 2*q ≤ a) :
    L.uniformSuccess ρ ε ≤
      (T+1 : ℝ≥0∞) * (ENNReal.ofReal ((3 : ℝ)*4^d) * ENNReal.ofReal (ε^a)) *
        streamFactor (E := Vector d) (J := State M) q ^ (T/q+1) := by
  let : NeZero d := ⟨by omega⟩
  let : SigmaFinite (observationReference d) := by unfold observationReference; infer_instance
  have hω : ∀ᵐ ω ∂ρ, ∀ t j,
      AEMeasurable (fun obs => (L.transition t ω j obs).2) (observationReference d) := by
    simp only [ae_all_iff]
    intro t j
    filter_upwards [ae_fiber_aemeasurable (hL.transition t j).prod_swap] with ω hω
    exact measurable_snd.comp_aemeasurable hω
  have hp := ((MeasurePreserving.id (uniformSphere d)).prod
      (Measure.measurePreserving_swap (μ := sampleLaw d T) (ν := ρ))).comp
    (measurePreserving_prodAssoc (uniformSphere d) (sampleLaw d T) ρ)
  let S := {z : UnitSphere d × (Ω × Samples d T) |
    angularError z.1 (L.estimate z.1 z.2.1 z.2.2) ≤ ε}
  have hS : NullMeasurableSet S ((uniformSphere d).prod (ρ.prod (sampleLaw d T))) :=
    L.angularSuccess_nullMeasurable ρ ε hL
  have he := hp.measure_preimage hS
  have hb := prod_null_set_bound (hS.preimage hp.quasiMeasurePreserving)
    (c := (T+1 : ℝ≥0∞) * (ENNReal.ofReal ((3 : ℝ)*4^d) * ENNReal.ofReal (ε^a)) *
      streamFactor (E := Vector d) (J := State M) q ^ (T/q+1))
    (by
      filter_upwards [hω] with ω hω
      exact L.frozen_success_bound ω hd hω hε ha hq hqa)
  simpa only [he, measure_univ, mul_one, S, uniformSuccess] using hb

end Learner

namespace Learner

lemma streaming_success_bound_real {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (hL : L.Admissible ρ) (hd : 3 ≤ d) {ε : ℝ} (hε : 0 < ε)
    {a q : ℕ} (ha : 2*a ≤ d-1) (hq : 2 ≤ q) (hqa : 2*q ≤ a)
    (hs : (2/3 : ℝ≥0∞) ≤ L.uniformSuccess ρ ε) :
    (2/3 : ℝ) ≤ ((T : ℝ)+1) * ((3 : ℝ)*4^d * ε^a) *
      ((32768 : ℝ)^d * ((2 : ℝ)^M)^(1/(q : ℝ)))^(T/q+1) := by
  have hb := hs.trans (L.streaming_success_bound ρ hL hd hε ha hq hqa)
  have ht : (T+1 : ℝ≥0∞) *
      (ENNReal.ofReal ((3 : ℝ)*4^d) * ENNReal.ofReal (ε^a)) *
      streamFactor (E := Vector d) (J := State M) q ^ (T/q+1) ≠ ∞ := by
    apply ENNReal.mul_ne_top
    · apply ENNReal.mul_ne_top (by simp)
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    · exact ENNReal.pow_ne_top (streamFactor_ne_top q)
  have hr := ENNReal.toReal_mono ht hb
  simpa [ENNReal.toReal_div, ENNReal.toReal_ofNat, ENNReal.toReal_mul,
    ENNReal.toReal_add, ENNReal.toReal_natCast, ENNReal.toReal_one,
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 3*4^d),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ ε^a), streamFactor,
    ENNReal.toReal_pow, ← ENNReal.toReal_rpow, finrank_euclideanSpace_fin,
    Fintype.card_fin, State, Nat.cast_pow, Nat.cast_ofNat, Vector] using hr

end Learner

lemma precision_from_stream_bound {d M T a q : ℕ} {ε A : ℝ}
    (hd : 32 ≤ d) (hT : d ≤ 4*T) (hq : 0 < q) (hdq : d ≤ 8*q)
    (ha : d ≤ 4*a) (hM : (M : ℝ) ≤ A * (d : ℝ)^2) (hA : 0 < A)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hbound : (2/3 : ℝ) ≤ ((T : ℝ)+1) * ((3 : ℝ)*4^d * ε^a) *
      ((32768 : ℝ)^d * ((2 : ℝ)^M)^(1/(q : ℝ)))^(T/q+1)) :
    (1 / (4*(400000+100*A))) * (d : ℝ) * Real.log (1/ε) ≤ (T : ℝ) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  have hdp : (d : ℝ) ≤ 4*T := by exact_mod_cast hT
  have hdqp : (d : ℝ) ≤ 8*q := by exact_mod_cast hdq
  have hap : (d : ℝ) ≤ 4*a := by exact_mod_cast ha
  have hB : ((T/q+1 : ℕ) : ℝ) * d ≤ 12*T := by
    have hbd : (T/q+1)*d ≤ 12*T := by
      have hmul := Nat.div_mul_le_self T q
      calc
        (T/q+1)*d = (T/q)*d+d := by ring
        _ ≤ (T/q)*(8*q)+d := Nat.add_le_add_right (Nat.mul_le_mul_left _ hdq) _
        _ = 8*((T/q)*q)+d := by ring
        _ ≤ 8*T+d := Nat.add_le_add_right (Nat.mul_le_mul_left 8 hmul) _
        _ ≤ 12*T := by omega
    exact_mod_cast hbd
  have hMq : (M : ℝ) / q ≤ 8*A*d := by
    apply (div_le_iff₀ hq0).2
    calc
      (M : ℝ) ≤ A*d^2 := hM
      _ ≤ A*d*(8*q) := by nlinarith [mul_le_mul_of_nonneg_left hdqp (by positivity : 0 ≤ A*d)]
      _ = 8*A*d*q := by ring
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2/3) hbound
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow,
    Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Real.log_rpow (by positivity), Real.log_pow] at hlog
  have hlogε : Real.log (1/ε) = -Real.log ε := by simp
  have hlogε0 : 0 ≤ Real.log (1/ε) := Real.log_nonneg ((le_div_iff₀ hε).2 (by simpa using hε1))
  have heq : (1/(q : ℝ)) * ((M : ℝ)*Real.log 2) = ((M : ℝ)/q)*Real.log 2 := by ring
  rw [heq] at hlog
  have hlT : Real.log ((T : ℝ)+1) ≤ T := by
    simpa using Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < T+1)
  have hl3 : Real.log (3 : ℝ) ≤ 3 := Real.log_le_self (by norm_num)
  have hl4 : Real.log (4 : ℝ) ≤ 4 := Real.log_le_self (by norm_num)
  have hl32 : Real.log (32768 : ℝ) ≤ 32768 := Real.log_le_self (by norm_num)
  have hl2 : Real.log (2 : ℝ) ≤ 1 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) using 1; norm_num
  have hl23 : -(1 : ℝ) ≤ Real.log (2/3 : ℝ) := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2/3)
    norm_num at h
    linarith
  have hinside : (d : ℝ)*Real.log 32768 + ((M : ℝ)/q)*Real.log 2 ≤
      (32768+8*A)*d := by
    have hm0 : (0 : ℝ) ≤ (M : ℝ)/q := by positivity
    have h1 := mul_le_mul_of_nonneg_left hl32 hd0.le
    have h2 := mul_le_mul_of_nonneg_left hl2 hm0
    nlinarith
  have hfull : ((T/q+1 : ℕ) : ℝ) *
      ((d : ℝ)*Real.log 32768 + ((M : ℝ)/q)*Real.log 2) ≤
      12*T*(32768+8*A) := by
    calc
      _ ≤ ((T/q+1 : ℕ) : ℝ) * ((32768+8*A)*d) :=
        mul_le_mul_of_nonneg_left hinside (Nat.cast_nonneg _)
      _ = (32768+8*A)*(((T/q+1 : ℕ) : ℝ)*d) := by ring
      _ ≤ (32768+8*A)*(12*T) := mul_le_mul_of_nonneg_left hB (by positivity)
      _ = _ := by ring
  have hd4 : (4 : ℝ) ≤ d := by exact_mod_cast (by omega : 4 ≤ d)
  have hlogbound : (a : ℝ)*Real.log (1/ε) ≤ (400000+100*A)*T := by
    have h4 := mul_le_mul_of_nonneg_left hl4 hd0.le
    rw [hlogε]
    nlinarith [mul_nonneg hA.le hT0]
  have hmain : (d : ℝ)*Real.log (1/ε) ≤ 4*(400000+100*A)*T := by
    have ham := mul_le_mul_of_nonneg_right hap hlogε0
    linarith
  have hden : (0 : ℝ) < 4*(400000+100*A) := by positivity
  calc
    _ = ((d : ℝ)*Real.log (1/ε))/(4*(400000+100*A)) := by ring
    _ ≤ T := (div_le_iff₀ hden).2 (by nlinarith [hmain])

theorem fixed_quadratic_memory : FixedQuadraticMemory.{u} := by
  intro A hA
  refine ⟨1/(4*(400000+100*A)), by positivity, 32, ?_⟩
  intro d hd M T hM ε hε hε10 Ω _ ρ hρ L hL hs
  let : IsProbabilityMeasure ρ := hρ
  have hT : d ≤ 4*T := by
    by_contra h
    have hb := hs.trans (L.linear_success_bound ρ (by omega) (by omega) hε10 hL)
    have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
    norm_num [ENNReal.toReal_div] at hr
  let q := (d-1)/4
  let a := 2*q
  have hq : 2 ≤ q := by dsimp [q]; omega
  have hqa : 2*q ≤ a := le_rfl
  have ha : 2*a ≤ d-1 := by dsimp [a, q]; omega
  have hdq : d ≤ 8*q := by dsimp [q]; omega
  have hda : d ≤ 4*a := by dsimp [a]; omega
  exact precision_from_stream_bound hd hT (by omega) hdq hda hM hA hε (by linarith)
    (L.streaming_success_bound_real ρ hL (by omega) hε ha hq hqa hs)

section LowerFubini
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
lemma prod_null_set_lower_bound {S : Set (X × Y)} (hS : NullMeasurableSet S (μ.prod ν))
    {c : ℝ≥0∞} (h : ∀ᵐ x ∂μ, c ≤ ν {y | (x,y) ∈ S}) :
    c * μ univ ≤ (μ.prod ν) S := by
  have hm : AEMeasurable (S.indicator (fun _ => (1 : ℝ≥0∞))) (μ.prod ν) :=
    aemeasurable_const.indicator₀ hS
  rw [← one_mul ((μ.prod ν) S), ← lintegral_indicator_const₀ hS 1, lintegral_prod _ hm]
  have hc : c * μ univ = ∫⁻ _ : X, c ∂μ := (lintegral_const c).symm
  rw [hc]
  apply lintegral_mono_ae
  filter_upwards [h, ae_fiber_aemeasurable hm.prod_swap] with x hx hmx
  have hs : NullMeasurableSet {y | (x,y) ∈ S} ν := by
    have heq : {y | (x,y) ∈ S} = {y | S.indicator (fun _ => (1 : ℝ≥0∞)) (x,y) = 1} := by
      ext y
      by_cases hy : (x,y) ∈ S <;> simp [hy]
    rw [heq]
    exact nullMeasurableSet_eq_fun hmx aemeasurable_const
  change c ≤ ∫⁻ y, ({y | (x,y) ∈ S}).indicator (fun _ => (1 : ℝ≥0∞)) y ∂ν
  simpa [lintegral_indicator_const₀ hs] using hx
end LowerFubini

namespace Learner
lemma uniformSuccess_of_pointwise {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (hL : L.Admissible ρ) (hd : 0 < d) (ε : ℝ) {c : ℝ≥0∞}
    (hs : ∀ s, c ≤ L.success ρ ε s) : c ≤ L.uniformSuccess ρ ε := by
  let : NeZero d := ⟨hd.ne'⟩
  have hb := prod_null_set_lower_bound (L.angularSuccess_nullMeasurable ρ ε hL)
    (c := c) (Filter.Eventually.of_forall hs)
  simpa only [measure_univ, mul_one, uniformSuccess] using hb
end Learner

/-- The constant is fixed before the memory sequence; only the dimension
threshold depends on its little-o convergence. -/
theorem subquadratic_memory : SubquadraticMemory.{u} := by
  obtain ⟨c, hc, d₁, hfixed⟩ := fixed_quadratic_memory (1 : ℝ) (by norm_num)
  refine ⟨c, hc, ?_⟩
  intro M hM
  obtain ⟨d₂, hd₂⟩ := eventually_atTop.1 hM.eventuallyLE
  refine ⟨max d₁ (max d₂ 1), ?_⟩
  intro d hd T ε hε hε10 Ω _ ρ hρ L hL hs
  let : IsProbabilityMeasure ρ := hρ
  have hmem : (M d : ℝ) ≤ 1 * (d : ℝ)^2 := by
    have hm := hd₂ d (by omega)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (M d) : (0 : ℝ) ≤ M d),
      abs_of_nonneg (sq_nonneg (d : ℝ)), one_mul] using hm
  apply hfixed d (by omega) (M d) T hmem ε hε hε10 Ω ρ hρ L hL
  rcases hs with hs | hs
  · exact hs
  · exact L.uniformSuccess_of_pointwise ρ hL (by omega) ε hs

theorem main : SubquadraticMemory.{u} ∧ FixedQuadraticMemory.{u} :=
  ⟨subquadratic_memory, fixed_quadratic_memory⟩

end SubsphereRegression

end
end

end OAI
