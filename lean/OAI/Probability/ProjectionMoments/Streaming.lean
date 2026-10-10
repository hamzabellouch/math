import OAI.Probability.ProjectionMoments.StoppingKernel

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
namespace NoiselessRegression

section
namespace Learner
universe u

theorem riesz_success :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ d M T : ℕ, 16 ≤ d → ∀ ε : ℝ,
      0 < ε → ε ≤ 1/10 →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (ρ : Measure Ω), IsProbabilityMeasure ρ →
      ∀ L : Learner d M T Ω, L.Admissible ρ →
      let q := d/8
      let W : ℝ := ((T:ℝ)+2)*2^M
      L.uniformSuccess ρ ε ≤ ENNReal.ofReal
        (C₀^d*ε^((d:ℝ)/2-1)*(1+C₀^d*(1+Real.log (1/ε))*W^(1/(q:ℝ)))^((T+q-1)/q)) := by
  refine ⟨32768,by norm_num,?_⟩
  intro d M T hd ε hε hε10 Ω _ ρ hρ L hL q W
  let : IsProbabilityMeasure ρ := hρ
  let a := (d-1)/2
  have hq : 2 ≤ q := by dsimp [q]; omega
  have ha : 2*a ≤ d-1 := by dsimp [a]; omega
  have hqa : 2*q ≤ a := by dsimp [a,q]; omega
  have hb := L.streaming_success_bound_tagged ρ hL (by omega) hε ha hq hqa
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hqn : 0 ≤ 1/(q:ℝ) := by positivity
  have he : ((T+2)*2^M:ℝ≥0∞)^(1/(q:ℝ)) = ENNReal.ofReal (W^(1/(q:ℝ))) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg hW hqn]
    congr 1
    dsimp [W]
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (T:ℝ)+2),
      ENNReal.ofReal_add (by positivity : 0 ≤ (T:ℝ)) (by norm_num : (0:ℝ) ≤ 2),
      ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 2),ENNReal.ofReal_natCast,ENNReal.ofReal_ofNat]
  have hfactor : streamFactor (E := Vector d) (J := TaggedState M T) q =
      ENNReal.ofReal ((32768:ℝ)^d*W^(1/(q:ℝ))) := by
    unfold streamFactor
    rw [finrank_euclideanSpace_fin,card_taggedState,Nat.cast_mul,Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat,he]
    rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_pow (by norm_num),ENNReal.ofReal_ofNat]
  rw [hfactor, ← ENNReal.ofReal_pow (by positivity : 0 ≤ (32768:ℝ)^d*W^(1/(q:ℝ))),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ (3:ℝ)*4^d),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ (3:ℝ)*4^d*ε^a)] at hb
  apply hb.trans
  apply ENNReal.ofReal_le_ofReal
  have hε1 : ε ≤ 1 := by linarith
  have hexp : (d:ℝ)/2-1 ≤ a := by
    have hh : d-1 ≤ 2*a+1 := by dsimp [a]; omega
    have hd1 : 1 ≤ d := by omega
    have hh' : (d:ℝ) ≤ 2*(a:ℝ)+2 := by
      exact_mod_cast (show d ≤ 2*a+2 by omega)
    linarith
  have heps : ε^a ≤ ε^((d:ℝ)/2-1) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge hε hε1 hexp
  have hconst : (3:ℝ)*4^d ≤ (32768:ℝ)^d := by
    have hp' : (3:ℝ)^1 ≤ 3^d := pow_le_pow_right₀ (by norm_num) (by omega)
    have hsmall : (12:ℝ)^d ≤ (32768:ℝ)^d := pow_le_pow_left₀ (by norm_num) (by norm_num) d
    calc
      (3:ℝ)*4^d ≤ 3^d*4^d := mul_le_mul_of_nonneg_right (by simpa using hp') (by positivity)
      _ = 12^d := by rw [← mul_pow]; norm_num
      _ ≤ _ := hsmall
  have hlog : 0 ≤ Real.log (1/ε) := Real.log_nonneg ((one_le_div hε).mpr hε1)
  have hstep : (32768:ℝ)^d*W^(1/(q:ℝ)) ≤
      1+(32768:ℝ)^d*(1+Real.log (1/ε))*W^(1/(q:ℝ)) := by
    have hm : (32768:ℝ)^d*W^(1/(q:ℝ)) ≤
        (32768:ℝ)^d*(1+Real.log (1/ε))*W^(1/(q:ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hW _)
      nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 32768) d]
    linarith
  exact mul_le_mul (mul_le_mul hconst heps (by positivity) (by positivity))
    (pow_le_pow_left₀ (by positivity) hstep _) (by positivity) (by positivity)

end Learner

universe u
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

lemma prefix_route_mixed_bound
    {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J] [Nonempty J]
    {δ : ℕ → J → (E × ℝ) → J} (hδ : ∀ n j, Measurable (δ n j)) (y : J → E)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {a q : ℕ} {b : ℝ}
    (hb : 0 ≤ b) (hab : (a:ℝ)+b ≤ (Module.finrank ℝ E-1:ℕ))
    (hq : 2 ≤ q) (hqa : 2*q ≤ a) {k T : ℕ} (hk : k ≤ T) (j : J) :
    ((sphereLaw (E := E)).prod (Measure.pi (fun _ : Fin T => stdGaussian E)))
      {z | dist z.1.val (y (streamRoute δ 0 k j
        ((fun i => z.2 (Fin.castLE hk i)),fun i => ⟪z.1.val,z.2 (Fin.castLE hk i)⟫))) ≤ ε} ≤
      (ENNReal.ofReal ((3:ℝ)*4^Module.finrank ℝ E)*ENNReal.ofReal (ε^b)) *
        streamFactor (E := E) (J := J) q ^ ((k+q-1)/q) := by
  have hp := (MeasurePreserving.id (sphereLaw (E := E))).prod
    (measurePreserving_pi_prefix (stdGaussian E) hk)
  have hs : MeasurableSet
      {z : (Metric.sphere (0:E) 1) × (Fin k → E) |
        dist z.1.val (y (streamRoute δ 0 k j (z.2,fun i => ⟪z.1.val,z.2 i⟫))) ≤ ε} := by
    apply measurableSet_le _ measurable_const
    exact (measurable_subtype_coe.comp measurable_fst).dist
      ((measurable_of_finite y).comp ((measurable_streamRoute hδ 0 k j).comp (by fun_prop)))
  apply (le_of_eq (hp.measure_preimage hs.nullMeasurableSet)).trans
  exact route_mixed_bound hδ y hε hε1 hb hab hq hqa k j

namespace Learner
variable {d M T : ℕ} {Ω : Type u}

lemma terminal_eq_forced_of_index (L : Learner d M T Ω) (s : UnitSphere d) (ω : Ω)
    (x : Samples d T) {t : ℕ} (ht : (L.terminal s ω x).1 = t) :
    L.terminal s ω x = (t,L.forcedRun s ω x t) := by
  rcases L.terminal_forced_witness s ω x with ⟨t',ht',he⟩
  have h : t' = t := (congrArg Prod.fst he).symm.trans ht
  subst t'
  exact he

lemma frozen_fixed_success_bound (L : Learner d M T Ω) (ω : Ω) (hd : 3 ≤ d)
    (htrans : ∀ t j, AEMeasurable (fun obs => (L.transition t ω j obs).2) (observationReference d))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {a q : ℕ} {b : ℝ}
    (hb : 0 ≤ b) (hab : (a:ℝ)+b ≤ (d-1:ℕ))
    (hq : 2 ≤ q) (hqa : 2*q ≤ a) {t : ℕ} (ht : t ≤ T) :
    ((uniformSphere d).prod (sampleLaw d T))
      {z | (L.terminal z.1 ω z.2).1 = t ∧ angularError z.1 (L.estimate z.1 ω z.2) ≤ ε} ≤
      (ENNReal.ofReal ((3:ℝ)*4^d)*ENNReal.ofReal (ε^b)) *
        streamFactor (E := Vector d) (J := State M) q ^ ((t+q-1)/q) := by
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
  let S := {z : UnitSphere d × Samples d T |
    dist z.1.val (L.output t ω (streamRoute δ 0 t (L.initialChoice ω).2
      ((fun i => z.2 (Fin.castLE ht i)),fun i => ⟪z.1.val,z.2 (Fin.castLE ht i)⟫))).val ≤ ε}
  have hmono : {z : UnitSphere d × Samples d T |
      (L.terminal z.1 ω z.2).1 = t ∧ angularError z.1 (L.estimate z.1 ω z.2) ≤ ε} ≤ᵐ[μ] S := by
    filter_upwards [hgood] with z hz
    rintro ⟨hzt,hs⟩
    have he := L.terminal_eq_forced_of_index z.1 ω z.2 hzt
    have hf : L.forcedRun z.1 ω z.2 t = streamRoute δ 0 t (L.initialChoice ω).2
        ((fun i => z.2 (Fin.castLE ht i)),fun i => ⟪z.1.val,z.2 (Fin.castLE ht i)⟫) := by
      rw [L.forcedRun_eq_route z.1 ω z.2 ht]
      exact streamRoute_congr _ _ 0 t _ _ _ (fun n j i => hz n j (Fin.castLE ht i))
    have hc : dist z.1.val (L.estimate z.1 ω z.2).val ≤ ε := by
      apply le_trans _ hs
      simpa only [angularError,dist_comm] using chord_le_arccos (L.estimate z.1 ω z.2) z.1
    change dist z.1.val _ ≤ ε
    simpa only [estimate,he,hf] using hc
  apply (measure_mono_ae hmono).trans
  simpa only [S,μ,uniformSphere,sphereLaw,sampleLaw,finrank_euclideanSpace_fin] using
    prefix_route_mixed_bound hδ (fun j => (L.output t ω j).val) hε hε1 hb (by simpa using hab)
      hq hqa ht (L.initialChoice ω).2

lemma streaming_fixed_success_bound [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (hL : L.Admissible ρ)
    (hstop : AEMeasurable (fun z : UnitSphere d × (Ω × Samples d T) =>
      (L.terminal z.1 z.2.1 z.2.2).1) ((uniformSphere d).prod (ρ.prod (sampleLaw d T))))
    (hd : 3 ≤ d) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {a q : ℕ} {b : ℝ}
    (hb : 0 ≤ b) (hab : (a:ℝ)+b ≤ (d-1:ℕ))
    (hq : 2 ≤ q) (hqa : 2*q ≤ a) {t : ℕ} (ht : t ≤ T) :
    L.uniformFixedSuccess ρ ε t ≤
      (ENNReal.ofReal ((3:ℝ)*4^d)*ENNReal.ofReal (ε^b)) *
        streamFactor (E := Vector d) (J := State M) q ^ ((t+q-1)/q) := by
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
    (L.terminal z.1 z.2.1 z.2.2).1 = t ∧ angularError z.1 (L.estimate z.1 z.2.1 z.2.2) ≤ ε}
  have hS : NullMeasurableSet S ((uniformSphere d).prod (ρ.prod (sampleLaw d T))) :=
    (nullMeasurableSet_eq_fun hstop aemeasurable_const).inter (L.angularSuccess_nullMeasurable ρ ε hL)
  have he := hp.measure_preimage hS
  have hbound := prod_null_set_bound (hS.preimage hp.quasiMeasurePreserving)
    (c := (ENNReal.ofReal ((3:ℝ)*4^d)*ENNReal.ofReal (ε^b)) *
      streamFactor (E := Vector d) (J := State M) q ^ ((t+q-1)/q))
    (by
      filter_upwards [hω] with ω hω
      exact L.frozen_fixed_success_bound ω hd hω hε hε1 hb hab hq hqa ht)
  simpa only [he,measure_univ,mul_one,S,uniformFixedSuccess] using hbound

end Learner
end

lemma streamFactor_ofReal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {J : Type*} [Fintype J] (q : ℕ) :
    streamFactor (E := E) (J := J) q = ENNReal.ofReal
      ((32768:ℝ)^Module.finrank ℝ E*(Fintype.card J:ℝ)^(1/(q:ℝ))) := by
  unfold streamFactor
  rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat,
    ← ENNReal.ofReal_rpow_of_nonneg (Nat.cast_nonneg _) (by positivity : 0 ≤ 1/(q:ℝ)),
    ENNReal.ofReal_natCast]

lemma three_mul_four_pow_le (d : ℕ) (hd : 1 ≤ d) : (3:ℝ)*4^d ≤ (32768:ℝ)^d := by
  have hp : (3:ℝ)^1 ≤ 3^d := pow_le_pow_right₀ (by norm_num) hd
  calc
    (3:ℝ)*4^d ≤ 3^d*4^d := mul_le_mul_of_nonneg_right (by simpa using hp) (by positivity)
    _ = 12^d := by rw [← mul_pow]; norm_num
    _ ≤ _ := pow_le_pow_left₀ (by norm_num) (by norm_num) d

namespace Learner

section
universe u

theorem cap_fixed_stop :
    ∃ C : ℝ, 0 < C ∧ ∀ d M T : ℕ, 32 ≤ d → ∀ ε : ℝ,
      0 < ε → ε ≤ 1/10 →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (ρ : Measure Ω), IsProbabilityMeasure ρ →
      ∀ L : Learner d M T Ω, L.Admissible ρ →
      AEMeasurable (fun z : UnitSphere d × (Ω × Samples d T) =>
        (L.terminal z.1 z.2.1 z.2.2).1) ((uniformSphere d).prod (ρ.prod (sampleLaw d T))) →
      ∀ t : ℕ, t ≤ T →
      let k := d/16
      let α : ℝ := ((d:ℝ)-1)/2
      L.uniformFixedSuccess ρ ε t ≤ ENNReal.ofReal
        (Real.exp (C*d)*(ε/2)^α*(Real.exp (C*d)*(2:ℝ)^((M:ℝ)/k))^((t+k-1)/k)) := by
  refine ⟨Real.log 65536,Real.log_pos (by norm_num),?_⟩
  intro d M T hd ε hε hε10 Ω _ ρ hρ L hL hstop t ht k α
  let : IsProbabilityMeasure ρ := hρ
  let a := (d-1)/2
  have hk : 2 ≤ k := by dsimp [k]; omega
  have hka : 2*k ≤ a := by dsimp [k,a]; omega
  have hα : 0 ≤ α := by
    dsimp [α]
    have hdR : (32:ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hαd : α ≤ (d:ℝ) := by
    dsimp [α]
    have := Nat.cast_nonneg (α := ℝ) d
    linarith
  have hab : (a:ℝ)+α ≤ (d-1:ℕ) := by
    have hh : (2:ℝ)*a ≤ (d-1:ℕ) := by exact_mod_cast (show 2*a ≤ d-1 by dsimp [a]; omega)
    rw [Nat.cast_sub (by omega : 1 ≤ d),Nat.cast_one] at hh ⊢
    dsimp [α]; linarith
  have hb := L.streaming_fixed_success_bound ρ hL hstop (by omega) hε (by linarith)
    hα hab hk hka ht
  have he : Real.exp (Real.log 65536*(d:ℝ)) = (65536:ℝ)^d := by
    rw [mul_comm,Real.exp_nat_mul,Real.exp_log (by norm_num)]
  rw [he]
  rw [streamFactor_ofReal,finrank_euclideanSpace_fin,Fintype.card_fin,
    Nat.cast_pow,Nat.cast_ofNat] at hb
  have hroot : ((2:ℝ)^M)^(1/(k:ℝ)) = (2:ℝ)^((M:ℝ)/k) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (by norm_num)]
    congr 1; ring
  rw [hroot, ← ENNReal.ofReal_pow (by positivity : 0 ≤ (32768:ℝ)^d*(2:ℝ)^((M:ℝ)/k)),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ (3:ℝ)*4^d),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ (3:ℝ)*4^d*ε^α)] at hb
  apply hb.trans
  apply ENNReal.ofReal_le_ofReal
  have hbase : (3:ℝ)*4^d*ε^α ≤ (65536:ℝ)^d*(ε/2)^α := by
    have heps : ε^α = 2^α*(ε/2)^α := by
      rw [← Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by positivity : 0 ≤ ε/2)]
      congr 1; ring
    rw [heps,← mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    calc
      (3:ℝ)*4^d*2^α ≤ (32768:ℝ)^d*(2:ℝ)^d := by
        apply mul_le_mul (three_mul_four_pow_le d (by omega)) _ (by positivity) (by positivity)
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hαd
      _ = 65536^d := by rw [← mul_pow]; norm_num
  apply mul_le_mul hbase _ (by positivity) (by positivity)
  exact pow_le_pow_left₀ (by positivity)
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) (by norm_num) d) (by positivity)) _

end

universe u
variable {d M T : ℕ} {Ω : Type u}

lemma frozen_success_bound_local (L : Learner d M T Ω) (ω : Ω) (hd : 3 ≤ d)
    (htrans : ∀ t j, AEMeasurable (L.transition t ω j) (observationReference d))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {a q : ℕ} {b : ℝ}
    (hb : 0 ≤ b) (hab : (a:ℝ)+b ≤ (d-1:ℕ)) (hq : 2 ≤ q) (hqa : 2*q ≤ a) :
    ((uniformSphere d).prod (sampleLaw d T))
      {z | angularError z.1 (L.estimate z.1 ω z.2) ≤ ε} ≤
      (ENNReal.ofReal ((3 : ℝ)*4^d) * ENNReal.ofReal (ε^b)) *
        streamFactor (E := Vector d) (J := TaggedState M q) q ^ ((T+q-1)/q) := by
  classical
  let : NeZero d := ⟨by omega⟩
  let τ : ℕ → State M → (Vector d × ℝ) → Bool × State M := fun t j => (htrans t j).mk _
  have hτ (t : ℕ) (j : State M) : Measurable (τ t j) := (htrans t j).measurable_mk
  let μ := (uniformSphere d).prod (sampleLaw d T)
  have hgood : ∀ᵐ z ∂μ, ∀ t j (i : Fin T),
      L.transition t ω j (z.2 i,⟪z.1.val,z.2 i⟫) = τ t j (z.2 i,⟪z.1.val,z.2 i⟫) := by
    simp only [ae_all_iff]
    intro t j i
    exact (sphere_sample_observation_quasi (by simpa using hd) i).ae (htrans t j).ae_eq_mk
  let S := {z : UnitSphere d × Samples d T | dist z.1.val
    (L.taggedOutput ω (streamRoute (taggedStep (T := T) τ) 0 T (taggedStart (L.initialChoice ω))
      (z.2,fun i => ⟪z.1.val,z.2 i⟫))).val ≤ ε}
  have hmono : {z : UnitSphere d × Samples d T | angularError z.1 (L.estimate z.1 ω z.2) ≤ ε}
      ≤ᵐ[μ] S := by
    filter_upwards [hgood] with z hz
    intro hs
    have he := streamRoute_congr (taggedStep (T := T) (fun t j => L.transition t ω j))
      (taggedStep (T := T) τ) 0 T (taggedStart (L.initialChoice ω)) z.2
      (fun i => ⟪z.1.val,z.2 i⟫) (fun t j i => taggedStep_congr t j _ (fun a => hz t a i))
    have hc : dist z.1.val (L.estimate z.1 ω z.2).val ≤ ε := by
      apply le_trans _ hs
      simpa only [angularError,dist_comm] using chord_le_arccos (L.estimate z.1 ω z.2) z.1
    change dist z.1.val _ ≤ ε
    rw [L.estimate_eq_taggedRoute,he] at hc
    exact hc
  apply (measure_mono_ae hmono).trans
  have hy (a : TaggedState M T) : (L.taggedOutput ω a).val =
      (match a with | .inl a => (L.output T ω a).val | .inr (t,a) => (L.output t ω a).val) := by
    cases a <;> rfl
  have hh := stopped_route_mixed_bound hτ (fun t j => (L.output t ω j).val) hε hε1 hb hab hq hqa
    (T := T) (taggedStart (L.initialChoice ω))
  have hset : S = {z : UnitSphere d × Samples d T | dist z.1.val
      (match streamRoute (taggedStep (T := T) τ) 0 T (taggedStart (L.initialChoice ω))
        (z.2,fun i => ⟪z.1.val,z.2 i⟫) with
      | .inl a => (L.output T ω a).val | .inr (t,a) => (L.output t ω a).val) ≤ ε} := by
    ext z
    change (dist z.1.val (L.taggedOutput ω _).val ≤ ε) ↔ _
    rw [hy]
    rfl
  rw [hset]
  exact hh

lemma streaming_success_bound_local [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (hL : L.Admissible ρ) (hd : 3 ≤ d) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {a q : ℕ} {b : ℝ} (hb : 0 ≤ b) (hab : (a:ℝ)+b ≤ (d-1:ℕ)) (hq : 2 ≤ q) (hqa : 2*q ≤ a) :
    L.uniformSuccess ρ ε ≤
      (ENNReal.ofReal ((3 : ℝ)*4^d) * ENNReal.ofReal (ε^b)) *
        streamFactor (E := Vector d) (J := TaggedState M q) q ^ ((T+q-1)/q) := by
  let : NeZero d := ⟨by omega⟩
  let : SigmaFinite (observationReference d) := by unfold observationReference; infer_instance
  have hω : ∀ᵐ ω ∂ρ, ∀ t j,
      AEMeasurable (L.transition t ω j) (observationReference d) := by
    simp only [ae_all_iff]
    intro t j
    exact ae_fiber_aemeasurable (hL.transition t j).prod_swap
  have hp := ((MeasurePreserving.id (uniformSphere d)).prod
      (Measure.measurePreserving_swap (μ := sampleLaw d T) (ν := ρ))).comp
    (measurePreserving_prodAssoc (uniformSphere d) (sampleLaw d T) ρ)
  let S := {z : UnitSphere d × (Ω × Samples d T) |
    angularError z.1 (L.estimate z.1 z.2.1 z.2.2) ≤ ε}
  have hS : NullMeasurableSet S ((uniformSphere d).prod (ρ.prod (sampleLaw d T))) :=
    L.angularSuccess_nullMeasurable ρ ε hL
  have he := hp.measure_preimage hS
  have hb := prod_null_set_bound (hS.preimage hp.quasiMeasurePreserving)
    (c := (ENNReal.ofReal ((3 : ℝ)*4^d) * ENNReal.ofReal (ε^b)) *
      streamFactor (E := Vector d) (J := TaggedState M q) q ^ ((T+q-1)/q))
    (by
      filter_upwards [hω] with ω hω
      exact L.frozen_success_bound_local ω hd hω hε hε1 hb hab hq hqa)
  simpa only [he,measure_univ,mul_one,S,uniformSuccess] using hb

theorem haar_success :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ d M T : ℕ, 16 ≤ d → ∀ ε : ℝ,
      0 < ε → ε ≤ 1/10 →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (ρ : Measure Ω), IsProbabilityMeasure ρ →
      ∀ L : Learner d M T Ω, L.Admissible ρ →
      let k := d/4
      let Nstar : ℝ := ((k:ℝ)+2)*2^M
      L.uniformSuccess ρ ε ≤ ENNReal.ofReal
        (C^d*ε^k*(C^d*Nstar^(1/(k:ℝ)))^((T+k-1)/k)) := by
  refine ⟨32768,by norm_num,?_⟩
  intro d M T hd ε hε hε10 Ω _ ρ hρ L hL k Nstar
  let : IsProbabilityMeasure ρ := hρ
  let a := d-1-k
  have hk : 2 ≤ k := by dsimp [k]; omega
  have hka : 2*k ≤ a := by dsimp [k,a]; omega
  have hab : (a:ℝ)+(k:ℝ) ≤ (d-1:ℕ) := by
    exact_mod_cast (show a+k ≤ d-1 by dsimp [a,k]; omega)
  have hb := L.streaming_success_bound_local ρ hL (by omega) hε (by linarith)
    (Nat.cast_nonneg k) hab hk hka
  have hcard : (Fintype.card (TaggedState M k):ℝ) = Nstar := by
    rw [card_taggedState]; simp [Nstar,Nat.cast_mul,Nat.cast_add,Nat.cast_pow]
  rw [Real.rpow_natCast,streamFactor_ofReal,finrank_euclideanSpace_fin,hcard,
    ← ENNReal.ofReal_pow (by positivity : 0 ≤ (32768:ℝ)^d*Nstar^(1/(k:ℝ))),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ (3:ℝ)*4^d),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ (3:ℝ)*4^d*ε^k)] at hb
  apply hb.trans
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (three_mul_four_pow_le d (by omega)) (by positivity)) (by positivity)

end Learner
end NoiselessRegression

end

end OAI
