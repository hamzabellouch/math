import Mathlib
import OAI.Probability.Subsphere.Kernels.Precision
import OAI.Probability.Subsphere.Geometry.Integration

namespace OAI

noncomputable section

namespace SubsphereRegression
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
lemma sphere_projection_eighth [Nontrivial E] (U : Submodule ℝ E)
    (hU : 16 * Module.finrank ℝ U ≤ Module.finrank ℝ E) :
    sphereLaw {x : Metric.sphere (0 : E) 1 | (4/5 : ℝ) ≤ ‖U.orthogonalProjectionOnto x.val‖^2} ≤
      ENNReal.ofReal (5/64 : ℝ) := by
  have hi := ofReal_integral_eq_lintegral_ofReal (sphere_projection_sq_integrable U)
    (Filter.Eventually.of_forall fun x => sq_nonneg ‖U.orthogonalProjectionOnto x‖)
  rw [sphere_projection_sq_integral] at hi
  have hmark := meas_ge_le_lintegral_div
    (μ := ambientSphereLaw (E := E)) (f := fun x => ENNReal.ofReal (‖U.orthogonalProjectionOnto x‖^2))
    (by fun_prop) (by norm_num : ENNReal.ofReal (4/5 : ℝ) ≠ 0) (ENNReal.ofReal_ne_top : ENNReal.ofReal (4/5 : ℝ) ≠ ∞)
  rw [← hi] at hmark
  have hset : {x : E | ENNReal.ofReal (4/5 : ℝ) ≤ ENNReal.ofReal (‖U.orthogonalProjectionOnto x‖^2)} =
      {x : E | (4/5 : ℝ) ≤ ‖U.orthogonalProjectionOnto x‖^2} := by
    ext x
    change ENNReal.ofReal (4/5 : ℝ) ≤ _ ↔ _
    exact ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)
  rw [hset, ambientSphereLaw,
    (MeasurableEmbedding.subtype_coe Metric.isClosed_sphere.measurableSet).map_apply] at hmark
  apply hmark.trans
  have hd : (0 : ℝ) < Module.finrank ℝ E := by
    exact_mod_cast Module.finrank_pos (R := ℝ) (M := E)
  have hdiv : (Module.finrank ℝ U : ℝ) / (Module.finrank ℝ E : ℝ) ≤ 1/16 := by
    rw [div_le_iff₀ hd]
    have : (16 : ℝ) * Module.finrank ℝ U ≤ Module.finrank ℝ E := by exact_mod_cast hU
    linarith
  calc
    _ ≤ ENNReal.ofReal (1/16 : ℝ) / ENNReal.ofReal (4/5 : ℝ) := by gcongr
    _ = ENNReal.ofReal (5/64 : ℝ) := by
      rw [← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4/5)]
      norm_num

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma three_sets_bound {μ : Measure E} [IsProbabilityMeasure μ] {A B C : Set E}
    (_hA : NullMeasurableSet A μ) (hB : NullMeasurableSet B μ) (hC : NullMeasurableSet C μ)
    {b : ℝ≥0∞} (hAB : μ (A∩B) ≤ b) (hAC : μ (A∩C) ≤ b) (hBC : μ (B∩C) ≤ b) :
    μ A + μ B + μ C ≤ 1 + (b+b+b) := by
  have h₁ := measure_union_add_inter₀ A hB
  have h₂ := measure_union_add_inter₀ (A∪B) hC
  calc
    _ = (μ (A∪B) + μ C) + μ (A∩B) := by rw [← h₁]; ac_rfl
    _ = μ ((A∪B)∪C) + μ ((A∪B)∩C) + μ (A∩B) := by rw [h₂]
    _ ≤ 1 + (μ (A∩C)+μ (B∩C)) + b := by
      apply add_le_add _ hAB
      apply add_le_add prob_le_one
      rw [union_inter_distrib_right]
      exact measure_union_le _ _
    _ ≤ 1 + (b+b) + b := by gcongr
    _ = _ := by ac_rfl

lemma sphere_three_orbit_bound [Nontrivial E] (F : Submodule ℝ E)
    (hF : 16*Module.finrank ℝ Fᗮ ≤ Module.finrank ℝ E)
    (e : F ≃ₗᵢ[ℝ] F) (he : ∀ x, ⟪x,e x⟫ = 0) (he2 : ∀ x, e (e x) = -x)
    (S : Set (Metric.sphere (0 : E) 1)) (hS : NullMeasurableSet S sphereLaw)
    (hnear : ∀ x y : Metric.sphere (0 : E) 1,
      (∀ u : E, u ∈ Fᗮ → ⟪u,x.val⟫ = ⟪u,y.val⟫) → x ∈ S → y ∈ S →
      dist x.val y.val ≤ 1/5) :
    sphereLaw S ≤ ENNReal.ofReal (7/16 : ℝ) := by
  let q := SubsphereCurrent.Quarter.extend F e
  let f := sphereIsometry q
  have hp := sphereIsometry_preserving q
  have hpf := hp.comp hp
  let B := {x : Metric.sphere (0 : E) 1 | (4/5 : ℝ) ≤ ‖Fᗮ.orthogonalProjectionOnto x.val‖^2}
  have hB : sphereLaw B ≤ ENNReal.ofReal (5/64 : ℝ) := sphere_projection_eighth Fᗮ hF
  have hlabel (x : Metric.sphere (0 : E) 1) :
      ∀ u : E, u ∈ Fᗮ → ⟪u,x.val⟫ = ⟪u,(f x).val⟫ := by
    intro u hu
    have hr := q.inner_map_map u x.val
    rw [SubsphereCurrent.Quarter.extend_fixed F e hu] at hr
    exact hr.symm
  have hsmall (x : Metric.sphere (0 : E) 1) {c : ℝ}
      (hc : 2 ≤ c) (hd : dist x.val (f x).val^2 = c*‖F.orthogonalProjectionOnto x.val‖^2)
      (hne : dist x.val (f x).val ≤ 1/5) : x ∈ B := by
    have hn := F.norm_sq_eq_add_norm_sq_starProjection x.val
    rw [mem_sphere_zero_iff_norm.mp x.property] at hn
    change (4/5 : ℝ) ≤ ‖Fᗮ.orthogonalProjectionOnto x.val‖^2
    change (1 : ℝ)^2 = ‖F.orthogonalProjectionOnto x.val‖^2 +
      ‖Fᗮ.orthogonalProjectionOnto x.val‖^2 at hn
    nlinarith [(dist_nonneg : 0 ≤ dist x.val (f x).val), sq_nonneg ‖F.orthogonalProjectionOnto x.val‖,
      mul_nonneg (sub_nonneg.mpr hc) (sq_nonneg ‖F.orthogonalProjectionOnto x.val‖)]
  have hAB : S ∩ f ⁻¹' S ⊆ B := by
    intro x hx
    exact hsmall x (by norm_num) (SubsphereCurrent.Quarter.extend_norm_sq F e he x.val)
      (hnear x (f x) (hlabel x) hx.1 hx.2)
  have hAC : S ∩ (f ∘ f) ⁻¹' S ⊆ B := by
    intro x hx
    have hne := hnear x (f (f x)) (fun u hu => (hlabel x u hu).trans (hlabel (f x) u hu)) hx.1 hx.2
    have hd := SubsphereCurrent.Quarter.extend_square_norm_sq F e he2 x.val
    have hn := F.norm_sq_eq_add_norm_sq_starProjection x.val
    rw [mem_sphere_zero_iff_norm.mp x.property] at hn
    change (4/5 : ℝ) ≤ ‖Fᗮ.orthogonalProjectionOnto x.val‖^2
    change (1 : ℝ)^2 = ‖F.orthogonalProjectionOnto x.val‖^2 +
      ‖Fᗮ.orthogonalProjectionOnto x.val‖^2 at hn
    change dist x.val (f (f x)).val^2 = _ at hd
    nlinarith [(dist_nonneg : 0 ≤ dist x.val (f (f x)).val)]
  have hBC : sphereLaw (f ⁻¹' S ∩ (f ∘ f) ⁻¹' S) ≤ ENNReal.ofReal (5/64 : ℝ) := by
    have heq : f ⁻¹' S ∩ (f ∘ f) ⁻¹' S = f ⁻¹' (S ∩ f ⁻¹' S) := rfl
    rw [heq,hp.measure_preimage (hS.inter (hS.preimage hp.quasiMeasurePreserving))]
    exact (measure_mono hAB).trans hB
  have hh := three_sets_bound hS (hS.preimage hp.quasiMeasurePreserving)
    (hS.preimage hpf.quasiMeasurePreserving) ((measure_mono hAB).trans hB)
    ((measure_mono hAC).trans hB) hBC
  rw [hp.measure_preimage hS,hpf.measure_preimage hS] at hh
  have hr := ENNReal.toReal_mono (by norm_num :
    (1+(ENNReal.ofReal (5/64 : ℝ)+ENNReal.ofReal (5/64 : ℝ)+ENNReal.ofReal (5/64 : ℝ))) ≠ ∞) hh
  simp only [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
    ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _,measure_ne_top _ _⟩) (measure_ne_top _ _)] at hr
  norm_num [ENNReal.toReal_add, ENNReal.add_ne_top] at hr
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
  norm_num
  linarith

namespace Learner
lemma half_linear_success_bound {d M T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (hd : 32 ≤ d) (hT : 32*T ≤ d) {ε : ℝ} (hε : ε ≤ 1/10) (hL : L.Admissible ρ) :
    L.uniformSuccess ρ ε ≤ ENNReal.ofReal (7/16 : ℝ) := by
  classical
  let : NeZero d := ⟨by omega⟩
  have hmeas := ae_fiber_aemeasurable hL.uniform_experiment
  unfold uniformSuccess
  refine (prod_null_set_bound (L.angularSuccess_nullMeasurable ρ ε hL)
    (c := ENNReal.ofReal (7/16 : ℝ)) ?_).trans_eq (by simp)
  filter_upwards [hmeas] with z hz
  let U : Submodule ℝ (Vector d) := Submodule.span ℝ (Set.range z.2)
  have hdim : Module.finrank ℝ U ≤ T := by
    have h := finrank_span_le_card (R := ℝ) (Set.range z.2)
    apply h.trans
    rw [Set.toFinset_range]
    exact (Finset.card_image_le).trans_eq (by simp)
  obtain ⟨F,hFU,hFdim,e,he,he2⟩ := SubsphereCurrent.Quarter.exists_small_fixed U
  have hUF : U ≤ Fᗮ := by
    have h := Submodule.orthogonal_le hFU
    simpa only [Submodule.orthogonal_orthogonal] using h
  have hF : 16 * Module.finrank ℝ Fᗮ ≤ Module.finrank ℝ (Vector d) := by
    rw [finrank_euclideanSpace_fin]
    omega
  change sphereLaw {s : UnitSphere d | angularError s (L.estimate s z.1 z.2) ≤ ε} ≤ _
  apply sphere_three_orbit_bound F hF e he he2
  · exact nullMeasurableSet_le
      (Real.continuous_arccos.measurable.comp_aemeasurable
        ((measurable_subtype_coe.comp_aemeasurable hz).inner measurable_subtype_coe.aemeasurable))
      aemeasurable_const
  · intro s t hlabel hs ht
    have hout : L.estimate s z.1 z.2 = L.estimate t z.1 z.2 := by
      apply L.estimate_congr_labels
      intro i
      exact hlabel (z.2 i) (hUF (Submodule.subset_span (Set.mem_range_self i)))
    have hs' : dist s.val (L.estimate s z.1 z.2).val ≤ ε := by
      apply (chord_le_arccos s (L.estimate s z.1 z.2)).trans
      simpa only [Set.mem_ofPred_eq, angularError, real_inner_comm] using hs
    have ht' : dist t.val (L.estimate t z.1 z.2).val ≤ ε := by
      apply (chord_le_arccos t (L.estimate t z.1 z.2)).trans
      simpa only [Set.mem_ofPred_eq, angularError, real_inner_comm] using ht
    calc
      _ ≤ dist s.val (L.estimate s z.1 z.2).val + dist (L.estimate s z.1 z.2).val t.val := dist_triangle _ _ _
      _ ≤ ε + ε := by rw [hout, dist_comm (L.estimate t z.1 z.2).val t.val] at *; exact add_le_add hs' ht'
      _ ≤ 1/5 := by linarith
end Learner
end SubsphereRegression
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
universe u
namespace SubsphereRegression
namespace Learner
lemma streaming_success_bound_half_real {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (hL : L.Admissible ρ) (hd : 3 ≤ d) {ε : ℝ} (hε : 0 < ε)
    {a q : ℕ} (ha : 2*a ≤ d-1) (hq : 2 ≤ q) (hqa : 2*q ≤ a)
    (hs : (1/2 : ℝ≥0∞) ≤ L.uniformSuccess ρ ε) :
    (1/2 : ℝ) ≤ ((T : ℝ)+1) * ((3 : ℝ)*4^d * ε^a) *
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

lemma precision_from_stream_bound_half_aux {d M T a q : ℕ} {ε A : ℝ}
    (hd : 32 ≤ d) (hT : d ≤ 32*T) (hq : 0 < q) (hdq : d ≤ 8*q)
    (ha : d ≤ 4*a) (hM : (M : ℝ) ≤ A * (d : ℝ)^2) (hA : 0 < A)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hbound : (1/2 : ℝ) ≤ ((T : ℝ)+1) * ((3 : ℝ)*4^d * ε^a) *
      ((32768 : ℝ)^d * ((2 : ℝ)^M)^(1/(q : ℝ)))^(T/q+1)) :
    (1 / (4*(1024+512*A))) * (d : ℝ) * Real.log (1/ε) ≤ (T : ℝ) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  have hdp : (d : ℝ) ≤ 32*T := by exact_mod_cast hT
  have hdqp : (d : ℝ) ≤ 8*q := by exact_mod_cast hdq
  have hap : (d : ℝ) ≤ 4*a := by exact_mod_cast ha
  have hB : ((T/q+1 : ℕ) : ℝ) * d ≤ 40*T := by
    have hbd : (T/q+1)*d ≤ 40*T := by
      have hmul := Nat.div_mul_le_self T q
      calc
        (T/q+1)*d = (T/q)*d+d := by ring
        _ ≤ (T/q)*(8*q)+d := Nat.add_le_add_right (Nat.mul_le_mul_left _ hdq) _
        _ = 8*((T/q)*q)+d := by ring
        _ ≤ 8*T+d := Nat.add_le_add_right (Nat.mul_le_mul_left 8 hmul) _
        _ ≤ 40*T := by omega
    exact_mod_cast hbd
  have hMq : (M : ℝ) / q ≤ 8*A*d := by
    apply (div_le_iff₀ hq0).2
    calc
      (M : ℝ) ≤ A*d^2 := hM
      _ ≤ A*d*(8*q) := by nlinarith [mul_le_mul_of_nonneg_left hdqp (by positivity : 0 ≤ A*d)]
      _ = 8*A*d*q := by ring
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 1/2) hbound
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
  have hl32 : Real.log (32768 : ℝ) ≤ 15 := by
    have hpow : (32768 : ℝ) = 2 ^ (15 : ℕ) := by norm_num
    rw [hpow, Real.log_pow]
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h2 ⊢
    linarith
  have hl2 : Real.log (2 : ℝ) ≤ 1 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) using 1; norm_num
  have hl23 : -(1 : ℝ) ≤ Real.log (1/2 : ℝ) := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 1/2)
    norm_num at h
    linarith
  have hinside : (d : ℝ)*Real.log 32768 + ((M : ℝ)/q)*Real.log 2 ≤
      (15+8*A)*d := by
    have hm0 : (0 : ℝ) ≤ (M : ℝ)/q := by positivity
    have h1 := mul_le_mul_of_nonneg_left hl32 hd0.le
    have h2 := mul_le_mul_of_nonneg_left hl2 hm0
    nlinarith
  have hfull : ((T/q+1 : ℕ) : ℝ) *
      ((d : ℝ)*Real.log 32768 + ((M : ℝ)/q)*Real.log 2) ≤
      40*T*(15+8*A) := by
    calc
      _ ≤ ((T/q+1 : ℕ) : ℝ) * ((15+8*A)*d) :=
        mul_le_mul_of_nonneg_left hinside (Nat.cast_nonneg _)
      _ = (15+8*A)*(((T/q+1 : ℕ) : ℝ)*d) := by ring
      _ ≤ (15+8*A)*(40*T) := mul_le_mul_of_nonneg_left hB (by positivity)
      _ = _ := by ring
  have hd4 : (4 : ℝ) ≤ d := by exact_mod_cast (by omega : 4 ≤ d)
  have hlogbound : (a : ℝ)*Real.log (1/ε) ≤ (1024+512*A)*T := by
    have h4 := mul_le_mul_of_nonneg_left hl4 hd0.le
    rw [hlogε]
    nlinarith [mul_nonneg hA.le hT0]
  have hmain : (d : ℝ)*Real.log (1/ε) ≤ 4*(1024+512*A)*T := by
    have ham := mul_le_mul_of_nonneg_right hap hlogε0
    linarith
  have hden : (0 : ℝ) < 4*(1024+512*A) := by positivity
  calc
    _ = ((d : ℝ)*Real.log (1/ε))/(4*(1024+512*A)) := by ring
    _ ≤ T := (div_le_iff₀ hden).2 (by nlinarith [hmain])

theorem half_precision_old_model :
  ∀ M : ℕ → ℕ,
    Asymptotics.IsLittleO atTop (fun d => (M d : ℝ)) (fun d => (d : ℝ) ^ 2) →
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ T : ℕ, ∀ ε : ℝ,
    0 < ε → ε ≤ 1 / 10 →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (ρ : Measure Ω), IsProbabilityMeasure ρ →
    ∀ L : Learner d (M d) T Ω, L.Admissible ρ →
    ((1 / 2 : ℝ≥0∞) ≤ L.uniformSuccess ρ ε) →
    (1 / (4 * (1024 + 512)) * Real.log 2 : ℝ) * (d : ℝ) * Real.logb 2 (1 / ε) ≤ (T : ℝ) := by
  intro M hM
  obtain ⟨d₂, hd₂⟩ := eventually_atTop.1 hM.eventuallyLE
  refine ⟨max 32 d₂, ?_⟩
  intro d hd T ε hε hε10 Ω _ ρ hρ L hL hs
  let : IsProbabilityMeasure ρ := hρ
  have hd32 : 32 ≤ d := by omega
  have hmem : (M d : ℝ) ≤ 1 * (d : ℝ)^2 := by
    have hm := hd₂ d (by omega)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (M d) : (0 : ℝ) ≤ M d),
      abs_of_nonneg (sq_nonneg (d : ℝ)), one_mul] using hm
  have hs' := hs
  have hT : d ≤ 32*T := by
    by_contra h
    have hb := hs'.trans (L.half_linear_success_bound ρ (by omega) (by omega) hε10 hL)
    have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
    norm_num [ENNReal.toReal_div] at hr
  let q := (d-1)/4
  let a := 2*q
  have hq : 2 ≤ q := by dsimp [q]; omega
  have hqa : 2*q ≤ a := le_rfl
  have ha : 2*a ≤ d-1 := by dsimp [a, q]; omega
  have hdq : d ≤ 8*q := by dsimp [q]; omega
  have hda : d ≤ 4*a := by dsimp [a]; omega
  have hp := precision_from_stream_bound_half_aux hd32 hT (by omega) hdq hda hmem
    (by norm_num : (0 : ℝ) < 1) hε (by linarith : ε ≤ 1)
    (L.streaming_success_bound_half_real ρ hL (by omega) hε ha hq hqa hs')
  have hlog2 : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
  calc
    _ = (1 / (4 * (1024 + 512))) * (d : ℝ) * Real.log (1 / ε) := by
      rw [Real.logb]
      field_simp
    _ ≤ T := by simpa only [mul_one] using hp

end SubsphereRegression
end
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
universe u
namespace SubsphereCurrent

theorem half_precision : HalfPrecision.{u} := by
  refine ⟨1 / (4 * (1024 + 512)) * Real.log 2, mul_pos (by norm_num) (Real.log_pos (by norm_num)), ?_⟩
  intro M hM
  obtain ⟨d₁, hd₁⟩ := SubsphereRegression.half_precision_old_model.{0} M hM
  refine ⟨max 3 d₁, ?_⟩
  intro d hd T ε hε hε10 Ω _ ρ hρ L hL hs
  let : IsProbabilityMeasure ρ := hρ
  let : NeZero d := ⟨by omega⟩
  obtain ⟨ω, hω, hgood⟩ := L.exists_good_seed ρ hL ε
  let K := (L.rules ω).borelVersion hω
  have hK : K.BorelRules := (L.rules ω).borelVersion_rules hω
  have hsuccess : (1/2 : ℝ≥0∞) ≤ K.asTape.uniformSuccess K.tapeLaw ε := by
    rw [K.uniformSuccess_asTape hK ε]
    calc
      (1/2 : ℝ≥0∞) ≤ L.uniformSuccess ρ ε := hs
      _ ≤ ∫⁻ z : UnitSphere d × Samples d T, (L.rules ω).conditionalSuccess ε z.1 z.2
          ∂(uniformSphere d).prod (sampleLaw d T) := hgood
      _ = ∫⁻ z : UnitSphere d × Samples d T, K.conditionalSuccess ε z.1 z.2
          ∂(uniformSphere d).prod (sampleLaw d T) :=
        lintegral_congr_ae ((L.rules ω).borelVersion_success_ae hω (by omega) ε)
  exact hd₁ d (by omega) T ε hε hε10 (KernelLearner.Tape d (M d) T)
    K.tapeLaw inferInstance K.asTape (K.asTape_admissible hK) hsuccess

end SubsphereCurrent

end

end OAI
