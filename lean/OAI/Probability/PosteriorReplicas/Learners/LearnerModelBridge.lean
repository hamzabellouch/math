import OAI.Probability.PosteriorReplicas.Regression.Conclusions

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace PosteriorRegression
namespace Learner

structure UniformAdmissible {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) : Prop where
  transition : ∀ᵐ ω ∂ρ, ∀ t a,
    AEMeasurable (fun obs => (L.transition t ω a obs).2) (observationReference d)
  uniform_experiment : AEMeasurable
    (fun z : UnitSphere d × (Ω × Samples d T) => L.estimate z.1 z.2.1 z.2.2)
    ((uniformSphere d).prod (ρ.prod (sampleLaw d T)))

lemma Admissible.uniformAdmissible {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    {L : Learner d M T Ω} {ρ : Measure Ω} [IsProbabilityMeasure ρ]
    (hL : L.Admissible ρ) : L.UniformAdmissible ρ := by
  have : SigmaFinite (observationReference d) := by unfold observationReference; infer_instance
  refine ⟨?_,hL.uniform_experiment⟩
  simp only [ae_all_iff]
  intro t a
  filter_upwards [ae_fiber_aemeasurable (hL.transition t a).prod_swap] with ω hω
  exact measurable_snd.comp_aemeasurable hω

lemma UniformAdmissible.angularSuccess_nullMeasurable {d M T : ℕ} {Ω : Type u}
    [MeasurableSpace Ω] {L : Learner d M T Ω} {ρ : Measure Ω}
    (hL : L.UniformAdmissible ρ) (ε : ℝ) :
    NullMeasurableSet {z : UnitSphere d × (Ω × Samples d T) |
      angularError z.1 (L.estimate z.1 z.2.1 z.2.2) ≤ ε}
      ((uniformSphere d).prod (ρ.prod (sampleLaw d T))) := by
  apply nullMeasurableSet_le _ aemeasurable_const
  exact Real.continuous_arccos.measurable.comp_aemeasurable
    ((measurable_subtype_coe.comp_aemeasurable hL.uniform_experiment).inner
      (measurable_subtype_coe.comp measurable_fst).aemeasurable)

lemma UniformAdmissible.linear_success_bound {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    {L : Learner d M T Ω} {ρ : Measure Ω} [IsProbabilityMeasure ρ]
    (hL : L.UniformAdmissible ρ) (hd : 0 < d) (hT : 4*T ≤ d) {ε : ℝ} (hε : ε ≤ 1/10) :
    L.uniformSuccess ρ ε ≤ ENNReal.ofReal (21/32 : ℝ) := by
  classical
  have : NeZero d := ⟨hd.ne'⟩
  have hmeas := ae_fiber_aemeasurable hL.uniform_experiment
  unfold uniformSuccess
  refine (prod_null_set_bound (hL.angularSuccess_nullMeasurable ε)
    (c := ENNReal.ofReal (21/32 : ℝ)) ?_).trans_eq (by simp)
  filter_upwards [hmeas] with z hz
  let U : Submodule ℝ (Vector d) := Submodule.span ℝ (Set.range z.2)
  have hdim : Module.finrank ℝ U ≤ T := by
    have h := finrank_span_le_card (R := ℝ) (Set.range z.2)
    apply h.trans
    rw [Set.toFinset_range]
    exact (Finset.card_image_le).trans_eq (by simp)
  have hU : 4 * Module.finrank ℝ U ≤ Module.finrank ℝ (Vector d) := by
    simpa only [Vector, finrank_euclideanSpace_fin] using (Nat.mul_le_mul_left 4 hdim).trans hT
  change sphereLaw {s : UnitSphere d | angularError s (L.estimate s z.1 z.2) ≤ ε} ≤ _
  apply sphere_reflection_success_bound U hU
  · exact nullMeasurableSet_le
      (Real.continuous_arccos.measurable.comp_aemeasurable
        ((measurable_subtype_coe.comp_aemeasurable hz).inner measurable_subtype_coe.aemeasurable))
      aemeasurable_const
  · intro s hs ht
    let t := sphereIsometry U.reflection s
    have he : L.estimate s z.1 z.2 = L.estimate t z.1 z.2 := by
      apply L.estimate_congr_labels
      intro i
      have hi : z.2 i ∈ U := Submodule.subset_span (Set.mem_range_self i)
      have he := U.reflection.inner_map_map (z.2 i) s.val
      rw [(Submodule.reflection_eq_self_iff (z.2 i)).2 hi] at he
      exact he.symm
    have hs' : dist s.val (L.estimate s z.1 z.2).val ≤ ε := by
      apply (chord_le_arccos s (L.estimate s z.1 z.2)).trans
      simpa only [Set.mem_ofPred_eq, angularError, real_inner_comm] using hs
    have ht' : dist t.val (L.estimate t z.1 z.2).val ≤ ε := by
      apply (chord_le_arccos t (L.estimate t z.1 z.2)).trans
      simpa only [Set.mem_ofPred_eq, angularError, real_inner_comm] using ht
    calc
      _ = dist s.val t.val := rfl
      _ ≤ dist s.val (L.estimate s z.1 z.2).val + dist (L.estimate s z.1 z.2).val t.val := dist_triangle _ _ _
      _ ≤ ε + ε := by rw [he, dist_comm (L.estimate t z.1 z.2).val t.val] at *; exact add_le_add hs' ht'
      _ ≤ 1/5 := by linarith

lemma UniformAdmissible.streaming_success_bound {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    {L : Learner d M T Ω} {ρ : Measure Ω} [IsProbabilityMeasure ρ]
    (hL : L.UniformAdmissible ρ) (hd : 3 ≤ d) {ε : ℝ} (hε : 0 < ε)
    {a q : ℕ} (ha : 2*a ≤ d-1) (hq : 2 ≤ q) (hqa : 2*q ≤ a) :
    L.uniformSuccess ρ ε ≤
      (T+1 : ℝ≥0∞) * (ENNReal.ofReal ((3 : ℝ)*4^d) * ENNReal.ofReal (ε^a)) *
        streamFactor (E := Vector d) (J := State M) q ^ (T/q+1) := by
  have : NeZero d := ⟨by omega⟩
  have hp := ((MeasurePreserving.id (uniformSphere d)).prod
      (Measure.measurePreserving_swap (μ := sampleLaw d T) (ν := ρ))).comp
    (measurePreserving_prodAssoc (uniformSphere d) (sampleLaw d T) ρ)
  let S := {z : UnitSphere d × (Ω × Samples d T) |
    angularError z.1 (L.estimate z.1 z.2.1 z.2.2) ≤ ε}
  have hS : NullMeasurableSet S ((uniformSphere d).prod (ρ.prod (sampleLaw d T))) :=
    hL.angularSuccess_nullMeasurable ε
  have he := hp.measure_preimage hS
  have hb := prod_null_set_bound (hS.preimage hp.quasiMeasurePreserving)
    (c := (T+1 : ℝ≥0∞) * (ENNReal.ofReal ((3 : ℝ)*4^d) * ENNReal.ofReal (ε^a)) *
      streamFactor (E := Vector d) (J := State M) q ^ (T/q+1))
    (by
      filter_upwards [hL.transition] with ω hω
      exact L.frozen_success_bound ω hd hω hε ha hq hqa)
  simpa only [he, measure_univ, mul_one, S, uniformSuccess] using hb

lemma UniformAdmissible.streaming_success_bound_real {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    {L : Learner d M T Ω} {ρ : Measure Ω} [IsProbabilityMeasure ρ]
    (hL : L.UniformAdmissible ρ) (hd : 3 ≤ d) {ε : ℝ} (hε : 0 < ε)
    {a q : ℕ} (ha : 2*a ≤ d-1) (hq : 2 ≤ q) (hqa : 2*q ≤ a)
    (hs : (2/3 : ℝ≥0∞) ≤ L.uniformSuccess ρ ε) :
    (2/3 : ℝ) ≤ ((T : ℝ)+1) * ((3 : ℝ)*4^d * ε^a) *
      ((32768 : ℝ)^d * ((2 : ℝ)^M)^(1/(q : ℝ)))^(T/q+1) := by
  have hb := hs.trans (hL.streaming_success_bound hd hε ha hq hqa)
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

def UniformSubquadraticMemory : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ M : ℕ → ℕ,
    Asymptotics.IsLittleO atTop (fun d => (M d : ℝ)) (fun d => (d : ℝ) ^ 2) →
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ T : ℕ, ∀ ε : ℝ,
    0 < ε → ε ≤ 1 / 10 →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (ρ : Measure Ω), IsProbabilityMeasure ρ →
    ∀ L : Learner d (M d) T Ω, L.UniformAdmissible ρ →
    (2 / 3 : ℝ≥0∞) ≤ L.uniformSuccess ρ ε →
    c * (d : ℝ) * Real.log (1 / ε) ≤ (T : ℝ)

lemma source_fixed_quadratic_memory {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    {A : ℝ} (hA : 0 < A) (hd : 32 ≤ d) (hM : (M:ℝ) ≤ A*(d:ℝ)^2)
    {ε : ℝ} (hε : 0<ε) (hε10 : ε≤1/10)
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] (L : Learner d M T Ω)
    (hL : L.UniformAdmissible ρ) (hs : (2/3 : ℝ≥0∞) ≤ L.uniformSuccess ρ ε) :
    (1 / (4*(400000+100*A))) * (d : ℝ) * Real.log (1/ε) ≤ (T : ℝ) := by
  have hT : d ≤ 4*T := by
    by_contra h
    have hb := hs.trans (hL.linear_success_bound (by omega) (by omega) hε10)
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
    (hL.streaming_success_bound_real (by omega) hε ha hq hqa hs)

theorem source_subquadratic_memory : UniformSubquadraticMemory.{u} := by
  refine ⟨1/(4*(400000+100*(1:ℝ))),by positivity,?_⟩
  intro M hM
  obtain ⟨d₂, hd₂⟩ := eventually_atTop.1 hM.eventuallyLE
  refine ⟨max 32 d₂, ?_⟩
  intro d hd T ε hε hε10 Ω _ ρ hρ L hL hs
  have : IsProbabilityMeasure ρ := hρ
  have hmem : (M d : ℝ) ≤ 1 * (d : ℝ)^2 := by
    have hm := hd₂ d (by omega)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (M d) : (0 : ℝ) ≤ M d),
      abs_of_nonneg (sq_nonneg (d : ℝ)), one_mul] using hm
  exact source_fixed_quadratic_memory (by norm_num) (by omega) hmem hε hε10 ρ L hL hs

end PosteriorRegression
end

end OAI
