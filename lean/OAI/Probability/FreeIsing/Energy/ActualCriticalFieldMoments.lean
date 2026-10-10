import OAI.Probability.FreeIsing.Conditioning.ComponentConditionalRecursionInputs
import OAI.Probability.FreeIsing.Conditioning.SelectedFieldConditionedMoments
import OAI.Probability.FreeIsing.Energy.OptionResponseReindex
import OAI.Probability.FreeIsing.Energy.UniformResponseMoments
import OAI.Probability.FreeIsing.Estimates.ComponentFieldRecursion
import OAI.Probability.FreeIsing.Gaussian.ConditionalNoise
import OAI.Probability.FreeIsing.Gaussian.Moments

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

namespace Problem367

open PlantedSymmetry

theorem HasFreeIsingLaw.conditioned_own_gaussian_abs_moments
    {d : ℕ} {theta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw theta μ) (t : ℝ≥0) (ht : 0 < t)
    (ht1 : (t : ℝ) ≤ 1) (r : TreeVertex d) (p : ℕ) :
    Integrable (fun q => |observation t q r| ^ p)
      ((μ.prod (gaussianNoiseLaw (TreeVertex d) t))[|{q | q.1 r = .pos}]) ∧
    (∫ q, |observation t q r| ^ p
      ∂((μ.prod (gaussianNoiseLaw (TreeVertex d) t))[|{q | q.1 r = .pos}])) ≤
      Real.exp (2 * (p : ℝ) ^ 2) * (t : ℝ) ^ ((p : ℝ) / 4) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let P := μ.prod (gaussianNoiseLaw (TreeVertex d) t)
  let ν := P[|{q | q.1 r = IsingSpin.pos}]
  have hmass : P {q | q.1 r = IsingSpin.pos} = (1 / 2 : ENNReal) :=
    hμ.planted_spin_event_mass (fun _ => gaussianReal 0 t) r .pos
  let : IsProbabilityMeasure ν := cond_isProbabilityMeasure (by rw [hmass]; norm_num)
  have hG := hμ.standard_gaussian_hasLaw_cond_spin t ht r r .pos
  have hEq : (fun q => |observation t q r| ^ p) =ᵐ[ν]
      fun q => |(t : ℝ) + Real.sqrt t * (q.2 r / Real.sqrt t)| ^ p := by
    filter_upwards [hμ.own_gaussian_observation_cond_pos t ht r] with q hq
    rw [hq]
  have hInt := integrable_gaussian_observation_abs_pow_of_hasLaw hG t.coe_nonneg ht1 p
  refine ⟨hInt.congr hEq.symm, ?_⟩
  change (∫ q, |observation t q r| ^ p ∂ν) ≤ _
  rw [integral_congr_ae hEq]
  rcases p with _ | p
  · simp
  · exact integral_gaussian_observation_abs_pow_le_of_hasLaw hG
      (show (0 : ℝ) < t from ht) ht1 (Nat.succ_pos p)

theorem exists_gaussianComponentField_critical_moment_tail
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} (hb : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * (Real.tanh beta) ^ 2 = 1) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (μ : Measure (TreeVertex d → IsingSpin)),
      HasFreeIsingLaw (Real.tanh beta) μ →
      ∀ (t : ℝ≥0), 0 < t → (t : ℝ) ≤ 1 → ∀ c : Fin d,
      (∀ p : ℕ, Integrable
        (fun q => |selectedGaussianField μ t (componentIndexVertex (c := c))
          (RootedBroadcast.branchRoot c) q| ^ p)
        (μ.prod (gaussianNoiseLaw (TreeVertex d) t))) ∧
      (∀ p : ℕ, (∫ q,
        |selectedGaussianField μ t (componentIndexVertex (c := c))
          (RootedBroadcast.branchRoot c) q| ^ p
        ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤
        Real.exp (K * (p : ℝ) ^ 2) * (t : ℝ) ^ ((p : ℝ) / 4)) ∧
      (32 * K ≤ Real.log (1 / (t : ℝ)) →
        (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
          {q | (t : ℝ) ^ (1 / 8 : ℝ) <
            |selectedGaussianField μ t (componentIndexVertex (c := c))
              (RootedBroadcast.branchRoot c) q|} ≤
          ENNReal.ofReal (Real.exp (-(Real.log (1 / (t : ℝ)) ^ 2) / (512 * K)))) := by
  classical
  have h0 := tanh_nonneg_of_beta_nonneg hb
  have h1 := Real.tanh_lt_one beta
  have hK0 : 0 < criticalComponentBaseExponent d beta :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2)
      (criticalComponentBaseExponent_ge_two d beta)
  obtain ⟨K, hKK0, hK, hUniform⟩ :=
    exists_measure_uniform_critical_response_moment_and_tail_bound
      (Ω := (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ))
      (Ξ := (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ))
      h0 h1 hcritical hK0
  refine ⟨K, hK, ?_⟩
  intro μ hμ t ht ht1 c
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let P := μ.prod (gaussianNoiseLaw (TreeVertex d) t)
  let r := RootedBroadcast.branchRoot c
  let ν := P[|{q | q.1 r = IsingSpin.pos}]
  let Y := selectedGaussianField μ t (componentIndexVertex (c := c)) r
  let F : IsingSpin → ℝ → ℝ := fun s z => (t : ℝ) * spinSign s + z
  let I := {a : Fin d // c ≠ a}
  have hcard : Fintype.card I = d - 1 := by
    dsimp [I]
    simp [Fintype.card_subtype_compl]
  let e : Fin (d - 1) ≃ I :=
    Fintype.equivOfCardEq (by simpa only [Fintype.card_fin] using hcard.symm)
  let Z := ownChildFinFamily e (componentOwnChildFields P F c)
  have hmass : P {q | q.1 r = IsingSpin.pos} = (1 / 2 : ENNReal) :=
    hμ.planted_spin_event_mass (fun _ => gaussianReal 0 t) r .pos
  let : IsProbabilityMeasure ν := cond_isProbabilityMeasure (by rw [hmass]; norm_num)
  have hF : Measurable (Function.uncurry F) :=
    ((PlantedInformation.measurable_spinSign.comp measurable_fst).const_mul _).add
      measurable_snd
  have hr : r ∈ Set.range (componentIndexVertex (c := c)) := by
    apply mem_range_componentIndexVertex.mpr
    exact ⟨[], by simp [r, RootedBroadcast.branchRoot]⟩
  have hInt (p : ℕ) : Integrable (fun q => |Y q| ^ p) P :=
    hμ.integrable_selectedGaussianField_abs_pow hb t _ r hr p
  have hz0 : Z 0 = fun q => observation t q r := by
    rfl
  have hzsucc (i : Fin (d - 1)) : Z i.succ =
      selectedGaussianField μ t (childComponentIndexVertex c (e i).1)
        (prefixFlip c (RootedBroadcast.branchRoot (e i).1)) := by
    dsimp only [Z]
    rw [ownChildFinFamily_succ]
    rfl
  have hZ : iIndepFun Z ν := by
    apply iIndepFun_ownChildFinFamily
    exact hμ.iIndepFun_component_fields_cond_spin (by linarith) h1.le
      (gaussianReal 0 t) hF c .pos
  have hmZ : ∀ i, Measurable (Z i) :=
    measurable_ownChildFinFamily e (measurable_componentOwnChildFields P hF c)
  have hOwn (p : ℕ) := hμ.conditioned_own_gaussian_abs_moments t ht ht1 r p
  have hOwnInt (p : ℕ) : Integrable (fun q => |Z 0 q| ^ p) ν := by
    rw [hz0]
    exact (hOwn p).1
  have hOwnBound (p : ℕ) : (∫ q, |Z 0 q| ^ p ∂ν) ≤
      Real.exp (criticalComponentBaseExponent d beta * (p : ℝ) ^ 2) *
        (t : ℝ) ^ ((p : ℝ) / 4) := by
    rw [hz0]
    apply (hOwn p).2.trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg t.coe_nonneg _)
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
      (criticalComponentBaseExponent_ge_two d beta) (sq_nonneg _))
  have hCond : IdentDistrib (fun q => |Y q|) (fun q => |Y q|) ν P :=
    hμ.selectedGaussianField_abs_identDistrib_cond_spin t _ r r .pos
  have hChild (i : Fin (d - 1)) :
      IdentDistrib (fun q => |Z i.succ q|) (fun q => |Y q|) ν P := by
    rw [hzsucc]
    exact hμ.childComponentField_cond_abs_identDistrib t c (e i).1 r .pos
  have hEq : ∀ᵐ q ∂ν, Y q =
      ∑ i : Fin (d - 1 + 1),
        Fin.cases (Z 0 q) (fun j => cavityMessage (Real.tanh beta) (Z j.succ q)) i := by
    have hRec := (cond_absolutelyContinuous (μ := P)
      (s := {q | q.1 r = IsingSpin.pos})).ae_le
      (hμ.gaussian_component_field_recursion (by omega) hb t c)
    filter_upwards [hRec] with q hq
    exact hq.trans (sum_response_ownChildFinFamily e
      (componentOwnChildFields P F c) (cavityMessage (Real.tanh beta)) q).symm
  refine ⟨hInt, ?_⟩
  exact hUniform P ν inferInstance inferInstance (t : ℝ) (show (0 : ℝ) < t from ht)
    Y Y Z (cavityMessage (Real.tanh beta))
    (lipschitzWith_cavityMessage h0 h1.le).continuous.measurable
    (cavityMessage_abs_le_mul h0 h1.le) hInt hOwnInt hZ hmZ hCond hChild hEq
    hOwnBound (hμ.gaussianComponentField_critical_base_moments hd hb hcritical t ht1 c)

end Problem367

end

end OAI
