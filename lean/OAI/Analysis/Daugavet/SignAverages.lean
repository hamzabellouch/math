import OAI.Analysis.Daugavet.TailEstimates

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators

universe u_1 uIota

namespace ExactModuli.KW

section Signs
variable {ι : Type uIota} [Fintype ι]

def signSum (ε : ι → Bool) (b : ι → ℝ) : ℝ :=
  ∑ j, if ε j then b j else -b j

def signAverage (b : ι → ℝ) : ℝ := by
  classical
  exact (∑ ε : ι → Bool, |signSum ε b|) / Fintype.card (ι → Bool)

lemma norm_le_signAverage (b : ι → ℝ) : ‖b‖ ≤ signAverage b := by
  classical
  have hcard : 0 < (Fintype.card (ι → Bool) : ℝ) := by exact_mod_cast Fintype.card_pos
  have havg : 0 ≤ signAverage b := div_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) hcard.le
  apply (pi_norm_le_iff_of_nonneg havg).mpr
  intro j
  let flipFn := fun ε : ι → Bool => Function.update ε j (!(ε j))
  have hinvol : Function.Involutive flipFn := by
    intro ε
    funext i
    by_cases hij : i = j
    · subst i; simp [flipFn]
    · simp [flipFn, Function.update_of_ne hij]
  let flip : (ι → Bool) ≃ (ι → Bool) := ⟨flipFn, flipFn, hinvol, hinvol⟩
  have hdiff : ∀ ε, signSum ε b - signSum (flip ε) b = 2 * (if ε j then b j else -b j) := by
    intro ε
    unfold signSum
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single j]
    · change (if ε j then b j else -b j) - (if flipFn ε j then b j else -b j) = _
      cases h : ε j <;> simp [flipFn, h] <;> ring
    · intro i hi hij
      change (if ε i then b i else -b i) - (if flipFn ε i then b i else -b i) = 0
      simp [flipFn, Function.update_of_ne hij]
    · simp
  have hpair : ∀ ε, 2 * |b j| ≤ |signSum ε b| + |signSum (flip ε) b| := by
    intro ε
    have he : |signSum ε b - signSum (flip ε) b| = 2 * |b j| := by
      rw [hdiff ε, abs_mul]
      cases ε j <;> simp
    rw [← he]
    simpa only [Real.norm_eq_abs] using norm_sub_le (signSum ε b) (signSum (flip ε) b)
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun ε _ => hpair ε)
  rw [Finset.sum_add_distrib, flip.sum_comp (fun ε => |signSum ε b|)] at hs
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  change |b j| ≤ (∑ ε, |signSum ε b|) / (Fintype.card (ι → Bool) : ℝ)
  apply (le_div_iff₀ hcard).mpr
  nlinarith

variable {Ω : Type u_1} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
lemma signSum_identDistrib [IsProbabilityMeasure μ]
    (X : ι → Ω → ℝ) (hX : ∀ j, Measurable (X j))
    (hind : iIndepFun X μ) (hsym : ∀ j, IdentDistrib (X j) (fun ω => -X j ω) μ μ)
    (ε : ι → Bool) :
    IdentDistrib (fun ω => signSum ε (fun j => X j ω)) (fun ω => ∑ j, X j ω) μ μ := by
  let g := fun j (x : ℝ) => if ε j then x else -x
  have hg : ∀ j, Measurable (g j) := by
    intro j; dsimp [g]; cases ε j <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> fun_prop
  have hdist : ∀ j, IdentDistrib (g j ∘ X j) (X j) μ μ := by
    intro j
    cases h : ε j
    · simpa only [g, h, Bool.false_eq_true, ite_false, Function.comp_def] using (hsym j).symm
    · simpa only [g, h, ite_true, Function.comp_def] using IdentDistrib.refl (hX j).aemeasurable
  exact (IdentDistrib.pi hdist (hind.comp g hg) hind).comp
    (show Measurable (fun b : ι → ℝ => ∑ j, b j) by fun_prop)

lemma expected_max_le_expected_abs_sum (X : ι → Ω → ℝ) (hX : ∀ j, Measurable (X j))
    (hi : ∀ j, Integrable (X j) μ) (hind : iIndepFun X μ)
    (hsym : ∀ j, IdentDistrib (X j) (fun ω => -X j ω) μ μ) :
    ∫ ω, ‖fun j => X j ω‖ ∂μ ≤ ∫ ω, |∑ j, X j ω| ∂μ := by
  classical
  have hcard : 0 < (Fintype.card (ι → Bool) : ℝ) := by exact_mod_cast Fintype.card_pos
  have hsumI : Integrable (fun ω => ∑ j, X j ω) μ := integrable_finsetSum _ (fun j _ => hi j)
  have hsignI : ∀ ε : ι → Bool, Integrable (fun ω => |signSum ε (fun j => X j ω)|) μ := by
    intro ε
    exact ((signSum_identDistrib X hX hind hsym ε).integrable_iff.mpr hsumI).abs
  have hmean : (∫ ω, signAverage (fun j => X j ω) ∂μ) = ∫ ω, |∑ j, X j ω| ∂μ := by
    unfold signAverage
    rw [integral_div, integral_finsetSum _ (fun ε _ => hsignI ε)]
    have heq : ∀ ε : ι → Bool, (∫ ω, |signSum ε (fun j => X j ω)| ∂μ) =
        ∫ ω, |∑ j, X j ω| ∂μ := by
      intro ε
      simpa only [Real.norm_eq_abs] using (signSum_identDistrib X hX hind hsym ε).norm.integral_eq
    simp_rw [heq]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  rw [← hmean]
  exact integral_mono (integrable_pi_iff.mpr hi).norm
    ((integrable_finsetSum _ (fun ε _ => hsignI ε)).div_const _)
    (fun ω => norm_le_signAverage (fun j => X j ω))

lemma one_sub_exp_neg_ge_half {v : ℝ} (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    v / 2 ≤ 1 - Real.exp (-v) := by
  rw [Real.exp_neg]
  have hb : 1 / Real.exp v ≤ 1 - v / 2 := by
    apply (div_le_iff₀ (Real.exp_pos v)).mpr
    have hm := mul_le_mul_of_nonneg_left (Real.add_one_le_exp v)
      (show 0 ≤ 1 - v / 2 by linarith)
    nlinarith
  rw [one_div] at hb
  linarith

lemma independent_max_tail_lower (X : ι → Ω → ℝ) (hX : ∀ j, Measurable (X j))
    (hind : iIndepFun X μ) {u : ℝ} (hu : 0 ≤ u) (b : ι → ℝ)
    (hb : ∀ j, 0 ≤ b j) (hb1 : ∑ j, b j ≤ 1)
    (htail : ∀ j, b j ≤ μ.real {ω | u < |X j ω|}) :
    (∑ j, b j) / 2 ≤ μ.real {ω | u < ‖fun j => X j ω‖} := by
  classical
  have hpi : μ.real {ω | ‖fun j => X j ω‖ ≤ u} =
      ∏ j, μ.real {ω | |X j ω| ≤ u} := by
    have h := hind.measure_inter_preimage_eq_mul Finset.univ
      (sets := fun _ => {x : ℝ | |x| ≤ u})
      (fun _ _ => measurableSet_le measurable_abs measurable_const)
    have hset : {ω | ‖fun j => X j ω‖ ≤ u} =
        ⋂ j ∈ (Finset.univ : Finset ι), X j ⁻¹' {x : ℝ | |x| ≤ u} := by
      ext ω
      simp only [Finset.mem_univ, iInter_true, mem_ofPred_eq, mem_iInter, mem_preimage]
      simpa only [Real.norm_eq_abs] using pi_norm_le_iff_of_nonneg (x := fun j => X j ω) hu
    rw [measureReal_def, hset, h, ENNReal.toReal_prod]
    rfl
  have hcomp : ∀ j, μ.real {ω | |X j ω| ≤ u} = 1 - μ.real {ω | u < |X j ω|} := by
    intro j
    have hset : {ω | |X j ω| ≤ u} = {ω | u < |X j ω|}ᶜ := by ext ω; simp
    rw [hset, measureReal_compl (measurableSet_lt measurable_const (hX j).abs)]
    simp
  have hallcomp : μ.real {ω | u < ‖fun j => X j ω‖} = 1 -
      μ.real {ω | ‖fun j => X j ω‖ ≤ u} := by
    have hset : {ω | u < ‖fun j => X j ω‖} = {ω | ‖fun j => X j ω‖ ≤ u}ᶜ := by ext ω; simp
    rw [hset, measureReal_compl (measurableSet_le
      (Measurable.of_eval hX).norm measurable_const)]
    simp
  have hprod : (∏ j, μ.real {ω | |X j ω| ≤ u}) ≤ Real.exp (-(∑ j, b j)) := by
    calc
      _ ≤ ∏ j, Real.exp (-b j) := by
        apply Finset.prod_le_prod₀ (fun _ _ => measureReal_nonneg)
        intro j hj
        rw [hcomp]
        have he := Real.add_one_le_exp (-b j)
        have ht := htail j
        linarith
      _ = _ := by rw [← Real.exp_sum, Finset.sum_neg_distrib]
  rw [hallcomp, hpi]
  exact (one_sub_exp_neg_ge_half (Finset.sum_nonneg (fun j _ => hb j)) hb1).trans
    (sub_le_sub_left hprod 1)

lemma integrable_real_tail {X : Ω → ℝ} (hX : Integrable X μ) (hX0 : 0 ≤ᵐ[μ] X) :
    IntegrableOn (fun t : ℝ => μ.real {ω | t < X ω}) (Ioi 0) volume := by
  refine ⟨(measurable_real_tail X).aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun _ => measureReal_nonneg))).mpr ?_⟩
  have heq : (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (μ.real {ω | t < X ω})) =
      ∫⁻ t in Ioi (0:ℝ), μ {ω | t < X ω} := by
    apply lintegral_congr
    intro t
    exact ENNReal.ofReal_toReal (measure_ne_top _ _)
  rw [heq, ← lintegral_eq_lintegral_meas_lt μ hX0 hX.aemeasurable]
  exact hX.lintegral_lt_top

lemma expectation_lower_from_power_tail {X : Ω → ℝ} (hX : Integrable X μ)
    (hX0 : 0 ≤ᵐ[μ] X) {p c d : ℝ} (hp : 1 < p) (hc : 0 ≤ c) (hd : 0 < d)
    (htail : ∀ t, d ≤ t → c * t ^ (-p) ≤ μ.real {ω | t < X ω}) :
    c * d ^ (1 - p) / (p - 1) ≤ ∫ ω, X ω ∂μ := by
  have hi := integrable_real_tail hX hX0
  have hsub : Ioi d ⊆ Ioi (0:ℝ) := Ioi_subset_Ioi hd.le
  have hinonneg : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), 0 ≤ μ.real {ω | t < X ω} :=
    ae_of_all _ (fun _ => measureReal_nonneg)
  rw [hX.integral_eq_integral_meas_lt hX0]
  calc
    _ = ∫ t in Ioi d, c * t ^ (-p) := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hd]
      have he : -p + 1 = 1 - p := by ring
      rw [he]
      field_simp [show p - 1 ≠ 0 by linarith, show 1 - p ≠ 0 by linarith]
      ring
    _ ≤ ∫ t in Ioi d, μ.real {ω | t < X ω} := by
      apply integral_mono_of_nonneg
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact mul_nonneg hc (Real.rpow_nonneg (hd.trans ht).le _)
      · exact hi.mono_set hsub
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact htail t ht.le
    _ ≤ _ := setIntegral_mono_set hi hinonneg (ae_of_all _ (fun t ht => hsub ht))

end Signs

end ExactModuli.KW

end

end OAI
