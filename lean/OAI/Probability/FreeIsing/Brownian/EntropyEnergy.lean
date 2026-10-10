import OAI.Probability.FreeIsing.Brownian.DriftMoments
import OAI.Probability.FreeIsing.Energy.FiniteIsingFieldEnergy
import OAI.Probability.FreeIsing.Stochastic.FiniteIsingBrownianEnergy
import OAI.Probability.FreeIsing.Trees.GibbsField

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace Problem367

local instance finiteIsingBrownianEntropyNonemptySpin : Nonempty IsingSpin := ⟨.neg⟩

def finiteIsingBrownianEntropy {d : ℕ} {Ω : Type*}
    (beta : ℝ) (D : Finset (TreeVertex d)) (v : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (t : ℝ)
    (p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) : ℝ :=
  FinitePosterior.fieldEntropy (finiteIsingEnergy beta D)
    (fun eta u => spinSign (eta u)) (fun eta => spinSign (eta v))
    (finiteIsingBrownianObservation B D t p)

def finiteIsingBrownianNormalizedCovariance {d : ℕ} {Ω : Type*}
    (beta : ℝ) (D : Finset (TreeVertex d)) (v u : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (t : ℝ)
    (p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) : ℝ :=
  FinitePosterior.normalizedFieldCovariance (finiteIsingEnergy beta D)
    (fun eta w => spinSign (eta w)) (fun eta => spinSign (eta v))
    (finiteIsingBrownianObservation B D t p) u

theorem finiteIsingBrownianEntropy_nonneg {d : ℕ} {Ω : Type*}
    (beta : ℝ) (D : Finset (TreeVertex d)) (v : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (t : ℝ)
    (p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) :
    0 ≤ finiteIsingBrownianEntropy beta D v B t p := by
  exact FinitePosterior.fieldEntropy_nonneg _ _ _ _
    (fun eta => by cases eta v <;> simp [spinSign])
    ⟨fun _ => .neg, rfl⟩ ⟨fun _ => .pos, rfl⟩

theorem finiteIsingBrownianEntropy_le_noise {d : ℕ} {Ω : Type*}
    {beta : ℝ} (hbeta : 0 ≤ beta) (D : Finset (TreeVertex d)) (v : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (t : ℝ≥0)
    (p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) :
    finiteIsingBrownianEntropy beta D v B t p ≤
      2 * ((d : ℝ) * beta + (t : ℝ) + |B v t (p.2 v)|) := by
  let y := finiteIsingBrownianObservation B D t p
  have he := FinitePosterior.fieldEntropy_le_abs_field (finiteIsingEnergy beta D)
    (fun (eta : D → IsingSpin) w => spinSign (eta w)) (fun eta => spinSign (eta v)) y
    (fun eta => by cases eta v <;> simp [spinSign])
    ⟨fun _ => .neg, rfl⟩ ⟨fun _ => .pos, rfl⟩
  have hb := finite_tree_gibbs_field_uniform_bound D hbeta y v
  have ho : |y v| ≤ (t : ℝ) + |B v t (p.2 v)| := by
    change |(t : ℝ) * spinSign (p.1 v) + B v (Real.toNNReal (t : ℝ)) (p.2 v)| ≤ _
    rw [Real.toNNReal_coe]
    calc
      _ ≤ |(t : ℝ) * spinSign (p.1 v)| + |B v t (p.2 v)| := abs_add_le _ _
      _ = _ := by cases p.1 v <;> simp [spinSign, abs_of_nonneg t.coe_nonneg]
  have hfield : |FinitePosterior.fieldField (finiteIsingEnergy beta D)
      (fun (eta : D → IsingSpin) w => spinSign (eta w)) (fun eta => spinSign (eta v)) y| ≤
      (d : ℝ) * beta + (t : ℝ) + |B v t (p.2 v)| := by
    have htri := abs_sub_le (FinitePosterior.fieldField (finiteIsingEnergy beta D)
      (fun (eta : D → IsingSpin) w => spinSign (eta w)) (fun eta => spinSign (eta v)) y)
      (y v) 0
    simp only [sub_zero] at htri
    change |FinitePosterior.fieldField (finiteIsingEnergy beta D)
      (fun (eta : D → IsingSpin) w => spinSign (eta w))
      (fun eta => spinSign (eta v)) y - y v| ≤ (d : ℝ) * beta at hb
    linarith
  exact he.trans (mul_le_mul_of_nonneg_left hfield (by norm_num))

private theorem integral_abs_gaussian_le_sqrt
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} {t : ℝ≥0} (hX : HasLaw X (gaussianReal 0 t) P) :
    (∫ ω, |X ω| ∂P) ≤ Real.sqrt (t : ℝ) := by
  have hX2 : Integrable (fun ω => X ω ^ 2) P := by
    simpa only [sq_abs] using integrable_abs_pow_of_gaussianLaw hX 2
  have htrans := hX.integral_comp (f := fun x : ℝ => x ^ 2) (by fun_prop)
  have hvar := variance_fun_id_gaussianReal (μ := 0) (v := t)
  rw [variance_of_integral_eq_zero (μ := gaussianReal 0 t) (X := fun x : ℝ => x)
    (by fun_prop) (by simp)] at hvar
  have hsq : (∫ ω, X ω ^ 2 ∂P) = (t : ℝ) := htrans.trans hvar
  exact (integral_abs_le_sqrt_integral_sq hX.aemeasurable hX2).trans_eq
    (congrArg Real.sqrt hsq)

theorem finiteIsingBrownianEntropy_moment
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {beta : ℝ} (hbeta : 0 ≤ beta)
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (D : Finset (TreeVertex d)) (v : D) (t : ℝ≥0) :
    Integrable (finiteIsingBrownianEntropy beta D v B t) (μ.prod (Measure.infinitePi ν)) ∧
      (∫ p, finiteIsingBrownianEntropy beta D v B t p ∂μ.prod (Measure.infinitePi ν)) ≤
        2 * ((d : ℝ) * beta + (t : ℝ) + Real.sqrt (t : ℝ)) := by
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let ρ := μ.prod (Measure.infinitePi ν)
  let X : ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) → ℝ :=
    fun p => B v t (p.2 v)
  have hcoord := (measurePreserving_eval_infinitePi ν (v : TreeVertex d)).comp
    (measurePreserving_snd (μ := μ) (ν := Measure.infinitePi ν))
  have hX : HasLaw X (gaussianReal 0 t) ρ :=
    (hB v).hasLaw_eval t |>.comp ⟨hcoord.measurable.aemeasurable, hcoord.map_eq⟩
  have hXi : Integrable (fun p => |X p|) ρ := by
    simpa only [pow_one] using integrable_abs_pow_of_gaussianLaw hX 1
  have hY : Measurable (finiteIsingBrownianObservation B D (t : ℝ)) := by
    apply Measurable.of_eval
    intro w
    exact (((measurable_of_finite spinSign).comp
      ((measurable_pi_apply (w : TreeVertex d)).comp measurable_fst)).const_mul (t : ℝ)).add
      ((hmB w (t : ℝ).toNNReal).comp ((measurable_pi_apply (w : TreeVertex d)).comp measurable_snd))
  have hF : Measurable (finiteIsingBrownianEntropy beta D v B (t : ℝ)) :=
    (FinitePosterior.continuous_fieldEntropy (finiteIsingEnergy beta D)
      (fun (eta : D → IsingSpin) w => spinSign (eta w)) (fun eta => spinSign (eta v))
      (fun eta => by cases eta v <;> simp [spinSign])
      ⟨fun _ => .neg, rfl⟩ ⟨fun _ => .pos, rfl⟩).measurable.comp hY
  have hdom : Integrable (fun p => 2 * ((d : ℝ) * beta + (t : ℝ) + |X p|)) ρ :=
    ((integrable_const _).add hXi).const_mul 2
  have hFi : Integrable (finiteIsingBrownianEntropy beta D v B t) ρ := by
    apply hdom.mono' hF.aestronglyMeasurable
    exact Eventually.of_forall fun p => by
      rw [Real.norm_of_nonneg (finiteIsingBrownianEntropy_nonneg beta D v B t p)]
      exact finiteIsingBrownianEntropy_le_noise hbeta D v B t p
  refine ⟨hFi, ?_⟩
  calc
    _ ≤ ∫ p, 2 * ((d : ℝ) * beta + (t : ℝ) + |X p|) ∂ρ :=
      integral_mono hFi hdom (finiteIsingBrownianEntropy_le_noise hbeta D v B t)
    _ = 2 * ((d : ℝ) * beta + (t : ℝ) + ∫ p, |X p| ∂ρ) := by
      rw [integral_const_mul, integral_add (integrable_const _) hXi]
      simp [ρ]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (integral_abs_gaussian_le_sqrt hX)) (by norm_num)

theorem HasFreeIsingLaw.integral_finiteIsingBrownianNormalizedEnergy_le
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (v : D)
    {T : ℝ} (hT : 0 ≤ T) :
    let ρ := μ.prod (Measure.infinitePi ν)
    let E : ℝ → ℝ := fun t => ∫ p,
      ∑ u : D, finiteIsingBrownianNormalizedCovariance beta D v u B t p ^ 2 ∂ρ
    IntervalIntegrable E volume 0 T ∧
      (∫ t in 0..T, E t) ≤ (∫ p, finiteIsingBrownianEntropy beta D v B T p ∂ρ) ∧
      0 ≤ (∫ t in 0..T, E t) ∧
      (∫ t in 0..T, E t) ≤ 2 * ((d : ℝ) * beta + T + Real.sqrt T) := by
  classical
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let π := μ.map D.restrict
  let : IsProbabilityMeasure π :=
    (Measure.isProbabilityMeasure_map_iff D.measurable_restrict.aemeasurable).mpr inferInstance
  let spin : (D → IsingSpin) → D → ℝ := fun eta u => spinSign (eta u)
  let q : (D → IsingSpin) → ℝ := fun eta => spinSign (eta v)
  let F : (D → ℝ) → ℝ := FinitePosterior.fieldEntropy (finiteIsingEnergy beta D) spin q
  let C : (D → ℝ) → D → ℝ :=
    FinitePosterior.normalizedFieldCovariance (finiteIsingEnergy beta D) spin q
  let ρ := μ.prod (Measure.infinitePi ν)
  let ρG := π.prod (Measure.pi fun _ : D => gaussianReal 0 1)
  let EG : ℝ → ℝ := fun t => ∫ p,
    ∑ u : D, C (FinitePosterior.finiteStandardObservation spin t p) u ^ 2 ∂ρG
  let MG : ℝ → ℝ := fun t => ∫ p,
    F (FinitePosterior.finiteStandardObservation spin t p) ∂ρG
  let E : ℝ → ℝ := fun t => ∫ p,
    ∑ u : D, finiteIsingBrownianNormalizedCovariance beta D v u B t p ^ 2 ∂ρ
  let M : ℝ → ℝ := fun t => ∫ p, finiteIsingBrownianEntropy beta D v B t p ∂ρ
  have hcoords (eta : D → IsingSpin) (u : D) : spin eta u = -1 ∨ spin eta u = 1 := by
    dsimp only [spin]
    cases eta u <;> simp [spinSign]
  have hneg : ∃ eta, q eta = -1 := ⟨fun _ => .neg, rfl⟩
  have hpos : ∃ eta, q eta = 1 := ⟨fun _ => .pos, rfl⟩
  have hfm : Measurable F :=
    (FinitePosterior.continuous_fieldEntropy _ _ _ (fun eta => hcoords eta v) hneg hpos).measurable
  have hcm : Measurable (fun y => ∑ u : D, C y u ^ 2) :=
    (FinitePosterior.continuous_normalizedRowEnergy _ _ _ (fun eta => hcoords eta v) hneg hpos).measurable
  have hE (t : ℝ) (ht : 0 ≤ t) : E t = EG t := by
    have h := integral_finiteIsingBrownian_observation_eq_standard μ ν hB hmB D
      t.toNNReal (fun y => ∑ u : D, C y u ^ 2) hcm
    unfold E EG finiteIsingBrownianNormalizedCovariance finiteIsingBrownianObservation
    simpa only [C, spin, q, ρ, ρG, π, Real.coe_toNNReal t ht] using h
  have hM (t : ℝ) (ht : 0 ≤ t) : M t = MG t := by
    have h := integral_finiteIsingBrownian_observation_eq_standard μ ν hB hmB D
      t.toNNReal F hfm
    unfold M MG finiteIsingBrownianEntropy finiteIsingBrownianObservation
    simpa only [F, spin, q, ρ, ρG, π, Real.coe_toNNReal t ht] using h
  have hstd := FinitePosterior.integral_finiteStandardNormalizedEnergy_le π
    (finiteIsingEnergy beta D) (hμ.restrict_real_eq_normalized_exp D hD)
    spin q (fun eta => hcoords eta v) hneg hpos hcoords hT
  change IntervalIntegrable EG volume 0 T ∧
    (∫ t in 0..T, EG t) ≤ MG T - F 0 ∧ 0 ≤ (∫ t in 0..T, EG t) at hstd
  have hzero : F 0 = 0 := finiteIsingEntropy_zero beta D v
  have hEq : EqOn EG E (uIcc 0 T) := by
    intro t ht
    exact (hE t (by simpa only [min_eq_left hT] using ht.1)).symm
  have hInt : (∫ t in 0..T, EG t) = ∫ t in 0..T, E t :=
    intervalIntegral.integral_congr hEq
  have hle : (∫ t in 0..T, E t) ≤ M T := by
    simpa only [hzero, sub_zero, hInt, ← hM T hT] using hstd.2.1
  have hterminal : M T ≤ 2 * ((d : ℝ) * beta + T + Real.sqrt T) := by
    have h := (finiteIsingBrownianEntropy_moment hbeta μ ν hB hmB D v T.toNNReal).2
    simpa only [M, ρ, Real.coe_toNNReal T hT] using h
  change IntervalIntegrable E volume 0 T ∧ (∫ t in 0..T, E t) ≤ M T ∧
    0 ≤ (∫ t in 0..T, E t) ∧ (∫ t in 0..T, E t) ≤ _
  exact ⟨hstd.1.congr (fun t ht => hEq (uIoc_subset_uIcc ht)), hle,
    by simpa only [hInt] using hstd.2.2, hle.trans hterminal⟩

theorem HasFreeIsingLaw.lintegral_finiteIsingBrownianNormalizedEnergy_le
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (v : D)
    {T : ℝ} (hT : 0 ≤ T) :
    (∫⁻ t in Ioc 0 T, ∫⁻ p,
      ENNReal.ofReal (∑ u : D, finiteIsingBrownianNormalizedCovariance beta D v u B t p ^ 2)
      ∂μ.prod (Measure.infinitePi ν)) ≤
      ENNReal.ofReal (2 * ((d : ℝ) * beta + T + Real.sqrt T)) := by
  classical
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let ρ := μ.prod (Measure.infinitePi ν)
  let R := fun t p => ∑ u : D, finiteIsingBrownianNormalizedCovariance beta D v u B t p ^ 2
  let E : ℝ → ℝ := fun t => ∫ p, R t p ∂ρ
  have hRpos (t : ℝ) (p) : 0 ≤ R t p := Finset.sum_nonneg fun u _ => sq_nonneg _
  have hRI (t : ℝ) : Integrable (R t) ρ := by
    have hY : Measurable (finiteIsingBrownianObservation B D t) := by
      apply Measurable.of_eval
      intro w
      exact (((measurable_of_finite spinSign).comp
        ((measurable_pi_apply (w : TreeVertex d)).comp measurable_fst)).const_mul t).add
        ((hmB w t.toNNReal).comp ((measurable_pi_apply (w : TreeVertex d)).comp measurable_snd))
    have hs (eta : D → IsingSpin) : spinSign (eta v) = -1 ∨ spinSign (eta v) = 1 := by
      cases eta v <;> simp [spinSign]
    have hn : ∃ eta : D → IsingSpin, spinSign (eta v) = -1 := ⟨fun _ => .neg, rfl⟩
    have hp : ∃ eta : D → IsingSpin, spinSign (eta v) = 1 := ⟨fun _ => .pos, rfl⟩
    apply Integrable.of_bound
      ((FinitePosterior.continuous_normalizedRowEnergy (finiteIsingEnergy beta D)
        (fun (eta : D → IsingSpin) w => spinSign (eta w)) (fun eta => spinSign (eta v))
        hs hn hp).measurable.comp hY).aestronglyMeasurable (Fintype.card D)
    exact Eventually.of_forall fun p => by
      simpa only [Real.norm_eq_abs, Function.comp_def] using
        FinitePosterior.abs_normalizedRowEnergy_le_card (finiteIsingEnergy beta D)
          (fun (eta : D → IsingSpin) w => spinSign (eta w)) (fun eta => spinSign (eta v))
          (finiteIsingBrownianObservation B D t p) hs hn hp
          (fun eta w => by cases eta w <;> norm_num [spinSign])
  have hinner (t : ℝ) : (∫⁻ p, ENNReal.ofReal (R t p) ∂ρ) = ENNReal.ofReal (E t) :=
    (ofReal_integral_eq_lintegral_ofReal (hRI t) (Eventually.of_forall (hRpos t))).symm
  have hbound := hμ.integral_finiteIsingBrownianNormalizedEnergy_le hbeta ν hB hmB D hD v hT
  have hEI : Integrable E (volume.restrict (Ioc 0 T)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp hbound.1
  change (∫⁻ t in Ioc 0 T, ∫⁻ p, ENNReal.ofReal (R t p) ∂ρ) ≤ _
  simp_rw [hinner]
  rw [← ofReal_integral_eq_lintegral_ofReal hEI
    (Eventually.of_forall fun t => integral_nonneg (hRpos t))]
  rw [← intervalIntegral.integral_of_le hT]
  exact ENNReal.ofReal_le_ofReal hbound.2.2.2

end Problem367

end

end OAI
