import Mathlib
import OAI.Combinatorics.StripMass.ColumnGeometry

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped BigOperators ENNReal
open Set MeasureTheory
theorem integral_le_of_power_tail {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {f : α → ℝ}
    (hf : Integrable f μ) (hfn : 0 ≤ᵐ[μ] f) {b q : ℝ}
    (hb : 0 < b) (hq : 1 < q)
    (htail : ∀ t > b, μ.real {x | t < f x} ≤ b ^ q * t ^ (-q)) :
    (∫ x, f x ∂μ) ≤ q / (q - 1) * b := by
  let g : ℝ → ℝ := fun t => if t ≤ b then 1 else b ^ q * t ^ (-q)
  have hg₁ : IntegrableOn g (Ioc 0 b) := by
    apply (integrableOn_const (C := (1 : ℝ)) (by simp)).congr_fun _ measurableSet_Ioc
    intro t ht
    simp [g, ht.2]
  have hg₂ : IntegrableOn g (Ioi b) := by
    apply IntegrableOn.congr_fun ((integrableOn_Ioi_rpow_of_lt (by linarith : -q < -1) hb).const_mul (b ^ q))
      _ measurableSet_Ioi
    intro t ht
    simp [g, not_le.mpr (mem_Ioi.1 ht)]
  have hg : IntegrableOn g (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi hb.le, integrableOn_union]
    exact ⟨hg₁, hg₂⟩
  calc
    (∫ x, f x ∂μ) = ∫ t in Ioi 0, μ.real {x | t < f x} := hf.integral_eq_integral_meas_lt hfn
    _ ≤ ∫ t in Ioi 0, g t := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg) hg
      filter_upwards with t
      change μ.real {x | t < f x} ≤ g t
      by_cases ht : t ≤ b
      · simpa only [g, ite_eq_left ht] using (measureReal_le_one (μ := μ) (s := {x | t < f x}))
      · simpa only [g, ite_eq_right ht] using htail t (lt_of_not_ge ht)
    _ = (∫ t in Ioc 0 b, g t) + ∫ t in Ioi b, g t := by
      rw [← Ioc_union_Ioi_eq_Ioi hb.le]
      exact setIntegral_union (disjoint_left.mpr (fun t ht ht' => (not_lt_of_ge ht.2) ht'))
        measurableSet_Ioi hg₁ hg₂
    _ = b + b ^ q * (-b ^ (-q + 1) / (-q + 1)) := by
      congr 1
      · calc
          (∫ t in Ioc 0 b, g t) = ∫ t in Ioc 0 b, (1 : ℝ) := by
            apply setIntegral_congr_fun measurableSet_Ioc
            intro t ht
            simp [g, ht.2]
          _ = b := by simp [hb.le]
      · calc
          (∫ t in Ioi b, g t) = ∫ t in Ioi b, b ^ q * t ^ (-q) := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro t ht
            simp [g, not_le.mpr (mem_Ioi.1 ht)]
          _ = _ := by rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith : -q < -1) hb]
    _ = q / (q - 1) * b := by
      have he : b ^ q * b ^ (-q + 1) = b := by
        rw [← Real.rpow_add hb, show q + (-q + 1) = 1 by ring, Real.rpow_one]
      have hq' : q - 1 ≠ 0 := ne_of_gt (by linarith)
      rw [← mul_div_assoc, mul_neg, he, show -q + 1 = -(q - 1) by ring]
      field_simp
      ring

 

theorem integrable_of_power_tail {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {f : α → ℝ}
    (hf : AEMeasurable f μ) (hfn : 0 ≤ᵐ[μ] f) {b q : ℝ}
    (hb : 0 < b) (hq : 1 < q)
    (htail : ∀ t > b, μ.real {x | t < f x} ≤ b ^ q * t ^ (-q)) :
    Integrable f μ := by
  let g : ℝ → ℝ := fun t => if t ≤ b then 1 else b ^ q * t ^ (-q)
  have hg₁ : IntegrableOn g (Ioc 0 b) := by
    apply (integrableOn_const (C := (1 : ℝ)) (by simp)).congr_fun _ measurableSet_Ioc
    intro t ht
    simp [g, ht.2]
  have hg₂ : IntegrableOn g (Ioi b) := by
    apply IntegrableOn.congr_fun ((integrableOn_Ioi_rpow_of_lt
      (by linarith : -q < -1) hb).const_mul (b ^ q)) _ measurableSet_Ioi
    intro t ht
    simp [g, not_le.mpr (mem_Ioi.1 ht)]
  have hg : IntegrableOn g (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi hb.le, integrableOn_union]
    exact ⟨hg₁, hg₂⟩
  refine ⟨hf.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hfn).2 ?_⟩
  rw [lintegral_eq_lintegral_meas_lt μ hfn hf]
  apply lt_of_le_of_lt _ hg.lintegral_lt_top
  apply lintegral_mono
  intro t
  change μ {x | t < f x} ≤ ENNReal.ofReal (g t)
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ {x | t < f x})]
  apply ENNReal.ofReal_le_ofReal
  change μ.real {x | t < f x} ≤ g t
  by_cases ht : t ≤ b
  · simpa only [g, ite_eq_left ht] using (measureReal_le_one (μ := μ) (s := {x | t < f x}))
  · simpa only [g, ite_eq_right ht] using htail t (lt_of_not_ge ht)

 

theorem integral_inverse_le_of_small_tail {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {X : α → ℝ}
    (hX : ∀ᵐ x ∂μ, 0 < X x) {A D p : ℝ} (hA : 0 < A) (hp : 0 < p)
    (hpD : p < D) (hXm : AEMeasurable X μ)
    (htail : ∀ h > 0, μ.real {x | X x < h} ≤ (A * h) ^ D) :
    (∫ x, (X x) ^ (-p) ∂μ) ≤ D / (D - p) * A ^ p := by
  have hq : 1 < D / p := (lt_div_iff₀ hp).2 (by simpa using hpD)
  have hnn : 0 ≤ᵐ[μ] (fun x => (X x) ^ (-p)) := by
    filter_upwards [hX] with x hx
    exact (Real.rpow_pos_of_pos hx _).le
  have hb : ∀ t > A ^ p, μ.real {x | t < (X x) ^ (-p)} ≤
      (A ^ p) ^ (D / p) * t ^ (-(D / p)) := by
    intro t ht
    have htpos : 0 < t := (Real.rpow_pos_of_pos hA p).trans ht
    have htpow : 0 < t ^ (-1 / p) := Real.rpow_pos_of_pos htpos _
    have hsets : {x | t < (X x) ^ (-p)} =ᵐ[μ] {x | X x < t ^ (-1 / p)} := by
      filter_upwards [hX] with x hx
      have hh := Real.rpow_lt_rpow_iff_of_neg htpow hx (by linarith : -p < 0)
      rw [← Real.rpow_mul htpos.le, show (-1 / p) * -p = (1 : ℝ) by field_simp, Real.rpow_one] at hh
      exact propext hh
    have hmeas : μ.real {x | t < (X x) ^ (-p)} = μ.real {x | X x < t ^ (-1 / p)} := by
      exact congrArg ENNReal.toReal (measure_congr hsets)
    rw [hmeas]
    calc
      _ ≤ (A * t ^ (-1 / p)) ^ D := htail _ htpow
      _ = (A ^ p) ^ (D / p) * t ^ (-(D / p)) := by
        rw [Real.mul_rpow hA.le htpow.le, ← Real.rpow_mul htpos.le, ← Real.rpow_mul hA.le,
          show p * (D / p) = D by field_simp,
          show (-1 / p) * D = -(D / p) by ring]
  have hint : Integrable (fun x => (X x) ^ (-p)) μ :=
    integrable_of_power_tail (hXm.pow_const _) hnn (Real.rpow_pos_of_pos hA p) hq hb
  have h := integral_le_of_power_tail hint hnn (Real.rpow_pos_of_pos hA p) hq hb
  convert h using 1
  congr 1
  field_simp

end

noncomputable section
open scoped BigOperators
open Set MeasureTheory

 

theorem laguerre_inverse_bound_of_small_coordinate_bound {N : ℕ} {a A p : ℝ}
    (ha : 0 < a) (hA : 0 < A) (i : Fin N) (hp : 0 < p)
    (hpD : p < a * (i.val + 1) + (i.val + 1) * i.val / 2)
    (htail : ∀ h > 0, (laguerreLaw N a).real {r | r i < h} ≤
      (A * h) ^ (a * (i.val + 1) + (i.val + 1) * i.val / 2)) :
    laguerreExpectation N a (fun r => (r i) ^ (-p)) ≤
      (a * (i.val + 1) + (i.val + 1) * i.val / 2) /
        (a * (i.val + 1) + (i.val + 1) * i.val / 2 - p) * A ^ p := by
  let := laguerreLaw_isProbabilityMeasure N ha
  rw [← integral_laguerreLaw N ha]
  apply integral_inverse_le_of_small_tail ?_ hA hp hpD (measurable_pi_apply i).aemeasurable htail
  filter_upwards [ae_laguerreDomain N a] with r hr
  exact hr.2 i


 


theorem laguerreDomain_cons_iff {n : ℕ} (x : ℝ) (r : Fin n → ℝ) :
    Fin.cons x r ∈ laguerreDomain (n + 1) ↔
      0 < x ∧ r ∈ laguerreDomain n ∧ ∀ i, x < r i := by
  simp only [laguerreDomain, mem_ofPred_eq, Fin.strictMono_cons, Fin.forall_fin_succ,
    Fin.cons_zero, Fin.cons_succ]
  tauto

theorem pairProduct_cons {n : ℕ} (x : ℝ) (r : Fin n → ℝ) :
    (∏ i : Fin (n + 1), ∏ j ∈ Finset.Ioi i,
      pairKernel ((Fin.cons x r : Fin (n + 1) → ℝ) i) ((Fin.cons x r : Fin (n + 1) → ℝ) j)) =
      (∏ j, pairKernel x (r j)) * ∏ i, ∏ j ∈ Finset.Ioi i, pairKernel (r i) (r j) := by
  classical
  have he {m : ℕ} (s : Fin m → ℝ) :
      (∏ i : Fin m, ∏ j ∈ Finset.Ioi i, pairKernel (s i) (s j)) =
        ∏ i : Fin m, ∏ j : Fin m, if i < j then pairKernel (s i) (s j) else 1 := by
    apply Finset.prod_congr rfl
    intro i _
    rw [← Finset.prod_filter]
    congr 1
    ext j
    simp
  rw [he, he]
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
    ↓reduceIte, Fin.succ_pos, Fin.not_lt_zero, Fin.succ_lt_succ_iff, one_mul]

theorem laguerreDensity_cons {n : ℕ} (a x : ℝ) (r : Fin n → ℝ) :
    laguerreDensity (n + 1) a (Fin.cons x r) =
      laguerreWeight a x * laguerreDensity n a r * ∏ i, pairKernel x (r i) := by
  unfold laguerreDensity
  rw [pairProduct_cons]
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  ring

theorem laguerreDensity_succ_parameter {n : ℕ} (a : ℝ) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) :
    laguerreDensity n (a + 1) r = laguerreDensity n a r * ∏ i, r i := by
  have he : ∀ i, laguerreWeight (a + 1) (r i) = laguerreWeight a (r i) * r i := by
    intro i
    unfold laguerreWeight
    rw [show a + 1 - 1 = (a - 1) + 1 by ring, Real.rpow_add (hr i), Real.rpow_one]
    ring
  simp only [laguerreDensity, he, Finset.prod_mul_distrib]
  ring

theorem laguerreDensity_cons_le {n : ℕ} (a : ℝ) {x : ℝ} {r : Fin n → ℝ}
    (hr : Fin.cons x r ∈ laguerreDomain (n + 1)) :
    laguerreDensity (n + 1) a (Fin.cons x r) ≤
      x ^ (a - 1) * laguerreDensity n (a + 1) r := by
  obtain ⟨hx, hr, hxr⟩ := (laguerreDomain_cons_iff x r).1 hr
  rw [laguerreDensity_cons, laguerreDensity_succ_parameter a r hr.2]
  have hw : laguerreWeight a x ≤ x ^ (a - 1) := by
    apply mul_le_of_le_one_right (Real.rpow_pos_of_pos hx _).le
    exact Real.exp_le_one_iff.2 (by linarith)
  have hp : (∏ i, pairKernel x (r i)) ≤ ∏ i, r i := by
    apply Finset.prod_le_prod₀
    · intro i _
      exact pairKernel_nonneg hx.le (hr.2 i).le
    · intro i _
      exact pairKernel_le_right hx.le (hr.2 i) (hxr i).le
  calc
    _ ≤ (x ^ (a - 1) * laguerreDensity n a r) * ∏ i, r i :=
      mul_le_mul (mul_le_mul_of_nonneg_right hw (laguerreDensity_pos a hr).le) hp
        (Finset.prod_nonneg fun i _ => pairKernel_nonneg hx.le (hr.2 i).le)
        (mul_nonneg (Real.rpow_pos_of_pos hx _).le (laguerreDensity_pos a hr).le)
    _ = _ := by ring

 
def laguerreCut (n k : ℕ) (h : ℝ) : Set (Fin n → ℝ) :=
  laguerreDomain n ∩ {r | ∀ i, i.val < k → r i < h}

def laguerreCutIntegral (n : ℕ) (a : ℝ) (k : ℕ) (h : ℝ) : ℝ :=
  ∫ r in laguerreCut n k h, laguerreDensity n a r

theorem measurableSet_laguerreCut (n k : ℕ) (h : ℝ) :
    MeasurableSet (laguerreCut n k h) := by
  apply (isOpen_laguerreDomain n).measurableSet.inter
  simp only [ofPred_forall]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
    measurableSet_lt (measurable_pi_apply i) measurable_const

theorem laguerreCut_zero (n : ℕ) (h : ℝ) : laguerreCut n 0 h = laguerreDomain n := by
  ext r
  simp [laguerreCut]

theorem integral_fin_cons_eq (n : ℕ) (f : (Fin (n + 1) → ℝ) → ℝ) :
    (∫ r, f r) = ∫ p : ℝ × (Fin n → ℝ), f (Fin.cons p.1 p.2) := by
  symm
  simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero, Fin.zero_succAbove, Equiv.coe_fn_mk, cast_eq] using
    ((volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm).integral_comp' f

theorem integrable_fin_cons {n : ℕ} {f : (Fin (n + 1) → ℝ) → ℝ}
    (hf : Integrable f) : Integrable (fun p : ℝ × (Fin n → ℝ) => f (Fin.cons p.1 p.2)) := by
  simpa only [Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero, Fin.zero_succAbove, Equiv.coe_fn_mk, cast_eq] using
    ((volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm).integrable_comp_of_integrable hf

theorem integral_Ioo_rpow_sub_one {a h : ℝ} (ha : 0 < a) (hh : 0 < h) :
    (∫ x in Ioo 0 h, x ^ (a - 1)) = h ^ a / a := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hh.le,
    integral_rpow (Or.inl (by linarith : -1 < a - 1))]
  simp [Real.zero_rpow ha.ne']

theorem integrable_laguerreCut_indicator (n : ℕ) {a : ℝ} (ha : 0 < a) (k : ℕ) (h : ℝ) :
    Integrable ((laguerreCut n k h).indicator (laguerreDensity n a)) := by
  apply (integrable_indicator_iff (measurableSet_laguerreCut n k h)).2
  exact (integrableOn_laguerreDensity n ha).mono_set inter_subset_left

theorem laguerreCut_indicator_nonneg (n : ℕ) (a : ℝ) (k : ℕ) (h : ℝ) (r : Fin n → ℝ) :
    0 ≤ (laguerreCut n k h).indicator (laguerreDensity n a) r := by
  by_cases hr : r ∈ laguerreCut n k h
  · rw [Set.indicator_of_mem hr]
    exact (laguerreDensity_pos a hr.1).le
  · rw [Set.indicator_of_notMem hr]

 

theorem laguerreCutIntegral_succ_le (n k : ℕ) {a h : ℝ} (ha : 0 < a) (hh : 0 < h) :
    laguerreCutIntegral (n + 1) a (k + 1) h ≤
      (h ^ a / a) * laguerreCutIntegral n (a + 1) k h := by
  let f : ℝ → ℝ := (Ioo 0 h).indicator (fun x => x ^ (a - 1))
  let g : (Fin n → ℝ) → ℝ := (laguerreCut n k h).indicator (laguerreDensity n (a + 1))
  have hfi : Integrable f := (integrable_indicator_iff measurableSet_Ioo).2
    ((intervalIntegral.integrableOn_Ioo_rpow_iff hh).2 (by linarith))
  have hgi : Integrable g := integrable_laguerreCut_indicator n (by linarith) k h
  have hfn : ∀ x, 0 ≤ f x := by
    intro x
    by_cases hx : x ∈ Ioo 0 h
    · simpa only [f, indicator_of_mem hx] using (Real.rpow_pos_of_pos hx.1 (a - 1)).le
    · simp only [f, indicator_of_notMem hx, le_refl]
  have hn (p : ℝ × (Fin n → ℝ)) :
      (laguerreCut (n + 1) (k + 1) h).indicator (laguerreDensity (n + 1) a)
        (Fin.cons p.1 p.2) ≤ f p.1 * g p.2 := by
    by_cases hp : Fin.cons p.1 p.2 ∈ laguerreCut (n + 1) (k + 1) h
    · have hm := (laguerreDomain_cons_iff p.1 p.2).1 hp.1
      have hx : p.1 ∈ Ioo 0 h := ⟨hm.1, by simpa using hp.2 0 (by simp)⟩
      have hr : p.2 ∈ laguerreCut n k h := ⟨hm.2.1, fun i hi => by
        simpa using hp.2 i.succ (by simpa using hi)⟩
      simpa only [f, g, indicator_of_mem hp, indicator_of_mem hx, indicator_of_mem hr] using
        laguerreDensity_cons_le a hp.1
    · rw [indicator_of_notMem hp]
      exact mul_nonneg (hfn _) (laguerreCut_indicator_nonneg n (a + 1) k h _)
  calc
    laguerreCutIntegral (n + 1) a (k + 1) h =
        ∫ p : ℝ × (Fin n → ℝ), (laguerreCut (n + 1) (k + 1) h).indicator
          (laguerreDensity (n + 1) a) (Fin.cons p.1 p.2) := by
      rw [laguerreCutIntegral, ← integral_indicator (measurableSet_laguerreCut _ _ _), integral_fin_cons_eq]
    _ ≤ ∫ p : ℝ × (Fin n → ℝ), f p.1 * g p.2 :=
      integral_mono (integrable_fin_cons (integrable_laguerreCut_indicator _ ha _ _))
        (hfi.mul_prod hgi) hn
    _ = (∫ x, f x) * ∫ r, g r := integral_prod_mul f g
    _ = (h ^ a / a) * laguerreCutIntegral n (a + 1) k h := by
      simp only [f, g, integral_indicator measurableSet_Ioo,
        integral_Ioo_rpow_sub_one ha hh, integral_indicator (measurableSet_laguerreCut n k h),
        laguerreCutIntegral]

 
theorem laguerreCutIntegral_le_product (n k : ℕ) {a h : ℝ}
    (ha : 0 < a) (hh : 0 < h) :
    laguerreCutIntegral (n + k) a k h ≤
      (∏ i : Fin k, h ^ (a + i.val) / (a + i.val)) * laguerreNormalizer n (a + k) := by
  induction k generalizing a with
  | zero => simp [laguerreCutIntegral, laguerreCut_zero, laguerreNormalizer]
  | succ k ih =>
    calc
      _ ≤ (h ^ a / a) * laguerreCutIntegral (n + k) (a + 1) k h :=
        laguerreCutIntegral_succ_le (n + k) k ha hh
      _ ≤ (h ^ a / a) * ((∏ i : Fin k, h ^ (a + 1 + i.val) / (a + 1 + i.val)) *
          laguerreNormalizer n (a + 1 + k)) :=
        mul_le_mul_of_nonneg_left (ih (by linarith)) (by positivity)
      _ = _ := by
        rw [Fin.prod_univ_succ]
        simp only [Fin.val_zero, Nat.cast_zero, add_zero, Fin.val_succ, Nat.cast_add, Nat.cast_one]
        simp_rw [show ∀ i : Fin k, a + 1 + i.val = a + (i.val + 1) by intro i; ring]
        rw [show a + 1 + (k : ℝ) = a + (k + 1) by ring]
        ring

 
def laguerreDimension (a : ℝ) (k : ℕ) : ℝ := a * k + (k : ℝ) * (k - 1) / 2

theorem laguerreDimension_succ (a : ℝ) (k : ℕ) :
    laguerreDimension a (k + 1) = a + laguerreDimension (a + 1) k := by
  simp only [laguerreDimension, Nat.cast_add, Nat.cast_one]
  ring

theorem product_coordinate_power_quotient (k : ℕ) {h : ℝ} (hh : 0 < h) (a : ℝ) :
    (∏ i : Fin k, h ^ (a + i.val) / (a + i.val)) =
      h ^ (laguerreDimension a k) / ∏ i : Fin k, (a + i.val) := by
  induction k generalizing a with
  | zero => simp [laguerreDimension]
  | succ k ih =>
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
    simp only [Fin.val_zero, Nat.cast_zero, add_zero, Fin.val_succ, Nat.cast_add, Nat.cast_one]
    simp_rw [show ∀ i : Fin k, a + (i.val + 1) = a + 1 + i.val by intro i; ring]
    rw [ih (a + 1), ← mul_div_mul_comm, ← Real.rpow_add hh, laguerreDimension_succ]

theorem laguerreCutIntegral_le_normalizer_ratio (n k : ℕ) {a h : ℝ}
    (ha : 0 < a) (hh : 0 < h) :
    laguerreCutIntegral (n + k) a k h ≤
      (h ^ laguerreDimension a k / ∏ i : Fin k, (a + i.val)) * laguerreNormalizer n (a + k) := by
  simpa only [product_coordinate_power_quotient k hh a] using
    laguerreCutIntegral_le_product n k ha hh

theorem laguerreCut_eq_coordinate_cut {n : ℕ} (i : Fin n) (h : ℝ) :
    laguerreCut n (i.val + 1) h = laguerreDomain n ∩ {r | r i < h} := by
  ext r
  constructor
  · intro hr
    exact ⟨hr.1, hr.2 i (by omega)⟩
  · rintro ⟨hr, hi⟩
    refine ⟨hr, fun j hj => ?_⟩
    exact lt_of_le_of_lt (hr.1.monotone (by change j.val ≤ i.val; omega)) hi

theorem laguerreLaw_small_coordinate_eq {n : ℕ} {a : ℝ} (ha : 0 < a)
    (i : Fin n) (h : ℝ) :
    (laguerreLaw n a).real {r | r i < h} =
      laguerreCutIntegral n a (i.val + 1) h / laguerreNormalizer n a := by
  have hm : MeasurableSet {r : Fin n → ℝ | r i < h} :=
    measurableSet_lt (measurable_pi_apply i) measurable_const
  rw [← integral_indicator_one hm, integral_laguerreLaw n ha]
  unfold laguerreExpectation laguerreCutIntegral
  simp_rw [← Set.indicator_mul_left, Pi.one_apply, one_mul]
  rw [setIntegral_indicator hm, laguerreCut_eq_coordinate_cut]

 

theorem laguerreLaw_small_coordinate_le_normalizer_ratio {N : ℕ} {a h : ℝ}
    (ha : 0 < a) (hh : 0 < h) (i : Fin N) :
    (laguerreLaw N a).real {r | r i < h} ≤
      h ^ laguerreDimension a (i.val + 1) /
        (∏ j : Fin (i.val + 1), (a + j.val)) *
      (laguerreNormalizer (N - (i.val + 1)) (a + (i.val + 1)) / laguerreNormalizer N a) := by
  rw [laguerreLaw_small_coordinate_eq ha i h]
  have H := laguerreCutIntegral_le_normalizer_ratio (N - (i.val + 1)) (i.val + 1) ha hh
  have hN : N - (i.val + 1) + (i.val + 1) = N := by omega
  rw [hN] at H
  have hh' := div_le_div_of_nonneg_right H (laguerreNormalizer_pos N ha).le
  simpa only [Nat.cast_add, Nat.cast_one, mul_div_assoc] using hh'

 

def laguerreSmallCoefficient (N : ℕ) (a : ℝ) (k : ℕ) : ℝ :=
  laguerreNormalizer (N - k) (a + k) /
    (laguerreNormalizer N a * ∏ j : Fin k, (a + j.val))

theorem laguerreSmallCoefficient_pos (N k : ℕ) {a : ℝ} (ha : 0 < a) :
    0 < laguerreSmallCoefficient N a k := by
  apply div_pos (laguerreNormalizer_pos _ (by positivity))
  exact mul_pos (laguerreNormalizer_pos _ ha) (Finset.prod_pos fun j _ => by positivity)

theorem laguerreDimension_pos {a : ℝ} (ha : 0 < a) {k : ℕ} (hk : 1 ≤ k) :
    0 < laguerreDimension a k := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  unfold laguerreDimension
  have hp : 0 < a * (k : ℝ) := mul_pos ha (by linarith)
  have hq : 0 ≤ (k : ℝ) * (k - 1) := mul_nonneg (by positivity) (by linarith)
  linarith

end
end CriticalStrip

end OAI
