import OAI.Geometry.Perimeter.Regularity.PerimeterAdmissiblePartitionPiece

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack

theorem smooth_layer_sum_bounds (N : ℕ) {a : ℝ} (ha : 0 ≤ a) (haN : a ≤ N) :
    a - 1 ≤ ∑ j ∈ Finset.range N, Real.smoothTransition (a - j) ∧
    (∑ j ∈ Finset.range N, Real.smoothTransition (a - j)) ≤ a + 1 := by
  induction N generalizing a with
  | zero => simp only [Nat.cast_zero] at haN; have : a = 0 := le_antisymm haN ha; simp [this]
  | succ N ih =>
    rw [Finset.sum_range_succ']
    by_cases ha1 : 1 ≤ a
    · have hrec := ih (a := a - 1) (by linarith) (by push_cast at haN; linarith)
      have he : (∑ j ∈ Finset.range N, Real.smoothTransition (a - (j + 1 : ℕ))) =
          ∑ j ∈ Finset.range N, Real.smoothTransition ((a - 1) - j) := by
        apply Finset.sum_congr rfl
        intro j hj
        congr 1
        push_cast
        ring
      rw [he, Nat.cast_zero, sub_zero, Real.smoothTransition.one_of_one_le ha1]
      constructor <;> linarith [hrec.1, hrec.2]
    · have ha1' : a ≤ 1 := le_of_not_ge ha1
      have hz : ∑ j ∈ Finset.range N, Real.smoothTransition (a - (j + 1 : ℕ)) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        apply Real.smoothTransition.zero_of_nonpos
        have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
        push_cast
        linarith
      rw [hz, zero_add, Nat.cast_zero, sub_zero]
      constructor
      · linarith [Real.smoothTransition.nonneg a]
      · linarith [Real.smoothTransition.le_one a]

theorem finite_level_count_le (N : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    (∑ j ∈ Finset.range N, if (j : ℝ) < a then (1 : ℝ) else 0) ≤ a + 1 := by
  classical
  induction N with
  | zero => simp; linarith
  | succ N ih =>
    rw [Finset.sum_range_succ]
    by_cases hN : (N : ℝ) < a
    · rw [ite_eq_left hN]
      have hsum : (∑ j ∈ Finset.range N, if (j : ℝ) < a then (1 : ℝ) else 0) ≤ N := by
        calc
          _ ≤ ∑ _j ∈ Finset.range N, (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro j hj
            split_ifs <;> norm_num
          _ = _ := by simp
      linarith
    · simpa [hN] using ih

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack

theorem abs_integral_divergence_le_bound_perimeter {n : ℕ} (E U : Set (Euc n))
    (hP : perimeter E U ≠ ⊤) {V : Euc n → Euc n}
    (hV : ContDiff ℝ ∞ V) (hc : HasCompactSupport V) (hs : tsupport V ⊆ U)
    {B : ℝ} (hB : 0 < B) (hb : ∀ x, ‖V x‖ ≤ B) :
    |∫ x in E, divergence V x| ≤ B * (perimeter E U).toReal := by
  let W : Euc n → Euc n := fun x ↦ B⁻¹ • V x
  have hW : PerimeterAdmissible U W := by
    have hsm : ContDiff ℝ ∞ (fun z : Euc n ↦ B⁻¹ • z) :=
      (contDiff_const (c := B⁻¹)).smul contDiff_id
    refine ⟨hsm.comp hV, hc.comp_left (g := fun z : Euc n ↦ B⁻¹ • z)
      (smul_zero _), ?_, ?_⟩
    · exact (tsupport_smul_subset_right (fun _ ↦ B⁻¹) V).trans hs
    · intro x
      simp only [W, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hB.le)]
      exact (mul_le_mul_of_nonneg_left (hb x) (inv_nonneg.mpr hB.le)).trans_eq
        (inv_mul_cancel₀ hB.ne')
  have hp := integral_divergence_le_perimeter_real E U hP hW
  have hn := integral_divergence_le_perimeter_real E U hP (perimeterAdmissible_neg hW)
  have hd : divergence W = fun x ↦ B⁻¹ * divergence V x := by
    funext x
    rw [divergence_smul (differentiable_const _) (hV.differentiable (by simp))]
    simp
  rw [divergence_neg (hW.1.differentiable (by simp))] at hn
  simp only [Pi.neg_apply] at hn
  rw [integral_neg] at hn
  rw [hd, integral_const_mul] at hp hn
  have hab : |B⁻¹ * ∫ x in E, divergence V x| ≤ (perimeter E U).toReal :=
    abs_le.mpr ⟨by linarith, hp⟩
  calc
    _ = B * |B⁻¹ * ∫ x in E, divergence V x| := by
      rw [abs_mul, abs_inv, abs_of_pos hB, ← mul_assoc, mul_inv_cancel₀ hB.ne', one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hab hB.le

theorem scalar_layer_admissible {n : ℕ} {U : Set (Euc n)}
    {Q : Euc n → Euc n} (hQ : PerimeterAdmissible U Q)
    {f : Euc n → ℝ} (hf : ContDiff ℝ ∞ f) {δ : ℝ} (hδ : 0 < δ) (j : ℕ) :
    PerimeterAdmissible (U ∩ {x | ((j : ℝ) - 1) * δ < f x})
      (fun x ↦ Real.smoothTransition (f x / δ - j) • Q x) := by
  let a : Euc n → ℝ := fun x ↦ Real.smoothTransition (f x / δ - j)
  have ha : ContDiff ℝ ∞ a :=
    Real.smoothTransition.contDiff.comp ((hf.div_const δ).sub contDiff_const)
  have hsa : tsupport a ⊆ {x | (j : ℝ) * δ ≤ f x} := by
    apply closure_minimal
    · intro x hx
      by_contra h
      have hlt : f x < (j : ℝ) * δ := lt_of_not_ge h
      have hd : f x / δ - j ≤ 0 := by
        have := (div_lt_iff₀ hδ).mpr hlt
        linarith
      exact hx (Real.smoothTransition.zero_of_nonpos hd)
    · exact isClosed_le continuous_const hf.continuous
  refine ⟨ha.smul hQ.1, hQ.2.1.smul_left (f := a), ?_, ?_⟩
  · intro x hx
    refine ⟨hQ.2.2.1 (tsupport_smul_subset_right _ _ hx), ?_⟩
    have h := hsa (tsupport_smul_subset_left _ _ hx)
    change (j : ℝ) * δ ≤ f x at h
    change ((j : ℝ) - 1) * δ < f x
    nlinarith
  · intro x
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact (mul_le_of_le_one_left (norm_nonneg _) (Real.smoothTransition.le_one _)).trans
      (hQ.2.2.2 x)

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack

theorem finite_level_integral_le {n : ℕ} (μ : Measure (Euc n)) [IsFiniteMeasure μ]
    {f : Euc n → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfi : Integrable f μ)
    {δ : ℝ} (hδ : 0 < δ) (N : ℕ) :
    δ * (∑ j ∈ Finset.range N, μ.real {x | ((j : ℝ) - 1) * δ < f x}) ≤
      (∫ x, f x ∂μ) + 2 * δ * μ.real univ := by
  classical
  let s : ℕ → Set (Euc n) := fun j ↦ {x | ((j : ℝ) - 1) * δ < f x}
  have hs : ∀ j, MeasurableSet (s j) := fun j ↦ measurableSet_lt measurable_const hf
  let g : ℕ → Euc n → ℝ := fun j ↦ (s j).indicator (fun _ ↦ 1)
  have hg : ∀ j, Integrable (g j) μ := fun j ↦ (integrable_const 1).indicator (hs j)
  have hpoint : ∀ x, δ * ∑ j ∈ Finset.range N, g j x ≤ f x + 2 * δ := by
    intro x
    have hcount := finite_level_count_le N (a := f x / δ + 1) (add_nonneg (div_nonneg (hf0 x) hδ.le) zero_le_one)
    have he : (∑ j ∈ Finset.range N, g j x) =
        ∑ j ∈ Finset.range N, if (j : ℝ) < f x / δ + 1 then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      have hc : ((j : ℝ) - 1) * δ < f x ↔ (j : ℝ) < f x / δ + 1 := by
        have heq : f x / δ * δ = f x := div_mul_cancel₀ _ hδ.ne'
        constructor <;> intro h <;> nlinarith
      simp only [g, Set.indicator_apply, s, Set.mem_ofPred_eq, hc]
    rw [he]
    have hh := mul_le_mul_of_nonneg_left hcount hδ.le
    have heq : δ * (f x / δ) = f x := mul_div_cancel₀ _ hδ.ne'
    nlinarith
  calc
    _ = ∫ x, δ * ∑ j ∈ Finset.range N, g j x ∂μ := by
      rw [integral_const_mul, integral_finsetSum _ (fun j _ ↦ hg j)]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      simp only [g, integral_indicator (hs j), integral_const, smul_eq_mul, mul_one,
        measureReal_restrict_apply_univ, s]
    _ ≤ ∫ x, (f x + 2 * δ) ∂μ := by
      exact integral_mono ((integrable_finsetSum _ (fun j _ ↦ hg j)).const_mul δ)
        (hfi.add (integrable_const _)) hpoint
    _ = _ := by rw [integral_add hfi (integrable_const _), integral_const]; simp [smul_eq_mul, mul_comm]

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack

theorem integral_divergence_scalar_le {n : ℕ} (E U : Set (Euc n))
    (hU : IsOpen U) (hP : perimeter E U ≠ ⊤)
    {Q : Euc n → Euc n} (hQ : PerimeterAdmissible U Q)
    {f : Euc n → ℝ} (hf : ContDiff ℝ ∞ f) (hf0 : ∀ x, 0 ≤ f x)
    {M : ℝ} (hfM : ∀ x, f x ≤ M) :
    (∫ x in E, divergence (fun y ↦ f y • Q y) x) ≤
      ∫ x in U, f x ∂perimeterMeasure E := by
  classical
  let μ := (perimeterMeasure E).restrict U
  have hμuniv : μ univ = perimeter E U := by
    rw [Measure.restrict_apply_univ, perimeterMeasure_open E hU]
  let : IsFiniteMeasure μ := ⟨by rw [hμuniv]; exact hP.lt_top⟩
  have hμr : μ.real univ = (perimeter E U).toReal := by rw [measureReal_def, hμuniv]
  have hfi : Integrable f μ := Integrable.of_bound hf.continuous.aestronglyMeasurable M
    (ae_of_all _ (fun x ↦ by rw [Real.norm_eq_abs, abs_of_nonneg (hf0 x)]; exact hfM x))
  let V : Euc n → Euc n := fun x ↦ f x • Q x
  have hVc : ContDiff ℝ ∞ V := hf.smul hQ.1
  have hVk : HasCompactSupport V := hQ.2.1.smul_left (f := f)
  have hVs : tsupport V ⊆ U := (tsupport_smul_subset_right _ _).trans hQ.2.2.1
  have hδbound : ∀ δ : ℝ, 0 < δ →
      (∫ x in E, divergence V x) ≤ (∫ x, f x ∂μ) + 3 * δ * μ.real univ := by
    intro δ hδ
    obtain ⟨N, hN⟩ := exists_nat_ge (M / δ)
    let s : ℕ → Set (Euc n) := fun j ↦ U ∩ {x | ((j : ℝ) - 1) * δ < f x}
    have hs : ∀ j, IsOpen (s j) := fun j ↦ hU.inter (isOpen_lt continuous_const hf.continuous)
    let W : ℕ → Euc n → Euc n := fun j x ↦ Real.smoothTransition (f x / δ - j) • Q x
    have hW : ∀ j, PerimeterAdmissible (s j) (W j) := scalar_layer_admissible hQ hf hδ
    let a : Euc n → ℝ := fun x ↦ δ * ∑ j ∈ Finset.range N, Real.smoothTransition (f x / δ - j)
    have hac : ContDiff ℝ ∞ a := contDiff_const.mul (ContDiff.sum (fun j _ ↦
      Real.smoothTransition.contDiff.comp ((hf.div_const δ).sub contDiff_const)))
    let A : Euc n → Euc n := fun x ↦ a x • Q x
    have hAc : ContDiff ℝ ∞ A := hac.smul hQ.1
    have hAk : HasCompactSupport A := hQ.2.1.smul_left (f := a)
    have hAs : tsupport A ⊆ U := (tsupport_smul_subset_right _ _).trans hQ.2.2.1
    have har : ∀ x, |f x - a x| ≤ δ := by
      intro x
      have hh := smooth_layer_sum_bounds N (a := f x / δ) (div_nonneg (hf0 x) hδ.le)
        ((div_le_div_of_nonneg_right (hfM x) hδ.le).trans hN)
      have h1 := mul_le_mul_of_nonneg_left hh.1 hδ.le
      have h2 := mul_le_mul_of_nonneg_left hh.2 hδ.le
      have heq : δ * (f x / δ) = f x := by field_simp
      dsimp [a]
      exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
    have hb : ∀ x, ‖(V - A) x‖ ≤ δ := by
      intro x
      change ‖f x • Q x - a x • Q x‖ ≤ δ
      rw [← sub_smul, norm_smul, Real.norm_eq_abs]
      exact (mul_le_mul (har x) (hQ.2.2.2 x) (norm_nonneg _) hδ.le).trans_eq (mul_one δ)
    have her := abs_integral_divergence_le_bound_perimeter E U hP
      (hVc.sub hAc) (hVk.sub hAk)
      ((tsupport_sub V A).trans (union_subset hVs hAs)) hδ hb
    change |∫ x in E, divergence (V - A) x| ≤ δ * (perimeter E U).toReal at her
    rw [divergence_sub (hVc.differentiable (by simp)) (hAc.differentiable (by simp))] at her
    simp only [Pi.sub_apply] at her
    rw [integral_sub (integrable_divergence hVc hVk).integrableOn
      (integrable_divergence hAc hAk).integrableOn] at her
    have hAid : A = fun x ↦ δ • (∑ j ∈ Finset.range N, W j) x := by
      funext x
      simp only [A, a, W, Finset.sum_apply, ← Finset.sum_smul, smul_smul]
    have hAdiv : divergence A = fun x ↦ δ * ∑ j ∈ Finset.range N, divergence (W j) x := by
      rw [hAid]
      funext x
      rw [divergence_smul (differentiable_const δ)
        (Differentiable.sum (fun j _ ↦ (hW j).1.differentiable (by simp)))]
      simp only [gradient_fun_const, inner_zero_left, add_zero]
      rw [divergence_finset_sum _ W (fun j _ ↦ (hW j).1.differentiable (by simp))]
      simp only [Finset.sum_apply]
    have hAint : (∫ x in E, divergence A x) =
        δ * ∑ j ∈ Finset.range N, ∫ x in E, divergence (W j) x := by
      rw [hAdiv, integral_const_mul, integral_finsetSum _
        (fun j _ ↦ (integrable_divergence (hW j).1 (hW j).2.1).integrableOn)]
    have hWbound : ∀ j, (∫ x in E, divergence (W j) x) ≤
        μ.real {x | ((j : ℝ) - 1) * δ < f x} := by
      intro j
      have hPs : perimeter E (s j) ≠ ⊤ := ne_top_of_le_ne_top hP
        (raw_perimeter_mono_region E inter_subset_left)
      have hd := integral_divergence_le_perimeter_real E (s j) hPs (hW j)
      convert hd using 1
      rw [measureReal_def, Measure.restrict_apply
        (measurableSet_lt measurable_const hf.continuous.measurable), inter_comm,
        perimeterMeasure_open E (hs j)]
    have hAupper : (∫ x in E, divergence A x) ≤ (∫ x, f x ∂μ) + 2 * δ * μ.real univ := by
      rw [hAint]
      exact (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ ↦ hWbound j)) hδ.le).trans
        (finite_level_integral_le μ hf.continuous.measurable hf0 hfi hδ N)
    rw [← hμr] at her
    have hh := (le_abs_self _).trans her
    linarith
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := ε / (3 * μ.real univ + 1)
  have hd : 0 < δ := by dsimp [δ]; positivity
  have hh := hδbound δ hd
  have hmul : δ * (3 * μ.real univ + 1) = ε := by
    dsimp [δ]
    exact div_mul_cancel₀ _ (by positivity)
  change (∫ x in E, divergence V x) ≤ (∫ x, f x ∂μ) + ε
  nlinarith

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack

theorem abs_integral_divergence_le_integral_norm {n : ℕ} (E U : Set (Euc n))
    (hU : IsOpen U) (hP : perimeter E U ≠ ⊤) {V : Euc n → Euc n}
    (hV : ContDiff ℝ ∞ V) (hc : HasCompactSupport V) (hs : tsupport V ⊆ U) :
    |∫ x in E, divergence V x| ≤ ∫ x in U, ‖V x‖ ∂perimeterMeasure E := by
  classical
  let μ := (perimeterMeasure E).restrict U
  let : IsFiniteMeasure μ := ⟨by
    rw [Measure.restrict_apply_univ, perimeterMeasure_open E hU]; exact hP.lt_top⟩
  obtain ⟨B, hB⟩ := (hc.isCompact_range hV.continuous).isBounded.exists_norm_le
  have hb : ∀ x, ‖V x‖ ≤ B := fun x ↦ hB _ (mem_range_self x)
  have hNi : Integrable (fun x ↦ ‖V x‖) μ :=
    Integrable.of_bound hV.continuous.norm.aestronglyMeasurable B
      (ae_of_all _ (fun x ↦ by simpa using hb x))
  have hbound : ∀ ε : ℝ, 0 < ε →
      |∫ x in E, divergence V x| ≤ (∫ x, ‖V x‖ ∂μ) + ε * μ.real univ := by
    intro ε hε
    let f : Euc n → ℝ := fun x ↦ Real.sqrt (‖V x‖ ^ 2 + ε ^ 2)
    have hsquare : ContDiff ℝ ∞ (fun x ↦ ‖V x‖ ^ 2 + ε ^ 2) := by
      simpa only [real_inner_self_eq_norm_sq] using (hV.inner ℝ hV).add (contDiff_const (c := ε^2))
    have hsq : ∀ x, 0 < ‖V x‖ ^ 2 + ε ^ 2 := fun x ↦ by positivity
    have hf : ContDiff ℝ ∞ f := hsquare.sqrt (fun x ↦ (hsq x).ne')
    have hfpos : ∀ x, 0 < f x := fun x ↦ Real.sqrt_pos.2 (hsq x)
    have hflo : ∀ x, ‖V x‖ ≤ f x := by
      intro x
      exact (Real.le_sqrt (norm_nonneg _) (hsq x).le).2 (by nlinarith [sq_nonneg ε])
    have hfhi : ∀ x, f x ≤ ‖V x‖ + ε := by
      intro x
      apply (Real.sqrt_le_iff).2
      constructor
      · positivity
      · nlinarith [norm_nonneg (V x)]
    let Q : Euc n → Euc n := fun x ↦ (f x)⁻¹ • V x
    have hQ : PerimeterAdmissible U Q := by
      refine ⟨(hf.inv (fun x ↦ (hfpos x).ne')).smul hV,
        hc.smul_left (f := fun x ↦ (f x)⁻¹),
        (tsupport_smul_subset_right _ _).trans hs, ?_⟩
      intro x
      simp only [Q, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (hfpos x).le)]
      exact (mul_le_mul_of_nonneg_left (hflo x) (inv_nonneg.mpr (hfpos x).le)).trans_eq
        (inv_mul_cancel₀ (hfpos x).ne')
    have hfM : ∀ x, f x ≤ B + ε := fun x ↦ (hfhi x).trans (add_le_add (hb x) le_rfl)
    have hfi : Integrable f μ := Integrable.of_bound hf.continuous.aestronglyMeasurable
      (B + ε) (ae_of_all _ (fun x ↦ by rw [Real.norm_eq_abs, abs_of_pos (hfpos x)]; exact hfM x))
    have hi := integral_divergence_scalar_le E U hU hP hQ hf (fun x ↦ (hfpos x).le) hfM
    have hn := integral_divergence_scalar_le E U hU hP (perimeterAdmissible_neg hQ)
      hf (fun x ↦ (hfpos x).le) hfM
    have heq : (fun x ↦ f x • Q x) = V := by
      funext x
      simp only [Q, smul_smul, mul_inv_cancel₀ (hfpos x).ne', one_smul]
    have heqn : (fun x ↦ f x • (-Q) x) = -V := by
      funext x
      simp only [Pi.neg_apply, smul_neg]
      rw [congrFun heq]
    rw [heq] at hi
    rw [heqn, divergence_neg (hV.differentiable (by simp))] at hn
    simp only [Pi.neg_apply, integral_neg] at hn
    have ha : |∫ x in E, divergence V x| ≤ ∫ x, f x ∂μ := abs_le.mpr ⟨by linarith, hi⟩
    refine ha.trans ?_
    calc
      (∫ x, f x ∂μ) ≤ ∫ x, ‖V x‖ + ε ∂μ := integral_mono hfi (hNi.add (integrable_const ε)) hfhi
      _ = (∫ x, ‖V x‖ ∂μ) + ε * μ.real univ := by
        rw [integral_add hNi (integrable_const ε), integral_const]; simp [mul_comm]
  apply le_of_forall_pos_le_add
  intro η hη
  let ε := η / (μ.real univ + 1)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hh := hbound ε hε
  have hm : ε * (μ.real univ + 1) = η := by
    dsimp [ε]
    exact div_mul_cancel₀ _ (by positivity)
  change |∫ x in E, divergence V x| ≤ (∫ x, ‖V x‖ ∂μ) + η
  nlinarith

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack

def smoothVariationDomain {n : ℕ} (U : Set (Euc n)) (μ : Measure (Euc n)) :
    Submodule ℝ (Lp (Euc n) 2 μ) where
  carrier := {u | ∃ V : Euc n → Euc n, ContDiff ℝ ∞ V ∧ HasCompactSupport V ∧
    tsupport V ⊆ U ∧ (u : Euc n → Euc n) =ᵐ[μ] V}
  zero_mem' := by
    refine ⟨0, contDiff_const, HasCompactSupport.zero, by simp, ?_⟩
    exact Lp.coeFn_zero _ _ _
  add_mem' := by
    rintro u v ⟨V, hV, hcV, hsV, heV⟩ ⟨W, hW, hcW, hsW, heW⟩
    refine ⟨V + W, hV.add hW, hcV.add hcW,
      (tsupport_add V W).trans (union_subset hsV hsW), ?_⟩
    exact (Lp.coeFn_add u v).trans (heV.add heW)
  smul_mem' := by
    rintro c u ⟨V, hV, hcV, hsV, heV⟩
    refine ⟨c • V, hV.const_smul c, hcV.comp_left (g := fun z : Euc n ↦ c • z) (smul_zero _),
      (tsupport_smul_subset_right (fun _ : Euc n ↦ c) V).trans hsV, ?_⟩
    exact (Lp.coeFn_smul c u).trans (heV.const_smul c)

noncomputable def smoothVariationRepresentative {n : ℕ} {U : Set (Euc n)}
    {μ : Measure (Euc n)} (u : smoothVariationDomain U μ) : Euc n → Euc n :=
  u.property.choose

theorem smoothVariationRepresentative_spec {n : ℕ} {U : Set (Euc n)}
    {μ : Measure (Euc n)} (u : smoothVariationDomain U μ) :
    ContDiff ℝ ∞ (smoothVariationRepresentative u) ∧
    HasCompactSupport (smoothVariationRepresentative u) ∧
    tsupport (smoothVariationRepresentative u) ⊆ U ∧
    ((u : Lp (Euc n) 2 μ) : Euc n → Euc n) =ᵐ[μ] smoothVariationRepresentative u :=
  u.property.choose_spec

theorem integral_divergence_eq_of_variation_ae {n : ℕ} (E U : Set (Euc n))
    (hU : IsOpen U) (hP : perimeter E U ≠ ⊤) {V W : Euc n → Euc n}
    (hV : ContDiff ℝ ∞ V) (hcV : HasCompactSupport V) (hsV : tsupport V ⊆ U)
    (hW : ContDiff ℝ ∞ W) (hcW : HasCompactSupport W) (hsW : tsupport W ⊆ U)
    (he : V =ᵐ[(perimeterMeasure E).restrict U] W) :
    (∫ x in E, divergence V x) = ∫ x in E, divergence W x := by
  have hh := abs_integral_divergence_le_integral_norm E U hU hP
    (hV.sub hW) (hcV.sub hcW) ((tsupport_sub V W).trans (union_subset hsV hsW))
  have he0 : (∫ x in U, ‖V x - W x‖ ∂perimeterMeasure E) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [he] with x hx
    simp [hx]
  change |∫ x in E, divergence (V - W) x| ≤ ∫ x in U, ‖V x - W x‖ ∂perimeterMeasure E at hh
  rw [he0, abs_nonpos_iff, divergence_sub (hV.differentiable (by simp))
    (hW.differentiable (by simp))] at hh
  simp only [Pi.sub_apply] at hh
  rw [integral_sub (integrable_divergence hV hcV).integrableOn
    (integrable_divergence hW hcW).integrableOn] at hh
  exact sub_eq_zero.mp hh

noncomputable def localVariationFunctional {n : ℕ} (E U : Set (Euc n))
    (hU : IsOpen U) (hP : perimeter E U ≠ ⊤) :
    smoothVariationDomain U ((perimeterMeasure E).restrict U) →ₗ[ℝ] ℝ where
  toFun u := ∫ x in E, divergence (smoothVariationRepresentative u) x
  map_add' u v := by
    obtain ⟨hVu, hcVu, hsVu, heVu⟩ := smoothVariationRepresentative_spec u
    obtain ⟨hVv, hcVv, hsVv, heVv⟩ := smoothVariationRepresentative_spec v
    obtain ⟨hVw, hcVw, hsVw, heVw⟩ := smoothVariationRepresentative_spec (u + v)
    have he := heVw.symm.trans ((Lp.coeFn_add (u : Lp (Euc n) 2 ((perimeterMeasure E).restrict U)) (v : Lp (Euc n) 2 ((perimeterMeasure E).restrict U))).trans
      (heVu.add heVv))
    rw [integral_divergence_eq_of_variation_ae E U hU hP hVw hcVw hsVw
      (hVu.add hVv) (hcVu.add hcVv)
      ((tsupport_add (smoothVariationRepresentative u) (smoothVariationRepresentative v)).trans (union_subset hsVu hsVv)) he]
    change (∫ x in E, divergence (smoothVariationRepresentative u + smoothVariationRepresentative v) x) = _
    rw [divergence_add (hVu.differentiable (by simp)) (hVv.differentiable (by simp))]
    exact integral_add (integrable_divergence hVu hcVu).integrableOn
      (integrable_divergence hVv hcVv).integrableOn
  map_smul' c u := by
    obtain ⟨hVu, hcVu, hsVu, heVu⟩ := smoothVariationRepresentative_spec u
    obtain ⟨hVw, hcVw, hsVw, heVw⟩ := smoothVariationRepresentative_spec (c • u)
    have he := heVw.symm.trans ((Lp.coeFn_smul c (u : Lp (Euc n) 2 ((perimeterMeasure E).restrict U))).trans (heVu.const_smul c))
    rw [integral_divergence_eq_of_variation_ae E U hU hP hVw hcVw hsVw
      (hVu.const_smul c) (hcVu.comp_left (g := fun z : Euc n ↦ c • z) (smul_zero _))
      ((tsupport_smul_subset_right (fun _ : Euc n ↦ c) (smoothVariationRepresentative u)).trans hsVu) he]
    change (∫ x in E, divergence (fun y ↦ c • smoothVariationRepresentative u y) x) = _
    simp_rw [divergence_smul (differentiable_const c) (hVu.differentiable (by simp)),
      gradient_fun_const, inner_zero_left, add_zero]
    exact integral_smul c _

theorem localVariationFunctional_le {n : ℕ} (E U : Set (Euc n))
    (hU : IsOpen U) (hP : perimeter E U ≠ ⊤)
    (u : smoothVariationDomain U ((perimeterMeasure E).restrict U)) :
    |localVariationFunctional E U hU hP u| ≤
      ∫ x in U, ‖(u : Lp (Euc n) 2 ((perimeterMeasure E).restrict U)) x‖ ∂perimeterMeasure E := by
  obtain ⟨hV, hcV, hsV, heV⟩ := smoothVariationRepresentative_spec u
  refine (abs_integral_divergence_le_integral_norm E U hU hP hV hcV hsV).trans_eq ?_
  apply integral_congr_ae
  filter_upwards [heV] with x hx
  rw [hx]

end RPISingularHarnack

end

end OAI
