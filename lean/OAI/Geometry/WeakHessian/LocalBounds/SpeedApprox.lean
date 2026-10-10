import Mathlib
import OAI.Geometry.WeakHessian.Transport.AeEvalAe

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable
namespace WeakHessian
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X}

def speedApprox (n : ℕ) (p : Curve X × ℝ) : ℝ≥0∞ :=
  ⨆ (h : ℝ) (_ : h ≠ 0 ∧ |h| < 1 / (n + 1 : ℝ)),
    ENNReal.ofReal (dist (evalReal p.1 (p.2 + h)) (evalReal p.1 p.2) / |h|)

omit [MeasurableSpace X] [BorelSpace X] in
lemma metricSpeed_eq_iInf_speedApprox (γ : Curve X) (t : ℝ) :
    metricSpeed γ t = ⨅ n : ℕ, speedApprox n (γ, t) := by
  rw [metricSpeed, nhdsWithin,
    ((Metric.nhds_basis_ball_inv_nat_succ (x := t)).inf_principal ({t}ᶜ)).limsup_eq_iInf_iSup]
  simp only [iInf_true]
  apply iInf_congr
  intro n
  apply le_antisymm
  · apply iSup_le
    intro s
    apply iSup_le
    rintro ⟨hs, hst⟩
    have hne : s - t ≠ 0 := sub_ne_zero.mpr hst
    have hlt : |s - t| < 1 / (n + 1 : ℝ) := by simpa only [Metric.mem_ball, Real.dist_eq] using hs
    calc
      ENNReal.ofReal (dist (evalReal γ s) (evalReal γ t) / |s - t|) =
          ENNReal.ofReal (dist (evalReal γ (t + (s - t))) (evalReal γ t) / |s - t|) := by
        rw [show t + (s - t) = s by ring]
      _ ≤ speedApprox n (γ, t) := le_iSup_of_le (s - t) (le_iSup_of_le ⟨hne, hlt⟩ le_rfl)
  · apply iSup_le
    intro h
    apply iSup_le
    rintro ⟨hne, hlt⟩
    have hball : t + h ∈ Metric.ball t (1 / (n + 1 : ℝ)) := by
      simpa only [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left] using hlt
    have hne' : t + h ∈ ({t}ᶜ : Set ℝ) := by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact fun heq => hne (by linarith)
    apply le_iSup_of_le (t + h)
    apply le_iSup_of_le (show t + h ∈ Metric.ball t (1 / (n + 1 : ℝ)) ∩ {t}ᶜ from
      ⟨hball, hne'⟩)
    simp only [add_sub_cancel_left, le_refl]

omit [MeasurableSpace X] [BorelSpace X] in
lemma lowerSemicontinuous_speedApprox (n : ℕ) :
    LowerSemicontinuous (speedApprox (X := X) n) := by
  apply lowerSemicontinuous_biSup
  intro h _hh
  apply Continuous.lowerSemicontinuous
  apply ENNReal.continuous_ofReal.comp
  exact ((continuous_evalReal.comp (continuous_fst.prodMk (continuous_snd.add_const h))).dist
    continuous_evalReal).div_const |h|

omit [MeasurableSpace X] [BorelSpace X] in
lemma measurable_metricSpeed : Measurable (fun p : Curve X × ℝ => metricSpeed p.1 p.2) := by
  simp_rw [metricSpeed_eq_iInf_speedApprox]
  exact Measurable.iInf fun n => (lowerSemicontinuous_speedApprox n).measurable

omit [BorelSpace X] in

lemma LocallyL2.aestronglyMeasurable {f : X → ℝ} (hf : LocallyL2 m f) :
    AEStronglyMeasurable f m := by
  cases isEmpty_or_nonempty X with
  | inl h => exact (measurable_of_empty f).aestronglyMeasurable
  | inr h =>
    obtain ⟨o⟩ := h
    have hm : AEStronglyMeasurable f (m.restrict (⋃ n : ℕ, Metric.ball o (n + 1))) :=
      AEStronglyMeasurable.iUnion fun n =>
        (hf o (n + 1) (by positivity)).aestronglyMeasurable
    simpa only [Metric.iUnion_ball_nat_succ, Measure.restrict_univ] using hm

omit [BorelSpace X] in
lemma LocallyL2.aemeasurable {f : X → ℝ} (hf : LocallyL2 m f) :
    AEMeasurable f m := hf.aestronglyMeasurable.aemeasurable

lemma IsTestPlan.ae_prod_eval_of_ae {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    {p : X → Prop} (hp : ∀ᵐ x ∂m, p x) :
    ∀ᵐ z ∂π.prod (volume.restrict (Set.Icc (0 : ℝ) 1)), p (evalReal z.1 z.2) := by
  let S := toMeasurable m {x | ¬ p x}
  have hSm : MeasurableSet S := measurableSet_toMeasurable _ _
  have hSzero : m S = 0 := by
    rw [measure_toMeasurable]
    exact ae_iff.mp hp
  have hSae : ∀ᵐ x ∂m, x ∉ S := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hSzero
  let : IsProbabilityMeasure π := hπ.1
  have hh : ∀ᵐ z ∂π.prod (volume.restrict (Set.Icc (0 : ℝ) 1)),
      evalReal z.1 z.2 ∉ S :=
    (Measure.ae_prod_iff_ae_ae
      (hSm.compl.preimage continuous_evalReal.measurable)).mpr (hπ.ae_ae_eval_of_ae hSae)
  filter_upwards [hh] with z hz
  by_contra hn
  exact hz (subset_toMeasurable m {x | ¬ p x} hn)

lemma IsTestPlan.aemeasurable_evalReal {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    {f : X → ℝ} (hf : AEMeasurable f m) :
    AEMeasurable (fun z : Curve X × ℝ => f (evalReal z.1 z.2))
      (π.prod (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
  exact ((hf.measurable_mk.comp continuous_evalReal.measurable).aemeasurable).congr
    (Filter.EventuallyEq.symm (hπ.ae_prod_eval_of_ae hf.ae_eq_mk))

lemma IsTestPlan.aemeasurable_eval {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    {f : X → ℝ} (hf : AEMeasurable f m) (t : Time) :
    AEMeasurable (fun γ : Curve X => f (γ t)) π := by
  exact ((hf.measurable_mk.comp (continuous_eval_const t).measurable).aemeasurable).congr
    (Filter.EventuallyEq.symm (hπ.ae_eval_of_ae hf.ae_eq_mk t))

lemma IsTestPlan.aemeasurable_action {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    {D : X → ℝ} (hD : LocallyL2 m D) :
    AEMeasurable (fun z : Curve X × ℝ =>
      ENNReal.ofReal (D (evalReal z.1 z.2)) * metricSpeed z.1 z.2)
      (π.prod (volume.restrict (Set.Icc (0 : ℝ) 1))) :=
  ((hπ.aemeasurable_evalReal hD.aemeasurable).ennreal_ofReal).mul
    measurable_metricSpeed.aemeasurable

omit [BorelSpace X] in
lemma LocallyL2.add {f g : X → ℝ} (hf : LocallyL2 m f) (hg : LocallyL2 m g) :
    LocallyL2 m (fun x => f x + g x) := by
  intro o R hR
  exact (hf o R hR).add (hg o R hR)

lemma IsLocalWeakUpperGradient.add {f g D E : X → ℝ}
    (hD : IsLocalWeakUpperGradient m f D) (hE : IsLocalWeakUpperGradient m g E)
    (hf : LocallyL2 m f) :
    IsLocalWeakUpperGradient m (fun x => f x + g x) (fun x => D x + E x) := by
  refine ⟨hD.1.add hE.1, ?_, ?_⟩
  · filter_upwards [hD.2.1, hE.2.1] with x hx hy
    exact add_nonneg hx hy
  · intro π hπ hb
    let ν := volume.restrict (Set.Icc (0 : ℝ) 1)
    have hDm := hπ.aemeasurable_action hD.1
    have hEm := hπ.aemeasurable_action hE.1
    have hfm := ((hπ.aemeasurable_eval hf.aemeasurable timeOne).sub
      (hπ.aemeasurable_eval hf.aemeasurable timeZero)).abs.ennreal_ofReal
    have hsum : (fun z : Curve X × ℝ =>
        ENNReal.ofReal ((D (evalReal z.1 z.2)) + E (evalReal z.1 z.2)) * metricSpeed z.1 z.2)
        =ᵐ[π.prod ν] (fun z => ENNReal.ofReal (D (evalReal z.1 z.2)) * metricSpeed z.1 z.2 +
          ENNReal.ofReal (E (evalReal z.1 z.2)) * metricSpeed z.1 z.2) := by
      filter_upwards [hπ.ae_prod_eval_of_ae hD.2.1,
        hπ.ae_prod_eval_of_ae hE.2.1] with z hz hz'
      rw [ENNReal.ofReal_add hz hz', add_mul]
    have hsm := (hDm.add hEm).congr hsum.symm
    calc
      (∫⁻ γ : Curve X, ENNReal.ofReal |f (γ timeOne) + g (γ timeOne) -
          (f (γ timeZero) + g (γ timeZero))| ∂π) ≤
        (∫⁻ γ : Curve X, ENNReal.ofReal |f (γ timeOne) - f (γ timeZero)| +
          ENNReal.ofReal |g (γ timeOne) - g (γ timeZero)| ∂π) := by
            apply lintegral_mono
            intro γ
            dsimp only
            rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
            apply ENNReal.ofReal_le_ofReal
            rw [show f (γ timeOne) + g (γ timeOne) - (f (γ timeZero) + g (γ timeZero)) =
              (f (γ timeOne) - f (γ timeZero)) + (g (γ timeOne) - g (γ timeZero)) by ring]
            exact abs_add_le _ _
      _ ≤ (∫⁻ γ : Curve X, ENNReal.ofReal |f (γ timeOne) - f (γ timeZero)| ∂π) +
          ∫⁻ γ : Curve X, ENNReal.ofReal |g (γ timeOne) - g (γ timeZero)| ∂π :=
        (lintegral_add_left' hfm _).le
      _ ≤ (∫⁻ γ, ∫⁻ t, ENNReal.ofReal (D (evalReal γ t)) * metricSpeed γ t ∂ν ∂π) +
          ∫⁻ γ, ∫⁻ t, ENNReal.ofReal (E (evalReal γ t)) * metricSpeed γ t ∂ν ∂π :=
        add_le_add (hD.2.2 π hπ hb) (hE.2.2 π hπ hb)
      _ = ∫⁻ z, ENNReal.ofReal (D (evalReal z.1 z.2) + E (evalReal z.1 z.2)) *
          metricSpeed z.1 z.2 ∂π.prod ν := by
        rw [← lintegral_prod _ hDm, ← lintegral_prod _ hEm,
          lintegral_congr_ae hsum, lintegral_add_left' hDm]
      _ = _ := lintegral_prod _ hsm

lemma IsTestPlan.of_plan_le_smul {π ρ : Measure (Curve X)} (hπ : IsTestPlan m π)
    (hρp : IsProbabilityMeasure ρ) {C : ℝ≥0∞} (hC : C < ∞) (hρ : ρ ≤ C • π) :
    IsTestPlan m ρ := by
  obtain ⟨D, hD⟩ := hπ.2.1
  refine ⟨hρp, ⟨C.toNNReal * D, fun t => ?_⟩, ?_, ?_⟩
  · calc
      Measure.map (fun γ : Curve X => γ t) ρ ≤
          Measure.map (fun γ : Curve X => γ t) (C • π) :=
        Measure.map_mono hρ (continuous_eval_const t).measurable
      _ = C • Measure.map (fun γ : Curve X => γ t) π :=
        Measure.map_smul C (continuous_eval_const t).measurable.aemeasurable
      _ ≤ C • ((D : ℝ≥0∞) • m) := by gcongr; exact hD t
      _ = ((C.toNNReal * D : ℝ≥0) : ℝ≥0∞) • m := by
        rw [smul_smul, ENNReal.coe_mul, ENNReal.coe_toNNReal hC.ne]
  · exact (Measure.absolutelyContinuous_of_le_smul hρ).ae_le hπ.2.2.1
  · calc
      (∫⁻ γ, ∫⁻ t in Set.Icc (0 : ℝ) 1, metricSpeed γ t ^ 2 ∂volume ∂ρ) ≤
          ∫⁻ γ, ∫⁻ t in Set.Icc (0 : ℝ) 1, metricSpeed γ t ^ 2 ∂volume ∂C • π :=
        lintegral_mono' hρ le_rfl
      _ = C * ∫⁻ γ, ∫⁻ t in Set.Icc (0 : ℝ) 1, metricSpeed γ t ^ 2 ∂volume ∂π :=
        lintegral_smul_measure _ _
      _ < ∞ := ENNReal.mul_lt_top hC hπ.2.2.2

omit [MeasurableSpace X] [BorelSpace X] in
lemma BoundedTracks.of_plan_le_smul {π ρ : Measure (Curve X)} (hπ : BoundedTracks π)
    {C : ℝ≥0∞} (hρ : ρ ≤ C • π) : BoundedTracks ρ := by
  obtain ⟨o, R, hR, hb⟩ := hπ
  exact ⟨o, R, hR, (Measure.absolutelyContinuous_of_le_smul hρ).ae_le hb⟩

lemma IsLocalWeakUpperGradient.ae_endpoint_le {f D : X → ℝ}
    (hD : IsLocalWeakUpperGradient m f D) (hf : AEMeasurable f m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π) :
    ∀ᵐ γ ∂π, ENNReal.ofReal |f (γ timeOne) - f (γ timeZero)| ≤
      ∫⁻ t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (D (evalReal γ t)) * metricSpeed γ t := by
  let : IsProbabilityMeasure π := hπ.1
  have hfm := ((hπ.aemeasurable_eval hf timeOne).sub
    (hπ.aemeasurable_eval hf timeZero)).abs.ennreal_ofReal
  apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite₀ hfm
  intro S _hS hSfin
  by_cases hS : π S = 0
  · simp only [Measure.restrict_eq_zero.mpr hS, lintegral_zero_measure, le_refl]
  have hSpos : 0 < π S := pos_iff_ne_zero.mpr hS
  let ρ := (π S)⁻¹ • π.restrict S
  have hρdom : ρ ≤ (π S)⁻¹ • π := by
    change (π S)⁻¹ • π.restrict S ≤ (π S)⁻¹ • π
    gcongr
    exact Measure.restrict_le_self
  have hρp : IsProbabilityMeasure ρ := by
    constructor
    simp only [ρ, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ,
      ENNReal.inv_mul_cancel hS hSfin.ne]
  have hρt := hπ.of_plan_le_smul hρp (ENNReal.inv_lt_top.mpr hSpos) hρdom
  have hρb := hb.of_plan_le_smul hρdom
  have hh := hD.2.2 ρ hρt hρb
  simp only [ρ, lintegral_smul_measure] at hh
  exact (ENNReal.mul_le_mul_iff_right (ENNReal.inv_ne_zero.mpr hSfin.ne)
    (ENNReal.inv_ne_top.mpr hS)).mp hh

end WeakHessian

lemma continuous_ae_map_of_ae
    {A B : Type*} [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A] [T2Space A]
    [TopologicalSpace B] [MeasurableSpace B] [BorelSpace B] [T2Space B]
    {μ : Measure A} [IsFiniteMeasure μ] [Measure.InnerRegularCompactLTTop μ]
    {f : A → B} (hf : Continuous f) {p : B → Prop}
    (hp : ∀ᵐ x ∂μ, p (f x)) : ∀ᵐ y ∂Measure.map f μ, p y := by
  let S := (toMeasurable μ {x | ¬p (f x)})ᶜ
  have hSm : MeasurableSet S := (measurableSet_toMeasurable _ _).compl
  have hSzero : μ Sᶜ = 0 := by
    simp only [S, compl_compl, measure_toMeasurable]
    exact ae_iff.mp hp
  have hSp : ∀ x ∈ S, p (f x) := by
    intro x hx
    by_contra hn
    exact hx (subset_toMeasurable μ {x | ¬p (f x)} hn)
  rw [ae_iff]
  apply le_antisymm _ bot_le
  apply le_of_forall_gt
  intro ε hε
  obtain ⟨K, hKS, hKc, hKsmall⟩ := hSm.exists_isCompact_sdiff_lt (measure_ne_top μ S) hε.ne'
  have hKp : {y | ¬p y} ⊆ (f '' K)ᶜ := by
    rintro y hy ⟨x, hx, rfl⟩
    exact hy (hSp x (hKS hx))
  calc
    Measure.map f μ {y | ¬p y} ≤ Measure.map f μ (f '' K)ᶜ := measure_mono hKp
    _ = μ (f ⁻¹' (f '' K)ᶜ) := Measure.map_apply hf.measurable (hKc.image hf).measurableSet.compl
    _ ≤ μ Kᶜ := measure_mono (by simpa only [preimage_compl, compl_subset_compl] using subset_preimage_image f K)
    _ ≤ μ (S \ K) + μ Sᶜ := by
      apply (measure_mono (show Kᶜ ⊆ (S \ K) ∪ Sᶜ by intro x hx; by_cases hs : x ∈ S <;> simp_all)).trans
      exact measure_union_le _ _
    _ < ε := by simpa only [hSzero, add_zero] using hKsmall

end
end InlinedFile0

end OAI
