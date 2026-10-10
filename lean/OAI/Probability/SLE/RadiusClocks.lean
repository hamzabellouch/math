import Mathlib
import OAI.Probability.SLE.BrownianStrongMarkov

namespace OAI

/-! Radius Clocks for chordal SLE. -/

section
section
section
open Set Filter MeasureTheory
open scoped Topology NNReal
namespace SLEExactGauge
lemma measurableSet_exists_zero_compact
    {Ω K : Type*} [MeasurableSpace Ω] [TopologicalSpace K]
    [CompactSpace K] [TopologicalSpace.SeparableSpace K] [Nonempty K]
    (f : K → Ω → ℝ) (hm : ∀ t, Measurable (f t))
    (hc : ∀ ω, Continuous (fun t => f t ω)) :
    MeasurableSet {ω | ∃ t, f t ω = 0} := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense K
  let : Countable D := hDc.to_subtype
  have hi : Measurable (fun ω => ⨅ t : D, |f t ω|) :=
    Measurable.iInf (fun t => (hm t).abs)
  have he (ω : Ω) : (∃ t, f t ω = 0) ↔ (⨅ t : D, |f t ω|) = 0 := by
    have hb : BddBelow (range (fun t => |f t ω|)) := ⟨0, by rintro _ ⟨t, rfl⟩; exact abs_nonneg _⟩
    rw [hDd.ciInf (hc ω).abs hb]
    obtain ⟨t, _, ht⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty : (univ : Set K).Nonempty)
      (hc ω).abs.continuousOn
    have hv : (⨅ s, |f s ω|) = |f t ω| :=
      le_antisymm (ciInf_le hb t) (le_ciInf (fun s => ht (mem_univ s)))
    rw [hv]
    constructor
    · rintro ⟨s, hs⟩
      have ht' : |f t ω| ≤ |f s ω| := ht (mem_univ s)
      rw [hs, abs_zero] at ht'
      exact le_antisymm ht' (abs_nonneg _)
    · intro h
      exact ⟨t, abs_eq_zero.mp h⟩
  have hs : MeasurableSet {ω | (⨅ t : D, |f t ω|) = 0} :=
    measurableSet_eq_fun hi measurable_const
  have heSet : {ω | ∃ t, f t ω = 0} = {ω | (⨅ t : D, |f t ω|) = 0} :=
    Set.ext he
  rw [heSet]
  exact hs

lemma hittingAfter_zero_le_iff
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (hc : ∀ ω, Continuous (fun t => X t ω)) (n T : ℝ≥0) (ω : Ω) :
    hittingAfter X {0} n ω ≤ (T : WithTop ℝ≥0) ↔
      ∃ t ∈ Icc n T, X t ω = 0 := by
  classical
  let V : Set ℝ≥0 := {t | n ≤ t ∧ X t ω = 0}
  have hV : IsClosed V := isClosed_Ici.inter (isClosed_eq (hc ω) continuous_const)
  have hb : BddBelow V := ⟨0, fun t _ => bot_le⟩
  change (if V.Nonempty then ((sInf V : ℝ≥0) : WithTop ℝ≥0) else ⊤) ≤ (T : WithTop ℝ≥0) ↔ _
  by_cases hv : V.Nonempty
  · obtain ⟨v, hv⟩ := hv
    have he : ∃ t, n ≤ t ∧ X t ω ∈ ({0} : Set ℝ) := ⟨v, hv.1, hv.2⟩
    have hin : sInf V ∈ V := hV.csInf_mem ⟨v, hv⟩ hb
    rw [ite_eq_left (show V.Nonempty from ⟨v, hv⟩), WithTop.coe_le_coe]
    constructor
    · intro h
      exact ⟨sInf V, ⟨hin.1, h⟩, hin.2⟩
    · rintro ⟨t, ht, hx⟩
      exact (csInf_le hb ⟨ht.1, hx⟩).trans ht.2
  · have he : ¬ ∃ t, n ≤ t ∧ X t ω ∈ ({0} : Set ℝ) := by
      exact hv
    rw [ite_eq_right hv]
    simp only [WithTop.not_top_le_coe, false_iff]
    rintro ⟨t, ht, hx⟩
    exact hv ⟨t, ht.1, hx⟩

 

theorem continuous_zero_hit_stopping
    {Ω : Type*} [m : MeasurableSpace Ω] (ℱ : Filtration ℝ≥0 m)
    (X : ℝ≥0 → Ω → ℝ) (hXa : Adapted ℱ X)
    (hXc : ∀ ω, Continuous (fun t => X t ω)) (n : ℝ≥0) :
    IsStoppingTime ℱ (hittingAfter X {0} n) := by
  intro T
  have he : {ω | hittingAfter X {0} n ω ≤ (T : WithTop ℝ≥0)} =
      {ω | ∃ t : Icc n T, X t ω = 0} := by
    ext ω
    simp only [mem_ofPred_eq, hittingAfter_zero_le_iff X hXc, Subtype.exists, exists_prop]
  rw [he]
  by_cases hnT : n ≤ T
  · let : Nonempty (Icc n T) := ⟨⟨n, le_rfl, hnT⟩⟩
    have hm (t : Icc n T) : @Measurable Ω ℝ (ℱ T) (borel ℝ) (X t) :=
      (hXa t).mono (ℱ.mono t.property.2) le_rfl
    let : MeasurableSpace Ω := ℱ T
    exact measurableSet_exists_zero_compact (fun t : Icc n T => X t) hm
      (fun ω => (hXc ω).comp continuous_subtype_val)
  · have hnil : IsEmpty (Icc n T) := ⟨fun t => hnT (t.property.1.trans t.property.2)⟩
    have : {ω | ∃ t : Icc n T, X t ω = 0} = ∅ := by ext ω; simp
    rw [this]
    exact @MeasurableSet.empty Ω (ℱ T)

end SLEExactGauge

end

 
section

open Set Filter MeasureTheory
open scoped Topology NNReal
namespace SLEExactGauge

lemma stopped_min_measurable {Ω : Type*} [m : MeasurableSpace Ω]
    {ℱ : Filtration ℝ≥0 m} {ρ : Ω → ℝ≥0}
    (hρ : IsStoppingTime ℱ (fun ω => (ρ ω : WithTop ℝ≥0))) (T : ℝ≥0) :
    Measurable[ℱ T] (fun ω => min (ρ ω) T) := by
  have h := ((hρ.min_const T).measurable_of_le (fun _ => min_le_right _ _)).untopD 0
  simpa only [← WithTop.coe_min, WithTop.untopD_coe] using h

 

theorem continuous_zero_hit_after_stopping
    {Ω : Type*} [m : MeasurableSpace Ω] (ℱ : Filtration ℝ≥0 m)
    (X : ℝ≥0 → Ω → ℝ) (hXa : Adapted ℱ X)
    (hXc : ∀ ω, Continuous (fun t => X t ω)) (ρ : Ω → ℝ≥0)
    (hρ : IsStoppingTime ℱ (fun ω => (ρ ω : WithTop ℝ≥0))) :
    IsStoppingTime ℱ (fun ω => hittingAfter X {0} (ρ ω) ω) := by
  intro T
  let f : Icc (0 : ℝ≥0) T → Ω → ℝ :=
    fun t ω => |X t ω| + max (((min (ρ ω) T : ℝ≥0) : ℝ) - (t : ℝ≥0)) 0
  have he : {ω | hittingAfter X {0} (ρ ω) ω ≤ (T : WithTop ℝ≥0)} =
      {ω | ρ ω ≤ T} ∩ {ω | ∃ t : Icc (0 : ℝ≥0) T, f t ω = 0} := by
    ext ω
    rw [mem_ofPred_eq, hittingAfter_zero_le_iff X hXc]
    constructor
    · rintro ⟨t, ht, hx⟩
      have hr : ρ ω ≤ T := ht.1.trans ht.2
      refine ⟨hr, ⟨⟨t, bot_le, ht.2⟩, ?_⟩⟩
      dsimp only [f]
      rw [hx, abs_zero, min_eq_left hr, max_eq_right (sub_nonpos.mpr (show (ρ ω : ℝ) ≤ (t : ℝ) from ht.1))]
      exact zero_add 0
    · rintro ⟨hr, t, ht⟩
      have hp : 0 ≤ max (((min (ρ ω) T : ℝ≥0) : ℝ) - (t : ℝ≥0)) 0 := le_max_right _ _
      have hx : X t ω = 0 := abs_eq_zero.mp (by dsimp only [f] at ht; linarith [abs_nonneg (X t ω)])
      have hle : (ρ ω : ℝ) ≤ (t : ℝ≥0) := by
        dsimp only [f] at ht
        rw [min_eq_left hr] at ht
        have hh := le_max_left ((ρ ω : ℝ) - (t : ℝ≥0)) 0
        linarith [abs_nonneg (X t ω)]
      exact ⟨t, ⟨hle, t.property.2⟩, hx⟩
  rw [he]
  have hmρ := stopped_min_measurable hρ T
  have hmX (t : Icc (0 : ℝ≥0) T) : Measurable[ℱ T] (X t) :=
    (hXa t).mono (ℱ.mono t.property.2) le_rfl
  let : MeasurableSpace Ω := ℱ T
  have hm (t : Icc (0 : ℝ≥0) T) : Measurable (f t) :=
    (hmX t).abs.add (((NNReal.continuous_coe.measurable.comp hmρ).sub measurable_const).max measurable_const)
  have hme : MeasurableSet {ω | ∃ t : Icc (0 : ℝ≥0) T, f t ω = 0} := by
    let : Nonempty (Icc (0 : ℝ≥0) T) := ⟨⟨0, le_rfl, bot_le⟩⟩
    apply measurableSet_exists_zero_compact f hm
    intro ω
    exact ((hXc ω).comp continuous_subtype_val).abs.add
      ((continuous_const.sub (NNReal.continuous_coe.comp continuous_subtype_val)).max continuous_const)
  have hmle : MeasurableSet {ω | ρ ω ≤ T} := by
    simpa only [WithTop.coe_le_coe] using hρ T
  exact hmle.inter hme

end SLEExactGauge

end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

noncomputable def diskHitAfter {Ω : Type*} (γ : Ω → ℝ≥0 → ℂ)
    (ρ : Ω → ℝ≥0) (z : ℂ) (r : ℝ) (ω : Ω) : WithTop ℝ≥0 :=
  hittingAfter (fun t ω => dist (γ ω t) z - r) {0} (ρ ω) ω

namespace RegularSLEPresentation
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)

lemma diskHitAfter_stopping (ρ : a.samples → ℝ≥0)
    (hρ : IsStoppingTime a.filtration (fun ω => (ρ ω : WithTop ℝ≥0)))
    (z : ℂ) (r : ℝ) :
    IsStoppingTime a.filtration (diskHitAfter (γ ∘ Subtype.val) ρ z r) := by
  apply continuous_zero_hit_after_stopping a.filtration
    (fun t ω => dist (γ ω t) z - r) ?_ ?_ ρ hρ
  · intro t
    have hm := a.trace_adapted t
    let : MeasurableSpace a.samples := a.filtration t
    exact (hm.dist measurable_const).sub measurable_const
  · intro ω
    exact ((a.trace_continuous ω).dist continuous_const).sub continuous_const

noncomputable def boundedDiskHit (ρ : a.samples → ℝ≥0) (z : ℂ) (r : ℝ)
    (T : ℝ≥0) (ω : a.samples) : ℝ≥0 :=
  (min (diskHitAfter (γ ∘ Subtype.val) ρ z r ω) T).untopD 0

lemma boundedDiskHit_coe (ρ : a.samples → ℝ≥0) (z : ℂ) (r : ℝ) (T : ℝ≥0)
    (ω : a.samples) :
    (a.boundedDiskHit ρ z r T ω : WithTop ℝ≥0) =
      min (diskHitAfter (γ ∘ Subtype.val) ρ z r ω) T := by
  have hn : min (diskHitAfter (γ ∘ Subtype.val) ρ z r ω) (T : WithTop ℝ≥0) ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_right _ _)
  obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp hn
  change (((min (diskHitAfter (γ ∘ Subtype.val) ρ z r ω) (T : WithTop ℝ≥0)).untopD 0 : ℝ≥0) : WithTop ℝ≥0) = _
  rw [← hv, WithTop.untopD_coe]

lemma boundedDiskHit_stopping (ρ : a.samples → ℝ≥0)
    (hρ : IsStoppingTime a.filtration (fun ω => (ρ ω : WithTop ℝ≥0)))
    (z : ℂ) (r : ℝ) (T : ℝ≥0) :
    IsStoppingTime a.filtration (fun ω => (a.boundedDiskHit ρ z r T ω : WithTop ℝ≥0)) := by
  simpa only [a.boundedDiskHit_coe] using (a.diskHitAfter_stopping ρ hρ z r).min_const T

 

theorem boundedDiskHit_restart_law [IsProbabilityMeasure P]
    (ρ : a.samples → ℝ≥0)
    (hρ : IsStoppingTime a.filtration (fun ω => (ρ ω : WithTop ℝ≥0)))
    (z : ℂ) (r : ℝ) (T : ℝ≥0) {A : Set a.samples}
    (hA : MeasurableSet[(a.boundedDiskHit_stopping ρ hρ z r T).measurableSpace] A) :
    ((P.comap (Subtype.val : a.samples → Ω)).restrict A).map
      (fun ω t => brownianRestart a.B (a.boundedDiskHit ρ z r T) t ω) =
    (P.comap (Subtype.val : a.samples → Ω)) A •
      (P.comap (Subtype.val : a.samples → Ω)).map (fun ω t => a.B t ω) :=
  brownian_restart_path_law a.brownian a.measurable_B a.continuous_B
    (a.boundedDiskHit_stopping ρ hρ z r T) hA

end RegularSLEPresentation
end SLEExactGauge

end

 
section

open Set Filter Metric Complex InnerProductSpace
open scoped Topology Laplacian
namespace SLEExactGauge

lemma complex_bilinear_rotation_trace (B : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (e : ℂ) :
    B e e + B (e * I) (e * I) = ‖e‖ ^ 2 * (B 1 1 + B I I) := by
  have he : e = e.re • (1 : ℂ) + e.im • I := by apply Complex.ext <;> simp
  have heI : e * I = (-e.im) • (1 : ℂ) + e.re • I := by apply Complex.ext <;> simp
  calc
    _ = B (e.re • 1 + e.im • I) (e.re • 1 + e.im • I) +
      B ((-e.im) • 1 + e.re • I) ((-e.im) • 1 + e.re • I) := by rw [← he, ← heI]
    _ = _ := by
      simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
      rw [Complex.sq_norm]
      simp only [Complex.normSq_apply]
      ring

lemma complex_hessian_rotation {u : ℂ → ℝ} (z e : ℂ) :
    fderiv ℝ (fderiv ℝ u) z e e + fderiv ℝ (fderiv ℝ u) z (e * I) (e * I) =
      ‖e‖ ^ 2 * (Δ u) z := by
  rw [complex_bilinear_rotation_trace]
  simp only [laplacian_eq_iteratedFDeriv_complexPlane, iteratedFDeriv_two_apply,
    Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]

noncomputable def polarPoint (r θ : ℝ) : ℂ := r • circleMap 0 1 θ

lemma polarPoint_eq_circleMap (r θ : ℝ) : polarPoint r θ = circleMap 0 r θ := by
  simp [polarPoint, circleMap]

lemma polarPoint_norm (r θ : ℝ) : ‖polarPoint r θ‖ = |r| := by
  simp [polarPoint, norm_circleMap_zero]

lemma polarPoint_radial_hasDeriv (r θ : ℝ) :
    HasDerivAt (fun s => polarPoint s θ) (circleMap 0 1 θ) r := by
  simpa [polarPoint] using (hasDerivAt_id r).smul_const (circleMap 0 1 θ)

lemma polarPoint_angular_hasDeriv (r θ : ℝ) :
    HasDerivAt (polarPoint r) (polarPoint r θ * I) θ := by
  simpa only [funext (polarPoint_eq_circleMap r), polarPoint_eq_circleMap] using
    hasDerivAt_circleMap 0 r θ

lemma radial_partial_hasDeriv {u : ℂ → ℝ} {r θ : ℝ}
    (hu : ContDiffAt ℝ 2 u (polarPoint r θ)) :
    HasDerivAt (fun s => u (polarPoint s θ))
      (fderiv ℝ u (polarPoint r θ) (circleMap 0 1 θ)) r :=
  (hu.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt r
    (polarPoint_radial_hasDeriv r θ)

lemma radial_second_hasDeriv {u : ℂ → ℝ} {r θ : ℝ}
    (hu : ContDiffAt ℝ 2 u (polarPoint r θ)) :
    HasDerivAt (fun s => fderiv ℝ u (polarPoint s θ) (circleMap 0 1 θ))
      (fderiv ℝ (fderiv ℝ u) (polarPoint r θ) (circleMap 0 1 θ) (circleMap 0 1 θ)) r := by
  have hd := ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hc : HasDerivAt (fun s => fderiv ℝ u (polarPoint s θ))
      (fderiv ℝ (fderiv ℝ u) (polarPoint r θ) (circleMap 0 1 θ)) r :=
    hd.comp_hasDerivAt r (polarPoint_radial_hasDeriv r θ)
  have ha := hc.clm_apply (hasDerivAt_const r (circleMap 0 1 θ))
  simpa only [map_zero, add_zero] using ha

lemma angular_partial_hasDeriv {u : ℂ → ℝ} {r θ : ℝ}
    (hu : ContDiffAt ℝ 2 u (polarPoint r θ)) :
    HasDerivAt (fun φ => u (polarPoint r φ))
      (fderiv ℝ u (polarPoint r θ) (polarPoint r θ * I)) θ :=
  (hu.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt θ
    (polarPoint_angular_hasDeriv r θ)

lemma angular_second_hasDeriv {u : ℂ → ℝ} {r θ : ℝ}
    (hu : ContDiffAt ℝ 2 u (polarPoint r θ)) :
    HasDerivAt (fun φ => fderiv ℝ u (polarPoint r φ) (polarPoint r φ * I))
      (fderiv ℝ (fderiv ℝ u) (polarPoint r θ) (polarPoint r θ * I) (polarPoint r θ * I)
        - fderiv ℝ u (polarPoint r θ) (polarPoint r θ)) θ := by
  have hd := ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have ht := (polarPoint_angular_hasDeriv r θ).mul_const I
  have hmul : (polarPoint r θ * I) * I = -polarPoint r θ := by rw [mul_assoc, I_mul_I, mul_neg_one]
  rw [hmul] at ht
  simpa [sub_eq_add_neg] using
    (hd.comp_hasDerivAt θ (polarPoint_angular_hasDeriv r θ)).clm_apply ht

 

lemma polar_laplacian_identity {u : ℂ → ℝ} (r θ : ℝ) :
    r ^ 2 * (Δ u) (polarPoint r θ) =
      r ^ 2 * fderiv ℝ (fderiv ℝ u) (polarPoint r θ) (circleMap 0 1 θ) (circleMap 0 1 θ) +
      fderiv ℝ (fderiv ℝ u) (polarPoint r θ) (polarPoint r θ * I) (polarPoint r θ * I) := by
  have hh := complex_hessian_rotation (u := u) (polarPoint r θ) (circleMap 0 1 θ)
  have he : polarPoint r θ * I = r • (circleMap 0 1 θ * I) := by
    simp [polarPoint, mul_assoc]
  rw [he]
  simp only [map_smul, smul_apply, smul_eq_mul]
  simp only [norm_circleMap_zero, abs_one, one_pow, one_mul] at hh
  nlinarith

end SLEExactGauge

end

 
section

open Set Filter Metric Complex MeasureTheory
open scoped Topology Laplacian
namespace SLEExactGauge

noncomputable def polarRadialFlux (u : ℂ → ℝ) (R : ℝ) (p : ℝ × ℝ) : ℝ :=
  p.1 * (Real.log R - Real.log p.1) *
    fderiv ℝ u (polarPoint p.1 p.2) (circleMap 0 1 p.2) + u (polarPoint p.1 p.2)

noncomputable def polarAngularFlux (u : ℂ → ℝ) (R : ℝ) (p : ℝ × ℝ) : ℝ :=
  (Real.log R - Real.log p.1) / p.1 *
    fderiv ℝ u (polarPoint p.1 p.2) (polarPoint p.1 p.2 * I)

lemma polarPoint_contDiff : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => polarPoint p.1 p.2) := by
  have hc : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => (p.2 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp contDiff_snd
  have he : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => circleMap 0 1 p.2) := by
    have hExp : ContDiff ℝ ⊤ Complex.exp := Complex.contDiff_exp
    simpa only [circleMap, Complex.ofReal_one, one_mul, zero_add, Function.comp_def] using
      hExp.comp (hc.mul (contDiff_const (c := I)))
  exact contDiff_fst.smul he

lemma polarRadialFlux_differentiableAt {u : ℂ → ℝ} {R r θ : ℝ}
    (hr : r ≠ 0) (hu : ContDiffAt ℝ 2 u (polarPoint r θ)) :
    DifferentiableAt ℝ (polarRadialFlux u R) (r, θ) := by
  have hp := polarPoint_contDiff.differentiable (by simp) (r, θ)
  have hv := (hu.differentiableAt (by norm_num)).comp (r, θ) hp
  have hd := ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).comp (r, θ) hp
  unfold polarRadialFlux
  exact ((differentiableAt_fst.mul ((differentiableAt_const (Real.log R)).sub
    (differentiableAt_fst.log hr))).mul (hd.clm_apply (by unfold circleMap; fun_prop))).add hv

lemma polarAngularFlux_differentiableAt {u : ℂ → ℝ} {R r θ : ℝ}
    (hr : r ≠ 0) (hu : ContDiffAt ℝ 2 u (polarPoint r θ)) :
    DifferentiableAt ℝ (polarAngularFlux u R) (r, θ) := by
  have hp := polarPoint_contDiff.differentiable (by simp) (r, θ)
  have hd := ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).comp (r, θ) hp
  have hfst : DifferentiableAt ℝ (Prod.fst : ℝ × ℝ → ℝ) (r, θ) := differentiableAt_fst
  have hl : DifferentiableAt ℝ (fun p : ℝ × ℝ => (Real.log R - Real.log p.1) / p.1) (r, θ) :=
    by
      simp only [div_eq_mul_inv]
      exact ((differentiableAt_const (Real.log R)).sub (hfst.log hr)).mul (hfst.inv hr)
  exact hl.mul (hd.clm_apply (hp.mul_const I))

lemma polarRadialFlux_radial_hasDeriv {u : ℂ → ℝ} {R r θ : ℝ}
    (hr : r ≠ 0) (hu : ContDiffAt ℝ 2 u (polarPoint r θ)) :
    HasDerivAt (fun s => polarRadialFlux u R (s, θ))
      ((Real.log R - Real.log r) * fderiv ℝ u (polarPoint r θ) (circleMap 0 1 θ) +
        r * (Real.log R - Real.log r) *
          fderiv ℝ (fderiv ℝ u) (polarPoint r θ) (circleMap 0 1 θ) (circleMap 0 1 θ)) r := by
  have hl := (Real.hasDerivAt_log hr).const_sub (Real.log R)
  have hh := (((hasDerivAt_id r).mul hl).mul (radial_second_hasDeriv hu)).add
    (radial_partial_hasDeriv hu)
  convert! hh using 1
  simp only [id_eq, Pi.mul_apply]
  field_simp [hr]
  ring

lemma polarAngularFlux_angular_hasDeriv {u : ℂ → ℝ} {R r θ : ℝ}
    (hu : ContDiffAt ℝ 2 u (polarPoint r θ)) :
    HasDerivAt (fun φ => polarAngularFlux u R (r, φ))
      ((Real.log R - Real.log r) / r *
        (fderiv ℝ (fderiv ℝ u) (polarPoint r θ) (polarPoint r θ * I) (polarPoint r θ * I) -
          fderiv ℝ u (polarPoint r θ) (polarPoint r θ))) θ :=
  (angular_second_hasDeriv hu).const_mul ((Real.log R - Real.log r) / r)

lemma polarGreen_divergence {u : ℂ → ℝ} {R r θ : ℝ}
    (hr : r ≠ 0) (hu : ContDiffAt ℝ 2 u (polarPoint r θ)) :
    fderiv ℝ (polarRadialFlux u R) (r, θ) (1, 0) +
      fderiv ℝ (polarAngularFlux u R) (r, θ) (0, 1) =
        r * (Real.log R - Real.log r) * (Δ u) (polarPoint r θ) := by
  have hf := (polarRadialFlux_differentiableAt (R := R) hr hu).hasFDerivAt.comp_hasDerivAt r
    ((hasDerivAt_id r).prodMk (hasDerivAt_const r θ))
  have hg := (polarAngularFlux_differentiableAt (R := R) hr hu).hasFDerivAt.comp_hasDerivAt θ
    ((hasDerivAt_const θ r).prodMk (hasDerivAt_id θ))
  rw [hf.unique (polarRadialFlux_radial_hasDeriv hr hu),
    hg.unique (polarAngularFlux_angular_hasDeriv hu)]
  have he : fderiv ℝ u (polarPoint r θ) (polarPoint r θ) =
      r * fderiv ℝ u (polarPoint r θ) (circleMap 0 1 θ) := by
    conv_lhs => arg 2; rw [polarPoint]
    simp only [map_smul, smul_eq_mul]
  rw [he]
  have hh := polar_laplacian_identity (u := u) r θ
  apply (mul_right_cancel₀ hr)
  field_simp [hr]
  have hmul := congrArg (fun x : ℝ => (Real.log R - Real.log r) * x) hh
  nlinarith only [hmul]

lemma polarPoint_endpoints (r : ℝ) : polarPoint r (-Real.pi) = polarPoint r Real.pi := by
  have hp := periodic_circleMap 0 1 (-Real.pi)
  have he : -Real.pi + 2 * Real.pi = Real.pi := by ring
  rw [he] at hp
  exact congrArg (fun z : ℂ => r • z) hp.symm

lemma polarAngularFlux_endpoints (u : ℂ → ℝ) (R r : ℝ) :
    polarAngularFlux u R (r, -Real.pi) = polarAngularFlux u R (r, Real.pi) := by
  simp only [polarAngularFlux, polarPoint_endpoints]

end SLEExactGauge

end

 
section

open Set Filter Metric Complex MeasureTheory InnerProductSpace
open scoped Topology Laplacian
namespace SLEExactGauge

lemma plane_laplacian_continuousAt {u : ℂ → ℝ} {z : ℂ} (hu : ContDiffAt ℝ 2 u z) :
    ContinuousAt (Δ u) z := by
  have hh := ((hu.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0)
    (by norm_num)).continuousAt
  have h1 := (hh.clm_apply (continuousAt_const (y := (1 : ℂ)))).clm_apply
    (continuousAt_const (y := (1 : ℂ)))
  have hI := (hh.clm_apply (continuousAt_const (y := I))).clm_apply
    (continuousAt_const (y := I))
  simpa only [laplacian_eq_iteratedFDeriv_complexPlane, iteratedFDeriv_two_apply,
    Fin.isValue, Pi.add_def, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    using h1.add hI

lemma polarPoint_mem_ball {a R r θ : ℝ} (ha : 0 < a) (hR : R < 1)
    (hr : r ∈ Icc a R) : polarPoint r θ ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff, polarPoint_norm, abs_of_pos (ha.trans_le hr.1)]
  exact hr.2.trans_lt hR

 

lemma annulus_green_identity {u : ℂ → ℝ} {a R : ℝ}
    (ha : 0 < a) (haR : a ≤ R) (hR : R < 1)
    (hu : ∀ z ∈ ball (0 : ℂ) 1, ContDiffAt ℝ 2 u z) :
    (∫ r in a..R, ∫ θ in -Real.pi..Real.pi,
      r * (Real.log R - Real.log r) * (Δ u) (polarPoint r θ)) =
      (∫ θ in -Real.pi..Real.pi, u (polarPoint R θ)) -
        ∫ θ in -Real.pi..Real.pi, polarRadialFlux u R (a, θ) := by
  let S := uIcc a R ×ˢ uIcc (-Real.pi) Real.pi
  have hmem (p : ℝ × ℝ) (hp : p ∈ S) : p.1 ≠ 0 ∧ polarPoint p.1 p.2 ∈ ball (0 : ℂ) 1 := by
    have hr : p.1 ∈ Icc a R := by simpa only [uIcc_of_le haR] using hp.1
    exact ⟨(ha.trans_le hr.1).ne', polarPoint_mem_ball ha hR hr⟩
  have hf : ContinuousOn (polarRadialFlux u R) S := fun p hp =>
    (polarRadialFlux_differentiableAt (hmem p hp).1 (hu _ (hmem p hp).2)).continuousAt.continuousWithinAt
  have hg : ContinuousOn (polarAngularFlux u R) S := fun p hp =>
    (polarAngularFlux_differentiableAt (hmem p hp).1 (hu _ (hmem p hp).2)).continuousAt.continuousWithinAt
  have hl : ContinuousOn (fun p : ℝ × ℝ =>
      p.1 * (Real.log R - Real.log p.1) * (Δ u) (polarPoint p.1 p.2)) S := by
    intro p hp
    exact ((continuousAt_fst.mul (continuousAt_const.sub (continuousAt_fst.log (hmem p hp).1))).mul
      ((plane_laplacian_continuousAt (hu _ (hmem p hp).2)).comp (f := fun p : ℝ × ℝ => polarPoint p.1 p.2)
        polarPoint_contDiff.continuous.continuousAt)).continuousWithinAt
  have he : EqOn (fun p : ℝ × ℝ => fderiv ℝ (polarRadialFlux u R) p (1, 0) +
      fderiv ℝ (polarAngularFlux u R) p (0, 1))
      (fun p => p.1 * (Real.log R - Real.log p.1) * (Δ u) (polarPoint p.1 p.2)) S :=
    fun p hp => polarGreen_divergence (hmem p hp).1 (hu _ (hmem p hp).2)
  have hi : IntegrableOn (fun p : ℝ × ℝ => fderiv ℝ (polarRadialFlux u R) p (1, 0) +
      fderiv ℝ (polarAngularFlux u R) p (0, 1)) S :=
    (hl.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).congr_fun
      (fun p hp => (he hp).symm) (measurableSet_uIcc.prod measurableSet_uIcc)
  have hm : Ioo (min a R) (max a R) ×ˢ Ioo (min (-Real.pi) Real.pi) (max (-Real.pi) Real.pi) ⊆ S :=
    prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self
  have hh := integral2_divergence_prod_of_hasFDerivAt (polarRadialFlux u R) (polarAngularFlux u R)
    (fderiv ℝ (polarRadialFlux u R)) (fderiv ℝ (polarAngularFlux u R)) a (-Real.pi) R Real.pi hf hg
    (fun p hp => (polarRadialFlux_differentiableAt (hmem p (hm hp)).1
      (hu _ (hmem p (hm hp)).2)).hasFDerivAt)
    (fun p hp => (polarAngularFlux_differentiableAt (hmem p (hm hp)).1
      (hu _ (hmem p (hm hp)).2)).hasFDerivAt) hi
  have hi_eq : (∫ r in a..R, ∫ θ in -Real.pi..Real.pi,
      fderiv ℝ (polarRadialFlux u R) (r, θ) (1, 0) +
        fderiv ℝ (polarAngularFlux u R) (r, θ) (0, 1)) =
      ∫ r in a..R, ∫ θ in -Real.pi..Real.pi,
        r * (Real.log R - Real.log r) * (Δ u) (polarPoint r θ) := by
    apply intervalIntegral.integral_congr
    intro r hr
    apply intervalIntegral.integral_congr
    intro θ hθ
    exact he ⟨hr, hθ⟩
  rw [hi_eq] at hh
  simpa only [polarAngularFlux_endpoints, sub_self, zero_add,
    polarRadialFlux, sub_self, mul_zero, zero_mul, zero_add] using hh

end SLEExactGauge

end

 
section

open Set Filter Metric Complex MeasureTheory
open scoped Topology Laplacian
namespace SLEExactGauge

lemma annulus_green_le {u : ℂ → ℝ} {a R C M : ℝ}
    (ha : 0 < a) (haR : a ≤ R) (hR : R < 1)
    (hu : ∀ z ∈ ball (0 : ℂ) 1, ContDiffAt ℝ 2 u z)
    (hun : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ u z)
    (hub : ∀ z ∈ ball (0 : ℂ) 1, u z ≤ C)
    (hM : 0 ≤ M) (hgrad : ∀ θ : ℝ, ‖fderiv ℝ u (polarPoint a θ)‖ ≤ M) :
    (∫ r in a..R, ∫ θ in -Real.pi..Real.pi,
      r * (Real.log R - Real.log r) * (-(Δ u) (polarPoint r θ))) ≤
        2 * Real.pi * (C + M * (-a * Real.log a)) := by
  have hRpos := ha.trans_le haR
  have ha_mem (θ : ℝ) : polarPoint a θ ∈ ball (0 : ℂ) 1 :=
    polarPoint_mem_ball ha hR ⟨le_rfl, haR⟩
  have hR_mem (θ : ℝ) : polarPoint R θ ∈ ball (0 : ℂ) 1 :=
    polarPoint_mem_ball ha hR ⟨haR, le_rfl⟩
  have hL : 0 ≤ Real.log R - Real.log a := sub_nonneg.mpr (Real.log_le_log ha haR)
  have hlogR : Real.log R ≤ 0 := Real.log_nonpos hRpos.le hR.le
  have hbound (θ : ℝ) : polarRadialFlux u R (a, θ) ≤ C + M * (-a * Real.log a) := by
    have hb : fderiv ℝ u (polarPoint a θ) (circleMap 0 1 θ) ≤ M := by
      apply (le_abs_self _).trans
      calc
        _ = ‖fderiv ℝ u (polarPoint a θ) (circleMap 0 1 θ)‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖fderiv ℝ u (polarPoint a θ)‖ * ‖circleMap 0 1 θ‖ :=
          (fderiv ℝ u (polarPoint a θ)).le_opNorm _
        _ ≤ M := by simpa using hgrad θ
    have hm := mul_le_mul_of_nonneg_left hb (mul_nonneg ha.le hL)
    have hn := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg ha.le hM) hlogR
    unfold polarRadialFlux
    nlinarith [hub _ (ha_mem θ)]
  have hf : Continuous (fun θ => polarRadialFlux u R (a, θ)) :=
    continuous_iff_continuousAt.mpr fun θ =>
      (polarRadialFlux_differentiableAt ha.ne' (hu _ (ha_mem θ))).continuousAt.comp
        (continuousAt_const.prodMk continuousAt_id)
  have hf_int := hf.intervalIntegrable (μ := volume) (-Real.pi) Real.pi
  have hlo_pi : -Real.pi ≤ Real.pi := by nlinarith [Real.pi_pos]
  have hf_le := intervalIntegral.integral_mono_on hlo_pi hf_int
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => C + M * (-a * Real.log a)) volume
      (-Real.pi) Real.pi) (fun θ _ => hbound θ)
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hf_le
  have huR := intervalIntegral.integral_nonneg_of_forall (μ := volume) hlo_pi (fun θ => hun _ (hR_mem θ))
  have hh := annulus_green_identity ha haR hR hu
  simp only [mul_neg, intervalIntegral.integral_neg]
  linarith

lemma derivative_locally_bounded {u : ℂ → ℝ}
    (hu : ContDiffAt ℝ 2 u 0) :
    ∃ δ M : ℝ, 0 < δ ∧ 0 ≤ M ∧ ∀ z : ℂ, ‖z‖ < δ → ‖fderiv ℝ u z‖ ≤ M := by
  have hc := (hu.fderiv_right (m := 1) (by norm_num)).continuousAt.norm
  have he : ∀ᶠ z in 𝓝 (0 : ℂ), ‖fderiv ℝ u z‖ < ‖fderiv ℝ u 0‖ + 1 :=
    hc (Iio_mem_nhds (show ‖fderiv ℝ u 0‖ < ‖fderiv ℝ u 0‖ + 1 by linarith))
  rcases Metric.eventually_nhds_iff.mp he with ⟨δ, hδ, hd⟩
  refine ⟨δ, ‖fderiv ℝ u 0‖ + 1, hδ, by positivity, ?_⟩
  intro z hz
  exact (hd (by simpa only [dist_zero_right] using hz)).le

end SLEExactGauge

end

 
section

open Set Filter Metric Complex MeasureTheory
open scoped Topology Laplacian ENNReal
namespace SLEExactGauge

noncomputable def annulusDensity (u : ℂ → ℝ) (R : ℝ) (p : ℝ × ℝ) : ℝ :=
  p.1 * (Real.log R - Real.log p.1) * (-(Δ u) (polarPoint p.1 p.2))

def greenRectangle (a R : ℝ) : Set (ℝ × ℝ) := Icc a R ×ˢ Icc (-Real.pi) Real.pi

noncomputable def greenTruncation (u : ℂ → ℝ) (a R : ℝ) : ℝ × ℝ → ℝ :=
  (greenRectangle a R).indicator (annulusDensity u R)

lemma annulusDensity_continuousOn {u : ℂ → ℝ} {a R : ℝ}
    (ha : 0 < a) (hR : R < 1)
    (hu : ∀ z ∈ ball (0 : ℂ) 1, ContDiffAt ℝ 2 u z) :
    ContinuousOn (annulusDensity u R) (greenRectangle a R) := by
  intro p hp
  have hr : p.1 ≠ 0 := (ha.trans_le hp.1.1).ne'
  have hz := polarPoint_mem_ball (θ := p.2) ha hR hp.1
  exact ((continuousAt_fst.mul (continuousAt_const.sub (continuousAt_fst.log hr))).mul
    ((plane_laplacian_continuousAt (hu _ hz)).neg.comp (f := fun p : ℝ × ℝ => polarPoint p.1 p.2)
      polarPoint_contDiff.continuous.continuousAt)).continuousWithinAt

lemma annulusDensity_integrableOn {u : ℂ → ℝ} {a R : ℝ}
    (ha : 0 < a) (hR : R < 1)
    (hu : ∀ z ∈ ball (0 : ℂ) 1, ContDiffAt ℝ 2 u z) :
    IntegrableOn (annulusDensity u R) (greenRectangle a R) :=
  (annulusDensity_continuousOn ha hR hu).integrableOn_compact (isCompact_Icc.prod isCompact_Icc)

lemma greenTruncation_integrable {u : ℂ → ℝ} {a R : ℝ}
    (ha : 0 < a) (hR : R < 1)
    (hu : ∀ z ∈ ball (0 : ℂ) 1, ContDiffAt ℝ 2 u z) :
    Integrable (greenTruncation u a R) :=
  (integrable_indicator_iff (measurableSet_Icc.prod measurableSet_Icc)).mpr
    (annulusDensity_integrableOn ha hR hu)

lemma greenTruncation_nonneg {u : ℂ → ℝ} {a R : ℝ}
    (ha : 0 < a) (hR : R < 1)
    (hΔ : ∀ z ∈ ball (0 : ℂ) 1, (Δ u) z ≤ 0) (p : ℝ × ℝ) :
    0 ≤ greenTruncation u a R p := by
  by_cases hp : p ∈ greenRectangle a R
  · rw [greenTruncation, indicator_of_mem hp]
    have hr := ha.trans_le hp.1.1
    exact mul_nonneg (mul_nonneg hr.le (sub_nonneg.mpr (Real.log_le_log hr hp.1.2)))
      (neg_nonneg.mpr (hΔ _ (polarPoint_mem_ball ha hR hp.1)))
  · simp [greenTruncation, indicator_of_notMem hp]

lemma greenTruncation_integral {u : ℂ → ℝ} {a R : ℝ}
    (ha : 0 < a) (haR : a ≤ R) (hR : R < 1)
    (hu : ∀ z ∈ ball (0 : ℂ) 1, ContDiffAt ℝ 2 u z) :
    (∫ p, greenTruncation u a R p) =
      ∫ r in a..R, ∫ θ in -Real.pi..Real.pi, annulusDensity u R (r, θ) := by
  rw [greenTruncation, greenRectangle, integral_indicator (measurableSet_Icc.prod measurableSet_Icc)]
  have hf := annulusDensity_integrableOn ha hR hu
  rw [Measure.volume_eq_prod] at hf ⊢
  rw [setIntegral_prod _ hf]
  have hpi : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  simp only [intervalIntegral.integral_of_le haR, intervalIntegral.integral_of_le hpi,
    integral_Icc_eq_integral_Ioc]

lemma greenTruncation_lintegral_le {u : ℂ → ℝ} {a R C M : ℝ}
    (ha : 0 < a) (haR : a ≤ R) (hR : R < 1)
    (hu : ∀ z ∈ ball (0 : ℂ) 1, ContDiffAt ℝ 2 u z)
    (hun : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ u z)
    (hub : ∀ z ∈ ball (0 : ℂ) 1, u z ≤ C)
    (hΔ : ∀ z ∈ ball (0 : ℂ) 1, (Δ u) z ≤ 0)
    (hM : 0 ≤ M) (hgrad : ∀ θ : ℝ, ‖fderiv ℝ u (polarPoint a θ)‖ ≤ M) :
    (∫⁻ p, ENNReal.ofReal (greenTruncation u a R p)) ≤
      ENNReal.ofReal (2 * Real.pi * (C + M * (-a * Real.log a))) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (greenTruncation_integrable ha hR hu)
    (Eventually.of_forall (greenTruncation_nonneg ha hR hΔ)), greenTruncation_integral ha haR hR hu]
  exact ENNReal.ofReal_le_ofReal (annulus_green_le ha haR hR hu hun hub hM hgrad)

end SLEExactGauge

end

 
section

open Set Filter Metric Complex MeasureTheory
open scoped Topology Laplacian ENNReal
namespace SLEExactGauge

end SLEExactGauge
end
end
end

end OAI
