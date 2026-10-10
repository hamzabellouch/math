import Mathlib
import OAI.NumberTheory.Jacobsthal.Partitions.BoundedOrderIntervals

namespace OAI

namespace Erdos970

section

open MeasureTheory Set
namespace ErdosMonotoneQuadrature

variable {α : Type*} [MeasurableSpace α]

theorem nonnegative_layercake_discrepancy
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f : α → ℝ) (K E : ℝ) (hK : 0 ≤ K)
    (hf : Measurable f) (hlo : ∀ x, 0 ≤ f x) (hhi : ∀ x, f x ≤ K)
    (hd : ∀ t ∈ Ioc 0 K, |μ.real {x | t ≤ f x} - ν.real {x | t ≤ f x}| ≤ E) :
    |(∫ x, f x ∂μ) - ∫ x, f x ∂ν| ≤ E*K := by
  have hfm : Integrable f μ := Integrable.of_bound hf.aestronglyMeasurable K
    (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs,abs_of_nonneg (hlo x)] using hhi x)
  have hfn : Integrable f ν := Integrable.of_bound hf.aestronglyMeasurable K
    (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs,abs_of_nonneg (hlo x)] using hhi x)
  have hm : Antitone (fun t : ℝ => μ.real {x | t ≤ f x}) := by
    intro s t hst
    exact measureReal_mono (fun x hx => hst.trans hx)
  have hn : Antitone (fun t : ℝ => ν.real {x | t ≤ f x}) := by
    intro s t hst
    exact measureReal_mono (fun x hx => hst.trans hx)
  have him : IntegrableOn (fun t : ℝ => μ.real {x | t ≤ f x}) (Ioc 0 K) :=
    ((hm.antitoneOn (Icc 0 K)).integrableOn_isCompact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hin : IntegrableOn (fun t : ℝ => ν.real {x | t ≤ f x}) (Ioc 0 K) :=
    ((hn.antitoneOn (Icc 0 K)).integrableOn_isCompact isCompact_Icc).mono_set Ioc_subset_Icc_self
  rw [hfm.integral_eq_integral_Ioc_meas_le (Filter.Eventually.of_forall hlo)
      (Filter.Eventually.of_forall hhi),
    hfn.integral_eq_integral_Ioc_meas_le (Filter.Eventually.of_forall hlo)
      (Filter.Eventually.of_forall hhi), ← integral_sub him hin]
  calc
    _ ≤ ∫ t in Ioc 0 K, |μ.real {x | t ≤ f x} - ν.real {x | t ≤ f x}| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ _t in Ioc 0 K, E := integral_mono_ae (him.sub hin).abs (integrable_const E)
      ((ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun t ht => hd t ht))
    _ = E*K := by simp [Real.volume_real_Ioc,max_eq_left hK,mul_comm]

end ErdosMonotoneQuadrature

end

section

open MeasureTheory Set
namespace ErdosMonotoneQuadrature

theorem integrable_layercake_discrepancy
    {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f : α → ℝ) (K E : ℝ) (hK : 0 ≤ K)
    (hfm : Integrable f μ) (hfn : Integrable f ν)
    (hloμ : 0 ≤ᵐ[μ] f) (hloν : 0 ≤ᵐ[ν] f)
    (hhiμ : f ≤ᵐ[μ] (fun _ => K)) (hhiν : f ≤ᵐ[ν] (fun _ => K))
    (hd : ∀ t ∈ Ioc 0 K, |μ.real {x | t ≤ f x} - ν.real {x | t ≤ f x}| ≤ E) :
    |(∫ x, f x ∂μ) - ∫ x, f x ∂ν| ≤ E*K := by
  have hm : Antitone (fun t : ℝ => μ.real {x | t ≤ f x}) := by
    intro s t hst
    exact measureReal_mono (fun x hx => hst.trans hx)
  have hn : Antitone (fun t : ℝ => ν.real {x | t ≤ f x}) := by
    intro s t hst
    exact measureReal_mono (fun x hx => hst.trans hx)
  have him : IntegrableOn (fun t : ℝ => μ.real {x | t ≤ f x}) (Ioc 0 K) :=
    ((hm.antitoneOn (Icc 0 K)).integrableOn_isCompact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hin : IntegrableOn (fun t : ℝ => ν.real {x | t ≤ f x}) (Ioc 0 K) :=
    ((hn.antitoneOn (Icc 0 K)).integrableOn_isCompact isCompact_Icc).mono_set Ioc_subset_Icc_self
  rw [hfm.integral_eq_integral_Ioc_meas_le hloμ hhiμ,
    hfn.integral_eq_integral_Ioc_meas_le hloν hhiν, ← integral_sub him hin]
  calc
    _ ≤ ∫ t in Ioc 0 K, |μ.real {x | t ≤ f x} - ν.real {x | t ≤ f x}| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ _t in Ioc 0 K, E := integral_mono_ae (him.sub hin).abs (integrable_const E)
      ((ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun t ht => hd t ht))
    _ = E*K := by simp [Real.volume_real_Ioc,max_eq_left hK,mul_comm]

theorem monotone_level_orderConnected {f : ℝ → ℝ} {J : Set ℝ}
    (hJ : J.OrdConnected) (hf : MonotoneOn f J ∨ AntitoneOn f J) (t : ℝ) :
    ({x | t ≤ f x} ∩ J).OrdConnected := by
  constructor
  intro x hx y hy z hz
  have hzJ : z ∈ J := hJ.out hx.2 hy.2 hz
  refine ⟨?_,hzJ⟩
  rcases hf with hm | ha
  · exact hx.1.trans (hm hx.2 hzJ hz.1)
  · exact hy.1.trans (ha hzJ hy.2 hz.2)

theorem nonnegative_monotone_integral_discrepancy
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (u v K E : ℝ) (hK : 0 ≤ K) (f : ℝ → ℝ)
    (hf : MonotoneOn f (Icc u v) ∨ AntitoneOn f (Icc u v))
    (hlo : ∀ x ∈ Icc u v, 0 ≤ f x) (hhi : ∀ x ∈ Icc u v, f x ≤ K)
    (hd : ∀ S : Set ℝ, S.OrdConnected → S ⊆ Icc u v → |μ.real S-ν.real S| ≤ E)
    {J : Set ℝ} (hJ : J.OrdConnected) (hsub : J ⊆ Icc u v) :
    |(∫ x in J, f x ∂μ) - ∫ x in J, f x ∂ν| ≤ E*K := by
  have hfm : IntegrableOn f (Icc u v) μ := by
    rcases hf with hm | ha
    · exact hm.integrableOn_isCompact isCompact_Icc
    · exact ha.integrableOn_isCompact isCompact_Icc
  have hfn : IntegrableOn f (Icc u v) ν := by
    rcases hf with hm | ha
    · exact hm.integrableOn_isCompact isCompact_Icc
    · exact ha.integrableOn_isCompact isCompact_Icc
  have hflocal : MonotoneOn f J ∨ AntitoneOn f J := hf.elim
    (fun hm => Or.inl (hm.mono hsub)) (fun ha => Or.inr (ha.mono hsub))
  apply integrable_layercake_discrepancy (μ.restrict J) (ν.restrict J) f K E hK
    (hfm.mono_set hsub) (hfn.mono_set hsub)
  · exact (ae_restrict_iff' hJ.measurableSet).mpr
      (Filter.Eventually.of_forall fun x hx => hlo x (hsub hx))
  · exact (ae_restrict_iff' hJ.measurableSet).mpr
      (Filter.Eventually.of_forall fun x hx => hlo x (hsub hx))
  · exact (ae_restrict_iff' hJ.measurableSet).mpr
      (Filter.Eventually.of_forall fun x hx => hhi x (hsub hx))
  · exact (ae_restrict_iff' hJ.measurableSet).mpr
      (Filter.Eventually.of_forall fun x hx => hhi x (hsub hx))
  · intro t _ht
    rw [measureReal_restrict_apply' hJ.measurableSet,measureReal_restrict_apply' hJ.measurableSet]
    exact hd _ (monotone_level_orderConnected hJ hflocal t) (fun x hx => hsub hx.2)

end ErdosMonotoneQuadrature

end

section

open MeasureTheory Set
namespace ErdosMonotoneQuadrature

noncomputable def reciprocalWeight (u x : ℝ) : ℝ := (max u x)⁻¹

theorem reciprocalWeight_pos {u : ℝ} (hu : 0 < u) (x : ℝ) :
    0 < reciprocalWeight u x := inv_pos.mpr (hu.trans_le (le_max_left _ _))

theorem reciprocalWeight_le {u : ℝ} (hu : 0 < u) (x : ℝ) :
    reciprocalWeight u x ≤ u⁻¹ := inv_anti₀ hu (le_max_left _ _)

theorem reciprocalWeight_continuous {u : ℝ} (hu : 0 < u) :
    Continuous (reciprocalWeight u) :=
  (continuous_const.max continuous_id).inv₀ (fun x => ne_of_gt (hu.trans_le (le_max_left u x)))

theorem reciprocalWeight_antitone {u : ℝ} (hu : 0 < u) :
    Antitone (reciprocalWeight u) := by
  intro x y hxy
  exact inv_anti₀ (hu.trans_le (le_max_left u x)) (max_le_max_left u hxy)

theorem reciprocalWeight_eq {u x : ℝ} (hx : u ≤ x) : reciprocalWeight u x=x⁻¹ := by
  simp only [reciprocalWeight,max_eq_right hx]

noncomputable def reciprocalMeasure (μ : Measure ℝ) (u : ℝ) : Measure ℝ :=
  μ.withDensity (fun x => ENNReal.ofReal (reciprocalWeight u x))

theorem reciprocalMeasure_finite (μ : Measure ℝ) [IsFiniteMeasure μ] {u : ℝ} (hu : 0 < u) :
    IsFiniteMeasure (reciprocalMeasure μ u) := by
  have h : Integrable (reciprocalWeight u) μ :=
    Integrable.of_bound (reciprocalWeight_continuous hu).measurable.aestronglyMeasurable u⁻¹
      (Filter.Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs,abs_of_pos (reciprocalWeight_pos hu x)] using reciprocalWeight_le hu x)
  exact isFiniteMeasure_withDensity_ofReal h.hasFiniteIntegral

theorem reciprocalMeasure_integral (μ : Measure ℝ) {u : ℝ} (hu : 0 < u)
    (g : ℝ → ℝ) {J : Set ℝ} (hJ : MeasurableSet J) :
    (∫ x in J, g x ∂reciprocalMeasure μ u) = ∫ x in J, reciprocalWeight u x*g x ∂μ := by
  have h := setIntegral_withDensity_eq_setIntegral_toReal_smul
    (μ:=μ) ((reciprocalWeight_continuous hu).measurable.ennreal_ofReal)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) g hJ
  simpa only [reciprocalMeasure,ENNReal.toReal_ofReal (reciprocalWeight_pos hu _).le,smul_eq_mul] using h

theorem reciprocalMeasure_real (μ : Measure ℝ) {u : ℝ} (hu : 0 < u)
    {J : Set ℝ} (hJ : MeasurableSet J) :
    (reciprocalMeasure μ u).real J = ∫ x in J, reciprocalWeight u x ∂μ := by
  simpa only [integral_const,smul_eq_mul,mul_one,measureReal_restrict_apply_univ] using
    reciprocalMeasure_integral μ hu (fun _ => (1:ℝ)) hJ

theorem reciprocalMeasure_discrepancy
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (u v E : ℝ) (hu : 0 < u)
    (hd : ∀ S : Set ℝ, S.OrdConnected → S ⊆ Icc u v → |μ.real S-ν.real S| ≤ E)
    {J : Set ℝ} (hJ : J.OrdConnected) (hsub : J ⊆ Icc u v) :
    |(reciprocalMeasure μ u).real J-(reciprocalMeasure ν u).real J| ≤ E*u⁻¹ := by
  rw [reciprocalMeasure_real μ hu hJ.measurableSet,reciprocalMeasure_real ν hu hJ.measurableSet]
  exact nonnegative_monotone_integral_discrepancy μ ν u v u⁻¹ E (inv_nonneg.mpr hu.le)
    (reciprocalWeight u) (Or.inr ((reciprocalWeight_antitone hu).antitoneOn _))
    (fun x _ => (reciprocalWeight_pos hu x).le) (fun x _ => reciprocalWeight_le hu x) hd hJ hsub

end ErdosMonotoneQuadrature

end

section

open MeasureTheory Set
namespace ErdosMonotoneQuadrature

theorem signed_monotone_integral_discrepancy
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (u v D E : ℝ) (hD : 0 ≤ D) (g : ℝ → ℝ)
    (hg : MonotoneOn g (Icc u v) ∨ AntitoneOn g (Icc u v))
    (hbound : ∀ x ∈ Icc u v, |g x| ≤ D)
    (hd : ∀ S : Set ℝ, S.OrdConnected → S ⊆ Icc u v → |μ.real S-ν.real S| ≤ E)
    {J : Set ℝ} (hJ : J.OrdConnected) (hsub : J ⊆ Icc u v) :
    |(∫ x in J, g x ∂μ) - ∫ x in J, g x ∂ν| ≤ 3*E*D := by
  have hgm : IntegrableOn g J μ := by
    rcases hg with hm | ha
    · exact (hm.integrableOn_isCompact isCompact_Icc).mono_set hsub
    · exact (ha.integrableOn_isCompact isCompact_Icc).mono_set hsub
  have hgn : IntegrableOn g J ν := by
    rcases hg with hm | ha
    · exact (hm.integrableOn_isCompact isCompact_Icc).mono_set hsub
    · exact (ha.integrableOn_isCompact isCompact_Icc).mono_set hsub
  have hshift : MonotoneOn (fun x => g x+D) (Icc u v) ∨
      AntitoneOn (fun x => g x+D) (Icc u v) := by
    rcases hg with hm | ha
    · exact Or.inl (fun x hx y hy hxy => by dsimp; linarith [hm hx hy hxy])
    · exact Or.inr (fun x hx y hy hxy => by dsimp; linarith [ha hx hy hxy])
  have hpos : ∀ x ∈ Icc u v, 0 ≤ g x+D := by
    intro x hx
    have h := (abs_le.mp (hbound x hx)).1
    linarith
  have hhi : ∀ x ∈ Icc u v, g x+D ≤ 2*D := by
    intro x hx
    have h := (abs_le.mp (hbound x hx)).2
    linarith
  have h := nonnegative_monotone_integral_discrepancy μ ν u v (2*D) E
    (by positivity) (fun x => g x+D) hshift hpos hhi hd hJ hsub
  have heq : (∫ x in J, g x ∂μ) - ∫ x in J, g x ∂ν =
      ((∫ x in J, g x+D ∂μ) - ∫ x in J, g x+D ∂ν) - D*(μ.real J-ν.real J) := by
    rw [integral_add hgm (integrable_const D),integral_add hgn (integrable_const D)]
    simp only [integral_const,smul_eq_mul,measureReal_restrict_apply_univ]
    ring
  rw [heq]
  calc
    _ ≤ |(∫ x in J, g x+D ∂μ) - ∫ x in J, g x+D ∂ν| + |D*(μ.real J-ν.real J)| :=
      abs_sub _ _
    _ ≤ E*(2*D) + D*E := add_le_add h (by
      rw [abs_mul,abs_of_nonneg hD]
      exact mul_le_mul_of_nonneg_left (hd J hJ hsub) hD)
    _ = 3*E*D := by ring

end ErdosMonotoneQuadrature

end

section

open MeasureTheory Set
namespace ErdosMonotoneQuadrature

theorem weighted_monotone_discrepancy
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (u v D E : ℝ) (hu : 0 < u) (hD : 0 ≤ D) (g : ℝ → ℝ)
    (hg : MonotoneOn g (Icc u v) ∨ AntitoneOn g (Icc u v))
    (hbound : ∀ x ∈ Icc u v, |g x| ≤ D)
    (hd : ∀ S : Set ℝ, S.OrdConnected → S ⊆ Icc u v → |μ.real S-ν.real S| ≤ E)
    {J : Set ℝ} (hJ : J.OrdConnected) (hsub : J ⊆ Icc u v) :
    |(∫ x in J, g x/x ∂μ) - ∫ x in J, g x/x ∂ν| ≤ 3*E*D/u := by
  let := reciprocalMeasure_finite μ hu
  let := reciprocalMeasure_finite ν hu
  have h := signed_monotone_integral_discrepancy (reciprocalMeasure μ u)
    (reciprocalMeasure ν u) u v D (E*u⁻¹) hD g hg hbound
    (fun S hS hs => reciprocalMeasure_discrepancy μ ν u v E hu hd hS hs) hJ hsub
  have hm : (∫ x in J, g x ∂reciprocalMeasure μ u) = ∫ x in J, g x/x ∂μ := by
    rw [reciprocalMeasure_integral μ hu g hJ.measurableSet]
    apply setIntegral_congr_fun hJ.measurableSet
    intro x hx
    dsimp only
    rw [reciprocalWeight_eq (hsub hx).1]
    simp only [div_eq_mul_inv,mul_comm]
  have hn : (∫ x in J, g x ∂reciprocalMeasure ν u) = ∫ x in J, g x/x ∂ν := by
    rw [reciprocalMeasure_integral ν hu g hJ.measurableSet]
    apply setIntegral_congr_fun hJ.measurableSet
    intro x hx
    dsimp only
    rw [reciprocalWeight_eq (hsub hx).1]
    simp only [div_eq_mul_inv,mul_comm]
  rw [hm,hn] at h
  convert! h using 1
  ring

theorem weighted_from_all_endpoint_intervals
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (u v D E : ℝ) (hu : 0 < u) (hD : 0 ≤ D) (hE : 0 ≤ E) (g : ℝ → ℝ)
    (hg : MonotoneOn g (Icc u v) ∨ AntitoneOn g (Icc u v))
    (hbound : ∀ x ∈ Icc u v, |g x| ≤ D)
    (hinterval : ∀ a b : ℝ, u ≤ a → a ≤ b → b ≤ v →
      |μ.real (Icc a b)-ν.real (Icc a b)| ≤ E ∧
      |μ.real (Ico a b)-ν.real (Ico a b)| ≤ E ∧
      |μ.real (Ioc a b)-ν.real (Ioc a b)| ≤ E ∧
      |μ.real (Ioo a b)-ν.real (Ioo a b)| ≤ E)
    {J : Set ℝ} (hJ : J.OrdConnected) (hsub : J ⊆ Icc u v) :
    |(∫ x in J, g x/x ∂μ) - ∫ x in J, g x/x ∂ν| ≤ 3*E*D/u :=
  weighted_monotone_discrepancy μ ν u v D E hu hD g hg hbound
    (fun _ hS hs => orderConnected_measure_discrepancy μ ν u v E hE hinterval hS hs) hJ hsub

end ErdosMonotoneQuadrature

end

end Erdos970

end OAI
