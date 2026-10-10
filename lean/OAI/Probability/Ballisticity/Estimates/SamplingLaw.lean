import Mathlib
import OAI.Probability.Ballisticity.Estimates.Sampling

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Classical
namespace DirectionalTransience

instance actualArray_borel {d : ℕ} (e : Direction d) : BorelSpace (ActualEpisodeArray e) := by
  have : BorelSpace (ℤ → StationaryCompact.MarkSpace) := inferInstance
  have : BorelSpace ((StationaryCompact.Label×StationaryCompact.Label) → OnePoint (HorizontalSpace e)) := inferInstance
  have : BorelSpace ((ℤ×StationaryCompact.Label×HorizontalSpace e) → Set.Icc (0:ℝ) 1) := inferInstance
  have : BorelSpace ((ℤ×ℕ×ℕ×ℕ×HorizontalSpace e) → Row d) := inferInstance
  have : BorelSpace (((ℤ×StationaryCompact.Label×HorizontalSpace e) → Set.Icc (0:ℝ) 1) ×
      ((ℤ×ℕ×ℕ×ℕ×HorizontalSpace e) → Row d)) := inferInstance
  have : SecondCountableTopology (((StationaryCompact.Label×StationaryCompact.Label) → OnePoint (HorizontalSpace e))) := inferInstance
  have : BorelSpace ((((StationaryCompact.Label×StationaryCompact.Label) → OnePoint (HorizontalSpace e))) ×
      (((ℤ×StationaryCompact.Label×HorizontalSpace e) → Set.Icc (0:ℝ) 1) ×
      ((ℤ×ℕ×ℕ×ℕ×HorizontalSpace e) → Row d))) := inferInstance
  have : SecondCountableTopology (ℤ → StationaryCompact.MarkSpace) := inferInstance
  unfold ActualEpisodeArray StationaryCompact.EpisodeArray
  infer_instance

lemma restrict_compProd_fst {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    (Q : Measure Ω) [SFinite Q] (K : Kernel Ω A) [IsSFiniteKernel K]
    (s : Set Ω) (hs : MeasurableSet s) :
    (Q.compProd K).restrict (Prod.fst ⁻¹' s)=(Q.restrict s).compProd K := by
  ext B hB
  rw [Measure.restrict_apply hB,Measure.compProd_apply (hB.inter (hs.preimage measurable_fst)),
    Measure.compProd_apply hB,←lintegral_indicator hs]
  apply lintegral_congr
  intro ω
  by_cases hω : ω∈s
  · have he : Prod.mk ω ⁻¹' Prod.fst ⁻¹' s = (Set.univ : Set A) := by
      ext a
      simp [hω]
    simp [Set.indicator_of_mem hω,he]
  · have he : Prod.mk ω ⁻¹' Prod.fst ⁻¹' s = (∅ : Set A) := by
      ext a
      simp [hω]
    simp [Set.indicator_of_notMem hω,he]

instance episodeInputLaw_finite {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i) :
    IsFiniteMeasure (episodeInputLaw e ν Q t ht) := by unfold episodeInputLaw; infer_instance

lemma episodeInputLaw_restrict {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (s : Set (Environment d)) (hs : MeasurableSet s) :
    (episodeInputLaw e ν Q t ht).restrict {X | X.1.1∈s}=
      episodeInputLaw e ν (Q.restrict s) t ht := by
  unfold episodeInputLaw
  rw [←restrict_compProd_fst Q (globalEpisodeAnchors e t ht) s hs,
    Measure.restrict_prod_eq_prod_univ]
  congr 1
  ext X
  simp

lemma actualArray_integrable {d : ℕ} (e : Direction d)
    (μ : Measure (EpisodeInput e)) [IsFiniteMeasure μ]
    (t J : Environment d → ℤ → ℕ)
    (ht : ∀ i, Measurable fun ω => t ω i) (hJ : ∀ i, Measurable fun ω => J ω i)
    (F : C(ActualEpisodeArray e,ℝ)) : Integrable (fun X => F (actualArrayMap e t J X)) μ := by
  obtain ⟨C,hC⟩ := isCompact_univ.exists_bound_of_continuousOn F.continuous.continuousOn
  apply (integrable_const C).mono'
    ((F.continuous.measurable.comp (actualArrayMap_measurable e t J ht hJ)).aestronglyMeasurable)
  exact Eventually.of_forall fun X => hC _ (Set.mem_univ _)

lemma actual_array_sampling_sq_law {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t J : Environment d → ℤ → ℕ)
    (ht : ∀ i, Measurable fun ω => t ω i) (hJ : ∀ i, Measurable fun ω => J ω i)
    (p : ℤ×ℕ) (j : ℤ) (z : HorizontalSpace e) (n : ℕ) (hn : 0<n) :
    (∫ X, (arraySamplingError e p j z n (actualArrayMap e t J X))^2
      ∂episodeInputLaw e ν Q t ht)≤Q.real Set.univ*(n:ℝ)⁻¹ := by
  let F : C(ActualEpisodeArray e,ℝ) := ⟨fun Y => (arraySamplingError e p j z n Y)^2,by fun_prop⟩
  have hi := actualArray_integrable e (episodeInputLaw e ν Q t ht) t J ht hJ F
  change (∫ X, F (actualArrayMap e t J X) ∂((Q.compProd (globalEpisodeAnchors e t ht)).prod
    (episodeAuxiliaryLaw e ν)))≤_
  rw [integral_prod_symm _ hi]
  have hc (ξ : EpisodeAuxiliary e) :
      (∫ w, F (actualArrayMap e t J (w,ξ)) ∂Q.compProd (globalEpisodeAnchors e t ht))≤
        Q.real Set.univ*(n:ℝ)⁻¹ := by
    have hm : Measurable (fun w => F (actualArrayMap e t J (w,ξ))) :=
      (F.continuous.measurable.comp (actualArrayMap_measurable e t J ht hJ)).comp measurable_prodMk_right
    have hib : Integrable (fun w => F (actualArrayMap e t J (w,ξ)))
        (Q.compProd (globalEpisodeAnchors e t ht)) := by
      apply (integrable_const (1:ℝ)).mono' hm.aestronglyMeasurable
      filter_upwards [] with w
      change ‖(arraySamplingError e p j z n (actualArrayMap e t J (w,ξ)))^2‖≤1
      rw [norm_pow]
      exact (pow_le_pow_left₀ (norm_nonneg _) (arraySamplingError_bound _ _ _ _ _ _) 2).trans_eq (one_pow _)
    rw [Measure.integral_compProd hib]
    have hbound ω := actual_array_sampling_sq_conditional e t J ht ω ξ p j z n hn
    calc
      _ ≤ (∫ _ω, (n:ℝ)⁻¹ ∂Q) := by
        apply integral_mono_of_nonneg (Eventually.of_forall fun ω => integral_nonneg fun U => sq_nonneg _)
          (integrable_const _)
        exact Eventually.of_forall hbound
      _ = _ := by simp [integral_const,smul_eq_mul]
  have hnon : 0≤Q.real Set.univ*(n:ℝ)⁻¹ := mul_nonneg measureReal_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
  calc
    _ ≤ (∫ _ξ, Q.real Set.univ*(n:ℝ)⁻¹ ∂episodeAuxiliaryLaw e ν) := by
      apply integral_mono_of_nonneg (Eventually.of_forall fun ξ => integral_nonneg fun w => sq_nonneg _)
        (integrable_const _)
      exact Eventually.of_forall hc
    _ = _ := by simp [integral_const,smul_eq_mul]

lemma actual_array_sampling_test_law {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t J : Environment d → ℤ → ℕ)
    (ht : ∀ i, Measurable fun ω => t ω i) (hJ : ∀ i, Measurable fun ω => J ω i)
    (p q : ℤ×ℕ) (hpq : p≠q) (z : HorizontalSpace e) (g : C(ℝ,ℝ)) :
    (∫ X, g (arrayProfileTest e q.1 p z (actualArrayMap e t J X))*
      (arrayOffsetTest e p q z (actualArrayMap e t J X)-
        arrayProfileTest e q.1 p z (actualArrayMap e t J X))
      ∂episodeInputLaw e ν Q t ht)=0 := by
  let F : C(ActualEpisodeArray e,ℝ) := ⟨fun Y => g (arrayProfileTest e q.1 p z Y)*
      (arrayOffsetTest e p q z Y-arrayProfileTest e q.1 p z Y),by fun_prop⟩
  have hi := actualArray_integrable e (episodeInputLaw e ν Q t ht) t J ht hJ F
  change (∫ X, F (actualArrayMap e t J X) ∂((Q.compProd (globalEpisodeAnchors e t ht)).prod
    (episodeAuxiliaryLaw e ν)))=0
  rw [integral_prod_symm _ hi]
  have hz (ξ : EpisodeAuxiliary e) :
      (∫ w, F (actualArrayMap e t J (w,ξ)) ∂Q.compProd (globalEpisodeAnchors e t ht))=0 := by
    obtain ⟨C,hC⟩ := isCompact_univ.exists_bound_of_continuousOn F.continuous.continuousOn
    have hm : Measurable (fun w => F (actualArrayMap e t J (w,ξ))) :=
      (F.continuous.measurable.comp (actualArrayMap_measurable e t J ht hJ)).comp measurable_prodMk_right
    have hib := (integrable_const C (μ:=Q.compProd (globalEpisodeAnchors e t ht))).mono' hm.aestronglyMeasurable
      (Eventually.of_forall fun w => hC _ (Set.mem_univ _))
    rw [Measure.integral_compProd hib]
    have he ω : (∫ U, F (actualArrayMap e t J ((ω,U),ξ)) ∂globalEpisodeAnchors e t ht ω)=0 :=
      actual_array_sampling_test_conditional e t J ht ω ξ p q hpq z g
    simp only [he,integral_zero]
  simp only [hz,integral_zero]

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
namespace DirectionalTransience

lemma arrayOffsetTest_shift {d : ℕ} (e : Direction d) (p q : ℤ×ℕ)
    (z : HorizontalSpace e) (Y : ActualEpisodeArray e) :
    arrayOffsetTest e p q z (StationaryCompact.shift Y)=
      arrayOffsetTest e (p.1+1,p.2) (q.1+1,q.2) z Y := rfl

lemma arrayProfileTest_shift {d : ℕ} (e : Direction d) (j : ℤ) (p : ℤ×ℕ)
    (z : HorizontalSpace e) (Y : ActualEpisodeArray e) :
    arrayProfileTest e j p z (StationaryCompact.shift Y)=
      arrayProfileTest e (j+1) (p.1+1,p.2) z Y := rfl

lemma arrayOffsetTest_iterate {d : ℕ} (e : Direction d) (p q : ℤ×ℕ)
    (z : HorizontalSpace e) (Y : ActualEpisodeArray e) (r : ℕ) :
    arrayOffsetTest e p q z (StationaryCompact.shift^[r] Y)=
      arrayOffsetTest e (p.1+r,p.2) (q.1+r,q.2) z Y := by
  induction r generalizing p q with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply',arrayOffsetTest_shift,ih]
    simp only [Nat.cast_add,Nat.cast_one,add_left_comm,add_comm]

lemma arrayProfileTest_iterate {d : ℕ} (e : Direction d) (j : ℤ) (p : ℤ×ℕ)
    (z : HorizontalSpace e) (Y : ActualEpisodeArray e) (r : ℕ) :
    arrayProfileTest e j p z (StationaryCompact.shift^[r] Y)=
      arrayProfileTest e (j+r) (p.1+r,p.2) z Y := by
  induction r generalizing j p with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply',arrayProfileTest_shift,ih]
    simp only [Nat.cast_add,Nat.cast_one,add_left_comm,add_comm]

lemma arraySamplingError_iterate {d : ℕ} (e : Direction d) (p : ℤ×ℕ) (j : ℤ)
    (z : HorizontalSpace e) (n r : ℕ) (Y : ActualEpisodeArray e) :
    arraySamplingError e p j z n (StationaryCompact.shift^[r] Y)=
      arraySamplingError e (p.1+r,p.2) (j+r) z n Y := by
  change (n:ℝ)⁻¹*(∑ b∈Finset.range n, arrayOffsetTest e p (j,b) z (StationaryCompact.shift^[r] Y))-
    arrayProfileTest e j p z (StationaryCompact.shift^[r] Y)=_
  simp only [arrayOffsetTest_iterate,arrayProfileTest_iterate]
  rfl

end DirectionalTransience

end

end OAI
