import Mathlib
import OAI.Geometry.CAT0Fillings.Slicing.ProfileIntegral
import OAI.Geometry.CAT0Fillings.Mass.Duality

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal BigOperators

namespace CAT0Fillings
namespace BorelCoefficients
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

abbrev CoefficientList (N : ℕ) :=
  {b : Fin N → C(X,ℝ) // (∀ i, BoundedLip (b i)) ∧ ∀ x, ∑ i, |b i x| ≤ 1}

instance coefficientList_nonempty (N : ℕ) : Nonempty (CoefficientList (X := X) N) := by
  refine ⟨⟨fun _ => 0,?_,?_⟩⟩
  · intro i
    exact ⟨⟨0,LipschitzWith.const 0⟩,0,by simp⟩
  · simp

lemma coefficientList_eval_continuous {k N : ℕ} {T : Functional X k} (hT : IsMetricCurrent T)
    (π : Fin N → Fin k → X → ℝ) (hπ : ∀ j i, LipschitzWith 1 (π j i)) :
    Continuous (fun b : CoefficientList (X := X) N => ∑ i, T (b.val i) (π i)) := by
  apply continuous_finsetSum
  intro i hi
  apply LipschitzWith.continuous (K := ⟨mass T,mass_nonneg _⟩)
  apply LipschitzWith.of_dist_le_mul
  intro b c
  have hh := Foundations.IsMetricCurrent.first_difference_bound hT (b.property.1 i) (c.property.1 i)
    (π i) 1 (hπ i) (nndist b c) (fun x =>
      (ContinuousMap.dist_apply_le_dist x).trans (dist_le_pi_dist b.val c.val i))
  change |T (b.val i) (π i)-T (c.val i) (π i)| ≤ mass T*dist b c
  simpa only [Real.dist_eq,NNReal.coe_one,one_pow,one_mul,coe_nndist,mul_comm] using hh

lemma finite_list_le_mass {k N : ℕ} {T : Functional X k} (hT : IsMetricCurrent T)
    (b : Fin N → X → ℝ) (hb : ∀ i, BoundedLip (b i))
    (hbudget : ∀ x, ∑ i, |b i x| ≤ 1)
    (π : Fin N → Fin k → X → ℝ) (hπ : ∀ j i, LipschitzWith 1 (π j i)) :
    (∑ i, T (b i) (π i)) ≤ mass T := by
  let μ := MassMeasure.currentMassMeasure hT
  have hi i : Integrable (fun x => |b i x|) μ := (integrable_boundedLip μ (hb i)).abs
  calc (∑ i, T (b i) (π i)) ≤ ∑ i, |T (b i) (π i)| :=
        Finset.sum_le_sum fun i _ => le_abs_self _
       _ ≤ ∑ i, ∫ x, |b i x| ∂μ := Finset.sum_le_sum fun i _ =>
        MassMeasure.currentMassMeasure_controls hT _ _ (hb i) (hπ i)
       _ = ∫ x, ∑ i, |b i x| ∂μ := (integral_finsetSum _ (fun i _ => hi i)).symm
       _ ≤ ∫ x, (1:ℝ) ∂μ := integral_mono (integrable_finsetSum _ fun i _ => hi i)
          (integrable_const _) hbudget
       _ = mass T := by simpa using MassMeasure.currentMassMeasure_total hT

theorem exists_countable_mass_lists (k : ℕ) :
    ∃ (π : ℕ → Fin k → X → ℝ) (b : (N : ℕ) → ℕ → Fin (N+1) → X → ℝ),
      (∀ j i, LipschitzWith 1 (π j i)) ∧
      (∀ N j i, BoundedLip (b N j i)) ∧
      (∀ N j x, ∑ i, |b N j i x| ≤ 1) ∧
      ∀ {T : Functional X k}, IsMetricCurrent T → ∀ C : ℝ,
        mass T ≤ C ↔ ∀ N j, (∑ i : Fin (N+1), T (b N j i) (π i)) ≤ C := by
  classical
  obtain ⟨π,hπ,hspec⟩ := exists_mass_spectrum (X := X) k
  choose bs hbs using fun N : ℕ => TopologicalSpace.exists_dense_seq (CoefficientList (X := X) (N+1))
  refine ⟨π,fun N j i => (bs N j).val i,hπ,fun N j => (bs N j).property.1,
    fun N j => (bs N j).property.2,?_⟩
  intro T hT C
  constructor
  · intro h N j
    exact (finite_list_le_mass hT _ (bs N j).property.1 (bs N j).property.2
      (fun i => π i) (fun i => hπ i)).trans h
  · intro h
    obtain ⟨ρ,hρm,hρ1,hρ,hmass⟩ := hspec hT
    apply mass_le_of_finite_tests hT π hπ ρ hρm hρ1 hρ hmass
    intro N a ha hbudget
    let q : CoefficientList (X := X) (N+1) := ⟨fun i => ⟨a i,(ha i).continuous⟩,ha,hbudget⟩
    change (∑ i, T (q.val i) (π i)) ≤ C
    apply (hbs N).induction_on (p := fun r : CoefficientList (X := X) (N+1) =>
      (∑ i, T (r.val i) (π i)) ≤ C) q
    · exact isClosed_le (coefficientList_eval_continuous hT _ (fun i => hπ i)) continuous_const
    · exact h N

theorem ae_mass_le_of_listwise {A : Type*} [MeasurableSpace A] (ν : Measure A)
    {k : ℕ} {T : A → Functional X k} {C : A → ℝ}
    (hT : ∀ᵐ a ∂ν, IsMetricCurrent (T a))
    (h : ∀ N (b : Fin (N+1) → X → ℝ) (π : Fin (N+1) → Fin k → X → ℝ),
      (∀ i, BoundedLip (b i)) → (∀ x, ∑ i, |b i x| ≤ 1) →
      (∀ j i, LipschitzWith 1 (π j i)) →
      ∀ᵐ a ∂ν, (∑ i, T a (b i) (π i)) ≤ C a) :
    ∀ᵐ a ∂ν, mass (T a) ≤ C a := by
  obtain ⟨π,b,hπ,hb,hbudget,hmass⟩ := exists_countable_mass_lists (X := X) k
  have hh : ∀ᵐ a ∂ν, ∀ N j, (∑ i : Fin (N+1), T a (b N j i) (π i)) ≤ C a :=
    ae_all_iff.mpr fun N => ae_all_iff.mpr fun j =>
      h N (b N j) (fun i => π i) (hb N j) (hbudget N j) (fun i => hπ i)
  filter_upwards [hT,hh] with a hta ha
  exact (hmass hta (C a)).mpr ha

end BorelCoefficients
end CAT0Fillings
end

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.SmoothCutoff

lemma dprofile_integrable_measure (μ : Measure ℝ) [IsFiniteMeasure μ] (a : ℝ≥0) (t : ℝ) :
    Integrable (dprofile a t) μ := by
  obtain ⟨C,hC⟩ := exists_profile_bounds
  exact Integrable.of_bound (hC a t).2.1.continuous.aestronglyMeasurable ((C*a:ℝ≥0):ℝ)
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using (hC a t).2.2 x)

theorem ae_tendsto_dprofile_measure (μ : Measure ℝ) [IsFiniteMeasure μ] :
    ∀ᵐ t : ℝ, Tendsto (fun n : ℕ => ∫ x : ℝ,
      dprofile ((n:ℝ≥0)+1) t x ∂μ) atTop (𝓝 ((μ.rnDeriv volume t).toReal)) := by
  obtain ⟨C,hC⟩ := exists_profile_bounds
  let σ := μ.singularPart volume
  let f : ℝ → ℝ := fun x => (μ.rnDeriv volume x).toReal
  have hf : Integrable f := μ.integrable_toReal_rnDeriv
  let a : ℕ → ℝ≥0 := fun n => (n:ℝ≥0)+1
  let r : ℕ → ℝ := fun n => ((a n:ℝ))⁻¹
  have hap n : 0 < a n := by dsimp [a]; positivity
  have harp n : 0 < (a n:ℝ) := hap n
  have hrp n : 0 < r n := inv_pos.mpr (harp n)
  have hrt : Tendsto r atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,Eventually.of_forall fun n => hrp n⟩
    exact tendsto_inv_atTop_zero.comp
      (show Tendsto (fun n : ℕ => (a n:ℝ)) atTop atTop from by
        simpa only [a,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one] using
          tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R := ℝ)))
  filter_upwards [ae_tendsto_dprofile_integral hf,Besicovitch.ae_tendsto_rnDeriv σ volume,
    μ.rnDeriv_singularPart volume] with t ht hσ hz
  have hz' : σ.rnDeriv volume t = 0 := hz
  have hs : Tendsto (fun n => ∫ x : ℝ, dprofile (a n) t x ∂σ) atTop (𝓝 0) := by
    have hratio := (ENNReal.continuousAt_toReal (by simpa only [hz'] using ENNReal.zero_ne_top)).tendsto.comp
      (hσ.comp hrt)
    have hbound n : ‖∫ x : ℝ, dprofile (a n) t x ∂σ‖ ≤
        (2*(C:ℝ)) * (σ (closedBall t (r n))/volume (closedBall t (r n))).toReal := by
      have hnz (x : ℝ) (hx : x ∉ closedBall t (r n)) : dprofile (a n) t x = 0 := by
        apply dprofile_zero (hap n)
        intro hi
        apply hx
        rw [Real.closedBall_eq_Icc]
        change t-r n ≤ x ∧ x ≤ t+r n
        exact ⟨by linarith [hi.1,hrp n],hi.2⟩
      calc
        _ ≤ ∫ x : ℝ, ‖dprofile (a n) t x‖ ∂σ := norm_integral_le_integral_norm _
        _ = ∫ x in closedBall t (r n), ‖dprofile (a n) t x‖ ∂σ :=
          (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by rw [hnz x hx,norm_zero])).symm
        _ ≤ ∫ _x in closedBall t (r n), (C:ℝ)*(a n:ℝ) ∂σ := by
          apply integral_mono (dprofile_integrable_measure σ _ _).norm.integrableOn (integrable_const _)
          intro x
          simpa only [Real.norm_eq_abs,NNReal.coe_mul] using (hC (a n) t).2.2 x
        _ = _ := by
          rw [integral_const,measureReal_def,Measure.restrict_apply_univ,smul_eq_mul,ENNReal.toReal_div]
          change σ.real (closedBall t (r n)) * ((C:ℝ)*(a n:ℝ)) =
            (2*(C:ℝ))*(σ.real (closedBall t (r n))/volume.real (closedBall t (r n)))
          rw [Real.volume_real_closedBall (hrp n).le]
          dsimp only [r]
          field_simp
    apply squeeze_zero_norm hbound
    simpa only [hz',ENNReal.toReal_zero,mul_zero,Function.comp_apply] using hratio.const_mul (2*(C:ℝ))
  have heq n : (∫ x : ℝ, dprofile (a n) t x ∂μ) =
      (∫ x : ℝ, dprofile (a n) t x ∂σ) +
        ∫ x : ℝ, dprofile (a n) t x*f x := by
    calc
      _ = (∫ x : ℝ, dprofile (a n) t x ∂σ) +
          ∫ x : ℝ, dprofile (a n) t x ∂volume.withDensity (μ.rnDeriv volume) := by
        rw [←integral_add_measure (dprofile_integrable_measure σ _ _)
          (dprofile_integrable_measure (volume.withDensity (μ.rnDeriv volume)) _ _)]
        rw [show σ + volume.withDensity (μ.rnDeriv volume) = μ from μ.singularPart_add_rnDeriv volume]
      _ = _ := by
        congr 1
        rw [integral_withDensity_eq_integral_toReal_smul (μ.measurable_rnDeriv volume)
          (μ.rnDeriv_lt_top volume)]
        apply integral_congr_ae
        exact Eventually.of_forall fun x => mul_comm _ _
  change Tendsto (fun n => ∫ x : ℝ, dprofile (a n) t x ∂μ) atTop (𝓝 (f t))
  simp_rw [heq]
  simpa only [zero_add] using hs.add ht

end CAT0Fillings.SmoothCutoff
end

end OAI
