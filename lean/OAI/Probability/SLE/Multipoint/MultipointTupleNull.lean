import OAI.Probability.SLE.Multipoint.MultipointDistanceKernel

namespace OAI

/-! Distinctness of planar integration tuples. The values assigned to
the distance kernel on collision diagonals do not affect its integral. -/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal

namespace SLEExactGauge.Multipoint

lemma ae_tuple_pair_ne {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Set ℂ) (i j : ι) (hij : i≠j) :
    ∀ᵐ x : ι → ℂ ∂Measure.pi (fun _ : ι => volume.restrict K), x i≠x j := by
  let μ : ι → Measure ℂ := fun _ => volume.restrict K
  let D : Set (ι → ℂ) := {x | x i=x j}
  let f : (ι → ℂ) → ℝ≥0∞ := D.indicator (fun _ => 1)
  have hD : MeasurableSet D := measurableSet_eq_fun (measurable_pi_apply i) (measurable_pi_apply j)
  have hf : Measurable f := measurable_const.indicator hD
  have hmarginal : lmarginal μ {i} f = lmarginal μ {i} (fun _ => 0) := by
    rw [lmarginal_singleton,lmarginal_singleton]
    funext x
    have he : (fun y : ℂ => f (Function.update x i y)) =
        ({x j} : Set ℂ).indicator (fun _ => (1 : ℝ≥0∞)) := by
      funext y
      simp only [f,D,indicator,mem_ofPred_eq,Function.update_self,
        Function.update_of_ne hij.symm,mem_singleton_iff]
    rw [he,lintegral_indicator (measurableSet_singleton _)]
    simp only [lintegral_const,Measure.restrict_apply_univ,measure_singleton,one_mul,zero_mul]
  have hint : (∫⁻ x, f x ∂Measure.pi μ) = 0 := by
    have hh := lintegral_eq_of_lmarginal_eq {i} hf measurable_const hmarginal
    simpa only [lintegral_zero] using hh
  have hnull : Measure.pi μ D = 0 := by
    simpa only [f,lintegral_indicator hD,lintegral_const,
      Measure.restrict_apply_univ,one_mul] using hint
  apply ae_iff.mpr
  simpa only [not_not] using hnull

theorem ae_tuple_injective {ι : Type*} [Fintype ι]
    (K : Set ℂ) :
    ∀ᵐ x : ι → ℂ ∂Measure.pi (fun _ : ι => volume.restrict K), Function.Injective x := by
  classical
  have hp : ∀ i j : ι,
      ∀ᵐ x : ι → ℂ ∂Measure.pi (fun _ : ι => volume.restrict K), i≠j → x i≠x j := by
    intro i j
    by_cases hij : i=j
    · exact ae_of_all _ (fun _ h => (h hij).elim)
    · exact (ae_tuple_pair_ne K i j hij).mono (fun _ h _ => h)
  filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (hp i))] with x hx
  intro i j he
  by_contra hij
  exact hx i j hij he

theorem ae_tuple_avoids {ι : Type*} [Fintype ι] (K : Set ℂ) (z : ℂ) :
    ∀ᵐ x : ι → ℂ ∂Measure.pi (fun _ : ι => volume.restrict K), ∀ i, x i≠z := by
  apply ae_all_iff.mpr
  intro i
  apply ae_iff.mpr
  simpa only [not_not,Set.preimage,Function.eval,Set.mem_singleton_iff] using
    Measure.pi_eval_preimage_null (i := i) (fun _ : ι => volume.restrict K)
    (by simp only [measure_singleton] : (volume.restrict K) {z}=0)

end SLEExactGauge.Multipoint

end

end OAI
