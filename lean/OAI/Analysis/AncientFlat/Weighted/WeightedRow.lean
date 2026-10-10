import OAI.Analysis.AncientFlat.Kernel.ClassicalBase

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped BoundedContinuousFunction SchwartzMap
namespace SourceFrozenOrder
open SchwartzTimeScale SourceFrozenCancellation
variable {V E : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
lemma exists_weighted_norm_bound [CompleteSpace E]
    (K : SchwartzMap V E) (j : ℕ) (α β : ℝ) (hα : 0<α) :
    ∃ C : ℝ, 0≤C ∧ ∀ (A : V → ℝ), Continuous A → (∀ y, A y∈Icc α β) →
      ∀ (r : ℝ), 0<r → ∀ (f : V →ᵇ ℂ) (x : V) (F d : ℝ), 0≤F → 0≤d →
      (∀ y, ‖f y‖≤F*(‖x-y‖+d)) →
      ‖value K A r f j x‖≤(r⁻¹)^j*F*(r+d)*C := by
  obtain ⟨B,hiB,hiBw,hB,hb⟩ := parameter_envelope K (Module.finrank ℝ V+j) α β hα
  have hnB : Integrable (fun z => ‖z‖*B z) := by
    convert hiBw.sub hiB using 1
    ext z; simp only [Pi.sub_apply]; ring
  let C := ∫ z,(1+‖z‖)*B z
  have hC : 0≤C := integral_nonneg (fun z => mul_nonneg (by positivity) (hB z))
  refine ⟨C,hC,fun A hA hAr r hr f x F d hF hd hf => ?_⟩
  rw [normalized K A (fun y => hα.trans_le (hAr y).1) r hr,norm_smul,
    Real.norm_of_nonneg (by positivity : 0≤(r⁻¹)^j)]
  have hg : Integrable (fun z => F*(r*‖z‖+d)*B z) := by
    convert (hnB.const_mul (F*r)).add (hiB.const_mul (F*d)) using 1
    ext z; simp only [Pi.add_apply]; ring
  have hp (z : V) : ‖f (x-r • z) • atTime K (Module.finrank ℝ V+j) (A (x-r • z)) z‖≤F*(r*‖z‖+d)*B z := by
    rw [norm_smul]
    have hn : ‖x-(x-r • z)‖=r*‖z‖ := by rw [sub_sub_cancel,norm_smul,Real.norm_of_nonneg hr.le]
    exact mul_le_mul (by simpa only [hn] using hf (x-r • z)) (hb _ (hAr _) z) (norm_nonneg _) (by positivity)
  have hi : Integrable (fun z => f (x-r • z) • atTime K (Module.finrank ℝ V+j) (A (x-r • z)) z) := by
    apply hg.mono'
    · exact ((f.continuous.comp (continuous_const.sub (continuous_const.smul continuous_id))).smul
        (continuous_variable K _ (fun z => A (x-r • z))
          (hA.comp (continuous_const.sub (continuous_const.smul continuous_id)))
          (fun z => hα.trans_le (hAr _).1))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall hp
  have he : ‖∫ z, f (x-r • z) • atTime K (Module.finrank ℝ V+j) (A (x-r • z)) z‖≤F*(r+d)*C := by
    calc
      _ ≤ ∫ z,F*(r*‖z‖+d)*B z := (norm_integral_le_integral_norm _).trans (integral_mono hi.norm hg hp)
      _ ≤ ∫ z,F*(r+d)*((1+‖z‖)*B z) := by
        apply integral_mono hg (hiBw.const_mul _) (fun z => ?_)
        have hz := norm_nonneg z
        nlinarith [mul_nonneg (mul_nonneg hF (hB z)) (mul_nonneg hd hz),
          mul_nonneg (mul_nonneg hF (hB z)) hr.le]
      _ = _ := by rw [integral_const_mul]
  exact (mul_le_mul_of_nonneg_left he (by positivity)).trans_eq (by ring)
end SourceFrozenOrder

end

end OAI
