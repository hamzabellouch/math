import OAI.Analysis.AncientFlat.Evolution.TimeFamilyEnvelope

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped BoundedContinuousFunction SchwartzMap
namespace SourceFrozenCancellation
open SchwartzTimeScale
variable {V E : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
omit [CompleteSpace E] in
lemma exists_normalized_variable_time_diff (K : SchwartzMap V E) (N : ℕ)
    (hz : ∫ z,K z=0) (α β γ : ℝ) (hα : 0<α) (hαβ : α≤β) (hγ : 0≤γ) (hγ1 : γ≤1) :
    ∃ C D : ℝ, 0≤C ∧ 0≤D ∧ ∀ ell∈Icc (1:ℝ) 2,
      ∀ (A : V → ℝ), Continuous A → (∀ y, A y∈Icc α β) →
      ∀ (L : ℝ), 0≤L → (∀ x y, ‖A x-A y‖≤L*‖x-y‖) →
      ∀ (f : V →ᵇ ℂ) (H : ℝ), 0≤H → (∀ x y, ‖f x-f y‖≤H*‖x-y‖^γ) →
      ∀ (r : ℝ), 0<r → ∀ x,
      ‖(∫ z, f (x-r • z) • atTime K N (ell*A (x-r • z)) z)-
        (∫ z, f (x-r • z) • atTime K N (A (x-r • z)) z)‖≤
        (ell-1)*(H*r^γ*C+‖f‖*L*r*D) := by
  obtain ⟨B,D,hiB,hiBw,hB,hiD,hiDw,hD,hh⟩ := timeDiff_envelopes K N α β hα hαβ
  have hiC := integrable_envelope_power B hiB hiBw hB γ hγ hγ1
  have hiE : Integrable (fun z => ‖z‖*D z) := by
    simpa using integrable_envelope_power D hiD hiDw hD 1 (by norm_num) le_rfl
  refine ⟨∫ z,‖z‖^γ*B z,∫ z,‖z‖*D z,
    integral_nonneg (fun z => mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (hB z)),
    integral_nonneg (fun z => mul_nonneg (norm_nonneg _) (hD z)),?_⟩
  intro ell hell A hA hAr L hL hAL f H hH hf r hr x
  have hd : 0≤ell-1 := sub_nonneg.mpr hell.1
  have hi (a : V → ℝ) (ha : Continuous a) (har : ∀ z, a z∈Icc α (2*β)) :
      Integrable (fun z => f (x-r • z) • atTime K N (a z) z) := by
    obtain ⟨P,hP,_,hPp,hp⟩ := parameter_envelope K N α (2*β) hα
    apply (hP.const_mul ‖f‖).mono'
    · exact ((f.continuous.comp (continuous_const.sub (continuous_const.smul continuous_id))).smul
        (continuous_variable K N a ha (fun z => hα.trans_le (har z).1))).aestronglyMeasurable
    · filter_upwards with z
      rw [norm_smul]
      exact mul_le_mul (f.norm_coe_le_norm _) (hp _ (har z) z) (norm_nonneg _) (norm_nonneg _)
  have ha : Continuous (fun z => A (x-r • z)) := hA.comp (continuous_const.sub (continuous_const.smul continuous_id))
  have hβ : 0<β := hα.trans_le hαβ
  rw [←integral_sub
    (hi (fun z => ell*A (x-r • z)) (continuous_const.mul ha) (fun z => scaled_mem hα hell (hAr _)))
    (hi (fun z => A (x-r • z)) ha (fun z => ⟨(hAr _).1,by linarith [(hAr (x-r • z)).2]⟩))]
  simp_rw [←smul_sub]
  have hbwi : Integrable (fun z => (1+‖z‖)*((ell-1)*B z)) := by
    simpa only [mul_left_comm, mul_assoc] using hiBw.const_mul (ell-1)
  have hdwi : Integrable (fun z => (1+‖z‖)*((ell-1)*D z)) := by
    simpa only [mul_left_comm, mul_assoc] using hiDw.const_mul (ell-1)
  have he := norm_normalized_family (timeDiff K N ell) α β
    (timeDiff_continuous K N hα hell)
    (fun a ha => integral_timeDiff_zero K N hz (zero_lt_one.trans_le hell.1) (hα.trans_le ha.1))
    (fun z => (ell-1)*B z) (fun z => (ell-1)*D z)
    (hiB.const_mul _) hbwi (fun z => mul_nonneg hd (hB z))
    (hiD.const_mul _) hdwi (fun z => mul_nonneg hd (hD z))
    (hh ell hell).1 (hh ell hell).2 A hA hAr L hL hAL f γ H hγ hγ1 hH hf r hr x
  apply he.trans_eq
  have h1 : (∫ z,‖z‖^γ*((ell-1)*B z))=(ell-1)*(∫ z,‖z‖^γ*B z) := by
    simp_rw [show ∀ z,‖z‖^γ*((ell-1)*B z)=(ell-1)*(‖z‖^γ*B z) by intro z; ring]
    rw [integral_const_mul]
  have h2 : (∫ z,‖z‖*((ell-1)*D z))=(ell-1)*(∫ z,‖z‖*D z) := by
    simp_rw [show ∀ z,‖z‖*((ell-1)*D z)=(ell-1)*(‖z‖*D z) by intro z; ring]
    rw [integral_const_mul]
  rw [h1,h2]; ring
end SourceFrozenCancellation

end

end OAI
