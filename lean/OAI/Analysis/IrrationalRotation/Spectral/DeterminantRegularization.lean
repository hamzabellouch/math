import OAI.Analysis.IrrationalRotation.Spectral.DeterminantNormBound

namespace OAI

noncomputable section
open Filter
open scoped ENNReal Topology CStarAlgebra

namespace Invariant233

variable {A : Type*} [CStarAlgebra A]

theorem regularizedDeterminant_monotone (τ : TracialState A) (a : A) :
    Monotone (fun ε : {r : ℝ // 0 < r} => ENNReal.ofReal
      (Real.exp ((τ (CFC.log (star a * a + ε.val • (1 : A)))).re / 2))) := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  intro ε δ hεδ
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply τ.real_mono
  apply CFC.log_le_log
  · apply add_le_add le_rfl
    exact smul_le_smul_of_nonneg_right hεδ zero_le_one
  · apply (StarOrderedRing.isStrictlyPositive_iff_spectrum_pos
      (R := ℝ) _ (by simp [IsSelfAdjoint])).mpr
    exact regularizedNormSquare_spectrum_pos a ε.val ε.property

theorem tendsto_positive_atBot_of_tendsto_zero {ι : Type*} {l : Filter ι}
    (ε : ι → ℝ) (hε : ∀ i, 0 < ε i) (hlim : Tendsto ε l (𝓝 0)) :
    Tendsto (fun i => (⟨ε i, hε i⟩ : {r : ℝ // 0 < r})) l atBot := by
  apply tendsto_atBot.2
  intro δ
  filter_upwards [hlim.eventually (gt_mem_nhds δ.property)] with i hi
  show ε i ≤ δ.val
  exact hi.le

theorem tendsto_monotone_positive_iInf (f : {r : ℝ // 0 < r} → ℝ≥0∞)
    (hf : Monotone f) {ι : Type*} {l : Filter ι}
    (ε : ι → ℝ) (hε : ∀ i, 0 < ε i) (hlim : Tendsto ε l (𝓝 0)) :
    Tendsto (fun i => f ⟨ε i, hε i⟩) l (𝓝 (⨅ δ, f δ)) := by
  have h : Tendsto f atBot (𝓝 (⨅ δ, f δ)) := tendsto_atBot_iInf hf
  exact h.comp (tendsto_positive_atBot_of_tendsto_zero ε hε hlim)

theorem tendsto_regularizedDeterminant
    (τ : TracialState A) (a : A) {ι : Type*} {l : Filter ι}
    (ε : ι → ℝ) (hε : ∀ i, 0 < ε i) (hlim : Tendsto ε l (𝓝 0)) :
    Tendsto (fun i => ENNReal.ofReal
      (Real.exp ((τ (CFC.log (star a * a + ε i • (1 : A)))).re / 2)))
      l (𝓝 (fugledeKadisonDeterminant τ a)) := by
  unfold fugledeKadisonDeterminant
  exact tendsto_monotone_positive_iInf _ (regularizedDeterminant_monotone τ a) ε hε hlim

theorem tendsto_regularizedDeterminant_reciprocal (τ : TracialState A) (a : A) :
    Tendsto (fun n : ℕ => ENNReal.ofReal
      (Real.exp ((τ (CFC.log (star a * a + (1 / ((n : ℝ) + 1)) • (1 : A)))).re / 2)))
      atTop (𝓝 (fugledeKadisonDeterminant τ a)) := by
  exact tendsto_regularizedDeterminant τ a _ (fun n => by positivity)
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

end Invariant233

end

end OAI
