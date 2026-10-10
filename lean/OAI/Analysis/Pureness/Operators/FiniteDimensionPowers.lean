import OAI.Analysis.Pureness.Projections.FiniteSpectralIntegralScaling
import OAI.Analysis.Pureness.Stabilization.RankBounds

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
variable {D : Type*} [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

theorem positive_power_cuntzBelow (M : Positive D) (r : ℝ≥0) (hr : 0 < r) :
    CuntzBelow (Positive.power r M) M := by
  apply CuntzBelow.of_tendsto (fun k => Positive.power r (Positive.cut (Positive.rootExponent k) M)) M
  · apply (Positive.power_continuous r).continuousAt.tendsto.comp
    apply Positive.tendsto_cut
    simpa [Positive.rootExponent] using (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun k : ℕ => 1/((k : ℝ)+1)) atTop (𝓝 0))
  · intro k
    have h := Positive.power_cut_le M (Positive.rootExponent k) (Positive.rootExponent_pos k) r hr
    exact CuntzBelow.of_le_smul _ _ _ (NNReal.coe_nonneg _) h

theorem positive_power_cuntz_equiv (M : Positive D) (r : ℝ≥0) (hr : 0 < r) :
    CuntzBelow (Positive.power r M) M ∧ CuntzBelow M (Positive.power r M) := by
  refine ⟨positive_power_cuntzBelow M r hr, ?_⟩
  have h := positive_power_cuntzBelow (Positive.power r M) r⁻¹ (inv_pos.mpr hr)
  have he : Positive.power r⁻¹ (Positive.power r M) = M := by
    apply Subtype.ext
    exact CFC.nnrpow_nnrpow_inv M.1 hr.ne' M.2
  rwa [he] at h

theorem positive_cfc_cut_mono (M : Positive D) (f g : ℝ → ℝ)
    (hf : Continuous f) (hg : Continuous g) (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (hfpos : ∀ t, 0 ≤ f t) (hgpos : ∀ t, 0 ≤ g t)
    (hfg : ∀ t ∈ quasispectrum ℝ M.1, f t ≤ g t) (ε : ℝ≥0) :
    Positive.cut ε ⟨cfcₙ f M.1,cfcₙ_nonneg (fun t _ => hfpos t)⟩ ≤
      Positive.cut ε ⟨cfcₙ g M.1,cfcₙ_nonneg (fun t _ => hgpos t)⟩ := by
  change cfcₙ (fun t : ℝ => max (t-ε) 0) (cfcₙ f M.1) ≤
    cfcₙ (fun t : ℝ => max (t-ε) 0) (cfcₙ g M.1)
  rw [← cfcₙ_comp' (fun t : ℝ => max (t-ε) 0) f M.1,
    ← cfcₙ_comp' (fun t : ℝ => max (t-ε) 0) g M.1]
  apply (cfcₙ_le_iff _ _ M.1 (hf0 := by simp [hf0]) (hg0 := by simp [hg0])
    (ha := IsSelfAdjoint.of_nonneg M.2)).mpr
  intro t ht
  exact max_le_max (sub_le_sub_right (hfg t ht) ε) le_rfl

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

local instance (n : ℕ) : Module ℝ (FinMatrix A n) :=
  Module.restrictScalars ℝ ℂ (FinMatrix A n)

lemma finitePositiveClass_power (n : ℕ) (M : Positive (FinMatrix A n)) (r : ℝ≥0) (hr : 0 < r) :
    finitePositiveClass n (Positive.power r M) = finitePositiveClass n M := by
  obtain ⟨h,h'⟩ := positive_power_cuntz_equiv M r hr
  exact le_antisymm ((finitePositiveClass_le_iff n _ _).mpr ((cuntzSubequiv_iff_shared _ _).mpr h))
    ((finitePositiveClass_le_iff n _ _).mpr ((cuntzSubequiv_iff_shared _ _).mpr h'))

lemma finiteSpectralIntegral_cfc_mono
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (n : ℕ) (M : Positive (FinMatrix A n)) (f g : ℝ → ℝ)
    (hf : Continuous f) (hg : Continuous g) (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (hfpos : ∀ t, 0 ≤ f t) (hgpos : ∀ t, 0 ≤ g t)
    (hfg : ∀ t ∈ quasispectrum ℝ M.1, f t ≤ g t) :
    finiteSpectralIntegral d n ⟨cfcₙ f M.1,cfcₙ_nonneg (fun t _ => hfpos t)⟩ ≤
      finiteSpectralIntegral d n ⟨cfcₙ g M.1,cfcₙ_nonneg (fun t _ => hgpos t)⟩ := by
  apply lintegral_mono
  intro t
  apply hd
  apply (finitePositiveClass_le_iff n _ _).mpr
  exact (cuntzSubequiv_iff_shared _ _).mpr (CuntzBelow.of_le _ _
    (positive_cfc_cut_mono M f g hf hg hf0 hg0 hfpos hgpos hfg t.toNNReal))
end CuntzPureness

end

end OAI
