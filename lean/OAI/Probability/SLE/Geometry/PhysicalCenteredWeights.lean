import OAI.Probability.SLE.Multipoint.MultipointCenteredWeights
import OAI.Probability.SLE.Angle.TargetDiskRadius

namespace OAI

/-! The fixed-center product estimate in physical conformal coordinates.
Derivative factors are retained so that area transport cancels them in
the disk moment integral, including near the endpoint angles. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SLEExactGauge.Multipoint

lemma physical_stoppedGreen_level_bound
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (hw : IsCapacityTwoWitness U γ G F)
    {κ : ℝ} (hκ : 0<κ) (hκ8 : κ<8) (z : ℂ) (hz : z ∈ upperHalfPlane)
    (D : ℝ) (hD : 0<D) (e : ℝ) (he : 0<e) :
    D^(-codimension κ) * stoppedGreen κ U γ G z (Real.log (2*z.im*D/e)) ≤
      e^(-codimension κ) := by
  have hh := stoppedGreen_level_bound hU hw hκ hκ8 z hz (e/D) (div_pos he hD)
  have heq : 2*z.im/(e/D)=2*z.im*D/e := by field_simp
  rw [heq] at hh
  apply (mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hD.le _)).trans_eq
  rw [Real.div_rpow he.le hD.le]
  field_simp [(Real.rpow_pos_of_pos hD (-codimension κ)).ne']

lemma centered_target_weights_capped
    (κ : ℝ) (m : ℕ) (b e : Fin (m+1) → ℝ)
    (hb : ∀ i, 0<b i) (he : ∀ i, 0<e i) :
    (∏ i : Fin m, (e i.succ)^(-codimension κ)) *
        (∏ i, min 1 ((e i/b i)^(1-κ/8))) ≤
      (e 0)^(codimension κ) * ∏ i, (b i)^(-codimension κ) := by
  have hα : codimension κ=1-κ/8 := by unfold codimension dimension; ring
  rw [← hα,Fin.prod_univ_succ]
  have hroot : min 1 ((e 0/b 0)^codimension κ) ≤
      (e 0)^codimension κ*(b 0)^(-codimension κ) := by
    rw [Real.rpow_neg (hb 0).le,← div_eq_mul_inv,← Real.div_rpow (he 0).le (hb 0).le]
    exact min_le_right _ _
  have htail : (∏ i : Fin m, (e i.succ)^(-codimension κ)) *
      (∏ i : Fin m, min 1 ((e i.succ/b i.succ)^codimension κ)) ≤
      ∏ i : Fin m, (b i.succ)^(-codimension κ) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod₀
    · intro i _
      exact mul_nonneg (Real.rpow_nonneg (he i.succ).le _)
        (le_min zero_le_one (Real.rpow_nonneg (div_nonneg (he i.succ).le (hb i.succ).le) _))
    · exact fun i _ => target_weight_capped (hb i.succ) (he i.succ)
  calc
    _ = min 1 ((e 0/b 0)^codimension κ) *
        ((∏ i : Fin m, (e i.succ)^(-codimension κ)) *
          ∏ i : Fin m, min 1 ((e i.succ/b i.succ)^codimension κ)) := by ring
    _ ≤ ((e 0)^codimension κ*(b 0)^(-codimension κ)) *
        ∏ i : Fin m, (b i.succ)^(-codimension κ) :=
      mul_le_mul hroot htail
        (mul_nonneg (Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (he i.succ).le _))
          (Finset.prod_nonneg (fun i _ =>
            le_min zero_le_one (Real.rpow_nonneg (div_nonneg (he i.succ).le (hb i.succ).le) _))))
        (mul_nonneg (Real.rpow_nonneg (he 0).le _) (Real.rpow_nonneg (hb 0).le _))
    _ = _ := by rw [Fin.prod_univ_succ]; ring

theorem physical_stoppedGreen_centered_product_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hBm : Measurable (Function.uncurry B))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0)
    {κ : ℝ} (hκ : 0<κ) (hκ8 : κ<8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth)
    (J : ℂ → ℂ) (hJ : DifferentiableOn ℂ J upperHalfPlane) (hJinj : InjOn J upperHalfPlane)
    (m : ℕ) (z : Fin (m+1) → ℂ) (hz : ∀ i, z i ∈ upperHalfPlane)
    (hne : Function.Injective z) (b e : Fin (m+1) → ℝ)
    (he : ∀ i, 0<e i) (hb : ∀ i, 0<b i)
    (hbR : ∀ i, b i ≤ 2*(z i).im*‖deriv J (z i)‖)
    (hsep : ∀ i j, i≠j → b i ≤ dist (J (z i)) (J (z j))) :
    (∫⁻ ω, {ω | ∃ t : ℝ≥0, z 0 ∈ survivingDomain (γ ω) t ∧
        physicalConformalRadius J (G ω) t (z 0) ≤ e 0}.indicator
      (fun ω => ENNReal.ofReal (∏ i : Fin m,
        ‖deriv J (z i.succ)‖^(-codimension κ) *
          stoppedGreen κ (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (z i.succ)
            (Real.log (2*(z i.succ).im*‖deriv J (z i.succ)‖/e i.succ)))) ω ∂P) ≤
      ENNReal.ofReal (multipointConstant κ (m+1) *
        (e 0)^(codimension κ) * ∏ i, (b i)^(-codimension κ)) := by
  classical
  let R := fun i => 2*(z i).im*‖deriv J (z i)‖
  have hR (i) : 0<R i := (hb i).trans_le (hbR i)
  have hD (i) : 0<‖deriv J (z i)‖ :=
    pos_of_mul_pos_right (hR i) (mul_nonneg (by norm_num) (hz i).le)
  let E₀ := {ω | ∃ t : ℝ≥0, z 0 ∈ survivingDomain (γ ω) t ∧
    physicalConformalRadius J (G ω) t (z 0) ≤ e 0}
  let E := {ω | ω ∈ E₀ ∧ ∀ i : Fin m,
    radiusLevelTime (γ ω) (G ω) (z i.succ) (Real.log (R i.succ/e i.succ))<∞}
  let Y := fun (i : Fin m) ω => ‖deriv J (z i.succ)‖^(-codimension κ) *
    stoppedGreen κ (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (z i.succ)
      (Real.log (R i.succ/e i.succ))
  let c := ∏ i : Fin m, (e i.succ)^(-codimension κ)
  have hc0 : 0 ≤ c := Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (he i.succ).le _)
  have hM : 0 ≤ multipointConstant κ (m+1) := (multipointConstant_pos _ _).le
  have hint := lintegral_indicator_ofReal_prod_le_event P E₀ E Y
    (fun i => (e i.succ)^(-codimension κ))
    (fun i ω => mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
      (stoppedGreen_nonneg (hw ω) κ _ _))
    (fun ω _ i => physical_stoppedGreen_level_bound ((hc ω).const_mul _) (hw ω)
      hκ hκ8 _ (hz i.succ) _ (hD i.succ) _ (he i.succ)) (fun ω hω hn => by
      have hn' : ¬∀ i : Fin m,
          radiusLevelTime (γ ω) (G ω) (z i.succ) (Real.log (R i.succ/e i.succ))<∞ :=
        fun hi => hn ⟨hω,hi⟩
      obtain ⟨i,hi⟩ := not_forall.mp hn'
      exact ⟨i,by simp only [Y,stoppedGreen,ite_eq_right hi,mul_zero]⟩)
  have hprob := capped_physical_radius_multipoint_bound hB hm hBm hc h0 hκ hκ8
    γ G F hw hgrowth J hJ hJinj z hz hne R b e he hb hbR (fun _ => rfl) hsep
  have hsub : E ⊆ {ω | ∀ i, ∃ t : ℝ≥0, z i ∈ survivingDomain (γ ω) t ∧
      physicalConformalRadius J (G ω) t (z i) ≤ e i} := by
    intro ω hω
    refine Fin.cases hω.1 (fun i => ?_)
    obtain ⟨t,ht,hRt⟩ := (physical_radius_eq_hit_iff_finite_level
      ((hc ω).const_mul _) (hw ω) J (z i.succ) (R i.succ) (e i.succ)
      (hR i.succ) (he i.succ) rfl).mpr (hω.2 i)
    exact ⟨t,ht,hRt.le⟩
  calc
    _ ≤ ENNReal.ofReal c * P E := hint
    _ ≤ ENNReal.ofReal c * ENNReal.ofReal
        (multipointConstant κ (m+1) * ∏ i, min 1 ((e i/b i)^(1-κ/8))) :=
      mul_le_mul' le_rfl ((measure_mono hsub).trans
        (by simpa only [multipointConstant,Fintype.card_fin] using hprob))
    _ = ENNReal.ofReal (multipointConstant κ (m+1) *
        (c * ∏ i, min 1 ((e i/b i)^(1-κ/8)))) := by
      rw [← ENNReal.ofReal_mul hc0]
      congr 1
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      simpa only [c,mul_assoc] using
        mul_le_mul_of_nonneg_left (centered_target_weights_capped κ m b e hb he) hM)

end SLEExactGauge.Multipoint

end

end OAI
