import OAI.Geometry.Relativity.CKS.CollarMomentumNormalization

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def meanResidual (p : MomentumInput) : ℝ :=
  2/(Real.sqrt (1+mz p^2)+1)+2*Real.sqrt (1+mz p^2)*mz p*
    ((mc p 0).1+(mc p 4).1+mz p^3*(mc p 0).1*(mc p 4).1)
lemma meanResidual_smooth : ContDiff ℝ ∞ meanResidual := by
  have hs : ContDiff ℝ ∞ (fun p : MomentumInput => Real.sqrt (1+mz p^2)) :=
    (by fun_prop : ContDiff ℝ ∞ (fun p : MomentumInput => 1+mz p^2)).sqrt
      (by intro p; positivity)
  unfold meanResidual
  exact (contDiff_const.fun_div (hs.add contDiff_const) (by intro p; positivity)).add
    ((((contDiff_const.mul hs).mul (by fun_prop))).mul (by fun_prop))
lemma normalizedMean_factor (p : MomentumInput) :
    normalizedMean p-2 = mz p^2*meanResidual p := by
  have hs := Real.sq_sqrt (show 0 ≤ 1+mz p^2 by positivity)
  have hn : Real.sqrt (1+mz p^2)+1 ≠ 0 := by positivity
  unfold normalizedMean normalizedSpeed meanResidual
  field_simp
  linear_combination hs

lemma momentum_uniform_on_compact {K : Set MomentumInput} (hK : IsCompact K)
    (hreg : K ⊆ momentumRegion) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ≥0, ∃ B : ℝ, 0 ≤ B ∧
      LipschitzOnWith C momentumResidual (Metric.cthickening δ K) ∧
      ∀ p ∈ Metric.cthickening δ K, ‖momentumResidual p‖ ≤ B ∧ |meanResidual p| ≤ B := by
  let : FiniteDimensional ℝ MomentumInput := inferInstance
  let : ProperSpace MomentumInput := FiniteDimensional.proper ℝ MomentumInput
  obtain ⟨δ,hδ,hsub⟩ := hK.exists_cthickening_subset_open momentumRegion_open hreg
  have hk := hK.cthickening (r := δ)
  obtain ⟨C,hC⟩ : ∃ C, LipschitzOnWith C momentumResidual (Metric.cthickening δ K) := by
    apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hk
    intro p hp
    obtain ⟨C,t,ht,hC⟩ := ((momentumResidual_smooth (hsub hp)).of_le
      (by simp : (1:ℕ∞ω) ≤ ∞)).exists_lipschitzOnWith
    exact ⟨C,t,mem_nhdsWithin_of_mem_nhds ht,hC⟩
  obtain ⟨B₁,hB₁⟩ := hk.exists_bound_of_continuousOn
    (fun p hp => (momentumResidual_smooth (hsub hp)).continuousAt.continuousWithinAt)
  obtain ⟨B₂,hB₂⟩ := hk.exists_bound_of_continuousOn meanResidual_smooth.continuous.continuousOn
  refine ⟨δ,hδ,C,max 0 (max B₁ B₂),le_max_left _ _,hC,?_⟩
  intro p hp
  constructor
  · exact (hB₁ p hp).trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact (hB₂ p hp).trans ((le_max_right _ _).trans (le_max_right _ _))

theorem weighted_momentum {K : Set MomentumInput} (hK : IsCompact K)
    (hreg : K ⊆ momentumRegion) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧
      ∀ p p₀ : MomentumInput, p ∈ Metric.cthickening δ K → p₀ ∈ Metric.cthickening δ K →
      ∀ r A : ℝ, 1 ≤ r → mz p = 1/r → mz p₀ = 1/r → mw p₀ = 0 →
      0 ≤ mw p → 0 ≤ A → ‖p-p₀‖ ≤ A*mw p →
      |coordinateQ p₀| ≤ B/r^3 ∧
      |coordinateQ p-coordinateQ p₀-normalizedMean p*mw p/r^2| ≤ C*A*mw p/r^3 ∧
      |coordinateQ p-coordinateQ p₀-2*mw p/r^2| ≤ (C*A+B)*mw p/r^3 ∧
      (∀ a, |coordinateZ p₀ a| ≤ B/r^2) ∧
      (∀ a, |coordinateZ p a-coordinateZ p₀ a| ≤ C*A*mw p/r^2) ∧
      |normalizedMean p-2| ≤ B/r^2 := by
  obtain ⟨δ,hδ,C,B,hB,hLip,hbound⟩ := momentum_uniform_on_compact hK hreg
  refine ⟨δ,hδ,C,B,C.coe_nonneg,hB,?_⟩
  intro p p₀ hp hp₀ r A hr hz hz₀ hw₀ hw hA hd
  have hr0 : 0 < r := by linarith
  have hzn : mz p ≠ 0 := by rw [hz]; positivity
  have hz₀n : mz p₀ ≠ 0 := by rw [hz₀]; positivity
  have hres : ‖momentumResidual p-momentumResidual p₀‖ ≤ (C:ℝ)*(A*mw p) := by
    have hh := hLip.dist_le_mul p hp p₀ hp₀
    rw [dist_eq_norm,dist_eq_norm] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hd C.coe_nonneg)
  have hn : |normalResidual p-normalResidual p₀| ≤ (C:ℝ)*(A*mw p) :=
    (show _ ≤ ‖momentumResidual p-momentumResidual p₀‖ from norm_fst_le _).trans hres
  have hn₀ : |normalResidual p₀| ≤ B := (norm_fst_le (momentumResidual p₀)).trans (hbound p₀ hp₀).1
  have ha (a : I) : |angularResidual p a-angularResidual p₀ a| ≤ (C:ℝ)*(A*mw p) :=
    (norm_le_pi_norm (angularResidual p-angularResidual p₀) a).trans ((norm_snd_le _).trans hres)
  have ha₀ (a : I) : |angularResidual p₀ a| ≤ B :=
    (norm_le_pi_norm (angularResidual p₀) a).trans ((norm_snd_le _).trans (hbound p₀ hp₀).1)
  have hq₀ : coordinateQ p₀ = normalResidual p₀/r^3 := by
    rw [coordinateQ_factor hz₀n,hz₀,hw₀]
    ring
  have hdiff : coordinateQ p-coordinateQ p₀-normalizedMean p*mw p/r^2 =
      (normalResidual p-normalResidual p₀)/r^3 := by
    rw [coordinateQ_factor hzn,hq₀,hz]
    ring
  have hmean : |normalizedMean p-2| ≤ B/r^2 := by
    rw [normalizedMean_factor,hz,abs_mul,abs_of_nonneg (sq_nonneg _)]
    calc
      _ ≤ (1/r)^2*B := mul_le_mul_of_nonneg_left (hbound p hp).2 (sq_nonneg _)
      _ = _ := by ring
  have hqd : |coordinateQ p-coordinateQ p₀-normalizedMean p*mw p/r^2| ≤ (C:ℝ)*A*mw p/r^3 := by
    rw [hdiff,abs_div,abs_of_pos (pow_pos hr0 3)]
    exact (div_le_div_of_nonneg_right hn (pow_nonneg hr0.le 3)).trans_eq (by ring)
  refine ⟨?_,hqd,?_,?_,?_,hmean⟩
  · rw [hq₀,abs_div,abs_of_pos (pow_pos hr0 3)]
    exact div_le_div_of_nonneg_right hn₀ (pow_nonneg hr0.le 3)
  · have he : coordinateQ p-coordinateQ p₀-2*mw p/r^2 =
        (coordinateQ p-coordinateQ p₀-normalizedMean p*mw p/r^2)+(normalizedMean p-2)*mw p/r^2 := by ring
    rw [he]
    apply (abs_add_le _ _).trans
    have ht : |(normalizedMean p-2)*mw p/r^2| ≤ B*mw p/r^3 := by
      rw [abs_div,abs_mul,abs_of_nonneg hw,abs_of_nonneg (sq_nonneg r)]
      calc
        _ ≤ (B/r^2)*mw p/r^2 := by gcongr
        _ = B*mw p/r^4 := by ring
        _ ≤ B*mw p/r^3 := by
          apply div_le_div_of_nonneg_left (mul_nonneg hB hw) (pow_pos hr0 3)
          simpa only [pow_succ,mul_one] using mul_le_mul_of_nonneg_left hr (pow_nonneg hr0.le 3)
    exact (add_le_add hqd ht).trans_eq (by ring)
  · intro a
    rw [coordinateZ_factor hz₀n,hz₀,abs_mul,abs_of_nonneg (sq_nonneg _)]
    exact (mul_le_mul_of_nonneg_left (ha₀ a) (sq_nonneg (1/r))).trans_eq (by ring)
  · intro a
    rw [coordinateZ_factor hzn,coordinateZ_factor hz₀n,hz,hz₀,← mul_sub,abs_mul,
      abs_of_nonneg (sq_nonneg _)]
    exact (mul_le_mul_of_nonneg_left (ha a) (sq_nonneg (1/r))).trans_eq (by ring)

end
end CKSAngularGeometry

end

end OAI
