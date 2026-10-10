import OAI.Geometry.PolarProducts.FiniteDescent

namespace OAI

universe u84 u85 u86 u87 u88

section NonsqueezingInline
section
open Set Filter Function MeasureTheory
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal

namespace GradientDescent
noncomputable section
open Set Filter Function Metric
open scoped Topology ContDiff
variable {E : Type u84} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

 theorem contDiff_gradient {Φ : E → ℝ} (hΦ : ContDiff ℝ ∞ Φ) :
    ContDiff ℝ ∞ (gradient Φ) := by
  exact (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.comp
    (hΦ.fderiv_right (by simp))

 def field (Φ σ : E → ℝ) (ε : ℝ) (x : E) : E :=
   (-(2*σ x/(‖gradient Φ x‖^2+ε^2))) • gradient Φ x

 theorem denom_pos (Φ : E → ℝ) {ε : ℝ} (hε : 0 < ε) (x : E) :
    0 < ‖gradient Φ x‖^2+ε^2 := add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hε)

 theorem contDiff_field {Φ σ : E → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (hσ : ContDiff ℝ ∞ σ)
    {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ ∞ (field Φ σ ε) := by
  have hg := contDiff_gradient hΦ
  exact ((contDiff_const.mul hσ).div (((contDiff_norm_sq ℝ).comp hg).add contDiff_const)
    (fun x => (denom_pos Φ hε x).ne')).neg.smul hg

 theorem field_eq_zero {Φ σ : E → ℝ} {ε : ℝ} {x : E} (hσ : σ x = 0) :
    field Φ σ ε x = 0 := by simp [field, hσ]

 theorem field_rate (Φ σ : E → ℝ) (ε : ℝ) (x : E) :
    fderiv ℝ Φ x (field Φ σ ε x) = -(2*σ x/(‖gradient Φ x‖^2+ε^2))*‖gradient Φ x‖^2 := by
  rw [field, map_smul, smul_eq_mul, ← inner_gradient_left]
  rw [real_inner_self_eq_norm_sq]

 theorem field_nonincrease (Φ : E → ℝ) {σ : E → ℝ} (hσ : ∀ x, 0 ≤ σ x)
    {ε : ℝ} (hε : 0 < ε) (x : E) : fderiv ℝ Φ x (field Φ σ ε x) ≤ 0 := by
  rw [field_rate]
  apply mul_nonpos_of_nonpos_of_nonneg
  · exact neg_nonpos.mpr (div_nonneg (mul_nonneg (by norm_num) (hσ x)) (denom_pos Φ hε x).le)
  · exact sq_nonneg _

 theorem field_decrease (Φ : E → ℝ) {σ : E → ℝ} {ε : ℝ} (hε : 0 < ε)
    {x : E} (hσ : σ x = 1) (hx : ε ≤ ‖gradient Φ x‖) :
    fderiv ℝ Φ x (field Φ σ ε x) ≤ -1 := by
  rw [field_rate, hσ, mul_one]
  have hd := denom_pos Φ hε x
  have he : -(2/(‖gradient Φ x‖^2+ε^2))*‖gradient Φ x‖^2 =
      -(2*‖gradient Φ x‖^2/(‖gradient Φ x‖^2+ε^2)) := by ring
  rw [he, neg_le_neg_iff, le_div_iff₀ hd]
  nlinarith [norm_nonneg (gradient Φ x)]

 theorem field_norm_le (Φ : E → ℝ) {σ : E → ℝ} (hσ : ∀ x, σ x ∈ Icc (0 : ℝ) 1)
    {ε : ℝ} (hε : 0 < ε) (x : E) : ‖field Φ σ ε x‖ ≤ 1/ε := by
  have hden := denom_pos Φ hε x
  rw [field, norm_smul, Real.norm_eq_abs, abs_neg,
    abs_of_nonneg (div_nonneg (mul_nonneg (by norm_num) (hσ x).1) hden.le)]
  rw [div_mul_eq_mul_div, div_le_div_iff₀ hden hε]
  have hs := mul_le_mul_of_nonneg_right (hσ x).2 (norm_nonneg (gradient Φ x))
  nlinarith [sq_nonneg (‖gradient Φ x‖-ε)]

 theorem field_hasCompactSupport {Φ σ : E → ℝ} (hσ : HasCompactSupport σ) (ε : ℝ) :
    HasCompactSupport (field Φ σ ε) := by
  apply HasCompactSupport.of_support_subset_isCompact hσ.isCompact
  intro x hx
  by_contra hn
  apply hx
  exact field_eq_zero (image_eq_zero_of_notMem_tsupport hn)

end
end GradientDescent

namespace GradientDescent
noncomputable section
open Set Filter Function Metric
open scoped Topology ContDiff NNReal
variable {E : Type u85} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

 theorem exists_uniform_gradient_lower {Φ : E → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    {a b : ℝ} (hnocrit : ∀ x, a ≤ Φ x → Φ x ≤ b → gradient Φ x ≠ 0)
    (hcoercive : ∃ R : ℝ, ∀ x, R ≤ ‖x‖ → 1 ≤ ‖gradient Φ x‖) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x, a ≤ Φ x → Φ x ≤ b → ε ≤ ‖gradient Φ x‖ := by
  obtain ⟨R,hR⟩ := hcoercive
  let S := closedBall (0 : E) R ∩ Φ ⁻¹' Icc a b
  have hS : IsCompact S := (isCompact_closedBall (0 : E) R).inter_right
    (isClosed_Icc.preimage hΦ.continuous)
  by_cases hne : S.Nonempty
  · obtain ⟨x,hx,hm⟩ := hS.exists_isMinOn hne (contDiff_gradient hΦ).continuous.norm.continuousOn
    have hxg : 0 < ‖gradient Φ x‖ := norm_pos_iff.mpr (hnocrit x hx.2.1 hx.2.2)
    refine ⟨min 1 ‖gradient Φ x‖, lt_min zero_lt_one hxg, ?_⟩
    intro y ha hb
    by_cases hy : ‖y‖ ≤ R
    · exact (min_le_right _ _).trans (hm ⟨by simpa using hy, ha, hb⟩)
    · exact (min_le_left _ _).trans (hR y (le_of_lt (lt_of_not_ge hy)))
  · refine ⟨1, zero_lt_one, ?_⟩
    intro y ha hb
    apply hR
    by_contra h
    exact hne ⟨y, by simpa using (le_of_lt (lt_of_not_ge h)), ha, hb⟩

 def energyCutoff (Φ : E → ℝ) (a : ℝ) (x : E) : ℝ :=
   Real.smoothTransition ((2*Φ x-a)/a)

 omit [FiniteDimensional ℝ E] in
 theorem energyCutoff_contDiff {Φ : E → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (a : ℝ) :
    ContDiff ℝ ∞ (energyCutoff Φ a) := by
  exact Real.smoothTransition.contDiff.comp
    (((contDiff_const.mul hΦ).sub contDiff_const).div_const a)

 omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
 theorem energyCutoff_mem (Φ : E → ℝ) (a : ℝ) (x : E) :
    energyCutoff Φ a x ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

 omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
 theorem energyCutoff_one (Φ : E → ℝ) {a : ℝ} (ha : 0 < a) {x : E} (hx : a ≤ Φ x) :
    energyCutoff Φ a x = 1 := by
  apply Real.smoothTransition.one_of_one_le
  rw [le_div_iff₀ ha]
  linarith

 omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
 theorem energyCutoff_zero (Φ : E → ℝ) {a : ℝ} (ha : 0 < a) {x : E} (hx : Φ x ≤ a/2) :
    energyCutoff Φ a x = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) ha.le

 theorem exists_cutoff_field {Φ : E → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    {a b ε M : ℝ} (ha : 0 < a) (hε : 0 < ε) (hM : 0 < M)
    (hgrad : ∀ x, a ≤ Φ x → Φ x ≤ b → ε ≤ ‖gradient Φ x‖) :
    ∃ (V : E → E) (K : ℝ≥0), ContDiff ℝ ∞ V ∧ LipschitzWith K V ∧
      (∀ x, ‖V x‖ ≤ 1/ε) ∧ (∀ x, fderiv ℝ Φ x (V x) ≤ 0) ∧
      (∀ x, Φ x ≤ a/2 → V x = 0) ∧
      (∀ x, ‖x‖ ≤ M → a ≤ Φ x → Φ x ≤ b → fderiv ℝ Φ x (V x) ≤ -1) := by
  let χ : ContDiffBump (0 : E) := ⟨M, M+1, hM, by linarith⟩
  let σ : E → ℝ := fun x => χ x * energyCutoff Φ a x
  have hσ : ContDiff ℝ ∞ σ := χ.contDiff.mul (energyCutoff_contDiff hΦ a)
  have hσc : HasCompactSupport σ := χ.hasCompactSupport.mul_right
  have hσm (x : E) : σ x ∈ Icc (0 : ℝ) 1 := by
    refine ⟨mul_nonneg χ.nonneg (energyCutoff_mem Φ a x).1, ?_⟩
    exact (mul_le_of_le_one_left (energyCutoff_mem Φ a x).1 χ.le_one).trans
      (energyCutoff_mem Φ a x).2
  let V := field Φ σ ε
  have hV : ContDiff ℝ ∞ V := contDiff_field hΦ hσ hε
  obtain ⟨K,hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (field_hasCompactSupport hσc ε) hV (by simp)
  refine ⟨V,K,hV,hK,field_norm_le Φ hσm hε,field_nonincrease Φ (fun x => (hσm x).1) hε,?_,?_⟩
  · intro x hx
    apply field_eq_zero
    simp only [σ, energyCutoff_zero Φ ha hx, mul_zero]
  · intro x hx hxa hxb
    apply field_decrease Φ hε _ (hgrad x hxa hxb)
    have hχ : χ x = 1 := χ.one_of_mem_closedBall (by simpa using hx)
    simp only [σ, hχ, energyCutoff_one Φ ha hxa, mul_one]

end
end GradientDescent

namespace FiniteLinking
noncomputable section
open Set Filter Function Metric
open scoped Topology ContDiff NNReal
variable {H : Type u86} {E : Type u87} {F : Type u88} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]

 theorem exists_critical (l : H ≃L[ℝ] E × F) {Φ : H → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    {e : F} (he : ‖e‖ = 1) {a b ρ ε R : ℝ}
    (ha : 0 < a) (hba : a ≤ b) (hρ : 0 < ρ) (hε : 0 < ε) (hR : ρ < R)
    (hpos : ∀ z : F, ‖z‖ = ρ → 2*a ≤ Φ (l.symm (0,z)))
    (hnear : ∀ (y : E) (s : ℝ), 0 < s → s < ε → Φ (l.symm (y,s • e)) ≤ a/2)
    (hfar : ∀ (y : E) (s : ℝ), 0 < s → R ≤ ‖(y,s)‖ → Φ (l.symm (y,s • e)) ≤ a/2)
    (hupper : ∀ (y : E) (s : ℝ), 0 < s → ‖(y,s)‖ < R → Φ (l.symm (y,s • e)) ≤ b)
    (hcoercive : ∃ C : ℝ, ∀ x, C ≤ ‖x‖ → 1 ≤ ‖gradient Φ x‖) :
    ∃ x : H, a ≤ Φ x ∧ Φ x ≤ b ∧ gradient Φ x = 0 := by
  by_contra! hn
  obtain ⟨δ,hδ,hgrad⟩ := GradientDescent.exists_uniform_gradient_lower hΦ hn hcoercive
  let B := ‖l.symm.toContinuousLinearMap‖ * R
  let T := b-a+1
  let M := B+T*(1/δ)+1
  have hR0 : 0 < R := hρ.trans hR
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hT : 0 < T := by dsimp [T]; linarith
  have hM : 0 < M := by
    have : 0 < T*(1/δ) := mul_pos hT (one_div_pos.mpr hδ)
    dsimp [M]
    linarith
  obtain ⟨V,K,hVs,hV,hL,hdec,hfix,hrate⟩ :=
    GradientDescent.exists_cutoff_field hΦ ha hδ hM hgrad
  obtain ⟨η,hη,_,hηfix,hηlow⟩ := FlowDescent.exists_descent_map hV hVs
    (hΦ.differentiable (by simp)) hdec hT (show b-T ≤ a by dsimp [T]; linarith)
    hL (show B+T*(1/δ) ≤ M by dsimp [M]; linarith) hrate
  let ψ : E × F → E × F := l ∘ η ∘ l.symm
  have hψ : ContDiff ℝ ∞ ψ := l.contDiff.comp (hη.comp l.symm.contDiff)
  have hψeq (y : E) (s : ℝ) (hx : Φ (l.symm (y,s • e)) ≤ a/2) :
      ψ (y,s • e) = (y,s • e) := by
    simp only [ψ, Function.comp_apply, hηfix _ (hfix _ hx), l.apply_symm_apply]
  obtain ⟨y,s,hs,hys,hfst,hsnd⟩ := SmoothLinking.sphere_linking hψ he hρ hε hR
    (fun y s hs heps => hψeq y s (hnear y s hs heps))
    (fun y s hs hnorm => hψeq y s (hfar y s hs hnorm))
  have hncone : ‖(y,s • e)‖ = ‖(y,s)‖ := by
    simp only [Prod.norm_def, norm_smul, he, mul_one, Real.norm_eq_abs]
  have hxB : ‖l.symm (y,s • e)‖ ≤ B :=
    (l.symm.toContinuousLinearMap.le_opNorm _).trans (by
      rw [hncone]
      exact mul_le_mul_of_nonneg_left hys.le (norm_nonneg l.symm.toContinuousLinearMap))
  have hlow := hηlow (l.symm (y,s • e)) hxB (hupper y s hs hys)
  have hhigh := hpos (ψ (y,s • e)).2 hsnd
  have heq : l.symm (0,(ψ (y,s • e)).2) = η (l.symm (y,s • e)) := by
    rw [← hfst]
    change l.symm (ψ (y,s • e)) = _
    simp only [ψ, Function.comp_apply, l.symm_apply_apply]
  rw [heq] at hhigh
  linarith

end
end FiniteLinking

end

end NonsqueezingInline

end OAI
