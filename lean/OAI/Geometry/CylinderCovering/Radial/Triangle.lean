import OAI.Geometry.CylinderCovering.Radial.TriangleDefinitions

namespace OAI

open Set MeasureTheory
open scoped BigOperators

namespace CylinderCovering.RadialTriangle

lemma mem_region_iff {l r m d : ℝ} {p : ℝ × ℝ} :
    p ∈ region l r m d ↔ l ≤ p.1 ∧ p.1 ≤ r ∧
      m * p.1 - d / 2 * (p.1-l) ≤ p.2 ∧
      p.2 ≤ m * p.1 + d / 2 * (p.1-l) := by
  simp only [region, mem_ofPred_eq, abs_le]
  constructor <;> rintro ⟨h₁, h₂, h₃, h₄⟩ <;> exact ⟨h₁, h₂, by linarith, by linarith⟩

lemma region_convex (l r m d : ℝ) : Convex ℝ (region l r m d) := by
  intro x hx y hy a b ha hb hab
  have hb_eq : b = 1-a := by linarith
  subst b
  rw [mem_region_iff] at hx hy ⊢
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left hx.1 ha, mul_le_mul_of_nonneg_left hy.1 hb]
  · nlinarith [mul_le_mul_of_nonneg_left hx.2.1 ha, mul_le_mul_of_nonneg_left hy.2.1 hb]
  · nlinarith [mul_le_mul_of_nonneg_left hx.2.2.1 ha,
      mul_le_mul_of_nonneg_left hy.2.2.1 hb]
  · nlinarith [mul_le_mul_of_nonneg_left hx.2.2.2 ha,
      mul_le_mul_of_nonneg_left hy.2.2.2 hb]

lemma vertices_mem_region {l r m d : ℝ} (hlr : l ≤ r) (hd : 0 ≤ d)
    (i : Fin 3) : vertices l r m d i ∈ region l r m d := by
  have hwidth : 0 ≤ d / 2 * (r-l) := mul_nonneg (by positivity) (sub_nonneg.mpr hlr)
  rw [mem_region_iff]
  fin_cases i <;> norm_num [vertices] <;> (try constructor) <;> nlinarith

lemma region_eq_convexHull {l r m d : ℝ} (hlr : l < r) (hd : 0 < d) :
    region l r m d = convexHull ℝ (range (vertices l r m d)) := by
  apply le_antisymm
  · intro p hp
    obtain ⟨hu₁, hu₂, hv₁, hv₂⟩ := mem_region_iff.mp hp
    let w : Fin 3 → ℝ := ![(r-p.1)/(r-l),
      (d/2*(p.1-l) - (p.2-m*p.1))/(d*(r-l)),
      (d/2*(p.1-l) + (p.2-m*p.1))/(d*(r-l))]
    have hrl : r-l ≠ 0 := ne_of_gt (sub_pos.mpr hlr)
    have hdd : d ≠ 0 := ne_of_gt hd
    have hden : 0 < d*(r-l) := mul_pos hd (sub_pos.mpr hlr)
    refine mem_convexHull_of_exists_fintype w (vertices l r m d) ?_ ?_ ?_ ?_
    · intro i
      fin_cases i
      · exact div_nonneg (sub_nonneg.mpr hu₂) (sub_pos.mpr hlr).le
      · change 0 ≤ (d/2*(p.1-l) - (p.2-m*p.1))/(d*(r-l))
        exact div_nonneg (by linarith) hden.le
      · change 0 ≤ (d/2*(p.1-l) + (p.2-m*p.1))/(d*(r-l))
        exact div_nonneg (by linarith) hden.le
    · simp [w, Fin.sum_univ_succ]
      field_simp [hrl, hdd]
      ring
    · exact fun i => mem_range_self i
    · ext <;> simp [w, vertices, Fin.sum_univ_succ]
      all_goals field_simp [hrl, hdd]
      all_goals ring
  · refine convexHull_min ?_ (region_convex l r m d)
    rintro _ ⟨i, rfl⟩
    exact vertices_mem_region hlr.le hd.le i

lemma region_compact {l r m d : ℝ} (hlr : l < r) (hd : 0 < d) :
    IsCompact (region l r m d) := by
  rw [region_eq_convexHull hlr hd]
  exact (finite_range (vertices l r m d)).isCompact_convexHull ℝ

lemma vertices_affineIndependent {l r m d : ℝ} (hlr : l < r) (hd : 0 < d) :
    AffineIndependent ℝ (vertices l r m d) := by
  rw [affineIndependent_iff_of_fintype]
  intro w hw hv i
  rw [Finset.weightedVSub_eq_linear_combination _ hw] at hv
  have h₀ := congrArg (fun p : ℝ × ℝ => p.1) hv
  have h₁ := congrArg (fun p : ℝ × ℝ => p.2) hv
  simp [vertices, Fin.sum_univ_succ] at hw h₀ h₁
  have hrl : r-l ≠ 0 := ne_of_gt (sub_pos.mpr hlr)
  have hden : d*(r-l) ≠ 0 := mul_ne_zero (ne_of_gt hd) hrl
  have hs₀ : (r-l)*(w 1+w 2) = 0 := by linear_combination h₀ - l*hw
  have hs : w 1+w 2 = 0 := (mul_eq_zero.mp hs₀).resolve_left hrl
  have ht₀ : (d*(r-l))*(w 2-w 1) = 0 := by linear_combination 2*h₁ - 2*m*h₀
  have ht : w 2-w 1 = 0 := (mul_eq_zero.mp ht₀).resolve_left hden
  fin_cases i <;> dsimp <;> linarith

private lemma closed_region_volume (f g : ℝ → ℝ) (s : Set ℝ)
    (hf : Measurable f) (hg : Measurable g) (hs : MeasurableSet s) :
    (volume.prod volume) {p : ℝ × ℝ | p.1 ∈ s ∧ p.2 ∈ Icc (f p.1) (g p.1)} =
      (volume.prod volume) (regionBetween f g s) := by
  rw [Measure.prod_apply (measurableSet_region_between_cc hf hg hs),
    Measure.prod_apply (measurableSet_regionBetween hf hg hs)]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ s
  · simp only [regionBetween, preimage_ofPred_eq, hx, true_and]
    change volume (Icc (f x) (g x)) = volume (Ioo (f x) (g x))
    rw [Real.volume_Icc, Real.volume_Ioo]
  · simp [regionBetween, hx]

lemma region_volume {l r m d : ℝ} (hlr : l ≤ r) (hd : 0 ≤ d) :
    volume (region l r m d) = ENNReal.ofReal (d * (r-l)^2 / 2) := by
  let f : ℝ → ℝ := fun u => m*u - d/2*(u-l)
  let g : ℝ → ℝ := fun u => m*u + d/2*(u-l)
  have heq : region l r m d =
      {p : ℝ × ℝ | p.1 ∈ Icc l r ∧ p.2 ∈ Icc (f p.1) (g p.1)} := by
    ext p
    rw [mem_region_iff]
    simp only [mem_ofPred_eq, mem_Icc, f, g]
    tauto
  rw [heq]
  change (volume.prod volume) _ = _
  rw [closed_region_volume f g (Icc l r) (by fun_prop) (by fun_prop) measurableSet_Icc]
  have hf : IntegrableOn f (Icc l r) := (by fun_prop : Continuous f).integrableOn_Icc
  have hg : IntegrableOn g (Icc l r) := (by fun_prop : Continuous g).integrableOn_Icc
  have hfg : ∀ u ∈ Icc l r, f u ≤ g u := by
    intro u hu
    dsimp [f,g]
    nlinarith [mul_nonneg hd (sub_nonneg.mpr hu.1)]
  rw [volume_regionBetween_eq_integral hf hg measurableSet_Icc hfg]
  congr 1
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hlr]
  have hfun : g-f = fun u => d*(u-l) := by funext u; dsimp [f,g]; ring
  rw [hfun, intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_sub (f := fun x : ℝ => x) (g := fun _ : ℝ => l)
    (continuous_id.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _),
    integral_id, intervalIntegral.integral_const]
  ring

lemma region_volume_toReal {l r m d : ℝ} (hlr : l ≤ r) (hd : 0 ≤ d) :
    (volume (region l r m d)).toReal = d * (r-l)^2 / 2 := by
  rw [region_volume hlr hd, ENNReal.toReal_ofReal]
  positivity

lemma vertices_det (l r m d : ℝ) :
    ((vertices l r m d 1).1 - (vertices l r m d 0).1) *
        ((vertices l r m d 2).2 - (vertices l r m d 0).2) -
      ((vertices l r m d 1).2 - (vertices l r m d 0).2) *
        ((vertices l r m d 2).1 - (vertices l r m d 0).1) = d*(r-l)^2 := by
  simp [vertices]
  ring

lemma region_measurable {l r m d : ℝ} (hlr : l < r) (hd : 0 < d) :
    MeasurableSet (region l r m d) := (region_compact hlr hd).measurableSet

lemma region_volume_ne_top {l r m d : ℝ} (hlr : l ≤ r) (hd : 0 ≤ d) :
    volume (region l r m d) ≠ ⊤ := by
  rw [region_volume hlr hd]
  exact ENNReal.ofReal_ne_top

lemma freezing_left_lt_right {A B R d : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hR : 0 ≤ R) (hd : 0 < d) :
    -(collar A B)*d < R+A*d := by
  have hC : 0 < collar A B := by dsimp [collar]; linarith
  have hCd : 0 < collar A B*d := mul_pos hC hd
  have hAd : 0 ≤ A*d := mul_nonneg hA hd.le
  linarith

lemma freezingRegion_volume {A B R m d : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hR : 0 ≤ R) (hd : 0 < d) :
    volume (freezingRegion A B R m d) =
      ENNReal.ofReal (d*(R+(A+collar A B)*d)^2/2) := by
  unfold freezingRegion
  rw [region_volume (freezing_left_lt_right hA hB hR hd).le hd.le]
  congr 1
  ring

section AffineImages
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

lemma region_image_eq_convexHull (f : (ℝ × ℝ) →ᵃ[ℝ] E)
    {l r m d : ℝ} (hlr : l < r) (hd : 0 < d) :
    f '' region l r m d = convexHull ℝ (range (f ∘ vertices l r m d)) := by
  rw [region_eq_convexHull hlr hd, f.image_convexHull, ← range_comp]

lemma image_vertices_affineIndependent (f : (ℝ × ℝ) →ᵃ[ℝ] E)
    (hf : Function.Injective f) {l r m d : ℝ} (hlr : l < r) (hd : 0 < d) :
    AffineIndependent ℝ (f ∘ vertices l r m d) :=
  (vertices_affineIndependent hlr hd).map' f hf

end AffineImages

end CylinderCovering.RadialTriangle

end OAI
