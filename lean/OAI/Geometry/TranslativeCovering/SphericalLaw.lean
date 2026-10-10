import OAI.Geometry.TranslativeCovering.LocalizationGood

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal

namespace SphericalLaw
open Set MeasureTheory Metric
open scoped ENNReal Pointwise
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev Sphere (n : ℕ) := sphere (0 : Space n) 1

noncomputable def σ (n : ℕ) : Measure (Sphere n) :=
  ((volume : Measure (Space n)).toSphere univ)⁻¹ • (volume : Measure (Space n)).toSphere

instance probability (n : ℕ) [NeZero n] : IsProbabilityMeasure (σ n) := by
  constructor
  rw [σ, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (fun h => Measure.toSphere_ne_zero (volume : Measure (Space n))
    (Measure.measure_univ_eq_zero.mp h)) (measure_ne_top _ _)

lemma sphere_singleton_zero {n : ℕ} (hn : 2 ≤ n) (u : Sphere n) :
    (volume : Measure (Space n)).toSphere {u} = 0 := by
  have hdim : Module.finrank ℝ (Space n) = n := by simp [Space]
  have hspan : Submodule.span ℝ ({u.val} : Set (Space n)) ≠ ⊤ := by
    intro he
    have hu : u.val ≠ 0 := by
      intro hu
      have hh := u.property
      simp [hu] at hh
    have h := finrank_span_singleton (K := ℝ) hu
    rw [he, finrank_top, hdim] at h
    omega
  have hnull := Measure.addHaar_submodule (volume : Measure (Space n)) _ hspan
  rw [Measure.toSphere_apply' _ (measurableSet_singleton u)]
  have hc : Ioo (0 : ℝ) 1 • ((↑) '' ({u} : Set (Sphere n))) ⊆
      (Submodule.span ℝ ({u.val} : Set (Space n)) : Set (Space n)) := by
    rintro y ⟨r, _, x, hx, rfl⟩
    obtain ⟨v, hv, rfl⟩ := hx
    have hv' : v = u := Set.mem_singleton_iff.mp hv
    subst v
    exact Submodule.smul_mem _ r (Submodule.subset_span (Set.mem_singleton _))
  rw [measure_mono_null hc hnull, mul_zero]

instance nonatomic {n : ℕ} [hn : Fact (2 ≤ n)] : NullSingletonClass (σ n) := by
  constructor
  intro u
  rw [σ, Measure.smul_apply, sphere_singleton_zero hn.out, smul_zero]

noncomputable def act {n : ℕ} (e : Space n ≃ₗᵢ[ℝ] Space n) (u : Sphere n) : Sphere n :=
  ⟨e u.val, by simpa only [mem_sphere_zero_iff_norm, e.norm_map] using u.property⟩

lemma continuous_act {n : ℕ} (e : Space n ≃ₗᵢ[ℝ] Space n) : Continuous (act e) :=
  (e.continuous.comp continuous_subtype_val).subtype_mk _

lemma cone_preimage {n : ℕ} (e : Space n ≃ₗᵢ[ℝ] Space n) (S : Set (Sphere n)) :
    Ioo (0 : ℝ) 1 • ((↑) '' (act e ⁻¹' S)) =
      e ⁻¹' (Ioo (0 : ℝ) 1 • ((↑) '' S)) := by
  ext y
  constructor
  · rintro ⟨r, hr, x, hx, rfl⟩
    obtain ⟨u, hu, rfl⟩ := hx
    exact ⟨r, hr, e u.val, ⟨act e u, hu, rfl⟩, (e.map_smul r u.val).symm⟩
  · intro hy
    obtain ⟨r, hr, x, hx, he⟩ := hy
    obtain ⟨u, hu, rfl⟩ := hx
    refine ⟨r, hr, e.symm u.val, ?_, ?_⟩
    · refine ⟨act e.symm u, ?_, rfl⟩
      change act e (act e.symm u) ∈ S
      have hh : act e (act e.symm u) = u := Subtype.ext (e.apply_symm_apply u.val)
      simpa only [hh] using hu
    · apply e.injective
      rw [e.map_smul, e.apply_symm_apply]
      exact he

lemma invariant {n : ℕ} (e : Space n ≃ₗᵢ[ℝ] Space n) (S : Set (Sphere n))
    (hS : MeasurableSet S) : σ n (act e ⁻¹' S) = σ n S := by
  simp only [σ, Measure.smul_apply]
  congr 1
  rw [Measure.toSphere_apply' _ ((continuous_act e).measurable hS),
    Measure.toSphere_apply' _ hS, cone_preimage]
  congr 1
  change volume (e.toHomeomorph ⁻¹' (Ioo (0:ℝ) 1 • ((↑) '' S))) = _
  rw [← e.toHomeomorph.measurableEmbedding.map_apply]
  exact congrArg (fun μ : Measure (Space n) => μ (Ioo (0:ℝ) 1 • ((↑) '' S)))
    e.measurePreserving.map_eq

def cap {n : ℕ} (x : Space n) (t : ℝ) : Set (Sphere n) :=
  {u | t < |inner ℝ u.val x|}

lemma cap_open {n : ℕ} (x : Space n) (t : ℝ) : IsOpen (cap x t) :=
  isOpen_lt continuous_const ((continuous_subtype_val.inner continuous_const).abs)

lemma cap_measurable {n : ℕ} (x : Space n) (t : ℝ) : MeasurableSet (cap x t) :=
  (cap_open x t).measurableSet

lemma positive_open {n : ℕ} [NeZero n] (U : Set (Sphere n))
    (hU : IsOpen U) (hne : U.Nonempty) : 0 < σ n U := by
  rw [σ, Measure.smul_apply, smul_eq_mul]
  apply ENNReal.mul_pos
  · exact ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)
  · exact hU.measure_ne_zero (volume : Measure (Space n)).toSphere hne

lemma cap_positive {n : ℕ} [NeZero n] (u : Sphere n) {t : ℝ} (ht : t < 1) :
    0 < σ n (cap u.val t) := by
  apply positive_open _ (cap_open _ _) ⟨u, ?_⟩
  change t < |inner ℝ u.val u.val|
  have hnorm : ‖u.val‖ = 1 := mem_sphere_zero_iff_norm.mp u.property
  simpa only [real_inner_self_eq_norm_sq, hnorm, one_pow, abs_one] using ht

lemma cap_equal_norm {n : ℕ} {x y : Space n} (hxy : ‖x‖ = ‖y‖) (t : ℝ) :
    σ n (cap x t) = σ n (cap y t) := by
  let e := (Submodule.span ℝ ({x-y} : Set (Space n)))ᗮ.reflection
  have he : e x = y := Submodule.reflection_sub hxy
  have hp : act e ⁻¹' cap y t = cap x t := by
    ext u
    change (t < |inner ℝ (e u.val) y|) ↔ (t < |inner ℝ u.val x|)
    rw [← he, e.inner_map_map]
  rw [← hp]
  exact invariant e _ (cap_measurable _ _)

lemma cap_smul {n : ℕ} (x : Space n) {a : ℝ} (ha : 0 < a) (t : ℝ) :
    cap (a • x) t = cap x (t/a) := by
  ext u
  simp only [cap, Set.mem_ofPred_eq, inner_smul_right, abs_mul, abs_of_pos ha]
  rw [div_lt_iff₀ ha]
  simp only [mul_comm]

lemma cutting_mass_le {n : ℕ} [NeZero n] (u : Sphere n) {a : ℝ} (ha : 1 < a)
    (x : Space n) (hx : ‖x‖ ≤ a) :
    σ n (cap x 1) ≤ σ n (cap u.val (1/a)) := by
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  by_cases hx0 : x = 0
  · subst x
    have he : cap (0 : Space n) 1 = ∅ := by ext v; simp [cap]
    rw [he, measure_empty]
    exact bot_le
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have heq : ‖x‖ = ‖‖x‖ • u.val‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hxpos,
      mem_sphere_zero_iff_norm.mp u.property, mul_one]
  rw [cap_equal_norm heq 1, cap_smul u.val hxpos 1]
  apply measure_mono
  intro v hv
  exact lt_of_le_of_lt (one_div_le_one_div_of_le hxpos hx) hv

end SphericalLaw

end OAI
