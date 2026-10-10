import OAI.Probability.ContinuumTransition.ThermodynamicExtension

namespace OAI

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

theorem convex_rightDeriv_support {f : ℝ → ℝ} {S : Set ℝ} (hf : ConvexOn ℝ S f)
    {x : ℝ} (hx : x ∈ interior S) :
    ∀ y ∈ S, f x + derivWithin f (Ioi x) x * (y-x) ≤ f y := by
  intro y hy
  obtain hxy | rfl | hyx := lt_trichotomy x y
  · have hh := hf.rightDeriv_le_slope_of_mem_interior hx hy hxy
    rw [slope_def_field] at hh
    have hh' := (le_div_iff₀ (sub_pos.mpr hxy)).1 hh
    linarith
  · simp
  · have hh := (hf.slope_le_leftDeriv_of_mem_interior hy hx hyx).trans
      (hf.leftDeriv_le_rightDeriv_of_mem_interior hx)
    rw [slope_def_field] at hh
    have hh' := (div_le_iff₀ (sub_pos.mpr hyx)).1 hh
    nlinarith only [hh']

theorem canonicalPressure_nonneg {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t β B μ : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) :
    0 ≤ canonicalPressure φ β μ := by
  have hh := le_csSup (canonicalPressure_bddAbove hφ ht hβ hstable hcore (μ := μ))
    (mem_image_of_mem (fun d : ℝ => μ*d-canonicalDensity φ β d) (show 0 ∈ Ici (0 : ℝ) by simp))
  simpa only [canonicalDensity_zero hφ ht hβ hstable hcore, mul_zero, sub_zero,
    canonicalPressure] using hh

theorem canonicalPressure_le_exp {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t β B μ : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) :
    canonicalPressure φ β μ ≤ Real.exp (μ+β*B) := by
  unfold canonicalPressure
  apply csSup_le (s := (fun d : ℝ => μ*d-canonicalDensity φ β d) '' Ici 0)
      ⟨μ*0-canonicalDensity φ β 0, ⟨0, by simp, rfl⟩⟩
  rintro _ ⟨d, hd, rfl⟩
  have hh := canonicalDensity_lower_entropy hφ ht hβ hstable hcore hd
  have he := entropy_dual_bound (μ+β*B) hd
  linarith

theorem canonical_fenchel_inequality {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t β B μ d : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) (hd : 0 ≤ d) :
    μ*d-canonicalPressure φ β μ ≤ canonicalDensity φ β d := by
  have hh := le_csSup (canonicalPressure_bddAbove hφ ht hβ hstable hcore (μ := μ))
    (mem_image_of_mem (fun d : ℝ => μ*d-canonicalDensity φ β d) hd)
  change μ*d-canonicalDensity φ β d ≤ canonicalPressure φ β μ at hh
  linarith

theorem canonical_fenchel_attained {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t β B d : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) (hd : 0 < d) :
    ∃ μ, canonicalPressure φ β μ = μ*d-canonicalDensity φ β d := by
  let μ := derivWithin (canonicalDensity φ β) (Ioi d) d
  have hs := convex_rightDeriv_support (convexOn_canonicalDensity hφ ht hβ hstable hcore)
    (show d ∈ interior (Ici (0 : ℝ)) by simpa using hd)
  refine ⟨μ, le_antisymm ?_ ?_⟩
  · unfold canonicalPressure
    apply csSup_le (s := (fun d : ℝ => μ*d-canonicalDensity φ β d) '' Ici 0)
      ⟨μ*0-canonicalDensity φ β 0, ⟨0, by simp, rfl⟩⟩
    rintro _ ⟨c, hc, rfl⟩
    have hh := hs c hc
    dsimp [μ]
    nlinarith only [hh]
  · exact le_csSup (canonicalPressure_bddAbove hφ ht hβ hstable hcore (μ := μ))
      ⟨d, hd.le, rfl⟩

theorem canonical_partialConjugate {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t B : ℝ} (ht : 1 < t)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) :
    IsPartialConjugate (fun x => canonicalPressure φ x.1 x.2) (canonicalDensity φ) := by
  intro β d hβ hd
  constructor
  · rintro _ ⟨μ, rfl⟩
    exact canonical_fenchel_inequality hφ ht hβ.le hstable hcore hd
  · intro z hz
    obtain rfl | hd := hd.eq_or_lt
    · rw [canonicalDensity_zero hφ ht hβ.le hstable hcore]
      by_contra hneg
      have hzneg : z < 0 := lt_of_not_ge hneg
      let μ := Real.log (-z/2)-β*B
      have hQ := canonicalPressure_le_exp hφ ht hβ.le hstable hcore (μ := μ)
      have he : Real.exp (μ+β*B) = -z/2 := by
        dsimp [μ]
        rw [sub_add_cancel, Real.exp_log (by linarith)]
      rw [he] at hQ
      have hbound := hz (mem_range_self μ)
      dsimp at hbound
      linarith
    · obtain ⟨μ, hμ⟩ := canonical_fenchel_attained hφ ht hβ.le hstable hcore hd
      have hh := hz (mem_range_self μ)
      dsimp at hh
      rw [hμ] at hh
      linarith

theorem physical_partialConjugate {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t B : ℝ} (ht : 1 < t)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) :
    IsPartialConjugate (physicalPressure φ t) (physicalCanonical φ t) := by
  have ht0 : 0 < t := lt_trans (by norm_num) ht
  intro β d hβ hd
  have hh := canonical_partialConjugate hφ ht hstable hcore β d hβ hd
  constructor
  · rintro _ ⟨h, rfl⟩
    have hz := hh.1 (mem_range_self (t*h))
    dsimp [physicalPressure, physicalCanonical]
    apply (le_div_iff₀ ht0).2
    have hne : t ≠ 0 := ht0.ne'
    field_simp [hne]
    dsimp only at hz
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hz
  · intro z hz
    apply (div_le_iff₀ ht0).2
    apply hh.2
    rintro _ ⟨μ, rfl⟩
    have hm := hz (mem_range_self (μ/t))
    dsimp [physicalPressure] at hm
    rw [mul_div_cancel₀ _ ht0.ne'] at hm
    have hm' := mul_le_mul_of_nonneg_right hm ht0.le
    dsimp [physicalCanonical]
    field_simp [ht0.ne'] at hm'
    nlinarith only [hm']

end ContinuumTemperature
end

end OAI
