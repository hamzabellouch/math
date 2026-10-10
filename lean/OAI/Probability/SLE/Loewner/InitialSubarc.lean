import OAI.Probability.SLE.Loewner.PositiveSlitCapacity

namespace OAI

/-! Initial subarcs of a prescribed simple attached arc, with their exact
range and nested domains. These are the family to be parametrized by capacity. -/
noncomputable section
open Set Function

namespace SLEExactGauge

def initialSubarc (p : C(unitInterval,ℂ)) (t : unitInterval) : C(unitInterval,ℂ) where
  toFun u := p (t*u)
  continuous_toFun := p.continuous.comp (continuous_const.mul continuous_id)

@[simp] lemma initialSubarc_apply (p : C(unitInterval,ℂ)) (t u : unitInterval) :
    initialSubarc p t u=p (t*u) := rfl

@[simp] lemma initialSubarc_zero (p : C(unitInterval,ℂ)) (t : unitInterval) :
    initialSubarc p t 0=p 0 := by simp [initialSubarc]

lemma initialSubarc_injective {p : C(unitInterval,ℂ)} (hp : Injective p)
    {t : unitInterval} (ht : t ≠ 0) : Injective (initialSubarc p t) := by
  intro u v he
  exact mul_left_cancel₀ ht (hp he)

lemma initialSubarc_upper {p : C(unitInterval,ℂ)}
    (hp : ∀ u : unitInterval, u ≠ 0 → p u ∈ upperHalfPlane)
    {t : unitInterval} (ht : t ≠ 0) :
    ∀ u : unitInterval, u ≠ 0 → initialSubarc p t u ∈ upperHalfPlane := by
  intro u hu
  exact hp (t*u) (mul_ne_zero ht hu)

theorem initialSubarc_range (p : C(unitInterval,ℂ)) (t : unitInterval) :
    range (initialSubarc p t)=p '' Icc 0 t := by
  apply Subset.antisymm
  · rintro _ ⟨u,rfl⟩
    refine ⟨t*u,⟨bot_le,?_⟩,rfl⟩
    have hh := mul_le_mul_of_nonneg_left u.property.2 t.property.1
    exact_mod_cast (by simpa only [mul_one] using hh : (t:ℝ)*(u:ℝ)≤(t:ℝ))
  · rintro _ ⟨r,hr,rfl⟩
    by_cases ht : t=0
    · have hr0 : r=0 := le_antisymm (ht ▸ hr.2) bot_le
      exact ⟨0,by simp [hr0]⟩
    · have htpos : 0<(t:ℝ) := by
        exact_mod_cast (unitInterval.pos_iff_ne_zero.mpr ht)
      let u : unitInterval := ⟨(r:ℝ)/(t:ℝ),div_nonneg r.property.1 htpos.le,
        (div_le_one htpos).mpr (by exact_mod_cast hr.2)⟩
      refine ⟨u,?_⟩
      have he : t*u=r := by
        apply Subtype.ext
        change (t:ℝ)*((r:ℝ)/(t:ℝ))=(r:ℝ)
        field_simp
      simp only [initialSubarc_apply,he]

lemma initialSubarc_range_mono (p : C(unitInterval,ℂ))
    {s t : unitInterval} (hst : s≤t) :
    range (initialSubarc p s) ⊆ range (initialSubarc p t) := by
  rw [initialSubarc_range,initialSubarc_range]
  exact image_mono (Icc_subset_Icc_right hst)

end SLEExactGauge

end

end OAI
