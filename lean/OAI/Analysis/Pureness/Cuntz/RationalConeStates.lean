import OAI.Analysis.Pureness.Cuntz.RationalRieszExtension
import Mathlib.Tactic.Linarith

namespace OAI
noncomputable section
namespace CuntzPureness
namespace RationalRiesz
open Set Submodule
variable {E : Type*} [AddCommGroup E] [Module ℚ E]

theorem exists_normalized_positive (C : PointedCone ℚ E) (u : E)
    (hu : -u ∉ C) (hbound : ∀ z : E, ∃ r : ℚ, r • u + z ∈ C) :
    ∃ f : E →ₗ[ℚ] ℝ, f u = 1 ∧ ∀ z ∈ C, 0 ≤ f z := by
  have hu0 : u ≠ 0 := by intro h; apply hu; simp [h]
  let p : E →ₗ.[ℚ] ℝ := LinearPMap.mkSpanSingleton u 1 hu0
  have hp : ∀ z : p.domain, (z : E) ∈ C → 0 ≤ p z := by
    rintro ⟨z,hz⟩ hzc
    obtain ⟨r,rfl⟩ := Submodule.mem_span_singleton.mp hz
    rw [LinearPMap.mkSpanSingleton'_apply]
    simp only [RingHom.id_apply, Rat.smul_def, mul_one]
    have hr : 0 ≤ r := by
      by_contra h
      have hr : r < 0 := lt_of_not_ge h
      apply hu
      have hmem := C.smul_mem (show 0 ≤ -r⁻¹ by exact neg_nonneg.mpr (inv_nonpos.mpr hr.le)) hzc
      simpa only [smul_smul, neg_mul, inv_mul_cancel₀ hr.ne, neg_smul, one_smul] using hmem
    exact_mod_cast hr
  have hd : ∀ z : E, ∃ x : p.domain, (x : E) + z ∈ C := by
    intro z
    obtain ⟨r,hr⟩ := hbound z
    exact ⟨⟨r • u, Submodule.mem_span_singleton.mpr ⟨r,rfl⟩⟩,hr⟩
  obtain ⟨f,hf,hpos⟩ := riesz_extension C p hp hd
  refine ⟨f, ?_, hpos⟩
  have h := hf ⟨u, Submodule.mem_span_singleton_self u⟩
  exact h.trans (LinearPMap.mkSpanSingleton_apply ℚ ℚ hu0 1)

def adjoinNegative (C : PointedCone ℚ E) (v : E) : PointedCone ℚ E where
  carrier := {z | ∃ c ∈ C, ∃ t : ℚ, 0 ≤ t ∧ z = c - t • v}
  zero_mem' := ⟨0,C.zero_mem,0,le_rfl,by simp⟩
  add_mem' := by
    rintro a b ⟨c,hc,t,ht,rfl⟩ ⟨d,hd,s,hs,rfl⟩
    exact ⟨c+d,C.add_mem hc hd,t+s,add_nonneg ht hs,by simp [add_smul]; abel⟩
  smul_mem' := by
    rintro ⟨r,hr⟩ z ⟨c,hc,t,ht,rfl⟩
    exact ⟨r • c,C.smul_mem hr hc,r*t,mul_nonneg hr ht,by simp [smul_sub,smul_smul]⟩

lemma mem_adjoinNegative (C : PointedCone ℚ E) (v z : E) (hz : z ∈ C) :
    z ∈ adjoinNegative C v := ⟨z,hz,0,le_rfl,by simp⟩

theorem separating_state (C : PointedCone ℚ E) (u x : E) (hu : u ∈ C)
    (hbound : ∀ z : E, ∃ r : ℚ, r • u + z ∈ C)
    (hfail : ∀ q : ℚ, q < 1 → q • u - x ∉ C) :
    ∃ f : E →ₗ[ℚ] ℝ, f u = 1 ∧ (∀ z ∈ C, 0 ≤ f z) ∧ 1 ≤ f x := by
  let D := adjoinNegative C (u-x)
  have hproper : -u ∉ D := by
    rintro ⟨c,hc,t,ht,heq⟩
    by_cases ht0 : t = 0
    · have hc' : -u ∈ C := by
        have heq0 : -u = c := by simpa [ht0] using heq
        exact heq0.symm ▸ hc
      obtain ⟨r,hr⟩ := hbound (-x)
      have hr' : -r • u ∈ C := by
        by_cases hr0 : 0 ≤ r
        · simpa only [smul_neg, neg_smul] using C.smul_mem hr0 hc'
        · exact C.smul_mem (neg_nonneg.mpr (le_of_not_ge hr0)) hu
      have hsum := C.add_mem hr hr'
      apply hfail 0 (by norm_num)
      simpa [neg_smul] using hsum
    · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
      have hcform : c = (t-1) • u - t • x := by
        have : c = -u + t • (u-x) := (eq_sub_iff_add_eq.mp heq).symm
        rw [this, smul_sub, sub_smul, one_smul]
        abel
      have hmem := C.smul_mem (inv_nonneg.mpr ht) hc
      have heq' : t⁻¹ • c = (1-t⁻¹) • u - x := by
        rw [hcform, smul_sub, smul_smul, smul_smul, inv_mul_cancel₀ ht0, one_smul]
        congr 2
        rw [mul_sub, inv_mul_cancel₀ ht0, mul_one]
      rw [heq'] at hmem
      exact hfail (1-t⁻¹) (by linarith [inv_pos.mpr htpos]) hmem
  obtain ⟨f,hfu,hf⟩ := exists_normalized_positive D u hproper
    (fun z => let ⟨r,hr⟩ := hbound z; ⟨r,mem_adjoinNegative C (u-x) _ hr⟩)
  refine ⟨f,hfu,fun z hz => hf z (mem_adjoinNegative C (u-x) z hz),?_⟩
  have hneg : -(u-x) ∈ D := ⟨0,C.zero_mem,1,by norm_num,by simp⟩
  have h := hf _ hneg
  rw [map_neg,map_sub,hfu] at h
  linarith

theorem strict_bound_of_states (C : PointedCone ℚ E) (u x : E) (hu : u ∈ C)
    (hbound : ∀ z : E, ∃ r : ℚ, r • u + z ∈ C)
    (hgap : ∀ f : E →ₗ[ℚ] ℝ, f u = 1 → (∀ z ∈ C, 0 ≤ f z) → f x < 1) :
    ∃ q : ℚ, q < 1 ∧ q • u - x ∈ C := by
  by_contra h
  push Not at h
  obtain ⟨f,hfu,hf,hfx⟩ := separating_state C u x hu hbound h
  exact (not_lt_of_ge hfx) (hgap f hfu hf)
end RationalRiesz
end CuntzPureness

end

end OAI
