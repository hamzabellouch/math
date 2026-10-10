import Mathlib

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

namespace CannonPlanarCorner

def graphShear (f : C(ℝ,ℝ)) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toFun p := (p.1,p.2+f p.1)
  invFun p := (p.1,p.2-f p.1)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] lemma graphShear_apply (f : C(ℝ,ℝ)) (x y : ℝ) :
    graphShear f (x,y)=(x,y+f x) := rfl

def bendHeight (m n : ℝ) : C(ℝ,ℝ) :=
  ⟨fun x => m*x+(n-m)*max x 0,by fun_prop⟩

lemma bendHeight_nonpos (m n : ℝ) {x : ℝ} (hx : x≤0) :
    bendHeight m n x=m*x := by simp [bendHeight,max_eq_right hx]
lemma bendHeight_nonneg (m n : ℝ) {x : ℝ} (hx : 0≤x) :
    bendHeight m n x=n*x := by simp [bendHeight,max_eq_left hx]; ring

lemma complex_real_inner (u v : ℂ) : inner ℝ u v=(star u*v).re := by
  simp [real_inner_eq_re_inner ℂ,RCLike.inner_apply]
  ring

theorem separating_multiplier {u v : ℂ} (h : ¬SameRay ℝ u v) :
    ∃ c : ℂ, c≠0 ∧ (c*u).re<0 ∧ 0<(c*v).re := by
  have hu : u≠0 := fun he => h (he ▸ SameRay.zero_left v)
  have hv : v≠0 := fun he => h (he ▸ SameRay.zero_right u)
  have hnu : 0<‖u‖ := norm_pos_iff.mpr hu
  have hnv : 0<‖v‖ := norm_pos_iff.mpr hv
  have hlt : inner ℝ u v<‖u‖*‖v‖ := by
    apply inner_lt_norm_mul_iff_real.mpr
    intro he
    exact h (sameRay_iff_norm_smul_eq.mpr he.symm)
  let w := ‖v‖⁻¹ • v-‖u‖⁻¹ • u
  have hwu : inner ℝ w u<0 := by
    simp only [w,inner_sub_left,real_inner_smul_left,real_inner_self_eq_norm_sq]
    rw [real_inner_comm u v]
    have hh := (div_lt_iff₀ hnv).mpr hlt
    rw [div_eq_mul_inv,mul_comm] at hh
    have he : ‖u‖⁻¹*‖u‖^2=‖u‖ := by field_simp
    rw [he]
    exact sub_neg.mpr hh
  have hwv : 0 < inner ℝ w v := by
    simp only [w,inner_sub_left,real_inner_smul_left,real_inner_self_eq_norm_sq]
    have hh : ‖u‖⁻¹*inner ℝ u v<‖v‖ := by
      rw [mul_comm,←div_eq_mul_inv]
      exact (div_lt_iff₀ hnu).mpr (by simpa only [mul_comm] using hlt)
    have he : ‖v‖⁻¹*‖v‖^2=‖v‖ := by field_simp
    rw [he]
    exact sub_pos.mpr hh
  refine ⟨star w,?_,?_,?_⟩
  · intro hz
    have hw : w=0 := star_eq_zero.mp hz
    simp [hw] at hwu
  · simpa only [complex_real_inner] using hwu
  · simpa only [complex_real_inner] using hwv

def ray (u : ℂ) : Set ℂ := {z | ∃ t : ℝ, 0≤t ∧ z=t•u}

def horizontal : Set (ℝ × ℝ) := {p | p.2=0}

theorem flattened_bend {u v : ℂ} (hu : u.re<0) (hv : 0<v.re) :
    let H := (graphShear (bendHeight (u.im/u.re) (v.im/v.re))).trans
      Complex.equivRealProdCLM.toHomeomorph.symm
    H '' horizontal=ray u∪ray v := by
  dsimp only
  let f := bendHeight (u.im/u.re) (v.im/v.re)
  ext z
  constructor
  · rintro ⟨⟨x,y⟩,hy,rfl⟩
    change y=0 at hy
    subst y
    by_cases hx : x≤0
    · left
      refine ⟨x/u.re,div_nonneg_of_nonpos hx hu.le,?_⟩
      apply Complex.ext
      · simp [graphShear,hu.ne]
      · simp [graphShear,bendHeight_nonpos _ _ hx]
        ring
    · right
      have hx' : 0≤x := le_of_not_ge hx
      refine ⟨x/v.re,div_nonneg hx' hv.le,?_⟩
      apply Complex.ext
      · simp [graphShear,hv.ne']
      · simp [graphShear,bendHeight_nonneg _ _ hx']
        ring
  · rintro (⟨t,ht,rfl⟩|⟨t,ht,rfl⟩)
    · refine ⟨(t*u.re,0),rfl,?_⟩
      have hx : t*u.re≤0 := mul_nonpos_of_nonneg_of_nonpos ht hu.le
      apply Complex.ext
      · simp [graphShear]
      · simp [graphShear,bendHeight_nonpos _ _ hx]
        field_simp [hu.ne]
    · refine ⟨(t*v.re,0),rfl,?_⟩
      have hx : 0≤t*v.re := mul_nonneg ht hv.le
      apply Complex.ext
      · simp [graphShear]
      · simp [graphShear,bendHeight_nonneg _ _ hx]
        field_simp [hv.ne']

theorem straighten_corner {u v : ℂ} (h : ¬SameRay ℝ u v) :
    ∃ H : (ℝ × ℝ) ≃ₜ ℂ, H (0,0)=0 ∧ H '' horizontal=ray u∪ray v := by
  obtain ⟨c,hc,hu,hv⟩ := separating_multiplier h
  let L : ℂ ≃ₜ ℂ := Homeomorph.mulLeft₀ c hc
  let H₀ := (graphShear (bendHeight ((c*u).im/(c*u).re) ((c*v).im/(c*v).re))).trans
    Complex.equivRealProdCLM.toHomeomorph.symm
  have hH₀ : H₀ '' horizontal=ray (c*u)∪ray (c*v) := flattened_bend hu hv
  have hL (w : ℂ) : L '' ray w=ray (c*w) := by
    ext z
    constructor
    · rintro ⟨_,⟨t,ht,rfl⟩,rfl⟩
      exact ⟨t,ht,by simp [L,mul_left_comm]⟩
    · rintro ⟨t,ht,rfl⟩
      exact ⟨t•w,⟨t,ht,rfl⟩,by simp [L,mul_left_comm]⟩
  refine ⟨H₀.trans L.symm,?_,?_⟩
  · have hzero : H₀ (0,0)=0 := by
      apply Complex.ext <;> simp [H₀,graphShear,bendHeight]
    simp only [Homeomorph.trans_apply,hzero]
    apply L.injective
    simp [L]
  · change (L.symm ∘ H₀) '' horizontal=ray u∪ray v
    rw [Set.image_comp]
    rw [hH₀,←hL u,←hL v,←image_union,Set.image_image]
    simp

end CannonPlanarCorner

namespace CannonPlanarCorner

lemma local_ray_segment {x u z : ℂ} {r : ℝ} (hru : r≤‖u‖) (hz : z∈ball x r) :
    (∃ s : ℝ, 0 ≤ s ∧ z = x+s•u) ↔ z∈segment ℝ x (x+u) := by
  rw [segment_eq_image']
  constructor
  · rintro ⟨s,hs,rfl⟩
    have hd : s*‖u‖<r := by
      simpa [dist_eq_norm,norm_smul,Real.norm_eq_abs,abs_of_nonneg hs] using hz
    have hu : 0<‖u‖ := by
      have : 0<r := (norm_nonneg (s•u)).trans_lt (by simpa [dist_eq_norm] using hz)
      exact this.trans_le hru
    have hs₁ : s≤1 := by nlinarith
    exact ⟨s,⟨hs,hs₁⟩,by simp⟩
  · rintro ⟨s,hs,he⟩
    exact ⟨s,hs.1,by simpa using he.symm⟩
end CannonPlanarCorner

end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
