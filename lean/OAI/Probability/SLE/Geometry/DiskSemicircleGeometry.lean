import OAI.Probability.SLE.Geometry.DiskLowerStraightening

namespace OAI

/-! Concrete boundary sets used in the relative disk extension. -/
noncomputable section
open Set Complex
open scoped ComplexConjugate

namespace SLEExactGauge

lemma diskUpperArc_im_nonneg {s : ℝ} (hs : s ∈ Icc 0 1) :
    0 ≤ (diskUpperArc s).im := by
  rw [diskUpperArc_im]
  exact Real.sin_nonneg_of_mem_Icc
    ⟨mul_nonneg Real.pi_pos.le hs.1,mul_le_of_le_one_right Real.pi_pos.le hs.2⟩

theorem diskUpperArc_image :
    diskUpperArc '' Icc 0 1 = {z : ℂ | ‖z‖=1 ∧ 0 ≤ z.im} := by
  ext z
  constructor
  · rintro ⟨s,hs,rfl⟩
    exact ⟨diskUpperArc_norm s,diskUpperArc_im_nonneg hs⟩
  · rintro ⟨hn,hi⟩
    have hr : |z.re| ≤ 1 := by simpa only [hn] using abs_re_le_norm z
    have ha := abs_le.mp hr
    let s := Real.arccos (-z.re)/Real.pi
    have hs : s ∈ Icc 0 1 := by
      constructor
      · exact div_nonneg (Real.arccos_nonneg _) Real.pi_pos.le
      · exact (div_le_one Real.pi_pos).mpr (Real.arccos_le_pi _)
    refine ⟨s,hs,?_⟩
    have hps : Real.pi*s=Real.arccos (-z.re) := by dsimp [s]; field_simp
    have hc : Real.cos (Real.pi*s) = -z.re := by
      rw [hps]
      exact Real.cos_arccos (by linarith [ha.2]) (by linarith [ha.1])
    have hsin := diskUpperArc_im_nonneg hs
    have hsq : z.re^2+z.im^2=1 := by
      have he := Complex.normSq_eq_norm_sq z
      rw [Complex.normSq_apply,hn] at he
      nlinarith
    apply Complex.ext
    · rw [diskUpperArc_re]
      rw [hc]; ring
    · rw [diskUpperArc_im]
      rw [diskUpperArc_im] at hsin
      nlinarith [Real.sin_sq_add_cos_sq (Real.pi*s)]

theorem diskLowerArc_image :
    diskLowerArc '' Icc 0 1 = {z : ℂ | ‖z‖=1 ∧ z.im ≤ 0} := by
  ext z
  constructor
  · rintro ⟨s,hs,rfl⟩
    have hh : diskUpperArc s ∈ diskUpperArc '' Icc 0 1 := mem_image_of_mem _ hs
    rw [diskUpperArc_image] at hh
    simpa [diskLowerArc] using hh
  · rintro ⟨hn,hi⟩
    have hc : conj z ∈ diskUpperArc '' Icc 0 1 := by
      rw [diskUpperArc_image]
      simpa using And.intro hn hi
    obtain ⟨s,hs,he⟩ := hc
    refine ⟨s,hs,?_⟩
    dsimp [diskLowerArc]
    rw [he,Complex.conj_conj]

theorem disk_semicircle_union :
    diskUpperArc '' Icc 0 1 ∪ diskLowerArc '' Icc 0 1 = {z : ℂ | ‖z‖=1} := by
  rw [diskUpperArc_image,diskLowerArc_image]
  ext z
  simp only [mem_union,mem_ofPred]
  constructor
  · rintro (h|h) <;> exact h.1
  · intro h
    rcases le_total 0 z.im with hi|hi
    · exact Or.inl ⟨h,hi⟩
    · exact Or.inr ⟨h,hi⟩

theorem disk_semicircle_inter :
    diskUpperArc '' Icc 0 1 ∩ diskLowerArc '' Icc 0 1 = ({-1,1} : Set ℂ) := by
  rw [diskUpperArc_image,diskLowerArc_image]
  ext z
  constructor
  · rintro ⟨⟨hn,hp⟩,⟨_,hm⟩⟩
    have hi : z.im=0 := le_antisymm hm hp
    have hz : z=(z.re : ℂ) := Complex.ext rfl hi
    rw [hz,Complex.norm_real,Real.norm_eq_abs] at hn
    rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hn with he|he
    · right
      rw [hz,he]
      norm_num
    · left
      rw [hz,he]
      norm_num
  · intro hz
    rcases hz with hz|hz <;> simp_all

theorem diskDiameter_image :
    diskDiameter '' Icc 0 1 = {z : ℂ | ‖z‖ ≤ 1 ∧ z.im=0} := by
  ext z
  constructor
  · rintro ⟨s,hs,rfl⟩
    change ‖((2*s-1:ℝ):ℂ)‖ ≤ 1 ∧ _
    rw [Complex.norm_real,Real.norm_eq_abs]
    exact ⟨abs_le.mpr ⟨by linarith [hs.1],by linarith [hs.2]⟩,rfl⟩
  · rintro ⟨hn,hi⟩
    have hr := (abs_re_le_norm z).trans hn
    have ha := abs_le.mp hr
    refine ⟨(z.re+1)/2,⟨by linarith [ha.1],by linarith [ha.2]⟩,?_⟩
    apply Complex.ext
    · change 2*((z.re+1)/2)-1=z.re
      ring
    · exact hi.symm

end SLEExactGauge

end

end OAI
