import OAI.Geometry.CylinderCovering.Beams.sDefinitions
import OAI.Geometry.CylinderCovering.Beams.Algebra

namespace OAI

namespace ShortenedBeam

theorem radial_representation_nonneg_shift {U Y k : ℝ}
    (hU : 0 ≤ U) (hY : 0 ≤ Y) (hk : 0 ≤ k) :
    ∃ p h : ℝ, 0 ≤ p ∧ p ≤ 1 ∧ 0 ≤ h ∧
      U = h*p-k*p^2 ∧ Y = h*(1-p)+k*(1-p)^2 := by
  by_cases hUzero : U = 0
  · subst U
    by_cases hYk : k ≤ Y
    · refine ⟨0, Y-k, by norm_num, by norm_num, sub_nonneg.mpr hYk, ?_, ?_⟩
      · ring
      · ring
    · have hkpos : 0 < k := lt_of_le_of_lt hY (lt_of_not_ge hYk)
      have hkne : k ≠ 0 := ne_of_gt hkpos
      have hYdiv : 0 ≤ Y/k := div_nonneg hY hk
      have hYdiv' : Y/k ≤ 1 := (div_le_one hkpos).2 (le_of_lt (lt_of_not_ge hYk))
      refine ⟨1-Y/k, k-Y, by linarith, by linarith, by linarith, ?_, ?_⟩
      · field_simp
        ring
      · field_simp
        ring
  · have hUpos : 0 < U := lt_of_le_of_ne hU (Ne.symm hUzero)
    let F : ℝ → ℝ := fun p => U*(1-p)-Y*p+k*p*(1-p)
    have hF : ContinuousOn F (Set.Icc 0 1) := by
      dsimp [F]
      fun_prop
    have hzero : (0 : ℝ) ∈ Set.Icc (F 1) (F 0) := by
      dsimp [F]
      constructor <;> nlinarith
    obtain ⟨p, hp, hFp⟩ := intermediate_value_Icc' (by norm_num : (0:ℝ) ≤ 1) hF hzero
    have hproot : U*(1-p)-Y*p+k*p*(1-p) = 0 := hFp
    have hpne : p ≠ 0 := by
      intro hpzero
      subst p
      norm_num at hproot
      exact hUzero hproot
    have hppos : 0 < p := lt_of_le_of_ne hp.1 (Ne.symm hpne)
    let h : ℝ := U+Y+k*(2*p-1)
    have heqU : U = h*p-k*p^2 := by
      dsimp [h]
      nlinarith [hproot]
    have heqY : Y = h*(1-p)+k*(1-p)^2 := by
      dsimp [h]
      nlinarith [hproot]
    have hhnonneg : 0 ≤ h := by
      have hkp : 0 ≤ k*p^2 := mul_nonneg hk (sq_nonneg p)
      have hhp : 0 ≤ h*p := by linarith
      exact nonneg_of_mul_nonneg_left hhp hppos
    exact ⟨p, h, hp.1, hp.2, hhnonneg, heqU, heqY⟩

theorem radial_representation {U Y k : ℝ} (hU : 0 ≤ U) (hY : 0 ≤ Y) :
    ∃ p h : ℝ, 0 ≤ p ∧ p ≤ 1 ∧ 0 ≤ h ∧
      U = h*p-k*p^2 ∧ Y = h*(1-p)+k*(1-p)^2 := by
  by_cases hk : 0 ≤ k
  · exact radial_representation_nonneg_shift hU hY hk
  · obtain ⟨p, h, hp0, hp1, hh, hYeq, hUeq⟩ :=
      radial_representation_nonneg_shift hY hU (by linarith : 0 ≤ -k)
    refine ⟨1-p, h, by linarith, by linarith, hh, ?_, ?_⟩
    · nlinarith [hUeq]
    · nlinarith [hYeq]

theorem coordinate_representation {x y t : ℝ} (a : ℝ)
    (hx : |x| ≤ 1-t) (hy : |y| ≤ 1+t) :
    ∃ p h : ℝ, 0 ≤ p ∧ p ≤ 1 ∧ 0 ≤ h ∧
      x = -1+h*p+t*(1-a*(2-a)*p^2) ∧
      y = -1+h*(1-p)+t*(-1+a*(2-a)*(1-p)^2) := by
  have hU : 0 ≤ x+1-t := by
    have := (abs_le.mp hx).1
    linarith
  have hY : 0 ≤ y+1+t := by
    have := (abs_le.mp hy).1
    linarith
  obtain ⟨p, h, hp0, hp1, hh, hxeq, hyeq⟩ :=
    radial_representation (k := a*(2-a)*t) hU hY
  refine ⟨p, h, hp0, hp1, hh, ?_, ?_⟩
  · nlinarith only [hxeq]
  · nlinarith only [hyeq]

theorem transverse_bounds {x y t : ℝ}
    (hx : |x| ≤ 1-t) (hy : |y| ≤ 1+t) :
    |(x-y)/2| ≤ 1 ∧ |(x-y)/2| ≤ 1-|t|+|x+y|/2 := by
  have habs : |(x-y)/2| = |x-y|/2 := by
    rw [abs_div]
    norm_num
  constructor
  · rw [habs]
    have := abs_sub x y
    linarith
  · by_cases ht : 0 ≤ t
    · rw [abs_of_nonneg ht]
      have heq : (x-y)/2 = x-(x+y)/2 := by ring
      rw [heq]
      have htri := abs_sub x ((x+y)/2)
      have hsum : |(x+y)/2| = |x+y|/2 := by
        rw [abs_div]
        norm_num
      rw [hsum] at htri
      linarith
    · have ht' : t ≤ 0 := le_of_not_ge ht
      rw [abs_of_nonpos ht']
      have heq : (x-y)/2 = (x+y)/2-y := by ring
      rw [heq]
      have htri := abs_sub ((x+y)/2) y
      have hsum : |(x+y)/2| = |x+y|/2 := by
        rw [abs_div]
        norm_num
      rw [hsum] at htri
      linarith

theorem outside_left_representation {a x y t : ℝ}
    (hx : |x| ≤ 1-t) (hy : |y| ≤ 1+t)
    (hout : ¬ leftCoordinates a x y t) :
    ∃ q d : ℝ, |q| ≤ 1 ∧ 0 < d ∧
      x+y = -a-2*a*t*((2-a)*q/2)+d ∧
      (x-y)/2 = t+(2-a)*q/2+d*q/2-a*t*((2-a)*(1+q^2)/4) := by
  obtain ⟨p, h, hp0, hp1, hh, hxeq, hyeq⟩ := coordinate_representation a hx hy
  have hhlarge : 2-a < h := by
    by_contra hle
    exact hout ⟨p, h, hp0, hp1, hh, le_of_not_gt hle, hxeq, hyeq⟩
  refine ⟨2*p-1, h-(2-a), abs_le.mpr ⟨by linarith, by linarith⟩,
    sub_pos.mpr hhlarge, ?_, ?_⟩
  · nlinarith only [hxeq, hyeq]
  · nlinarith only [hxeq, hyeq]

theorem coordinate_coverage {a x y t : ℝ}
    (ha : 0 ≤ a) (ha' : a ≤ 1/2) (ht : |t| ≤ 1)
    (hx : |x| ≤ 1-t) (hy : |y| ≤ 1+t) :
    leftCoordinates a x y t ∨ leftCoordinates a (-x) (-y) t ∨
      |x+y+drift a t*((x-y)/2)| ≤ width a t := by
  by_cases hminus : leftCoordinates a x y t
  · exact Or.inl hminus
  by_cases hplus : leftCoordinates a (-x) (-y) t
  · exact Or.inr (Or.inl hplus)
  refine Or.inr (Or.inr ?_)
  obtain ⟨q,d,hq,hd,hs,hl⟩ := outside_left_representation hx hy hminus
  obtain ⟨q',d',hq',hd',hs',hl'⟩ := outside_left_representation
    (by simpa only [abs_neg] using hx) (by simpa only [abs_neg] using hy) hplus
  have hN : 2-a ≠ 0 := by linarith
  have hform (r : ℝ) :
      (2-a)*(1+r^2)/4 = (2-a)/4+((2-a)*r/2)^2/(2-a) := by
    field_simp
    ring
  rw [hform] at hl hl'
  have hsref : -(x+y) = -a-2*a*t*((2-a)*q'/2)+d' := by
    linarith only [hs']
  have hlref : -((x-y)/2) =
      t+(2-a)*q'/2+d'*q'/2-a*t*((2-a)/4+((2-a)*q'/2)^2/(2-a)) := by
    linarith only [hl']
  exact CylinderCovering.BeamAlgebra.explicit_strip_bound ha ha' ht
    (transverse_bounds hx hy).1 (transverse_bounds hx hy).2
    hd.le hd'.le hq hq' rfl rfl hs hsref hl hlref

theorem tetrahedron_covered {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1/2) :
    tetrahedron ⊆ beamMinus a ∪ beamPlus a ∪ strip a := by
  rintro z ⟨x,y,t,ht,hx,hy,rfl⟩
  rcases coordinate_coverage ha ha' ht hx hy with hm | hp | hs
  · exact Or.inl (Or.inl ⟨x,y,t,ht,hm,rfl⟩)
  · exact Or.inl (Or.inr ⟨x,y,t,ht,hp,rfl⟩)
  · exact Or.inr ⟨x,y,t,ht,hx,hy,hs,rfl⟩

theorem beamMinus_isCompact (a : ℝ) : IsCompact (beamMinus a) := by
  let D : Set (ℝ × ℝ × ℝ) :=
    Set.Icc 0 1 ×ˢ (Set.Icc 0 (2-a) ×ˢ Set.Icc (-1) 1)
  let F : (ℝ × ℝ × ℝ) → Space := fun z =>
    point (-1+z.2.1*z.1+z.2.2*(1-a*(2-a)*z.1^2))
      (-1+z.2.1*(1-z.1)+z.2.2*(-1+a*(2-a)*(1-z.1)^2)) z.2.2
  have hD : IsCompact D := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hF : Continuous F := by
    dsimp [F, point]
    fun_prop
  have heq : F '' D = beamMinus a := by
    ext z
    constructor
    · rintro ⟨⟨p,h,t⟩, hpht, rfl⟩
      rcases hpht with ⟨hp, hh, ht⟩
      refine ⟨_, _, t, abs_le.mpr ht, ?_, rfl⟩
      exact ⟨p, h, hp.1, hp.2, hh.1, hh.2, rfl, rfl⟩
    · rintro ⟨x,y,t,ht,⟨p,h,hp0,hp1,hh0,hh1,hx,hy⟩,hz⟩
      refine ⟨(p,h,t), ⟨⟨hp0,hp1⟩,⟨hh0,hh1⟩,abs_le.mp ht⟩, ?_⟩
      dsimp [F]
      rw [← hx, ← hy]
      exact hz.symm
  rw [← heq]
  exact hD.image hF

theorem beamPlus_isCompact (a : ℝ) : IsCompact (beamPlus a) := by
  let D : Set (ℝ × ℝ × ℝ) :=
    Set.Icc 0 1 ×ˢ (Set.Icc 0 (2-a) ×ˢ Set.Icc (-1) 1)
  let F : (ℝ × ℝ × ℝ) → Space := fun z =>
    point (-(-1+z.2.1*z.1+z.2.2*(1-a*(2-a)*z.1^2)))
      (-(-1+z.2.1*(1-z.1)+z.2.2*(-1+a*(2-a)*(1-z.1)^2))) z.2.2
  have hD : IsCompact D := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hF : Continuous F := by
    dsimp [F, point]
    fun_prop
  have heq : F '' D = beamPlus a := by
    ext z
    constructor
    · rintro ⟨⟨p,h,t⟩, hpht, rfl⟩
      rcases hpht with ⟨hp, hh, ht⟩
      refine ⟨_, _, t, abs_le.mpr ht, ?_, rfl⟩
      refine ⟨p, h, hp.1, hp.2, hh.1, hh.2, ?_, ?_⟩ <;> simp
    · rintro ⟨x,y,t,ht,⟨p,h,hp0,hp1,hh0,hh1,hx,hy⟩,hz⟩
      refine ⟨(p,h,t), ⟨⟨hp0,hp1⟩,⟨hh0,hh1⟩,abs_le.mp ht⟩, ?_⟩
      dsimp [F]
      rw [← hx, ← hy, neg_neg, neg_neg]
      exact hz.symm
  rw [← heq]
  exact hD.image hF

end ShortenedBeam

end OAI
