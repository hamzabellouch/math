import OAI.Geometry.CylinderCovering.Beams.sDefinitions

namespace OAI

noncomputable section
namespace ShortenedBeam

theorem leftCoordinates_zero_iff {a x y : ℝ} (ha : a ≤ 2) :
    leftCoordinates a x y 0 ↔ -1 ≤ x ∧ -1 ≤ y ∧ x+y ≤ -a := by
  constructor
  · rintro ⟨p,h,hp0,hp1,hh0,hh1,hx,hy⟩
    simp only [zero_mul, add_zero] at hx hy
    refine ⟨?_,?_,?_⟩
    · nlinarith [mul_nonneg hh0 hp0]
    · nlinarith [mul_nonneg hh0 (sub_nonneg.mpr hp1)]
    · nlinarith
  · rintro ⟨hx,hy,hxy⟩
    let h : ℝ := x+y+2
    have hh0 : 0 ≤ h := by dsimp [h]; linarith
    have hh1 : h ≤ 2-a := by dsimp [h]; linarith
    by_cases hh : h=0
    · have hxe : x = -1 := by dsimp [h] at hh; linarith
      have hye : y = -1 := by dsimp [h] at hh; linarith
      refine ⟨0,0,by norm_num,by norm_num,by norm_num,by linarith,?_,?_⟩
      · simp [hxe]
      · simp [hye]
    · have hhp : 0 < h := lt_of_le_of_ne hh0 (Ne.symm hh)
      refine ⟨(x+1)/h,h,div_nonneg (by linarith) hh0,?_,hh0,hh1,?_,?_⟩
      · apply (div_le_one hhp).mpr
        dsimp [h]
        linarith
      · simp only [zero_mul, add_zero]
        field_simp
        ring
      · simp only [zero_mul, add_zero]
        field_simp
        dsimp [h]
        ring

theorem reflected_leftCoordinates_zero_iff {a x y : ℝ} (ha : a ≤ 2) :
    leftCoordinates a (-x) (-y) 0 ↔ x ≤ 1 ∧ y ≤ 1 ∧ a ≤ x+y := by
  rw [leftCoordinates_zero_iff ha]
  constructor <;> rintro ⟨h1,h2,h3⟩ <;> constructor
  all_goals first | linarith | exact ⟨by linarith,by linarith⟩

theorem point_injective_three {x y t x' y' t' : ℝ}
    (h : point x y t = point x' y' t') : x=x' ∧ y=y' ∧ t=t' := by
  have hx := congrArg (fun z : Space => z 0) h
  have hy := congrArg (fun z : Space => z 1) h
  have ht := congrArg (fun z : Space => z 2) h
  change x / Real.sqrt 2 = x' / Real.sqrt 2 at hx
  change y / Real.sqrt 2 = y' / Real.sqrt 2 at hy
  change t=t' at ht
  have hs : Real.sqrt (2:ℝ) ≠ 0 := by positivity
  exact ⟨(div_left_inj' hs).mp hx,(div_left_inj' hs).mp hy,ht⟩

theorem point_zero_mem_beamMinus_iff {a x y : ℝ} (ha : a ≤ 2) :
    point x y 0 ∈ beamMinus a ↔ -1 ≤ x ∧ -1 ≤ y ∧ x+y ≤ -a := by
  constructor
  · rintro ⟨x',y',t,ht,hc,heq⟩
    obtain ⟨hx,hy,hz⟩ := point_injective_three heq
    subst x'
    subst y'
    subst t
    exact (leftCoordinates_zero_iff ha).mp hc
  · intro h
    exact ⟨x,y,0,by norm_num,(leftCoordinates_zero_iff ha).mpr h,rfl⟩

theorem point_zero_mem_beamPlus_iff {a x y : ℝ} (ha : a ≤ 2) :
    point x y 0 ∈ beamPlus a ↔ x ≤ 1 ∧ y ≤ 1 ∧ a ≤ x+y := by
  constructor
  · rintro ⟨x',y',t,ht,hc,heq⟩
    obtain ⟨hx,hy,hz⟩ := point_injective_three heq
    subst x'
    subst y'
    subst t
    exact (reflected_leftCoordinates_zero_iff ha).mp hc
  · intro h
    exact ⟨x,y,0,by norm_num,(reflected_leftCoordinates_zero_iff ha).mpr h,rfl⟩

theorem point_zero_outside_beams_iff {a x y : ℝ} (ha : a ≤ 2)
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    (point x y 0 ∉ beamMinus a ∧ point x y 0 ∉ beamPlus a) ↔ |x+y| < a := by
  rw [point_zero_mem_beamMinus_iff ha,point_zero_mem_beamPlus_iff ha]
  have hxl : -1 ≤ x := (abs_le.mp hx).1
  have hxu : x ≤ 1 := (abs_le.mp hx).2
  have hyl : -1 ≤ y := (abs_le.mp hy).1
  have hyu : y ≤ 1 := (abs_le.mp hy).2
  simp only [hxl,hxu,hyl,hyu,true_and,not_le,abs_lt]

end ShortenedBeam

end

end OAI
