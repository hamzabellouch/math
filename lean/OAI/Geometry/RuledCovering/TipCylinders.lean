import OAI.Geometry.RuledCovering.ConeVolume

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma IsTriangle.linear_image {E F : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    {P : Set E} (hP : IsTriangle P) (f : E →ₗ[ℝ] F) (hf : Function.Injective f) :
    IsTriangle (f '' P) := by
  obtain ⟨c,u,v,hli,rfl⟩ := hP
  refine ⟨f c,f u,f v,?_,?_⟩
  · have hli' := hli.map' f (LinearMap.ker_eq_bot.mpr hf)
    have heq : f ∘ ![u,v] = ![f u,f v] := by funext i; fin_cases i <;> rfl
    rwa [heq] at hli'
  · ext x
    constructor
    · rintro ⟨_,⟨s,t,hs,ht,hst,rfl⟩,rfl⟩
      exact ⟨s,t,hs,ht,hst,by simp⟩
    · rintro ⟨s,t,hs,ht,hst,rfl⟩
      exact ⟨c+s•u+t•v,⟨s,t,hs,ht,hst,rfl⟩,by simp⟩

lemma IsTriangle.translate {E : Type*} [AddCommGroup E] [Module ℝ E]
    {P : Set E} (hP : IsTriangle P) (a : E) :
    IsTriangle ((fun x => a+x) '' P) := by
  obtain ⟨c,u,v,hli,rfl⟩ := hP
  refine ⟨a+c,u,v,hli,?_⟩
  ext x
  constructor
  · rintro ⟨_,⟨s,t,hs,ht,hst,rfl⟩,rfl⟩
    exact ⟨s,t,hs,ht,hst,by abel_nf⟩
  · rintro ⟨s,t,hs,ht,hst,rfl⟩
    exact ⟨c+s•u+t•v,⟨s,t,hs,ht,hst,rfl⟩,by abel_nf⟩

lemma Cylinder.rotate_triangle {C : Cylinder} (hC : C.triangle)
    (R : Space ≃ₗᵢ[ℝ] Space) : (C.rotate R).triangle :=
  hC.linear_image (rotatedPlane C.axis R).toLinearMap (rotatedPlane C.axis R).injective

lemma Cylinder.translate_triangle {C : Cylinder} (hC : C.triangle) (q : Space) :
    (C.translate q).triangle := hC.translate (C.transversePart q)

lemma coneTriangle_triangle {a : ℝ} (ha : 0 < a) : IsTriangle (coneTriangle a) := by
  refine ⟨0,vec2 a a,vec2 (-a) a,?_,?_⟩
  · rw [LinearIndependent.pair_iff]
    intro s t he
    have h0 := congrArg (fun z : Plane => z 0) he
    have h1 := congrArg (fun z : Plane => z 1) he
    simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,vec2_apply_zero,vec2_apply_one,
      PiLp.zero_apply] at h0 h1
    constructor
    · exact (mul_eq_zero.mp (by linarith : s*a=0)).resolve_right ha.ne'
    · exact (mul_eq_zero.mp (by linarith : t*a=0)).resolve_right ha.ne'
  · ext z
    constructor
    · intro hz
      have hab := abs_le.mp hz.2.2
      refine ⟨(z 1+z 0)/(2*a),(z 1-z 0)/(2*a),
        div_nonneg (by linarith [hab.1]) (by positivity),
        div_nonneg (by linarith [hab.2]) (by positivity),?_,?_⟩
      · rw [← add_div,div_le_one (by positivity : 0 < 2*a)]
        linarith [hz.2.1]
      · ext i
        fin_cases i <;> simp [vec2] <;> field_simp <;> ring
    · rintro ⟨s,t,hs,ht,hst,rfl⟩
      simp only [coneTriangle,mem_ofPred_eq,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,
        vec2_apply_one,vec2_apply_zero,zero_add]
      refine ⟨by positivity,by nlinarith,abs_le.mpr ⟨by nlinarith,by nlinarith⟩⟩

def lowerTipCylinder (d : ℝ) : Cylinder :=
  projectedCylinder (Real.sqrt 2) 0 (coneTriangle (2*d))

def upperTipCylinder (d : ℝ) : Cylinder :=
  ((lowerTipCylinder d).rotate swapReflect).translate (vec3 0 0 (Real.sqrt 2))

lemma lowerTipCylinder_triangle {d : ℝ} (hd : 0 < d) : (lowerTipCylinder d).triangle :=
  (coneTriangle_triangle (by positivity : 0 < 2*d)).linear_image _
    (perpendicularProjection_injective (Real.sqrt_pos.mpr (by norm_num)) 0)

lemma upperTipCylinder_triangle {d : ℝ} (hd : 0 < d) : (upperTipCylinder d).triangle :=
  Cylinder.translate_triangle (Cylinder.rotate_triangle (lowerTipCylinder_triangle hd) swapReflect) _

lemma lowerTipCylinder_area {d : ℝ} (hd : 0 ≤ d) :
    (lowerTipCylinder d).area = 4*Real.sqrt 2*d^2 := by
  rw [lowerTipCylinder,projectedCylinder_area (Real.sqrt_pos.mpr (by norm_num)),
    coneTriangle_volume (by positivity : 0 ≤ 2*d)]
  simp only [physicalWeight,PiLp.zero_apply,zero_pow (by norm_num : 2 ≠ 0),add_zero,
    mul_zero,Real.sqrt_one,div_one,mul_one]
  ring

lemma upperTipCylinder_area {d : ℝ} (hd : 0 ≤ d) :
    (upperTipCylinder d).area = 4*Real.sqrt 2*d^2 := by
  rw [upperTipCylinder,Cylinder.translate_area,Cylinder.rotate_area,lowerTipCylinder_area hd]

lemma lowerTipCylinder_carrier (d : ℝ) : (lowerTipCylinder d).carrier = lowerTip d := by
  ext z
  rw [lowerTipCylinder,projectedCylinder_mem_iff]
  constructor
  · rintro ⟨b,hb,s,rfl⟩
    exact ⟨b 1,hb.1,hb.2.1,by simpa [planeEmbedding,physicalDirection,vec3] using hb.2.2,
      by simp [planeEmbedding,physicalDirection,vec3]⟩
  · rintro ⟨t,ht0,htd,hy,hz⟩
    refine ⟨vec2 (z 1) t,⟨ht0,htd,hy⟩,z 0,?_⟩
    ext i
    fin_cases i <;> simp [planeEmbedding,physicalDirection,vec3,hz]

lemma upperTip_image (d : ℝ) :
    (fun z => vec3 0 0 (Real.sqrt 2)+z) '' (swapReflect '' lowerTip d) = upperTip d := by
  ext z
  constructor
  · rintro ⟨_,⟨w,⟨t,ht0,htd,hy,hz⟩,rfl⟩,rfl⟩
    refine ⟨t,ht0,htd,by simpa [swapReflect,vec3] using hy,?_⟩
    change Real.sqrt 2 + -(w 2) = Real.sqrt 2*(1-t)
    rw [hz]
    ring
  · rintro ⟨t,ht0,htd,hx,hz⟩
    refine ⟨swapReflect (vec3 (z 1) (z 0) (Real.sqrt 2*t)),
      ⟨vec3 (z 1) (z 0) (Real.sqrt 2*t),⟨t,ht0,htd,hx,rfl⟩,rfl⟩,?_⟩
    ext i
    fin_cases i <;> simp [swapReflect,vec3,hz]
    ring

lemma upperTipCylinder_carrier (d : ℝ) : (upperTipCylinder d).carrier = upperTip d := by
  rw [upperTipCylinder,Cylinder.translate_carrier,Cylinder.rotate_carrier,lowerTipCylinder_carrier,
    upperTip_image]

end RuledApproximation

end

end OAI
