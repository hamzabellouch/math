import Mathlib

namespace OAI

noncomputable section
namespace EuclideanFiveColor
def ThreeLabelRegion (x y : ℝ) : Prop :=
  0<x^2+y^2 ∧ x^2+y^2<4 ∧
    y^2*(3*x^2-y^2)^2 < (x^2+y^2)^3*(1-(x^2+y^2)/4)*(x^2+y^2-1)^2
lemma square_coordinate_bounds {x c h : ℝ} (_hh : 0≤h) (hc : h≤|c|) (hx : |x-c|≤h) :
    (|c|-h)^2≤x^2 ∧ x^2≤(|c|+h)^2 := by
  have hu : |x|≤|c|+h := by
    calc |x|=|c+(x-c)| := by congr 1; ring
         _≤|c|+|x-c| := abs_add_le _ _
         _≤|c|+h := by linarith
  have hl : |c|-h≤|x| := by
    have ht : |c|≤|x|+|x-c| := by
      calc |c|=|x-(x-c)| := by congr 1; ring
           _≤|x|+|x-c| := abs_sub _ _
    linarith
  constructor
  · simpa only [sq_abs] using pow_le_pow_left₀ (sub_nonneg.mpr hc) hl 2
  · simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg x) hu 2
lemma region_of_rational_bounds {x y a b Y H d : ℝ}
    (ha : 0<a) (hb : b<4) (hY : 0≤Y) (_hH : 0≤H) (hd : 0≤d)
    (hl : a≤x^2+y^2) (hu : x^2+y^2≤b)
    (hy : y^2≤Y) (habs : |3*x^2-y^2|≤H) (hg : d≤|x^2+y^2-1|)
    (hnum : Y*H^2<a^3*(1-b/4)*d^2) : ThreeLabelRegion x y := by
  refine ⟨lt_of_lt_of_le ha hl,lt_of_le_of_lt hu hb,?_⟩
  calc y^2*(3*x^2-y^2)^2 ≤ Y*H^2 := by
         have hpow : (3*x^2-y^2)^2≤H^2 := by
           simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) habs 2
         exact mul_le_mul hy hpow (sq_nonneg _) hY
       _ < a^3*(1-b/4)*d^2 := hnum
       _ ≤ (x^2+y^2)^3*(1-(x^2+y^2)/4)*(x^2+y^2-1)^2 := by
         have hnonneg : 0≤1-b/4 := by linarith
         have hgap : d^2≤(x^2+y^2-1)^2 := by
           simpa only [sq_abs] using pow_le_pow_left₀ hd hg 2
         have hpos : 0≤(x^2+y^2)^3*(1-(x^2+y^2)/4) :=
           mul_nonneg (pow_nonneg (le_trans ha.le hl) _) (by linarith)
         gcongr
lemma abs_le_of_bounds {x l u c h : ℝ} (hl : l≤x) (hu : x≤u)
    (hc1 : c-h≤l) (hc2 : u≤c+h) : |x-c|≤h := by
  rw [abs_le]; constructor <;> linarith
end EuclideanFiveColor
end

noncomputable section
namespace EuclideanFiveColor
lemma sin_sub_add_product (a b : ℝ) :
    Real.sin (a-b)*Real.sin (a+b)=Real.sin a^2-Real.sin b^2 := by
  rw [Real.sin_sub,Real.sin_add]
  have ha : Real.cos a^2=1-Real.sin a^2 := by linarith [Real.sin_sq_add_cos_sq a]
  have hb : Real.cos b^2=1-Real.sin b^2 := by linarith [Real.sin_sq_add_cos_sq b]
  calc _ = Real.sin a^2*Real.cos b^2-Real.cos a^2*Real.sin b^2 := by ring
       _ = _ := by rw [ha,hb]; ring
lemma sin_three_using_cos (a : ℝ) :
    Real.sin (3*a)=Real.sin a*(4*Real.cos a^2-1) := by
  rw [Real.sin_three_mul]
  nlinarith [congrArg (fun x : ℝ => Real.sin a*x) (Real.sin_sq_add_cos_sq a)]
/-- Exact strict angular form of the manuscript's polynomial region. -/
lemma polynomial_region_angles {z : ℂ} (hz : ThreeLabelRegion z.re z.im) :
    ∃ t u : ℝ, (Circle.exp t : ℂ)+(Circle.exp u : ℂ)=z ∧
      Real.sin (u-t)≠0 ∧ Real.sin (3*t)*Real.sin (3*u)<0 := by
  let r : ℝ := ‖z‖
  let p : ℝ := z.arg
  let d : ℝ := Real.arccos (r/2)
  have hr2 : r^2=z.re^2+z.im^2 := by
    change ‖z‖^2=_
    rw [Complex.sq_norm,Complex.normSq_apply]
    ring
  have hr0 : 0<r := by
    have hn : 0≤r := norm_nonneg z
    nlinarith [hz.1]
  have hrlt : r<2 := by nlinarith [hz.2.1]
  have hdcos : Real.cos d=r/2 := Real.cos_arccos (by linarith) (by linarith)
  have hd0 : 0<d := Real.arccos_pos.mpr (by linarith)
  have hdlt : d<Real.pi/2 := Real.arccos_lt_pi_div_two.mpr (by positivity)
  have hdsin : 0<Real.sin d := Real.sin_pos_of_pos_of_lt_pi hd0 (by linarith [Real.pi_pos])
  have hdsq : Real.sin d^2=1-r^2/4 := by
    have hh := Real.sin_sq_add_cos_sq d
    rw [hdcos] at hh
    nlinarith
  have hdp : Real.sin (3*d)=Real.sin d*(r^2-1) := by
    rw [sin_three_using_cos,hdcos]; ring
  have hpysin : r*Real.sin p=z.im := Complex.norm_mul_sin_arg z
  have hpxcos : r*Real.cos p=z.re := Complex.norm_mul_cos_arg z
  have hpy : r^3*Real.sin (3*p)=z.im*(3*z.re^2-z.im^2) := by
    rw [Real.sin_three_mul]
    calc _ = 3*r^2*(r*Real.sin p)-4*(r*Real.sin p)^3 := by ring
         _ = _ := by rw [hr2,hpysin]; ring
  have hP : z.im^2*(3*z.re^2-z.im^2)^2=r^6*Real.sin (3*p)^2 := by
    calc _ = (z.im*(3*z.re^2-z.im^2))^2 := by ring
         _ = (r^3*Real.sin (3*p))^2 := by rw [hpy]
         _ = _ := by ring
  have hP' : (z.re^2+z.im^2)^3*(1-(z.re^2+z.im^2)/4)*(z.re^2+z.im^2-1)^2=
      r^6*Real.sin (3*d)^2 := by
    rw [←hr2,hdp]
    rw [show 1-r^2/4=Real.sin d^2 from hdsq.symm]
    ring
  have hlt : Real.sin (3*p)^2<Real.sin (3*d)^2 := by
    have hh := hz.2.2
    rw [hP,hP'] at hh
    exact (mul_lt_mul_iff_right₀ (pow_pos hr0 6)).mp hh
  refine ⟨p-d,p+d,?_,?_,?_⟩
  · apply Complex.ext
    · simp only [Complex.add_re,Circle.coe_exp,Complex.exp_mul_I,
        ←Complex.ofReal_cos,←Complex.ofReal_sin,Complex.add_re,Complex.mul_re,
        Complex.ofReal_re,Complex.I_re,Complex.ofReal_im,Complex.I_im,mul_zero,
        sub_zero,zero_mul,add_zero]
      rw [Real.cos_sub,Real.cos_add,hdcos]
      nlinarith
    · simp only [Complex.add_im,Circle.coe_exp,Complex.exp_mul_I,
        ←Complex.ofReal_cos,←Complex.ofReal_sin,Complex.add_im,Complex.mul_im,
        Complex.ofReal_re,Complex.I_re,Complex.ofReal_im,Complex.I_im,mul_zero,
        mul_one,add_zero,zero_add]
      rw [Real.sin_sub,Real.sin_add,hdcos]
      nlinarith
  · rw [show p+d-(p-d)=2*d by ring,Real.sin_two_mul,hdcos]
    exact ne_of_gt (by positivity)
  · rw [mul_sub,mul_add,sin_sub_add_product]
    linarith
end EuclideanFiveColor
end

noncomputable section
namespace EuclideanFiveColor
def moserA : ℂ := ((Real.sqrt 3 : ℂ)+Complex.I)/2
def moserB : ℂ := ((Real.sqrt 3 : ℂ)-Complex.I)/2
def moserT : ℂ := Real.sqrt 3
def moserU : ℂ := (5+Complex.I*(Real.sqrt 11 : ℂ))/6
def moserPoint : Fin 7 → ℂ := ![0,moserA,moserB,moserT,moserU*moserA,moserU*moserB,moserU*moserT]
@[simp] lemma moserPoint_0 : moserPoint 0=0 := rfl
@[simp] lemma moserPoint_1 : moserPoint 1=moserA := rfl
@[simp] lemma moserPoint_2 : moserPoint 2=moserB := rfl
@[simp] lemma moserPoint_3 : moserPoint 3=moserT := rfl
@[simp] lemma moserPoint_4 : moserPoint 4=moserU*moserA := rfl
@[simp] lemma moserPoint_5 : moserPoint 5=moserU*moserB := rfl
@[simp] lemma moserPoint_6 : moserPoint 6=moserU*moserT := rfl
def moserEdges : Finset (Fin 7 × Fin 7) :=
  {(0,1),(0,2),(1,2),(3,1),(3,2),(0,4),(0,5),(4,5),(6,4),(6,5),(3,6)}
lemma complex_norm_one_of_sq {z : ℂ} (h : z.re^2+z.im^2=1) : ‖z‖=1 := by
  have he : ‖z‖^2=1 := by rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply]; nlinarith
  nlinarith [norm_nonneg z]
lemma moser_edge_unit {i j : Fin 7} (h : (i,j)∈moserEdges) : ‖moserPoint i-moserPoint j‖=1 := by
  have h3 := Real.sq_sqrt (show (0:ℝ)≤3 by norm_num)
  have h11 := Real.sq_sqrt (show (0:ℝ)≤11 by norm_num)
  simp only [moserEdges,Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq] at h
  rcases h with h|h|h|h|h|h|h|h|h|h|h <;> rcases h with ⟨rfl,rfl⟩
  all_goals
    apply complex_norm_one_of_sq
    norm_num [moserA,moserB,moserT,moserU,Complex.mul_re,Complex.mul_im,
      Complex.div_ofReal_re,Complex.div_ofReal_im,Complex.sub_re,Complex.sub_im,
      Complex.add_re,Complex.add_im] <;>
      (ring_nf; norm_num [h3,h11])
lemma three_color_diamond {a b p q : Fin 3} (hab : a≠b)
    (hpa : p≠a) (hpb : p≠b) (hqa : q≠a) (hqb : q≠b) : p=q := by
  fin_cases a <;> fin_cases b <;> fin_cases p <;> fin_cases q <;> simp_all
lemma moser_not_three_colorable (f : Fin 7 → Fin 3)
    (hf : ∀i j,(i,j)∈moserEdges → f i≠f j) : False := by
  have h03 : f 0=f 3 := three_color_diamond
    (hf 1 2 (by decide)) (hf 0 1 (by decide)) (hf 0 2 (by decide))
    (hf 3 1 (by decide)) (hf 3 2 (by decide))
  have h06 : f 0=f 6 := three_color_diamond
    (hf 4 5 (by decide)) (hf 0 4 (by decide)) (hf 0 5 (by decide))
    (hf 6 4 (by decide)) (hf 6 5 (by decide))
  exact hf 3 6 (by decide) (h03.symm.trans h06)
def moserRotation : ℂ := (35+12*Complex.I)/37
def placedMoser (i : Fin 7) : ℂ := moserRotation*(moserPoint i+(-290+149*Complex.I)/250)
lemma moserRotation_unit : ‖moserRotation‖=1 := by
  apply complex_norm_one_of_sq
  norm_num [moserRotation,Complex.div_ofReal_re,Complex.div_ofReal_im]
lemma placedMoser_edge_unit {i j : Fin 7} (h : (i,j)∈moserEdges) : ‖placedMoser i-placedMoser j‖=1 := by
  have he : placedMoser i-placedMoser j=moserRotation*(moserPoint i-moserPoint j) := by
    unfold placedMoser; ring
  rw [he,norm_mul,moserRotation_unit,moser_edge_unit h,one_mul]
end EuclideanFiveColor
end

noncomputable section
namespace EuclideanFiveColor
def certificateX : Fin 7 → ℝ := ![-1.2906,-0.6335,-0.3092,0.3478,-1.1598,-0.3666,-0.2358]
def certificateY : Fin 7 → ℝ := ![0.1876,0.9414,-0.0045,0.7493,1.1790,0.5700,1.5614]
lemma radical_bounds : 1.73205<Real.sqrt 3 ∧ Real.sqrt 3<1.73206 ∧
    3.31662<Real.sqrt 11 ∧ Real.sqrt 11<3.31663 := by
  have h3 := Real.sq_sqrt (show (0:ℝ)≤3 by norm_num)
  have h11 := Real.sq_sqrt (show (0:ℝ)≤11 by norm_num)
  have hn3 := Real.sqrt_nonneg (3:ℝ)
  have hn11 := Real.sqrt_nonneg (11:ℝ)
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith
lemma radical_product_bounds : (1.73205*3.31662 : ℝ)≤Real.sqrt 3*Real.sqrt 11 ∧
    Real.sqrt 3*Real.sqrt 11≤1.73206*3.31663 := by
  obtain ⟨ha,hb,hc,hd⟩ := radical_bounds
  constructor <;> gcongr
lemma seven_point_box_0 :
    |(placedMoser 0).re-certificateX 0|≤(0.00011 : ℝ) ∧
    |(placedMoser 0).im-certificateY 0|≤(0.00011 : ℝ) := by
  obtain ⟨ha,hb,hc,hd⟩ := radical_bounds
  obtain ⟨hp,hq⟩ := radical_product_bounds
  change |(placedMoser 0).re-(-1.2906)|≤0.00011 ∧ |(placedMoser 0).im-(0.1876)|≤0.00011
  norm_num [placedMoser,moserRotation,moserA,moserB,moserT,moserU,
    Complex.mul_re,Complex.mul_im,Complex.div_ofReal_re,Complex.div_ofReal_im,
    Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im]
lemma seven_point_box_1 :
    |(placedMoser 1).re-certificateX 1|≤(0.00011 : ℝ) ∧
    |(placedMoser 1).im-certificateY 1|≤(0.00011 : ℝ) := by
  obtain ⟨ha,hb,hc,hd⟩ := radical_bounds
  obtain ⟨hp,hq⟩ := radical_product_bounds
  change |(placedMoser 1).re-(-0.6335)|≤0.00011 ∧ |(placedMoser 1).im-(0.9414)|≤0.00011
  norm_num [placedMoser,moserRotation,moserA,moserB,moserT,moserU,
    Complex.mul_re,Complex.mul_im,Complex.div_ofReal_re,Complex.div_ofReal_im,
    Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im]
  constructor <;> rw [abs_le] <;> constructor <;> nlinarith
lemma seven_point_box_2 :
    |(placedMoser 2).re-certificateX 2|≤(0.00011 : ℝ) ∧
    |(placedMoser 2).im-certificateY 2|≤(0.00011 : ℝ) := by
  obtain ⟨ha,hb,hc,hd⟩ := radical_bounds
  obtain ⟨hp,hq⟩ := radical_product_bounds
  change |(placedMoser 2).re-(-0.3092)|≤0.00011 ∧ |(placedMoser 2).im-(-0.0045)|≤0.00011
  norm_num [placedMoser,moserRotation,moserA,moserB,moserT,moserU,
    Complex.mul_re,Complex.mul_im,Complex.div_ofReal_re,Complex.div_ofReal_im,
    Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im]
  constructor <;> rw [abs_le] <;> constructor <;> nlinarith
lemma seven_point_box_3 :
    |(placedMoser 3).re-certificateX 3|≤(0.00011 : ℝ) ∧
    |(placedMoser 3).im-certificateY 3|≤(0.00011 : ℝ) := by
  obtain ⟨ha,hb,hc,hd⟩ := radical_bounds
  obtain ⟨hp,hq⟩ := radical_product_bounds
  change |(placedMoser 3).re-(0.3478)|≤0.00011 ∧ |(placedMoser 3).im-(0.7493)|≤0.00011
  norm_num [placedMoser,moserRotation,moserA,moserB,moserT,moserU,
    Complex.mul_re,Complex.mul_im,Complex.div_ofReal_re,Complex.div_ofReal_im,
    Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im]
  constructor <;> rw [abs_le] <;> constructor <;> nlinarith
lemma seven_point_box_4 :
    |(placedMoser 4).re-certificateX 4|≤(0.00011 : ℝ) ∧
    |(placedMoser 4).im-certificateY 4|≤(0.00011 : ℝ) := by
  obtain ⟨ha,hb,hc,hd⟩ := radical_bounds
  obtain ⟨hp,hq⟩ := radical_product_bounds
  change |(placedMoser 4).re-(-1.1598)|≤0.00011 ∧ |(placedMoser 4).im-(1.1790)|≤0.00011
  norm_num [placedMoser,moserRotation,moserA,moserB,moserT,moserU,
    Complex.mul_re,Complex.mul_im,Complex.div_ofReal_re,Complex.div_ofReal_im,
    Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im]
  constructor <;> rw [abs_le] <;> constructor <;> nlinarith
lemma seven_point_box_5 :
    |(placedMoser 5).re-certificateX 5|≤(0.00011 : ℝ) ∧
    |(placedMoser 5).im-certificateY 5|≤(0.00011 : ℝ) := by
  obtain ⟨ha,hb,hc,hd⟩ := radical_bounds
  obtain ⟨hp,hq⟩ := radical_product_bounds
  change |(placedMoser 5).re-(-0.3666)|≤0.00011 ∧ |(placedMoser 5).im-(0.5700)|≤0.00011
  norm_num [placedMoser,moserRotation,moserA,moserB,moserT,moserU,
    Complex.mul_re,Complex.mul_im,Complex.div_ofReal_re,Complex.div_ofReal_im,
    Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im]
  constructor <;> rw [abs_le] <;> constructor <;> nlinarith
lemma seven_point_box_6 :
    |(placedMoser 6).re-certificateX 6|≤(0.00011 : ℝ) ∧
    |(placedMoser 6).im-certificateY 6|≤(0.00011 : ℝ) := by
  obtain ⟨ha,hb,hc,hd⟩ := radical_bounds
  obtain ⟨hp,hq⟩ := radical_product_bounds
  change |(placedMoser 6).re-(-0.2358)|≤0.00011 ∧ |(placedMoser 6).im-(1.5614)|≤0.00011
  norm_num [placedMoser,moserRotation,moserA,moserB,moserT,moserU,
    Complex.mul_re,Complex.mul_im,Complex.div_ofReal_re,Complex.div_ofReal_im,
    Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im]
  constructor <;> rw [abs_le] <;> constructor <;> nlinarith
lemma seven_point_boxes (i : Fin 7) :
    |(placedMoser i).re-certificateX i|≤(0.00011 : ℝ) ∧
    |(placedMoser i).im-certificateY i|≤(0.00011 : ℝ) := by
  fin_cases i
  · exact seven_point_box_0
  · exact seven_point_box_1
  · exact seven_point_box_2
  · exact seven_point_box_3
  · exact seven_point_box_4
  · exact seven_point_box_5
  · exact seven_point_box_6
end EuclideanFiveColor
end

noncomputable section
namespace EuclideanFiveColor
/-- Exact rational interval certificate for the manuscript's seven placed vertices. -/
lemma seven_point_certificate (i : Fin 7) :
    ThreeLabelRegion (placedMoser i).re (placedMoser i).im := by
  obtain ⟨hx,hy⟩ := seven_point_boxes i
  fin_cases i
  · change ThreeLabelRegion (placedMoser 0).re (placedMoser 0).im
    change |(placedMoser 0).re-(-1.2906)|≤0.00011 at hx
    change |(placedMoser 0).im-(0.1876)|≤0.00011 at hy
    have hxx := square_coordinate_bounds (by norm_num : (0:ℝ)≤0.00011)
      (by norm_num : (0.00011:ℝ)≤|(-1.2906:ℝ)|) hx
    have hyy := square_coordinate_bounds (by norm_num : (0:ℝ)≤0.00011)
      (by norm_num : (0.00011:ℝ)≤|(0.1876:ℝ)|) hy
    norm_num at hxx hyy
    apply region_of_rational_bounds (a := 1.70) (b := 1.71) (Y := 0.0353) (H := 4.963) (d := 0.70)
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · nlinarith [hxx.1,hyy.1]
    · nlinarith [hxx.2,hyy.2]
    · nlinarith [hyy.2]
    · rw [abs_le]; constructor <;> nlinarith [hxx.1,hxx.2,hyy.1,hyy.2]
    · have hh := le_abs_self ((placedMoser 0).re^2+(placedMoser 0).im^2-1)
      nlinarith [hxx.1,hxx.2,hyy.1,hyy.2]
    · norm_num
  · change ThreeLabelRegion (placedMoser 1).re (placedMoser 1).im
    change |(placedMoser 1).re-(-0.6335)|≤0.00011 at hx
    change |(placedMoser 1).im-(0.9414)|≤0.00011 at hy
    have hxx := square_coordinate_bounds (by norm_num : (0:ℝ)≤0.00011)
      (by norm_num : (0.00011:ℝ)≤|(-0.6335:ℝ)|) hx
    have hyy := square_coordinate_bounds (by norm_num : (0:ℝ)≤0.00011)
      (by norm_num : (0.00011:ℝ)≤|(0.9414:ℝ)|) hy
    norm_num at hxx hyy
    apply region_of_rational_bounds (a := 1.28) (b := 1.29) (Y := 0.887) (H := 0.319) (d := 0.28)
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · nlinarith [hxx.1,hyy.1]
    · nlinarith [hxx.2,hyy.2]
    · nlinarith [hyy.2]
    · rw [abs_le]; constructor <;> nlinarith [hxx.1,hxx.2,hyy.1,hyy.2]
    · have hh := le_abs_self ((placedMoser 1).re^2+(placedMoser 1).im^2-1)
      nlinarith [hxx.1,hxx.2,hyy.1,hyy.2]
    · norm_num
  · change ThreeLabelRegion (placedMoser 2).re (placedMoser 2).im
    change |(placedMoser 2).re-(-0.3092)|≤0.00011 at hx
    change |(placedMoser 2).im-(-0.0045)|≤0.00011 at hy
    have hxx := square_coordinate_bounds (by norm_num : (0:ℝ)≤0.00011)
      (by norm_num : (0.00011:ℝ)≤|(-0.3092:ℝ)|) hx
    have hyy := square_coordinate_bounds (by norm_num : (0:ℝ)≤0.00011)
      (by norm_num : (0.00011:ℝ)≤|(-0.0045:ℝ)|) hy
    norm_num at hxx hyy
    apply region_of_rational_bounds (a := 0.095) (b := 0.096) (Y := 0.000022) (H := 0.287) (d := 0.904)
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · nlinarith [hxx.1,hyy.1]
    · nlinarith [hxx.2,hyy.2]
    · nlinarith [hyy.2]
    · rw [abs_le]; constructor <;> nlinarith [hxx.1,hxx.2,hyy.1,hyy.2]
    · have hh := neg_le_abs ((placedMoser 2).re^2+(placedMoser 2).im^2-1)
      nlinarith [hxx.1,hxx.2,hyy.1,hyy.2]
    · norm_num
  · change ThreeLabelRegion (placedMoser 3).re (placedMoser 3).im
    change |(placedMoser 3).re-(0.3478)|≤0.00011 at hx
    change |(placedMoser 3).im-(0.7493)|≤0.00011 at hy
    have hxx := square_coordinate_bounds (by norm_num : (0:ℝ)≤0.00011)
      (by norm_num : (0.00011:ℝ)≤|(0.3478:ℝ)|) hx
    have hyy := square_coordinate_bounds (by norm_num : (0:ℝ)≤0.00011)
      (by norm_num : (0.00011:ℝ)≤|(0.7493:ℝ)|) hy
    norm_num at hxx hyy
    apply region_of_rational_bounds (a := 0.682) (b := 0.683) (Y := 0.562) (H := 0.199) (d := 0.317)
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · nlinarith [hxx.1,hyy.1]
    · nlinarith [hxx.2,hyy.2]
    · nlinarith [hyy.2]
    · rw [abs_le]; constructor <;> nlinarith [hxx.1,hxx.2,hyy.1,hyy.2]
    · have hh := neg_le_abs ((placedMoser 3).re^2+(placedMoser 3).im^2-1)
      nlinarith [hxx.1,hxx.2,hyy.1,hyy.2]
    · norm_num
  · change ThreeLabelRegion (placedMoser 4).re (placedMoser 4).im
    change |(placedMoser 4).re-(-1.1598)|≤0.00011 at hx
    change |(placedMoser 4).im-(1.1790)|≤0.00011 at hy
    have hxx := square_coordinate_bounds (by norm_num : (0:ℝ)≤0.00011)
      (by norm_num : (0.00011:ℝ)≤|(-1.1598:ℝ)|) hx
    have hyy := square_coordinate_bounds (by norm_num : (0:ℝ)≤0.00011)
      (by norm_num : (0.00011:ℝ)≤|(1.1790:ℝ)|) hy
    norm_num at hxx hyy
    apply region_of_rational_bounds (a := 2.73) (b := 2.74) (Y := 1.391) (H := 2.647) (d := 1.73)
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · nlinarith [hxx.1,hyy.1]
    · nlinarith [hxx.2,hyy.2]
    · nlinarith [hyy.2]
    · rw [abs_le]; constructor <;> nlinarith [hxx.1,hxx.2,hyy.1,hyy.2]
    · have hh := le_abs_self ((placedMoser 4).re^2+(placedMoser 4).im^2-1)
      nlinarith [hxx.1,hxx.2,hyy.1,hyy.2]
    · norm_num
  · change ThreeLabelRegion (placedMoser 5).re (placedMoser 5).im
    change |(placedMoser 5).re-(-0.3666)|≤0.00011 at hx
    change |(placedMoser 5).im-(0.5700)|≤0.00011 at hy
    have hxx := square_coordinate_bounds (by norm_num : (0:ℝ)≤0.00011)
      (by norm_num : (0.00011:ℝ)≤|(-0.3666:ℝ)|) hx
    have hyy := square_coordinate_bounds (by norm_num : (0:ℝ)≤0.00011)
      (by norm_num : (0.00011:ℝ)≤|(0.5700:ℝ)|) hy
    norm_num at hxx hyy
    apply region_of_rational_bounds (a := 0.459) (b := 0.46) (Y := 0.326) (H := 0.079) (d := 0.54)
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · nlinarith [hxx.1,hyy.1]
    · nlinarith [hxx.2,hyy.2]
    · nlinarith [hyy.2]
    · rw [abs_le]; constructor <;> nlinarith [hxx.1,hxx.2,hyy.1,hyy.2]
    · have hh := neg_le_abs ((placedMoser 5).re^2+(placedMoser 5).im^2-1)
      nlinarith [hxx.1,hxx.2,hyy.1,hyy.2]
    · norm_num
  · change ThreeLabelRegion (placedMoser 6).re (placedMoser 6).im
    change |(placedMoser 6).re-(-0.2358)|≤0.00011 at hx
    change |(placedMoser 6).im-(1.5614)|≤0.00011 at hy
    have hxx := square_coordinate_bounds (by norm_num : (0:ℝ)≤0.00011)
      (by norm_num : (0.00011:ℝ)≤|(-0.2358:ℝ)|) hx
    have hyy := square_coordinate_bounds (by norm_num : (0:ℝ)≤0.00011)
      (by norm_num : (0.00011:ℝ)≤|(1.5614:ℝ)|) hy
    norm_num at hxx hyy
    apply region_of_rational_bounds (a := 2.493) (b := 2.495) (Y := 2.44) (H := 2.273) (d := 1.493)
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · nlinarith [hxx.1,hyy.1]
    · nlinarith [hxx.2,hyy.2]
    · nlinarith [hyy.2]
    · rw [abs_le]; constructor <;> nlinarith [hxx.1,hxx.2,hyy.1,hyy.2]
    · have hh := le_abs_self ((placedMoser 6).re^2+(placedMoser 6).im^2-1)
      nlinarith [hxx.1,hxx.2,hyy.1,hyy.2]
    · norm_num
end EuclideanFiveColor
end

end OAI
