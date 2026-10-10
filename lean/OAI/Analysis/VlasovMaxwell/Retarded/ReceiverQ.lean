import Mathlib
import OAI.Analysis.VlasovMaxwell.Population.NullConeFlux

namespace OAI

noncomputable section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

def receiverQ (a n h : Vec) : Vec := (1-dot n a) • h + dot a h • n

lemma receiverQ_force (a n h : Vec) : receiverQ a n h=h+cross a (cross n h) := by
  ext i
  fin_cases i <;> simp [receiverQ,cross,dot,Fin.sum_univ_succ] <;> ring

lemma receiverQ_add (a n h k : Vec) : receiverQ a n (h+k)=receiverQ a n h+receiverQ a n k := by
  simp only [receiverQ,dot_add_right,smul_add,add_smul]
  module

lemma receiverQ_smul (a n h : Vec) (c : ℝ) : receiverQ a n (c • h)=c • receiverQ a n h := by
  simp only [receiverQ,dot_smul_right,smul_add,smul_smul]
  module

lemma receiverQ_normal (a n : Vec) : receiverQ a n n=n := by
  rw [receiverQ,dot_comm a n,← add_smul]
  simp

lemma cone_denom_le_two (v n : Vec) (hn : ‖n‖=1) : 1-dot n (velocity v)≤2 := by
  have h := abs_dot_le n (velocity v)
  rw [hn,one_mul] at h
  have h' := (neg_le_abs (dot n (velocity v))).trans h
  linarith [norm_velocity_lt_one v]

lemma receiverQ_tangent_bound (w n h : Vec) (hn : ‖n‖=1) (hh : dot n h=0) :
    ‖receiverQ (velocity w) n h‖≤2*Real.sqrt (2*(1-dot n (velocity w)))*‖h‖ := by
  let D := 1-dot n (velocity w)
  have hD : 0≤D := (cone_denom_pos w n hn).le
  have hD2 : D≤2 := cone_denom_le_two w n hn
  have hDs : D≤Real.sqrt (2*D) := by
    nlinarith [Real.sq_sqrt (mul_nonneg (by norm_num : (0:ℝ)≤2) hD),Real.sqrt_nonneg (2*D)]
  have ha : |dot (velocity w) h|≤Real.sqrt (2*D)*‖h‖ := by
    rw [show dot (velocity w) h=dot (velocity w-n) h by rw [dot_sub_left,hh,sub_zero]]
    exact (abs_dot_le _ _).trans (mul_le_mul_of_nonneg_right
      (velocity_normal_distance_bound w n hn) (norm_nonneg h))
  calc
    _ ≤ ‖D • h‖+‖dot (velocity w) h • n‖ := norm_add_le _ _
    _ = D*‖h‖+|dot (velocity w) h| := by rw [norm_smul,norm_smul,Real.norm_eq_abs,
        Real.norm_eq_abs,abs_of_nonneg hD,hn,mul_one]
    _ ≤ 2*Real.sqrt (2*D)*‖h‖ := by nlinarith [mul_le_mul_of_nonneg_right hDs (norm_nonneg h)]

lemma velocity_tangent_norm (v n : Vec) (hn : ‖n‖=1) :
    ‖(n-velocity v)-(1-dot n (velocity v)) • n‖≤Real.sqrt (2*(1-dot n (velocity v))) := by
  have he : (n-velocity v)-(1-dot n (velocity v)) • n =
      -(velocityProjection n (velocity v-n)) := by
    simp only [velocityProjection,dot_sub_right,dot_self,hn,one_pow]
    module
  rw [he,norm_neg]
  exact (velocityProjection_norm _ _ hn.le).trans (velocity_normal_distance_bound v n hn)

lemma receiverQ_transport_bound (w v n : Vec) (hn : ‖n‖=1) :
    ‖receiverQ (velocity w) n (n-velocity v)‖ ≤ (1-dot n (velocity v))+
      2*Real.sqrt (2*(1-dot n (velocity w)))*Real.sqrt (2*(1-dot n (velocity v))) := by
  let d := 1-dot n (velocity v)
  let h := (n-velocity v)-d • n
  have hh : dot n h=0 := by
    dsimp only [h,d]
    simp only [dot_sub_right,dot_smul_right,dot_self,hn,one_pow,mul_one]
    ring
  have he : n-velocity v=d • n+h := by dsimp [h]; module
  rw [he,receiverQ_add,receiverQ_smul,receiverQ_normal]
  calc
    _ ≤ ‖d • n‖+‖receiverQ (velocity w) n h‖ := norm_add_le _ _
    _ ≤ d+2*Real.sqrt (2*(1-dot n (velocity w)))*Real.sqrt (2*d) := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (cone_denom_pos v n hn),hn,mul_one]
      exact add_le_add le_rfl ((receiverQ_tangent_bound w n h hn hh).trans
        (mul_le_mul_of_nonneg_left (velocity_tangent_norm v n hn) (by positivity)))

def sourceNumerator (n u b : Vec) : Vec := (dot n b) • (n-u)-(1-dot n u) • b

lemma sourceNumerator_tangent (n u b : Vec) (hn : ‖n‖=1) :
    dot n (sourceNumerator n u b)=0 := by
  simp only [sourceNumerator,dot_sub_right,dot_smul_right,dot_self,hn,one_pow]
  ring

lemma sourceNumerator_bound (v E B n : Vec) (hn : ‖n‖=1) :
    ‖sourceNumerator n (velocity v) (fderiv ℝ velocity v (E+cross (velocity v) B))‖ ≤
      5*(1-dot n (velocity v))*(q v)⁻¹*(goodField E B n+(1-dot n (velocity v))*‖B‖) := by
  let d := 1-dot n (velocity v)
  let b := fderiv ℝ velocity v (E+cross (velocity v) B)
  have hd : 0≤d := (cone_denom_pos v n hn).le
  have hq : 0≤(q v)⁻¹ := (inv_pos.mpr (q_pos v)).le
  have hG : 0≤goodField E B n := add_nonneg (norm_nonneg _) (abs_nonneg _)
  have hb := lorentz_source_acceleration_bound v E B n hn
  have hnb := lorentz_source_normal_acceleration_bound v E B n hn
  have hnu : ‖n-velocity v‖≤Real.sqrt (2*d) := by
    rw [norm_sub_rev]
    exact velocity_normal_distance_bound v n hn
  have hprod : |dot n b| *‖n-velocity v‖ ≤
      (q v)⁻¹*(2*d)*(goodField E B n+d*‖B‖) := by
    calc
      _ ≤ ((q v)⁻¹*Real.sqrt (2*d)*(goodField E B n+d*‖B‖))*Real.sqrt (2*d) :=
        mul_le_mul hnb hnu (norm_nonneg _) (by positivity)
      _ = (q v)⁻¹*(Real.sqrt (2*d))^2*(goodField E B n+d*‖B‖) := by ring
      _ = _ := by rw [Real.sq_sqrt (mul_nonneg (by norm_num : (0:ℝ)≤2) hd)]
  have hdb := mul_le_mul_of_nonneg_left hb hd
  calc
    _ ≤ |dot n b| *‖n-velocity v‖+d*‖b‖ := by
      exact (norm_sub_le _ _).trans (by rw [norm_smul,norm_smul,Real.norm_eq_abs,
        Real.norm_eq_abs,abs_of_nonneg hd])
    _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg hd hq) hG]

lemma receiverQ_source_bound (w v E B n : Vec) (hn : ‖n‖=1) :
    ‖receiverQ (velocity w) n
        (sourceNumerator n (velocity v) (fderiv ℝ velocity v (E+cross (velocity v) B)))‖ ≤
      10*Real.sqrt (2*(1-dot n (velocity w)))*(1-dot n (velocity v))*(q v)⁻¹*
        (goodField E B n+(1-dot n (velocity v))*‖B‖) := by
  exact (receiverQ_tangent_bound _ _ _ hn (sourceNumerator_tangent _ _ _ hn)).trans
    (by convert mul_le_mul_of_nonneg_left (sourceNumerator_bound v E B n hn)
          (show 0≤2*Real.sqrt (2*(1-dot n (velocity w))) by positivity) using 1; ring)

def transverseProjection (w h : Vec) : Vec := velocityProjection (‖w‖⁻¹ • w) h

lemma transverseProjection_norm (w h : Vec) : ‖transverseProjection w h‖≤‖h‖ := by
  apply velocityProjection_norm
  by_cases hw : w=0
  · simp [hw]
  · rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg w)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw)]

lemma velocityProjection_smul (u h : Vec) (c : ℝ) :
    velocityProjection u (c • h)=c • velocityProjection u h := by
  simp only [velocityProjection,dot_smul_right,smul_sub,smul_smul]

lemma transverseProjection_velocity (w : Vec) : transverseProjection w (velocity w)=0 := by
  by_cases hw : w=0
  · simp [hw,transverseProjection,velocityProjection,velocity,dot]
  · have hn := norm_ne_zero_iff.mpr hw
    ext i
    simp only [transverseProjection,velocityProjection,velocity,dot_smul_left,dot_smul_right,
      dot_self,PiLp.sub_apply,PiLp.smul_apply,PiLp.zero_apply,smul_eq_mul]
    field_simp
    ring

lemma transverseProjection_normal_bound (w n : Vec) (hn : ‖n‖=1) :
    ‖transverseProjection w n‖≤Real.sqrt (2*(1-dot n (velocity w))) := by
  have he : transverseProjection w n=transverseProjection w (n-velocity w) := by
    have h := velocityProjection_add (‖w‖⁻¹ • w) (n-velocity w) (velocity w)
    rw [sub_add_cancel] at h
    change transverseProjection w n=transverseProjection w (n-velocity w)+transverseProjection w (velocity w) at h
    rwa [transverseProjection_velocity,add_zero] at h
  rw [he]
  exact (transverseProjection_norm _ _).trans (by simpa only [norm_sub_rev] using velocity_normal_distance_bound w n hn)

lemma transverse_receiverQ_tangent_bound (w n h : Vec) (hn : ‖n‖=1) (hh : dot n h=0) :
    ‖transverseProjection w (receiverQ (velocity w) n h)‖≤3*(1-dot n (velocity w))*‖h‖ := by
  let D := 1-dot n (velocity w)
  have hD : 0≤D := (cone_denom_pos w n hn).le
  have ha : |dot (velocity w) h|≤Real.sqrt (2*D)*‖h‖ := by
    rw [show dot (velocity w) h=dot (velocity w-n) h by rw [dot_sub_left,hh,sub_zero]]
    exact (abs_dot_le _ _).trans (mul_le_mul_of_nonneg_right
      (velocity_normal_distance_bound w n hn) (norm_nonneg h))
  have hp := transverseProjection_normal_bound w n hn
  have he : transverseProjection w (receiverQ (velocity w) n h)=
      D • transverseProjection w h+dot (velocity w) h • transverseProjection w n := by
    exact (velocityProjection_add _ _ _).trans
      (congrArg₂ (·+·) (velocityProjection_smul _ _ _) (velocityProjection_smul _ _ _))
  rw [he]
  calc
    _ ≤ ‖D • transverseProjection w h‖+‖dot (velocity w) h • transverseProjection w n‖ := norm_add_le _ _
    _ = D*‖transverseProjection w h‖+|dot (velocity w) h| *‖transverseProjection w n‖ := by
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hD]
    _ ≤ D*‖h‖+(Real.sqrt (2*D)*‖h‖)*Real.sqrt (2*D) :=
      add_le_add (mul_le_mul_of_nonneg_left (transverseProjection_norm _ _) hD)
        (mul_le_mul ha hp (norm_nonneg _) (by positivity))
    _ = D*‖h‖+(Real.sqrt (2*D))^2*‖h‖ := by ring
    _ = _ := by rw [Real.sq_sqrt (by positivity : 0≤2*D)]; ring

lemma transverse_receiverQ_source_bound (w v E B n : Vec) (hn : ‖n‖=1) :
    ‖transverseProjection w (receiverQ (velocity w) n
        (sourceNumerator n (velocity v) (fderiv ℝ velocity v (E+cross (velocity v) B))))‖ ≤
      15*(1-dot n (velocity w))*(1-dot n (velocity v))*(q v)⁻¹*
        (goodField E B n+(1-dot n (velocity v))*‖B‖) := by
  apply (transverse_receiverQ_tangent_bound _ _ _ hn (sourceNumerator_tangent _ _ _ hn)).trans
  convert mul_le_mul_of_nonneg_left (sourceNumerator_bound v E B n hn)
    (show 0≤3*(1-dot n (velocity w)) by positivity [cone_denom_pos w n hn]) using 1
  ring

end RVM

end

end OAI
