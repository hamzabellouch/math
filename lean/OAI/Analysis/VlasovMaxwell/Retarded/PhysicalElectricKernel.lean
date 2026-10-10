import Mathlib
import OAI.Analysis.VlasovMaxwell.Continuation.IncrementBootstrap

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
open scoped Topology ContDiff NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal RealInnerProductSpace

namespace RVM

def physicalElectricKernel (r : ℝ) (n u b : Vec) : Vec :=
  ((1-dot u u)/(r^2*(1-dot n u)^3)) • (n-u) +
    (r*(1-dot n u)^3)⁻¹ • ((dot n b) • (n-u)-(1-dot n u) • b)

def potentialSourceRate (r : ℝ) (n u b : Vec) : ℝ :=
  ((1-dot u u)-(1-dot n u))/(r^2*(1-dot n u)^2) +
    dot n b/(r*(1-dot n u)^2)

def potentialSpaceRate (r : ℝ) (n u b e : Vec) : ℝ :=
  -dot (n-u) e/(r^2*(1-dot n u)^2) -
    dot n e/(1-dot n u)*potentialSourceRate r n u b

def potentialVectorTimeRate (r : ℝ) (n u b : Vec) : Vec :=
  (r*(1-dot n u)^2)⁻¹ • b +
    (potentialSourceRate r n u b/(1-dot n u)) • u

lemma potential_kernel_component (r : ℝ) (n u b e : Vec)
    (hr : r≠0) (hd : 1-dot n u≠0) :
    -potentialSpaceRate r n u b e - dot (potentialVectorTimeRate r n u b) e =
      dot (physicalElectricKernel r n u b) e := by
  simp only [potentialSpaceRate,potentialVectorTimeRate,physicalElectricKernel,
    potentialSourceRate,dot_add_left,dot_smul_left,dot_sub_left]
  field_simp
  ring

lemma physical_kernel_signed_transform (r : ℝ) (n u b a : Vec)
    (hr : r≠0) (hd : 1-dot n u≠0) (hD : 1-dot n a≠0) :
    ((1-dot n u)/(1-dot n a)) •
      ((1-dot n a) • physicalElectricKernel r n u b +
        (dot a (physicalElectricKernel r n u b)) • n) =
      signedForceKernel r a u n b := by
  ext i
  simp only [physicalElectricKernel,signedForceKernel,coneTransform,sourceVelocityRate,
    dot_add_right,dot_sub_right,dot_smul_right,PiLp.add_apply,PiLp.sub_apply,
    PiLp.smul_apply,PiLp.neg_apply,smul_eq_mul]
  field_simp
  ring

lemma hasDerivAt_potential_source {r : ℝ → ℝ} {n u : ℝ → Vec} {s : ℝ} {b : Vec}
    (hr : HasDerivAt r (-dot (n s) (u s)) s)
    (hn : HasDerivAt n ((r s)⁻¹ • (dot (n s) (u s) • n s-u s)) s)
    (hu : HasDerivAt u b s) (hr0 : r s≠0) (hd : 1-dot (n s) (u s)≠0) :
    HasDerivAt (fun t => (r t*(1-dot (n t) (u t)))⁻¹)
      (potentialSourceRate (r s) (n s) (u s) b) s := by
  have hh := (hr.mul ((hasDerivAt_const s (1:ℝ)).sub (hasDerivAt_dot hn hu))).inv
    (mul_ne_zero hr0 hd)
  convert hh using 1
  simp only [potentialSourceRate,dot_smul_left,dot_sub_left,Pi.mul_apply,Pi.sub_apply]
  field_simp
  ring

lemma hasDerivAt_label_scalar_potential {r : ℝ → ℝ} {n u : ℝ → Vec}
    {s : ℝ} {b e : Vec} {z : ℝ}
    (hr : HasDerivAt r (dot (n s) e-z*dot (n s) (u s)) s)
    (hn : HasDerivAt n ((r s)⁻¹ • (e-z • u s-
      (dot (n s) e-z*dot (n s) (u s)) • n s)) s)
    (hu : HasDerivAt u (z • b) s) (hr0 : r s≠0) (hd : 1-dot (n s) (u s)≠0) :
    HasDerivAt (fun t => (r t*(1-dot (n t) (u t)))⁻¹)
      (-dot (n s-u s) e/((r s)^2*(1-dot (n s) (u s))^2)+
        z*potentialSourceRate (r s) (n s) (u s) b) s := by
  have hh := (hr.mul ((hasDerivAt_const s (1:ℝ)).sub (hasDerivAt_dot hn hu))).inv
    (mul_ne_zero hr0 hd)
  convert hh using 1
  simp only [potentialSourceRate,dot_smul_left,dot_sub_left,dot_smul_right,
    Pi.mul_apply,Pi.sub_apply,dot_comm (u s) e]
  field_simp
  ring

def potentialSpatialGradient (r : ℝ) (n u b : Vec) : Vec :=
  -(r^2*(1-dot n u)^2)⁻¹ • (n-u) -
    (potentialSourceRate r n u b/(1-dot n u)) • n

lemma dot_potentialSpatialGradient (r : ℝ) (n u b e : Vec) :
    dot (potentialSpatialGradient r n u b) e = potentialSpaceRate r n u b e := by
  simp only [potentialSpatialGradient,potentialSpaceRate,dot_sub_left,dot_smul_left]
  ring

lemma potential_magnetic_kernel (r : ℝ) (n u b : Vec)
    (hr : r≠0) (hd : 1-dot n u≠0) :
    cross (potentialSpatialGradient r n u b) u -
      (r*(1-dot n u)^2)⁻¹ • cross n b =
      cross n (physicalElectricKernel r n u b) := by
  ext i
  fin_cases i <;>
    simp [potentialSpatialGradient,physicalElectricKernel,potentialSourceRate,cross,
      PiLp.sub_apply,PiLp.smul_apply] <;>
    field_simp <;> ring

end RVM

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma IncrementBootstrap.reflect {V : ℝ → Vec} {T M A P L : ℝ}
    (H : IncrementBootstrap V T M A P L) :
    IncrementBootstrap (fun t => V (T-t)) T M A P L := by
  intro n a b ha hab hb hband
  have h := H n (T-b) (T-a) (by linarith) (by linarith) (by linarith)
    (by
      intro t ht
      have hh := hband (T-t) ⟨by linarith [ht.2],by linarith [ht.1]⟩
      simpa only [sub_sub_cancel] using hh)
  have he : T-(T-a)=a := by ring
  have he' : T-(T-b)=b := by ring
  have hd : (T-a)-(T-b)=b-a := by ring
  simpa only [he,he',hd,norm_sub_rev] using h

lemma IncrementBootstrap.velocity_stopped_backward {V : ℝ → Vec} {T M A P L a b ε : ℝ}
    (H : IncrementBootstrap V T M A P L) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T)
    (hV : ContinuousOn V (Icc a b)) (hM : 0 ≤ M) (hA : 0 ≤ A) (hP : 0 ≤ P)
    (hL : 0 ≤ L) (hε : ε < q (V b)/2)
    (hstep : M*P*Real.sqrt (b-a)+2*A*(b-a)*P^2*L/q (V b) ≤ ε) :
    ∀ t ∈ Icc a b, ‖V t-V b‖ ≤ ε ∧
      ‖velocity (V t)-velocity (V b)‖ ≤ 2*ε/q (V b) ∧
      q (V b)/2 ≤ q (V t) ∧ q (V t) ≤ 2*q (V b) := by
  have he : T-(T-b)=b := by ring
  have hd : (T-a)-(T-b)=b-a := by ring
  have hcont : ContinuousOn (fun t => V (T-t)) (Icc (T-b) (T-a)) :=
    hV.comp (continuous_const.sub continuous_id).continuousOn
      (fun t ht => ⟨by linarith [ht.2],by linarith [ht.1]⟩)
  have hh := H.reflect.velocity_stopped_forward (a:=T-b) (b:=T-a)
    (by linarith) (by linarith) (by linarith) hcont hM hA hP hL
    (by simpa only [he] using hε) (by simpa only [he,hd] using hstep)
  intro t ht
  have hht := hh (T-t) ⟨by linarith [ht.2],by linarith [ht.1]⟩
  have het : T-(T-t)=t := by ring
  simpa only [he,het] using hht

lemma stopping_modulus_mono {M A P L q l l' : ℝ}
    (hM : 0≤M) (hA : 0≤A) (hP : 0≤P) (hL : 0≤L) (hq : 0≤q) (hll : l≤l') :
    M*P*Real.sqrt l+2*A*l*P^2*L/q ≤
      M*P*Real.sqrt l'+2*A*l'*P^2*L/q := by
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hll) (mul_nonneg hM hP)
  · apply div_le_div_of_nonneg_right _ hq
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hll (by positivity))
        (sq_nonneg P)) hL

lemma IncrementBootstrap.velocity_stopped_about {V : ℝ → Vec} {T M A P L a b r ε : ℝ}
    (H : IncrementBootstrap V T M A P L) (ha : 0 ≤ a) (hb : b ≤ T)
    (hr : r ∈ Icc a b) (hV : ContinuousOn V (Icc a b))
    (hM : 0 ≤ M) (hA : 0 ≤ A) (hP : 0 ≤ P) (hL : 0 ≤ L)
    (hε : ε < q (V r)/2)
    (hstep : M*P*Real.sqrt (b-a)+2*A*(b-a)*P^2*L/q (V r) ≤ ε) :
    ∀ t ∈ Icc a b, ‖V t-V r‖ ≤ ε ∧
      ‖velocity (V t)-velocity (V r)‖ ≤ 2*ε/q (V r) ∧
      q (V r)/2 ≤ q (V t) ∧ q (V t) ≤ 2*q (V r) := by
  intro t ht
  by_cases htr : r≤t
  · apply H.velocity_stopped_forward (ha.trans hr.1) hr.2 hb
      (hV.mono (Icc_subset_Icc hr.1 le_rfl)) hM hA hP hL hε
      ((stopping_modulus_mono hM hA hP hL (q_pos (V r)).le (by linarith [hr.1])).trans hstep)
      t ⟨htr,ht.2⟩
  · apply H.velocity_stopped_backward ha hr.1 (hr.2.trans hb)
      (hV.mono (Icc_subset_Icc le_rfl hr.2)) hM hA hP hL hε
      ((stopping_modulus_mono hM hA hP hL (q_pos (V r)).le (by linarith [hr.2])).trans hstep)
      t ⟨ht.1,le_of_not_ge htr⟩

end RVM

end

end OAI
