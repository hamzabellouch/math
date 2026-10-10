import OAI.Analysis.BernoulliCone.UpperSeam

namespace OAI

universe uE

section
noncomputable section
open Set Filter
open scoped Topology ContDiff Laplacian
namespace Bernoulli.Cylindrical
lemma axis_smul {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e x:E) (t:ℝ) : axis e (t • x)=t*axis e x := by simp [axis,real_inner_smul_left]
lemma radiusSq_smul {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e x:E) (t:ℝ) : radiusSq e (t • x)=t^2*radiusSq e x := by
  simp only [radiusSq,axis_smul,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  ring
end Bernoulli.Cylindrical
namespace Bernoulli.DeSilvaJerison
lemma angle_smul (x:Space 7) {t:ℝ} (ht:0<t) : angle (t • x)=angle x := by
  simp only [angle,norm_smul,Real.norm_eq_abs,abs_of_pos ht,PiLp.smul_apply,smul_eq_mul]
  exact mul_div_mul_left _ _ ht.ne'
lemma Zsigned_smul (x:Space 7) {t:ℝ} (ht:0<t) : Zsigned (t • x)=t*Zsigned x := by
  rw [Zsigned_eq,Zsigned_eq,angle_smul x ht,norm_smul,Real.norm_eq_abs,abs_of_pos ht]
  ring
lemma KSup_smul {x:Space 7} (hq:0<Cylindrical.radiusSq axis x) {t:ℝ} (ht:0<t) :
    KSup (t • x)=t^(-2:ℤ)*KSup x := by
  have hqt:0<Cylindrical.radiusSq axis (t • x):=by rw [Cylindrical.radiusSq_smul]; positivity
  rw [KSup_cylindrical hqt,KSup_cylindrical hq,Cylindrical.radiusSq_smul,Cylindrical.axis_smul]
  norm_num only [zpow_neg,zpow_ofNat]
  field_simp
lemma outerSigned_cylindrical {x:Space 7} (hq:0<Cylindrical.radiusSq axis x) :
    let r:=Real.sqrt (Cylindrical.radiusSq axis x)
    let s:=Cylindrical.axis axis x/r
    outerSigned x=r*capH s+capAmplitude*((Cylindrical.radiusSq axis x)⁻¹-r)*(1+2*s^2) := by
  dsimp only
  let q:=Cylindrical.radiusSq axis x
  let r:=Real.sqrt q
  let a:=Cylindrical.axis axis x
  have hr:0<r:=Real.sqrt_pos.mpr hq
  have hr2:r^2=q:=Real.sq_sqrt hq.le
  let y:=r⁻¹ • x
  have hy:Cylindrical.radiusSq axis y=1 := by
    rw [Cylindrical.radiusSq_smul]
    change (r⁻¹)^2*q=1
    rw [←hr2]; field_simp
  have hay:Cylindrical.axis axis y=a/r := by rw [Cylindrical.axis_smul]; dsimp [a]; ring
  have he:=outerSigned_at_seam hy
  rw [outerSigned,Zsigned_smul x (inv_pos.mpr hr),KSup_smul hq (inv_pos.mpr hr),hay] at he
  change r⁻¹*Zsigned x+capAmplitude*( (r⁻¹)^(-2:ℤ)*KSup x)=capH (a/r) at he
  norm_num only [zpow_neg,zpow_ofNat,inv_inv] at he
  rw [outerSigned,KSup_cylindrical hq]
  rw [KSup_cylindrical hq] at he
  change Zsigned x+capAmplitude*((q+2*a^2)/q^2)=r*capH (a/r)+capAmplitude*(q⁻¹-r)*(1+2*(a/r)^2)
  change r⁻¹*Zsigned x+capAmplitude*((r⁻¹^2)⁻¹*((q+2*a^2)/q^2))=capH (a/r) at he
  rw [←he,←hr2]
  field_simp
  ring

lemma outer_positive_sector {x:Space 7} (hq:1≤Cylindrical.radiusSq axis x) (hp:0<outerSigned x) :
    |Cylindrical.axis axis x/Real.sqrt (Cylindrical.radiusSq axis x)|<3/4 := by
  have hqp:0<Cylindrical.radiusSq axis x:=by linarith
  have hr:1≤Real.sqrt (Cylindrical.radiusSq axis x):= (Real.le_sqrt (by norm_num) hqp.le).mpr (by simpa)
  have hqi:(Cylindrical.radiusSq axis x)⁻¹≤1 := inv_le_one_of_one_le₀ hq
  have hs:capAmplitude*((Cylindrical.radiusSq axis x)⁻¹-Real.sqrt (Cylindrical.radiusSq axis x))*
      (1+2*(Cylindrical.axis axis x/Real.sqrt (Cylindrical.radiusSq axis x))^2)≤0 :=
    mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos capAmplitude_pos.le (by linarith)) (by positivity)
  rw [outerSigned_cylindrical hqp] at hp
  have hh:0<capH (Cylindrical.axis axis x/Real.sqrt (Cylindrical.radiusSq axis x)) := by
    apply pos_of_mul_pos_right (show 0<Real.sqrt (Cylindrical.radiusSq axis x)*capH
      (Cylindrical.axis axis x/Real.sqrt (Cylindrical.radiusSq axis x)) by linarith) (by positivity)
  exact (capH_pos_iff _).mp hh

lemma capH_nonneg_iff (s:ℝ) : 0≤capH s ↔ |s|≤3/4 := by
  constructor
  · intro hs
    by_contra hn
    have hh:=capH_strictAnti (show (3/4:ℝ)∈Ici 0 by norm_num) (abs_nonneg s) (lt_of_not_ge hn)
    rw [capH_end,capH_abs] at hh
    linarith
  · exact capH_nonneg
lemma outer_nonnegative_sector {x:Space 7} (hq:1≤Cylindrical.radiusSq axis x) (hp:0≤outerSigned x) :
    |Cylindrical.axis axis x/Real.sqrt (Cylindrical.radiusSq axis x)|≤3/4 := by
  have hqp:0<Cylindrical.radiusSq axis x:=by linarith
  have hr:1≤Real.sqrt (Cylindrical.radiusSq axis x):= (Real.le_sqrt (by norm_num) hqp.le).mpr (by simpa)
  have hqi:(Cylindrical.radiusSq axis x)⁻¹≤1 := inv_le_one_of_one_le₀ hq
  have hs:capAmplitude*((Cylindrical.radiusSq axis x)⁻¹-Real.sqrt (Cylindrical.radiusSq axis x))*
      (1+2*(Cylindrical.axis axis x/Real.sqrt (Cylindrical.radiusSq axis x))^2)≤0 :=
    mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos capAmplitude_pos.le (by linarith)) (by positivity)
  rw [outerSigned_cylindrical hqp] at hp
  have hh:0≤capH (Cylindrical.axis axis x/Real.sqrt (Cylindrical.radiusSq axis x)) := by
    apply nonneg_of_mul_nonneg_right (show 0≤Real.sqrt (Cylindrical.radiusSq axis x)*capH
      (Cylindrical.axis axis x/Real.sqrt (Cylindrical.radiusSq axis x)) by linarith) (by positivity)
  exact (capH_nonneg_iff _).mp hh
lemma outer_nonnegative_angle {x:Space 7} (hq:1≤Cylindrical.radiusSq axis x) (hp:0≤outerSigned x) : |angle x|≤3/5 := by
  have hqp:0<Cylindrical.radiusSq axis x:=by linarith
  have hx: x≠0:=(radiusSq_pos_data hqp).1
  have hr:0<Real.sqrt (Cylindrical.radiusSq axis x):=Real.sqrt_pos.mpr hqp
  have hh:=outer_nonnegative_sector hq hp
  rw [abs_div,abs_of_pos hr,div_le_iff₀ hr] at hh
  have hsq:=Real.sq_sqrt hqp.le
  have hn:0<‖x‖:=norm_pos_iff.mpr hx
  rw [angle,abs_div,abs_norm,div_le_iff₀ hn]
  rw [Cylindrical.axis,inner_axis] at hh
  have hh2:= (sq_le_sq₀ (abs_nonneg (x 6)) (show 0≤3/4*Real.sqrt (Cylindrical.radiusSq axis x) by positivity)).mpr hh
  rw [mul_pow,sq_abs,hsq] at hh2
  rw [Cylindrical.radiusSq,Cylindrical.axis,inner_axis] at hh2
  nlinarith [sq_abs (x 6)]

/-- The actual signed glued DSJ upper profile, including the symmetry axis. -/
def upperSigned (x:Space 7) :ℝ := if Cylindrical.radiusSq axis x≤1 then smoothCap x else outerSigned x

def upperFamily (l:ℝ) (x:Space 7) :ℝ := κ*l*max (upperSigned (l⁻¹ • x)) 0
lemma upperSigned_cap {x:Space 7} (hq:Cylindrical.radiusSq axis x≤1) : upperSigned x=smoothCap x := ite_eq_left hq
lemma upperSigned_outer {x:Space 7} (hq:1≤Cylindrical.radiusSq axis x) : upperSigned x=outerSigned x := by
  rcases hq.eq_or_lt with h|h
  · rw [upperSigned_cap h.ge,upper_seam_agreement h.symm]
  · exact ite_eq_right (not_le.mpr h)
lemma upperFamily_nonneg {l:ℝ} (hl:0≤l) (x:Space 7) : 0≤upperFamily l x := by
  unfold upperFamily
  exact mul_nonneg (mul_nonneg κ_pos.le hl) (le_max_right _ _)

lemma upperSigned_continuous : Continuous upperSigned := by
  have hc:Continuous (Cylindrical.radiusSq axis):=(Cylindrical.radiusSq_contDiff axis (n:=1)).continuous
  have hcl:IsClosed {x:Space 7|Cylindrical.radiusSq axis x≤1}:=isClosed_le hc continuous_const
  apply continuous_if
  · intro x hx
    exact upper_seam_agreement (frontier_le_subset_eq hc continuous_const hx)
  · rw [hcl.closure_eq]
    intro x hx
    exact (smoothCap_contDiffAt hx).continuousAt.continuousWithinAt
  · intro x hx
    have hge:1≤Cylindrical.radiusSq axis x:=
      (closure_minimal (fun y hy=>le_of_lt (not_le.mp hy)) (isClosed_le continuous_const hc)) hx
    have hqp:0<Cylindrical.radiusSq axis x:=by linarith
    obtain ⟨hx0,ha⟩:=radiusSq_pos_data hqp
    exact (outerSigned_contDiffAt (n:=1) hx0 ha).continuousAt.continuousWithinAt
lemma upperFamily_continuous (l:ℝ) : Continuous (upperFamily l) := by
  have hc:Continuous (fun x:Space 7=>l⁻¹ • x):=continuous_id.const_smul l⁻¹
  have hg:Continuous (fun x:Space 7=>max (upperSigned (l⁻¹ • x)) 0):=
    (upperSigned_continuous.comp hc).max continuous_const
  exact continuous_const.mul hg
lemma upperFamily_joint_continuous : ContinuousOn (fun z:ℝ×Space 7=>upperFamily z.1 z.2) {z|0<z.1} := by
  intro z hz
  unfold upperFamily
  exact ((continuousAt_const.mul continuous_fst.continuousAt).mul
    ((upperSigned_continuous.continuousAt.comp
      ((continuous_fst.continuousAt.inv₀ (ne_of_gt hz)).smul continuous_snd.continuousAt)).max continuousAt_const)).continuousWithinAt
end Bernoulli.DeSilvaJerison

end
end

end OAI
