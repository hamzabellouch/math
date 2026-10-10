import OAI.Analysis.BernoulliCone.CapFoliation

namespace OAI

section
noncomputable section
open Set Filter
open scoped Topology ContDiff Laplacian
namespace Bernoulli.DeSilvaJerison
open Axisymmetric

def gSup2 (t:ℝ) :ℝ := (6+36*t^2+6*t^4)/(1-t^2)^4
lemma hasDerivAt_gSup1 {t:ℝ} (ht:|t|<1) : HasDerivAt gSup1 (gSup2 t) t := by
  have hd:1-t^2≠0 := by obtain ⟨h1,h2⟩:=abs_lt.mp ht; nlinarith
  convert! ((((hasDerivAt_id t).const_mul 2).mul
    ((hasDerivAt_const t (3:ℝ)).add ((hasDerivAt_id t).pow 2))).div
      (((hasDerivAt_const t (1:ℝ)).sub ((hasDerivAt_id t).pow 2)).pow 3)
        (pow_ne_zero 3 hd)) using 1
  norm_num only [gSup1,gSup2,id_eq,pow_one,Pi.add_apply,Pi.sub_apply,Pi.pow_apply,Pi.mul_apply]
  field_simp [hd]
  ring
lemma gSup_contDiffAt {t:ℝ} {n:WithTop ℕ∞} (ht:|t|<1) : ContDiffAt ℝ n gSup t := by
  have hd:1-t^2≠0 := by obtain ⟨h1,h2⟩:=abs_lt.mp ht; nlinarith
  exact (contDiffAt_const.add (contDiffAt_id.pow 2)).div
    ((contDiffAt_const.sub (contDiffAt_id.pow 2)).pow 2) (pow_ne_zero 2 hd)
lemma gSup_equation {t:ℝ} (ht:|t|<1) : (1-t^2)*gSup2 t-6*t*gSup1 t-6*gSup t=0 := by
  have hd:1-t^2≠0 := by obtain ⟨h1,h2⟩:=abs_lt.mp ht; nlinarith
  unfold gSup2 gSup1 gSup
  field_simp [hd]
  ring

def KSup : Space 7→ℝ := lift axis (-2) gSup
def outerSigned (x:Space 7) :ℝ := Zsigned x+capAmplitude*KSup x

lemma KSup_pos {x:Space 7} (hx:x≠0) (ha:|angle x|<1) :0<KSup x := by
  unfold KSup lift
  apply mul_pos (Real.rpow_pos_of_pos (norm_pos_iff.mpr hx) _)
  exact gSup_pos (by simpa [inner_axis,angle] using ha)
lemma KSup_contDiffAt {x:Space 7} {n:WithTop ℕ∞} (hx:x≠0) (ha:|angle x|<1) :ContDiffAt ℝ n KSup x := by
  exact contDiffAt_lift hx (gSup_contDiffAt (by simpa [inner_axis,angle] using ha))
lemma KSup_laplacian {x:Space 7} (hx:x≠0) (ha:|angle x|<1) : Δ KSup x=0 := by
  have hi:|inner ℝ x axis/‖x‖|<1:=by simpa only [inner_axis,angle] using ha
  have hp:∀ᶠ s in 𝓝 (inner ℝ x axis/‖x‖),HasDerivAt gSup (gSup1 s) s := by
    filter_upwards [isOpen_Ioo.mem_nhds (abs_lt.mp hi)] with s hs
    exact hasDerivAt_gSup (abs_lt.mpr hs)
  have hh:=laplacian_lift axis x (-2) axis_norm hx (gSup_contDiffAt hi) hp (hasDerivAt_gSup1 hi)
  have he:=gSup_equation hi
  simp only [Space,finrank_euclideanSpace_fin,Nat.cast_ofNat] at hh
  norm_num only at hh
  rw [KSup,hh]
  convert mul_zero (‖x‖^(-2:ℝ)/‖x‖^2) using 1
  congr 1
  linarith
lemma KSup_gradient {x:Space 7} (hx:x≠0) (ha:|angle x|<1) :
    gradient KSup x=(‖x‖^(-2:ℝ)/‖x‖) • polarGradient axis x (-2*gSup (angle x)) (gSup1 (angle x)) := by
  have hi:|inner ℝ x axis/‖x‖|<1:=by simpa only [inner_axis,angle] using ha
  simpa only [KSup,inner_axis,angle] using (hasGradientAt_lift axis x (-2) hx (hasDerivAt_gSup hi)).gradient
lemma outerSigned_contDiffAt {x:Space 7} {n:WithTop ℕ∞} (hx:x≠0) (ha:|angle x|<1) :
    ContDiffAt ℝ n outerSigned x := (signed_contDiffAt hx ha).add
      (contDiffAt_const.mul (KSup_contDiffAt hx ha))
lemma outerSigned_laplacian {x:Space 7} (hx:x≠0) (ha:|angle x|<1) : Δ outerSigned x=0 := by
  have hc : ContDiffAt ℝ 2 (fun y:Space 7=>capAmplitude*KSup y) x :=
    contDiffAt_const.mul (KSup_contDiffAt hx ha)
  have hadd : Δ outerSigned x=Δ Zsigned x+Δ (fun y:Space 7=>capAmplitude*KSup y) x :=
    (signed_contDiffAt hx ha).laplacian_add hc
  have hmul : Δ (fun y:Space 7=>capAmplitude*KSup y) x=capAmplitude*Δ KSup x :=
    InnerProductSpace.laplacian_smul capAmplitude (KSup_contDiffAt hx ha)
  rw [hadd,hmul,signed_laplacian hx ha,KSup_laplacian hx ha]
  ring

lemma polarGradient_inner_radial (x:Space 7) (hx:x≠0) (a b:ℝ) :
    inner ℝ x (polarGradient axis x a b)=‖x‖*a := by
  have hn:‖x‖≠0:=norm_ne_zero_iff.mpr hx
  simp only [polarGradient,inner_add_right,inner_sub_right,real_inner_smul_right,
    radial,real_inner_smul_right,real_inner_self_eq_norm_sq]
  field_simp
  ring
lemma gradient_add' {d:ℕ} {f g:Space d→ℝ} {x:Space d}
    (hf:DifferentiableAt ℝ f x) (hg:DifferentiableAt ℝ g x) :
    gradient (fun x=>f x+g x) x=gradient f x+gradient g x := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_add_left,inner_gradient_left,inner_gradient_left,inner_gradient_left]
  change (fderiv ℝ (f+g) x) v=_
  rw [fderiv_add hf hg]
  rfl
lemma outerSigned_radial_defect {x:Space 7} (hx:x≠0) (ha:|angle x|<1) :
    outerSigned x-inner ℝ x (gradient outerSigned x)=3*capAmplitude*KSup x := by
  have hdz: DifferentiableAt ℝ Zsigned x := (signed_contDiffAt (n:=1) hx ha).differentiableAt (by norm_num)
  have hdk: DifferentiableAt ℝ KSup x := (KSup_contDiffAt (n:=1) hx ha).differentiableAt (by norm_num)
  have hg:gradient Zsigned x=polarGradient axis x (f (angle x)) (fp (angle x)) := by
    have hi:inner ℝ x axis/‖x‖∈Ioo (-1:ℝ) 1:=by simpa only [inner_axis,angle] using (show angle x∈Ioo (-1:ℝ) 1 from abs_lt.mp ha)
    rw [Zsigned,(hasGradientAt_lift axis x 1 hx (hasDerivAt_f hi)).gradient]
    simp only [Real.rpow_one,div_self (norm_ne_zero_iff.mpr hx),one_smul,one_mul,inner_axis,angle]
  change Zsigned x+capAmplitude*KSup x-inner ℝ x (gradient (fun x=>Zsigned x+capAmplitude*KSup x) x)=_
  rw [gradient_add' hdz (hdk.const_mul capAmplitude),gradient_const_mul _ hdk,hg,KSup_gradient hx ha]
  simp only [inner_add_right,real_inner_smul_right,polarGradient_inner_radial x hx]
  rw [Zsigned_eq]
  unfold KSup lift
  simp only [inner_axis,angle]
  field_simp
  ring
lemma outerSigned_radial_defect_pos {x:Space 7} (hx:x≠0) (ha:|angle x|<1) :
    0<outerSigned x-inner ℝ x (gradient outerSigned x) := by
  rw [outerSigned_radial_defect hx ha]
  exact mul_pos (mul_pos (by norm_num) capAmplitude_pos) (KSup_pos hx ha)

lemma radiusSq_pos_data {x:Space 7} (hq:0<Cylindrical.radiusSq axis x) : x≠0 ∧ |angle x|<1 := by
  have he:Cylindrical.radiusSq axis x=‖x‖^2-(x 6)^2 := by rw [Cylindrical.radiusSq,Cylindrical.axis,inner_axis]
  have hx:x≠0 := by intro hh; simp [hh,Cylindrical.radiusSq,Cylindrical.axis] at hq
  have hn:0<‖x‖:=norm_pos_iff.mpr hx
  refine ⟨hx,?_⟩
  rw [angle,abs_div,abs_norm,div_lt_iff₀ hn]
  rw [he] at hq
  nlinarith [sq_abs (x 6)]
lemma KSup_cylindrical {x:Space 7} (hq:0<Cylindrical.radiusSq axis x) :
    KSup x=(Cylindrical.radiusSq axis x+2*(Cylindrical.axis axis x)^2)/(Cylindrical.radiusSq axis x)^2 := by
  obtain ⟨hx,ha⟩:=radiusSq_pos_data hq
  have hn:=norm_ne_zero_iff.mpr hx
  have hd:1-(inner ℝ x axis/‖x‖)^2≠0 := by
    have hh:|inner ℝ x axis/‖x‖|<1:=by simpa only [inner_axis,angle] using ha
    obtain ⟨h1,h2⟩:=abs_lt.mp hh; nlinarith
  unfold KSup lift gSup Cylindrical.radiusSq Cylindrical.axis
  rw [Real.rpow_neg (norm_nonneg x),show ‖x‖^(2:ℝ)=‖x‖^2 by norm_cast]
  have hqne:‖x‖^2-(inner ℝ x axis)^2≠0:=hq.ne'
  field_simp [hn,hd,hqne]
  ring
lemma outerSigned_at_seam {x:Space 7} (hq:Cylindrical.radiusSq axis x=1) :
    outerSigned x=capH (Cylindrical.axis axis x) := by
  have hqp:0<Cylindrical.radiusSq axis x:=by rw [hq]; norm_num
  have hn:‖x‖=capRadius (Cylindrical.axis axis x) := by
    have he:‖x‖^2=1+(Cylindrical.axis axis x)^2 := by
      rw [Cylindrical.radiusSq] at hq; linarith
    apply (sq_eq_sq₀ (norm_nonneg x) (capRadius_pos _).le).mp
    rw [capRadius_sq,he]
  rw [outerSigned,KSup_cylindrical hqp,hq,Zsigned_eq]
  simp only [one_pow,div_one]
  rw [angle,←inner_axis,←Cylindrical.axis,hn]
  rfl
end Bernoulli.DeSilvaJerison

end
end

end OAI
