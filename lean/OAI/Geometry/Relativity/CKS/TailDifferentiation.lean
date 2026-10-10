import OAI.Geometry.Relativity.CKS.ADMTail

namespace OAI

noncomputable section
namespace CKSADM
noncomputable section
open Set Filter Finset CKSSphericalHarmonics CKSInducedSphere CKSSphericalChart
open scoped Topology ContDiff

lemma unitVector_ne {x : E} (hx : x ≠ 0) : unitVector x ≠ 0 := by
  intro hh
  have h := unitVector_norm hx
  simp [hh] at h

lemma unitVector_component (x : E) (i : Ix) : unitVector x i = normal x i := by
  simp [unitVector,normal,div_eq_mul_inv,mul_comm]

lemma fderiv_unitVector_component {x : E} (hx : x ≠ 0) (j i : Ix) :
    (fderiv ℝ unitVector x (e j)) i =
      ((if i=j then 1 else 0)-unitVector x i*unitVector x j)/‖x‖ := by
  have hh := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Ix) i).hasFDerivAt.comp x
    ((unitVector_smooth hx).differentiableAt (by simp)).hasFDerivAt
  have he : (fun y : E => unitVector y i) = (fun y => normal y i) := funext (fun y => unitVector_component y i)
  have he' := congrArg (fun L : E →L[ℝ] ℝ => L (e j)) hh.fderiv
  change pd j (fun y => unitVector y i) x = (fderiv ℝ unitVector x (e j)) i at he'
  rw [he] at he'
  have hh' : pd j (fun y => normal y i) x = (fderiv ℝ unitVector x (e j)) i := he'
  rw [← hh',pd_normal hx]
  simp only [unitVector_component]

lemma joint_fderiv_split {F : ℝ → E → ℝ} {t a : ℝ} {n v : E}
    (hF : DifferentiableAt ℝ (fun z : ℝ × E => F z.1 z.2) (t,n)) :
    fderiv ℝ (fun z : ℝ × E => F z.1 z.2) (t,n) (a,v) =
      a*td F t n + ∑ i : Ix, v i*pd i (F t) n := by
  let L := fderiv ℝ (fun z : ℝ × E => F z.1 z.2) (t,n)
  have ht := hF.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t n))
  have hx := hF.hasFDerivAt.comp n ((hasFDerivAt_const t n).prodMk (hasFDerivAt_id n))
  have ht' : td F t n = L (1,0) := ht.deriv
  have hx' : fderiv ℝ (F t) n v = L (0,v) := by
    erw [hx.fderiv]
    rfl
  change L (a,v) = _
  have hv : (a,v) = a • ((1:ℝ),(0:E)) + (0,v) := by simp
  rw [hv,map_add,map_smul,←ht',←hx',fderiv_expand]
  rfl

def radialHeat (F : ℝ → E → ℝ) (T a d : ℝ) (x : E) : ℝ :=
  ‖x‖ ^ (-d) * F (T+a*Real.log ‖x‖) (unitVector x)

lemma radialHeat_smooth {F : ℝ → E → ℝ}
    (hF : ContDiffOn ℝ ∞ (fun z : ℝ × E => F z.1 z.2) heatDomain)
    (T a d : ℝ) {x : E} (hx : x ≠ 0) : ContDiffAt ℝ ∞ (radialHeat F T a d) x := by
  have hn : ContDiffAt ℝ ∞ (fun y : E => ‖y‖) x := contDiffAt_norm ℝ hx
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hpow : ContDiffAt ℝ ∞ (fun y : E => ‖y‖^(-d)) x := hn.rpow_const_of_ne hr.ne'
  have ht : ContDiffAt ℝ ∞ (fun y : E => T+a*Real.log ‖y‖) x :=
    contDiffAt_const.add (contDiffAt_const.mul (hn.log hr.ne'))
  have hf := hF.contDiffAt (heatDomain_open.mem_nhds (show (T+a*Real.log ‖x‖,unitVector x) ∈ heatDomain from unitVector_ne hx))
  have hc := hf.comp x (ht.prodMk (unitVector_smooth hx))
  exact hpow.mul hc

lemma pd_log_norm {x : E} (hx : x ≠ 0) (j : Ix) :
    pd j (fun y : E => Real.log ‖y‖) x = unitVector x j/‖x‖ := by
  have hn := ((contDiffAt_norm ℝ hx : ContDiffAt ℝ 1 (fun y : E => ‖y‖) x).differentiableAt (by simp)).hasFDerivAt
  rw [pd,(hn.log (norm_ne_zero_iff.mpr hx)).fderiv]
  change ‖x‖⁻¹ * pd j (fun y : E => ‖y‖) x = _
  rw [pd_norm hx,unitVector_component]
  ring

lemma pd_norm_rpow {x : E} (hx : x ≠ 0) (d : ℝ) (j : Ix) :
    pd j (fun y : E => ‖y‖^(-d)) x = ‖x‖^(-(d+1))*(-d*unitVector x j) := by
  have hn := ((contDiffAt_norm ℝ hx : ContDiffAt ℝ 1 (fun y : E => ‖y‖) x).differentiableAt (by simp)).hasFDerivAt
  rw [pd,(hn.rpow_const (p := -d) (Or.inl (norm_ne_zero_iff.mpr hx))).fderiv]
  change (-d*‖x‖^(-d-1))*pd j (fun y : E => ‖y‖) x = _
  rw [pd_norm hx,unitVector_component]
  rw [show -d-1 = -(d+1) by ring]
  ring

lemma pd_heat_pullback {F : ℝ → E → ℝ}
    (hF : ContDiffOn ℝ ∞ (fun z : ℝ × E => F z.1 z.2) heatDomain)
    (T a : ℝ) {x : E} (hx : x ≠ 0) (j : Ix) :
    pd j (fun y => F (T+a*Real.log ‖y‖) (unitVector y)) x =
      (a*unitVector x j*td F (T+a*Real.log ‖x‖) (unitVector x) +
      ∑ i : Ix, ((if i=j then 1 else 0)-unitVector x i*unitVector x j)*
        pd i (F (T+a*Real.log ‖x‖)) (unitVector x))/‖x‖ := by
  let t := T+a*Real.log ‖x‖
  let n := unitVector x
  have hn : DifferentiableAt ℝ (fun y : E => ‖y‖) x :=
    (contDiffAt_norm ℝ hx : ContDiffAt ℝ 1 _ _).differentiableAt (by simp)
  have ht : DifferentiableAt ℝ (fun y : E => T+a*Real.log ‖y‖) x :=
    (differentiableAt_const T).add ((differentiableAt_const a).fun_mul (hn.log (norm_ne_zero_iff.mpr hx)))
  have hf := (hF.contDiffAt (heatDomain_open.mem_nhds (show (t,n) ∈ heatDomain from unitVector_ne hx))).differentiableAt (by simp)
  have hc := hf.hasFDerivAt.comp x (ht.hasFDerivAt.prodMk ((unitVector_smooth hx).differentiableAt (by simp)).hasFDerivAt)
  unfold pd
  erw [hc.fderiv]
  change fderiv ℝ (fun z : ℝ × E => F z.1 z.2) (t,n)
    (pd j (fun y => T+a*Real.log ‖y‖) x,fderiv ℝ unitVector x (e j)) = _
  rw [joint_fderiv_split hf]
  have ht' : pd j (fun y => T+a*Real.log ‖y‖) x = a*unitVector x j/‖x‖ := by
    rw [pd,fderiv_const_add,fderiv_const_mul (hn.log (norm_ne_zero_iff.mpr hx)) a]
    change a*pd j (fun y : E => Real.log ‖y‖) x = _
    rw [pd_log_norm hx]
    ring
  rw [ht']
  simp_rw [fderiv_unitVector_component hx]
  simp only [t,n]
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div,← add_div]
  congr 1

def radialNext (F : ℝ → E → ℝ) (a d : ℝ) (j : Ix) (t : ℝ) (n : E) : ℝ :=
  (-d*n j)*F t n + (a*n j)*td F t n +
    ∑ i : Ix, ((if i=j then 1 else 0)-n i*n j)*pd i (F t) n

lemma pd_radialHeat {F : ℝ → E → ℝ}
    (hF : ContDiffOn ℝ ∞ (fun z : ℝ × E => F z.1 z.2) heatDomain)
    (T a d : ℝ) {x : E} (hx : x ≠ 0) (j : Ix) :
    pd j (radialHeat F T a d) x = radialHeat (radialNext F a d j) T a (d+1) x := by
  have hn : ContDiffAt ℝ ∞ (fun y : E => ‖y‖) x := contDiffAt_norm ℝ hx
  have hp := (hn.rpow_const_of_ne (p := -d) (norm_ne_zero_iff.mpr hx)).differentiableAt (by simp)
  have hf : DifferentiableAt ℝ (fun y => F (T+a*Real.log ‖y‖) (unitVector y)) x := by
    have hh := (radialHeat_smooth hF T a 0 hx).differentiableAt (by simp)
    have he : radialHeat F T a 0 = fun y => F (T+a*Real.log ‖y‖) (unitVector y) := by
      funext y
      simp only [radialHeat, neg_zero, Real.rpow_zero, one_mul]
    rw [he] at hh
    exact hh
  unfold radialHeat
  rw [pd_mul hp hf,pd_norm_rpow hx,pd_heat_pullback hF T a hx]
  have hm : ‖x‖^(-d)/‖x‖ = ‖x‖^(-(d+1)) := by
    rw [show -(d+1) = -d-1 by ring,Real.rpow_sub (norm_pos_iff.mpr hx),Real.rpow_one]
  unfold radialNext
  rw [←hm]
  ring

lemma HeatGenerated.radialNext {p : ℕ → Poly} (hp : PolynomialRapid p)
    {F : ℝ → E → ℝ} (hF : HeatGenerated p F) (a d : ℝ) (j : Ix) :
    HeatGenerated p (radialNext F a d j) := by
  exact ((HeatGenerated.coeff (fun n => -d*n j) (contDiffOn_const.mul (coordinate_smooth j)) hF).add
    (HeatGenerated.coeff (fun n => a*n j) (contDiffOn_const.mul (coordinate_smooth j)) (hF.time hp))).add
    (HeatGenerated.sum univ (fun i _ => HeatGenerated.coeff
      (fun n => (if i=j then 1 else 0)-n i*n j)
      (contDiffOn_const.sub ((coordinate_smooth i).mul (coordinate_smooth j))) (hF.partial hp i)))

def cartWord : List Ix → (E → ℝ) → E → ℝ
  | [], F => F
  | j::w, F => cartWord w (pd j F)

lemma pd_congr_on {s : Set E} (hs : IsOpen s) {F G : E → ℝ} (he : EqOn F G s) (j : Ix) :
    EqOn (pd j F) (pd j G) s := by
  intro x hx
  exact congrArg (fun L : E →L[ℝ] ℝ => L (e j))
    (Filter.EventuallyEq.fderiv_eq (Filter.eventually_of_mem (hs.mem_nhds hx) (fun y hy => he hy)))

lemma cartWord_congr_on {s : Set E} (hs : IsOpen s) {F G : E → ℝ} (he : EqOn F G s) (w : List Ix) :
    EqOn (cartWord w F) (cartWord w G) s := by
  induction w generalizing F G with
  | nil => exact he
  | cons j w ih => exact ih (pd_congr_on hs he j)

lemma pd_smooth_on {s : Set E} (hs : IsOpen s) {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F s) (j : Ix) :
    ContDiffOn ℝ ∞ (pd j F) s :=
  (hF.fderiv_of_isOpen hs (by simp)).clm_apply contDiffOn_const

lemma cartWord_smooth_on {s : Set E} (hs : IsOpen s) {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F s) (w : List Ix) :
    ContDiffOn ℝ ∞ (cartWord w F) s := by
  induction w generalizing F with
  | nil => exact hF
  | cons j w ih => exact ih (pd_smooth_on hs hF j)

theorem radialHeat_word {p : ℕ → Poly} (hp : PolynomialRapid p)
    {F : ℝ → E → ℝ} (hF : HeatGenerated p F) (T a d : ℝ) (w : List Ix) :
    ∃ G : ℝ → E → ℝ, HeatGenerated p G ∧
      ∀ x : E, x ≠ 0 → cartWord w (radialHeat F T a d) x =
        radialHeat G T a (d+w.length) x := by
  induction w generalizing F d with
  | nil => exact ⟨F,hF,by intros; simp [cartWord]⟩
  | cons j w ih =>
    obtain ⟨G,hG,he⟩ := ih (HeatGenerated.radialNext hp hF a d j) (d+1)
    refine ⟨G,hG,?_⟩
    intro x hx
    have he' : EqOn (pd j (radialHeat F T a d)) (radialHeat (radialNext F a d j) T a (d+1)) U :=
      fun y hy => pd_radialHeat (hF.joint_smooth hp) T a d hy j
    change cartWord w (pd j (radialHeat F T a d)) x = _
    rw [cartWord_congr_on U_open he' w hx,he x hx]
    congr 1
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
    ring

theorem radialHeat_word_decay {p : ℕ → Poly} (hp : PolynomialRapid p)
    {F : ℝ → E → ℝ} (hF : HeatGenerated p F) (T a d : ℝ) (w : List Ix) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E, x ≠ 0 → 0 ≤ T+a*Real.log ‖x‖ →
      |cartWord w (radialHeat F T a d) x| ≤
        C*‖x‖^(-(d+w.length))*Real.exp (-6*(T+a*Real.log ‖x‖)) := by
  obtain ⟨G,hG,he⟩ := radialHeat_word hp hF T a d w
  obtain ⟨C,hC,hb⟩ := hG.decay hp
  refine ⟨C,hC,?_⟩
  intro x hx ht
  rw [he x hx,radialHeat,abs_mul,abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  have hh := mul_le_mul_of_nonneg_left (hb _ ht _ (unitVector_norm hx))
    (Real.rpow_nonneg (norm_nonneg x) (-(d+w.length)))
  simpa only [Real.norm_eq_abs,mul_left_comm,mul_assoc] using hh

end
end CKSADM

end

end OAI
