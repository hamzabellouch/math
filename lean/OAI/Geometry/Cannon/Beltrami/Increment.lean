import Mathlib
import OAI.Geometry.Cannon.Beltrami.Mollifier

namespace OAI

section
section
section
section
section
section
section
noncomputable section
namespace CannonOrientation
open Set Topology
open scoped ComplexConjugate

private lemma simplyConnected_univ (X : Type*) [TopologicalSpace X]
    [SimplyConnectedSpace X] : IsSimplyConnected (univ : Set X) :=
  (Homeomorph.Set.univ X).toHomotopyEquiv.simplyConnectedSpace

lemma continuous_log_exists {X : Type*} [TopologicalSpace X]
    [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    {g : X → ℂ} (hg : Continuous g) (h0 : ∀ x, g x ≠ 0) :
    ∃ L : X → ℂ, Continuous L ∧ ∀ x, Complex.exp (L x)=g x := by
  obtain ⟨L,hL,he⟩ := Complex.exists_continuousOn_eqOn_exp_comp
    (simplyConnected_univ X) isOpen_univ hg.continuousOn
    (by rintro ⟨x,-,hx⟩; exact h0 x hx)
  exact ⟨L,continuousOn_univ.mp hL,fun x => he (mem_univ x)⟩

lemma exp_equal_difference_constant {X : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] {L M : X → ℂ} (hL : Continuous L) (hM : Continuous M)
    (he : ∀ x, Complex.exp (L x)=Complex.exp (M x)) (x y : X) :
    L x-M x=L y-M y := by
  let D : X → AddSubgroup.zmultiples (2*(Real.pi:ℂ)*Complex.I) := fun x =>
    ⟨L x-M x, by
      obtain ⟨n,hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp (he x)
      exact AddSubgroup.mem_zmultiples_iff.mpr ⟨n,by simpa [zsmul_eq_mul] using
        (eq_sub_iff_add_eq.mpr (by simpa [add_comm] using hn.symm))⟩⟩
  have hD : Continuous D := (hL.sub hM).subtype_mk _
  exact congrArg Subtype.val (PreconnectedSpace.constant inferInstance hD (x:=x) (y:=y))

def HasIncrement (g : ℝ → ℂ) (w : ℂ) : Prop :=
  ∃ L : ℝ → ℂ, Continuous L ∧ (∀ t, Complex.exp (L t)=g t) ∧ L 1-L 0=w

lemma HasIncrement.unique {g : ℝ → ℂ} {u v : ℂ}
    (hu : HasIncrement g u) (hv : HasIncrement g v) : u=v := by
  obtain ⟨L,hL,heL,hu⟩ := hu
  obtain ⟨M,hM,heM,hv⟩ := hv
  have h := exp_equal_difference_constant hL hM (fun t => (heL t).trans (heM t).symm) 1 0
  linear_combination -hu+hv+h

lemma HasIncrement.of_homotopy {g : ℝ × ℝ → ℂ} (hg : Continuous g)
    (h0 : ∀ p, g p ≠ 0) (hloop : ∀ s, g (s,1)=g (s,0))
    {w : ℂ} (hw : HasIncrement (fun t => g (0,t)) w) :
    HasIncrement (fun t => g (1,t)) w := by
  obtain ⟨L,hL,he⟩ := continuous_log_exists hg h0
  have hL0 : Continuous (fun s => L (s,0)) := hL.comp (continuous_id.prodMk continuous_const)
  have hL1 : Continuous (fun s => L (s,1)) := hL.comp (continuous_id.prodMk continuous_const)
  have hsame : L (1,1)-L (1,0)=L (0,1)-L (0,0) :=
    exp_equal_difference_constant hL1 hL0
      (fun s => (he (s,1)).trans ((hloop s).trans (he (s,0)).symm)) 1 0
  have hstart : HasIncrement (fun t => g (0,t)) (L (0,1)-L (0,0)) :=
    ⟨fun t => L (0,t),hL.comp (continuous_const.prodMk continuous_id),fun t => he (0,t),rfl⟩
  exact ⟨fun t => L (1,t),hL.comp (continuous_const.prodMk continuous_id),
    fun t => he (1,t),hsame.trans (hstart.unique hw)⟩

def circle (t : ℝ) : ℂ := Complex.exp ((2*Real.pi*t:ℝ)*Complex.I)

@[fun_prop] lemma continuous_circle : Continuous circle := by unfold circle; fun_prop
lemma norm_circle (t : ℝ) : ‖circle t‖=1 := Complex.norm_exp_ofReal_mul_I _
lemma circle_ne_zero (t : ℝ) : circle t ≠ 0 := Complex.exp_ne_zero _
@[simp] lemma circle_zero : circle 0=1 := by simp [circle]
@[simp] lemma circle_one : circle 1=1 := by simp [circle]

lemma increment_circle_mul {a : ℂ} (ha : a ≠ 0) :
    HasIncrement (fun t => a*circle t) (2*(Real.pi:ℂ)*Complex.I) := by
  refine ⟨fun t => Complex.log a + (2*Real.pi*t:ℝ)*Complex.I,by fun_prop,?_,?_⟩
  · intro t; rw [Complex.exp_add,Complex.exp_log ha]; rfl
  · push_cast; ring

lemma increment_conj_circle_mul {a : ℂ} (ha : a ≠ 0) :
    HasIncrement (fun t => a*conj (circle t)) (-(2*(Real.pi:ℂ)*Complex.I)) := by
  refine ⟨fun t => Complex.log a - (2*Real.pi*t:ℝ)*Complex.I,by fun_prop,?_,?_⟩
  · intro t
    dsimp only
    rw [sub_eq_add_neg,Complex.exp_add,Complex.exp_log ha]
    congr 1
    simp [circle, ← Complex.exp_conj]
    rw [show (starRingEnd ℂ) (2:ℂ)=2 by apply Complex.ext <;> norm_num]
  · push_cast; ring

def clip (s : ℝ) : ℝ := max 0 (min 1 s)
@[fun_prop] lemma continuous_clip : Continuous clip := by unfold clip; fun_prop
lemma clip_nonneg (s : ℝ) : 0 ≤ clip s := le_max_left _ _
lemma clip_le_one (s : ℝ) : clip s ≤ 1 := max_le (by norm_num) (min_le_left _ _)
@[simp] lemma clip_zero : clip 0=0 := by norm_num [clip]
@[simp] lemma clip_one : clip 1=1 := by norm_num [clip]
end CannonOrientation

namespace CannonOrientation
open Set Topology Filter
open scoped ComplexConjugate

lemma HasIncrement.mul_const {g : ℝ → ℂ} {w a : ℂ} (hw : HasIncrement g w)
    (ha : a ≠ 0) : HasIncrement (fun t => a*g t) w := by
  obtain ⟨L,hL,he,hw⟩ := hw
  refine ⟨fun t => Complex.log a+L t,continuous_const.add hL,?_,?_⟩
  · intro t
    simpa only [Complex.exp_add,Complex.exp_log ha] using congrArg (a*·) (he t)
  · dsimp only
    linear_combination hw

lemma HasIncrement.of_close {g h : ℝ → ℂ} {w : ℂ}
    (hg : Continuous g) (hh : Continuous h) (hgl : g 1=g 0) (hhl : h 1=h 0)
    (hc : ∀ t, ‖g t-h t‖ < ‖h t‖) (hw : HasIncrement h w) : HasIncrement g w := by
  let G : ℝ × ℝ → ℂ := fun p => h p.2+(clip p.1) • (g p.2-h p.2)
  have hG : Continuous G := by
    dsimp [G]
    fun_prop
  have hn (p : ℝ × ℝ) : G p ≠ 0 := by
    intro hz
    have he : h p.2 = -((clip p.1) • (g p.2-h p.2)) := by
      dsimp [G] at hz
      exact eq_neg_of_add_eq_zero_left hz
    have hn : ‖h p.2‖ ≤ ‖g p.2-h p.2‖ := by
      calc
        _ = clip p.1*‖g p.2-h p.2‖ := by
          conv_lhs => rw [he]
          rw [norm_neg,norm_smul,Real.norm_eq_abs,abs_of_nonneg (clip_nonneg _)]
        _ ≤ 1*‖g p.2-h p.2‖ := mul_le_mul_of_nonneg_right (clip_le_one _) (norm_nonneg _)
        _ = _ := one_mul _
    exact (not_lt_of_ge hn) (hc p.2)
  have hl (s : ℝ) : G (s,1)=G (s,0) := by simp [G,hgl,hhl]
  have hs : HasIncrement (fun t => G (0,t)) w := by simpa [G] using hw
  simpa [G] using hs.of_homotopy hG hn hl

lemma increment_move_circle {f : ℂ → ℂ} (hf : Continuous f) (hi : Function.Injective f)
    {x y : ℂ} {r R : ℝ} (hr : 0 < r) (hR : 0 < R) {w : ℂ}
    (hw : HasIncrement (fun t => f (x+r • circle t)-f x) w) :
    HasIncrement (fun t => f (y+R • circle t)-f y) w := by
  let center (s : ℝ) : ℂ := (1-clip s) • x+clip s • y
  let radius (s : ℝ) : ℝ := (1-clip s)*r+clip s*R
  have hcenter : Continuous center := by dsimp [center]; fun_prop
  have hradius : Continuous radius := by dsimp [radius]; fun_prop
  have hpos (s : ℝ) : 0 < radius s := by
    have h0 := clip_nonneg s
    have h1 := clip_le_one s
    dsimp [radius]
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) hr.le,mul_nonneg h0 hR.le]
  let G : ℝ × ℝ → ℂ := fun p =>
    f (center p.1+radius p.1 • circle p.2)-f (center p.1)
  have hG : Continuous G := by dsimp [G]; fun_prop
  have hn (p : ℝ × ℝ) : G p ≠ 0 := by
    intro he
    have hz : radius p.1 • circle p.2=0 := add_eq_left.mp (hi (sub_eq_zero.mp he))
    exact (smul_ne_zero (ne_of_gt (hpos _)) (circle_ne_zero _)) hz
  have hl (s : ℝ) : G (s,1)=G (s,0) := by simp [G]
  have hs : HasIncrement (fun t => G (0,t)) w := by simpa [G,center,radius] using hw
  simpa [G,center,radius] using hs.of_homotopy hG hn hl

end CannonOrientation

namespace CannonOrientation
open Set Topology Filter
open scoped ComplexConjugate

lemma increment_at_derivative {f : ℂ → ℂ} (hf : Continuous f)
    {x : ℂ} {A : ℂ →L[ℝ] ℂ} (hA : HasFDerivAt f A x)
    {m : ℝ} (hm : 0 < m) (hn : ∀ t, ‖A (circle t)‖=m)
    {w : ℂ} (hw : HasIncrement (fun t => A (circle t)) w) :
    ∃ r : ℝ, 0 < r ∧ HasIncrement (fun t => f (x+r • circle t)-f x) w := by
  obtain ⟨ε,hε,he⟩ := Metric.eventually_nhds_iff.mp (hA.isLittleO.bound (half_pos hm))
  let r : ℝ := ε/2
  have hr : 0 < r := half_pos hε
  have hd (t : ℝ) : dist (x+r • circle t) x=r := by
    simp [dist_eq_norm,Real.norm_eq_abs,abs_of_pos hr,norm_circle]
  have hs : HasIncrement (fun t => r • A (circle t)) w := by
    simpa only [Complex.real_smul] using hw.mul_const (a:=(r:ℂ)) (by exact_mod_cast hr.ne')
  refine ⟨r,hr,HasIncrement.of_close ?_ ?_ ?_ ?_ ?_ hs⟩
  · exact (hf.comp (continuous_const.add (continuous_circle.const_smul r))).sub continuous_const
  · exact (A.continuous.comp continuous_circle).const_smul r
  · simp
  · simp
  · intro t
    have hh := he (y:=x+r • circle t) (by rw [hd]; dsimp [r]; linarith)
    have hl : ‖f (x+r • circle t)-f x-r • A (circle t)‖ ≤ (m/2)*r := by
      simpa only [add_sub_cancel_left,map_smul,norm_smul,norm_circle,mul_one,
        Real.norm_eq_abs,abs_of_pos hr] using hh
    have hn' : ‖r • A (circle t)‖=r*m := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr,hn]
    rw [hn']
    exact hl.trans_lt (by nlinarith)

theorem no_opposite_similarities {f : ℂ → ℂ} (hf : Continuous f)
    (hi : Function.Injective f) {x y : ℂ} {A B : ℂ →L[ℝ] ℂ}
    (hA : HasFDerivAt f A x) (hB : HasFDerivAt f B y)
    {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hAz : ∀ z, A z=a*z) (hBz : ∀ z, B z=b*conj z) : False := by
  obtain ⟨r,hr,hri⟩ := increment_at_derivative hf hA (norm_pos_iff.mpr ha)
    (fun t => by rw [hAz,norm_mul,norm_circle,mul_one])
    (by simpa only [hAz] using increment_circle_mul ha)
  obtain ⟨R,hR,hRi⟩ := increment_at_derivative hf hB (norm_pos_iff.mpr hb)
    (fun t => by rw [hBz,norm_mul,Complex.norm_conj,norm_circle,mul_one])
    (by simpa only [hBz] using increment_conj_circle_mul hb)
  have he := (increment_move_circle hf hi hr hR hri).unique hRi
  have hh := congrArg Complex.im he
  norm_num [Complex.mul_im] at hh
  linarith [Real.pi_pos]
end CannonOrientation

namespace CannonOrientation
open scoped ComplexConjugate

lemma conformal_scalar_cases {A : ℂ →L[ℝ] ℂ} (hA : IsConformalMap A) :
    (∃ a : ℂ, a ≠ 0 ∧ ∀ z, A z=a*z) ∨
    (∃ a : ℂ, a ≠ 0 ∧ ∀ z, A z=a*conj z) := by
  have hn : A 1 ≠ 0 := fun he => one_ne_zero (hA.injective (he.trans (map_zero A).symm))
  rcases hA.is_complex_or_conj_linear with ⟨L,hL⟩ | ⟨L,hL⟩
  · left
    refine ⟨A 1,hn,?_⟩
    intro z
    have he : L z=z*L 1 := by simpa using L.map_smul z (1:ℂ)
    have he' : ∀ u, L u=A u := fun u => congrArg (fun T : ℂ →L[ℝ] ℂ => T u) hL
    simpa only [he',mul_comm] using he
  · right
    refine ⟨A 1,hn,?_⟩
    intro z
    have he : L (conj z)=conj z*L 1 := by simpa using L.map_smul (conj z) (1:ℂ)
    have he' : ∀ u, L u=A (conj u) := fun u => congrArg (fun T : ℂ →L[ℝ] ℂ => T u) hL
    simpa only [he',map_one,starRingEnd_self_apply,mul_comm] using he

theorem conformal_differential_orientation {f : ℂ → ℂ} (hf : Continuous f)
    (hi : Function.Injective f) :
    (∀ x, DifferentiableAt ℝ f x → IsConformalMap (fderiv ℝ f x) →
      ∃ a : ℂ, a ≠ 0 ∧ ∀ z, fderiv ℝ f x z=a*z) ∨
    (∀ x, DifferentiableAt ℝ f x → IsConformalMap (fderiv ℝ f x) →
      ∃ a : ℂ, a ≠ 0 ∧ ∀ z, fderiv ℝ f x z=a*conj z) := by
  classical
  by_cases h : ∃ x, DifferentiableAt ℝ f x ∧ IsConformalMap (fderiv ℝ f x) ∧
      ∃ a : ℂ, a ≠ 0 ∧ ∀ z, fderiv ℝ f x z=a*z
  · obtain ⟨x,hx,-,a,ha,haz⟩ := h
    left
    intro y hy hfy
    rcases conformal_scalar_cases hfy with han | ⟨b,hb,hbz⟩
    · exact han
    · exact (no_opposite_similarities hf hi hx.hasFDerivAt hy.hasFDerivAt ha hb haz hbz).elim
  · right
    intro y hy hfy
    rcases conformal_scalar_cases hfy with ⟨a,ha,haz⟩ | han
    · exact (h ⟨y,hy,hfy,a,ha,haz⟩).elim
    · exact han
end CannonOrientation

end
end
section
noncomputable section
open MeasureTheory Filter FourierTransform Set Metric
open scoped Real SchwartzMap ContDiff Topology

noncomputable section
open MeasureTheory Filter Set Metric Function ContinuousLinearMap
open scoped Topology Convolution ContDiff Pointwise

namespace CannonBeltrami
open ContinuousLinearMap

lemma partialBar_reflect {κ : ℂ → ℂ} (hκ : Differentiable ℝ κ) (x z : ℂ) :
    partialBar (fun w => κ (x-w)) z = -partialBar κ (x-z) := by
  have hd := (hκ (x-z)).hasFDerivAt.comp z ((hasFDerivAt_const x z).sub (hasFDerivAt_id z))
  have hd' : fderiv ℝ (fun w => κ (x-w)) z = _ := hd.fderiv
  unfold partialBar
  rw [hd']
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,zero_sub,
    neg_apply,map_neg]
  ring

def barProject : (ℂ →L[ℝ] ℂ) →L[ℝ] ℂ :=
  (1/2:ℂ) • ((apply ℝ ℂ (1:ℂ)) + Complex.I • (apply ℝ ℂ Complex.I))

lemma barProject_apply (D : ℂ →L[ℝ] ℂ) :
    barProject D=(D 1+Complex.I*D Complex.I)/2 := by
  simp [barProject,smul_eq_mul]; ring

lemma convolution_partialBar {F κ : ℂ → ℂ} (hF : LocallyIntegrable F volume)
    (hκ : ContDiff ℝ ∞ κ) (hc : HasCompactSupport κ) (x : ℂ) :
    partialBar (F ⋆[mul ℝ ℂ,volume] κ) x=
      ∫ z, F z*partialBar κ (x-z) := by
  let L := mul ℝ ℂ
  let D : ℂ → (ℂ →L[ℝ] ℂ) := fun z => L.precompR ℂ (F z) (fderiv ℝ κ (x-z))
  have hD : Integrable D volume :=
    (hc.fderiv ℝ).convolutionExists_right (L.precompR ℂ) hF
      ((hκ.of_le (by simp) : ContDiff ℝ 1 κ).continuous_fderiv (by simp)) x
  have hd := hc.hasFDerivAt_convolution_right L hF (hκ.of_le (by simp)) x
  change (fderiv ℝ (F ⋆[L,volume] κ) x 1 +
    Complex.I * fderiv ℝ (F ⋆[L,volume] κ) x Complex.I) / 2 = _
  rw [← barProject_apply]
  rw [hd.fderiv]
  change barProject (∫ z, D z)=_
  rw [← barProject.integral_comp_comm hD]
  apply integral_congr_ae
  exact .of_forall (fun z => by
    change barProject (D z) = F z * partialBar κ (x-z)
    rw [barProject_apply]
    simp only [D,L,precompR_apply,compL_apply,ContinuousLinearMap.comp_apply,mul_apply']
    unfold partialBar
    ring)

lemma weak_partialBar_convolution {F : ℂ → ℂ} (hF : LocallyIntegrable F volume)
    (hw : ∀ φ : SchwartzMap ℂ ℂ, HasCompactSupport (φ : ℂ → ℂ) →
      (∫ z, F z*partialBar φ z)=0)
    {κ : ℂ → ℂ} (hκ : ContDiff ℝ ∞ κ) (hc : HasCompactSupport κ) :
    Differentiable ℂ (F ⋆[mul ℝ ℂ,volume] κ) := by
  have hs := hc.contDiff_convolution_right (mul ℝ ℂ) hF hκ
  intro x
  apply differentiableAt_of_partialBar_zero (hs.differentiable (by simp) x)
  rw [convolution_partialBar hF hκ hc]
  let ψ : ℂ → ℂ := fun z => κ (x-z)
  have hψ : ContDiff ℝ ∞ ψ := hκ.comp (contDiff_const.sub contDiff_id)
  have hcψ : HasCompactSupport ψ := by
    exact hc.comp_homeomorph ((Homeomorph.neg ℂ).trans (Homeomorph.addLeft x))
  let φ := hcψ.toSchwartzMap hψ
  have hh := hw φ hcψ
  have he (z : ℂ) : partialBar φ z=-partialBar κ (x-z) :=
    partialBar_reflect (hκ.differentiable (by simp)) x z
  simp only [he,mul_neg,integral_neg,neg_eq_zero] at hh
  exact hh

lemma mollify_eq_complex_convolution (F : ℂ → ℂ) (n : ℕ) :
    mollify F n = F ⋆[mul ℝ ℂ,volume] (fun z => ((mollifier n).normed volume z:ℂ)) := by
  rw [← convolution_flip]
  funext x
  unfold mollify convolution
  apply integral_congr_ae
  exact .of_forall (fun z => by simp [mul_comm,lsmul_apply])

lemma mollifier_radius_tendsto : Tendsto (fun n => (mollifier n).rOut) atTop (𝓝 0) := by
  have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2:ℝ)
  simpa [mollifier,div_eq_mul_inv] using h

lemma mollify_locally_uniform {F : ℂ → ℂ} (hF : Continuous F) :
    TendstoLocallyUniformly (mollify F) F atTop := by
  rw [tendstoLocallyUniformly_iff_forall_tendsto]
  intro x
  have ht : Tendsto (fun p : ℕ × ℂ => mollify F p.1 p.2)
      (atTop ×ˢ 𝓝 x) (𝓝 (F x)) := by
    apply ContDiffBump.convolution_tendsto_right
    · exact mollifier_radius_tendsto.comp tendsto_fst
    · exact .of_forall (fun _ => hF.aestronglyMeasurable)
    · exact (hF.tendsto x).comp tendsto_snd
    · exact tendsto_snd
  exact ((hF.tendsto x).comp tendsto_snd).prodMk_nhds ht |>.mono_right (nhds_le_uniformity (F x))

theorem weak_partialBar_zero_holomorphic {F : ℂ → ℂ} (hF : Continuous F)
    (hw : ∀ φ : SchwartzMap ℂ ℂ, HasCompactSupport (φ : ℂ → ℂ) →
      (∫ z, F z*partialBar φ z)=0) : Differentiable ℂ F := by
  have hs (n : ℕ) : Differentiable ℂ (mollify F n) := by
    rw [mollify_eq_complex_convolution]
    exact weak_partialBar_convolution hF.locallyIntegrable hw
      (Complex.ofRealCLM.contDiff.comp (mollifier n).contDiff_normed)
      ((mollifier n).hasCompactSupport_normed.comp_left Complex.ofReal_zero)
  exact differentiableOn_univ.mp
    ((tendstoLocallyUniformlyOn_univ.mpr (mollify_locally_uniform hF)).differentiableOn
      (.of_forall (fun n => (hs n).differentiableOn)) isOpen_univ)
end CannonBeltrami

end
end
end
end
end
end
end
end
end

end OAI
