import Mathlib
import OAI.Geometry.Cannon.Modulus.AnnularCutoffEnergy2
import OAI.Geometry.Cannon.Energy.StopInside

namespace OAI

section
section
section
section
section
section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology

noncomputable section
open MeasureTheory Filter FourierTransform
open scoped SchwartzMap Real Topology ContDiff

noncomputable section
open MeasureTheory Filter FourierTransform Set Metric
open scoped Real SchwartzMap ContDiff Topology

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

noncomputable section
open Set Topology

namespace CannonPlane

lemma segment_isCompact (a b : ℂ) : IsCompact (segment ℝ a b) := by
  rw [segment_eq_image]
  exact isCompact_Icc.image (by fun_prop)

lemma segment_isConnected (a b : ℂ) : IsConnected (segment ℝ a b) := by
  rw [segment_eq_image]
  exact (isConnected_Icc (by norm_num : (0:ℝ) ≤ 1)).image _ (by fun_prop)

lemma ray_image_escapes (F : ℂ ≃ₜ ℂ) {b : ℂ} (hb : b ≠ 0) (S : ℝ) :
    ∃ t : ℝ, 1 ≤ t ∧ S < ‖F (t • b)‖ := by
  obtain ⟨M,hM,hbound⟩ := ((isCompact_closedBall (0:ℂ) S).image F.symm.continuous).isBounded.exists_pos_norm_lt
  let t : ℝ := 1+M/‖b‖
  have hb0 : 0 < ‖b‖ := norm_pos_iff.mpr hb
  have ht : 1 ≤ t := by dsimp [t]; linarith [div_nonneg hM.le hb0.le]
  refine ⟨t,ht,?_⟩
  by_contra hn
  have hin : t • b ∈ F.symm '' closedBall (0:ℂ) S := by
    refine ⟨F (t • b),?_,F.symm_apply_apply _⟩
    simpa using le_of_not_gt hn
  have hm := hbound _ hin
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by linarith : 0 ≤ t)] at hm
  dsimp only [t] at hm
  have hh : (1+M/‖b‖)*‖b‖=‖b‖+M := by field_simp
  rw [hh] at hm
  linarith

lemma norm_ge_of_mem_radial_segment {b z : ℂ} {t : ℝ} (ht : 1 ≤ t)
    (hz : z ∈ segment ℝ b (t • b)) : ‖b‖ ≤ ‖z‖ := by
  obtain ⟨a₁,a₂,ha₁,ha₂,ha,rfl⟩ := hz
  rw [smul_smul,← add_smul,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (add_nonneg ha₁ (mul_nonneg ha₂ (by linarith)))]
  have hc : 1 ≤ a₁+a₂*t := by nlinarith
  nlinarith [norm_nonneg b]

theorem annular_ratio (F : ℂ ≃ₜ ℂ) (hF0 : F 0=0)
    (hF : ContDiff ℝ 1 (F.symm : ℂ → ℂ)) {K : ℝ} (hK : 0 ≤ K)
    (hD : ∀ z, ‖fderiv ℝ (F.symm : ℂ → ℂ) z‖^2 ≤ K*|(fderiv ℝ (F.symm : ℂ → ℂ) z).det|)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ t, |deriv Real.smoothTransition t| ≤ C)
    {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : 2*‖a‖ ≤ ‖b‖) :
    Real.log (‖b‖/‖a‖) ≤
      128*(16*‖F b‖/min ‖F a‖ ‖F b‖+1)*K*Real.pi*C^2 := by
  have ha0 : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hAf : F a ≠ 0 := by rw [← hF0]; exact fun h => ha (F.injective h)
  have hBf : F b ≠ 0 := by rw [← hF0]; exact fun h => hb (F.injective h)
  have hA : 0 < ‖F a‖ := norm_pos_iff.mpr hAf
  have hB : 0 < ‖F b‖ := norm_pos_iff.mpr hBf
  let d := min ‖F a‖ ‖F b‖/2
  have hd : 0 < d := by dsimp [d]; positivity
  have hdA : d < ‖F a‖ := by have := min_le_left ‖F a‖ ‖F b‖; dsimp [d]; linarith
  have hdB : d ≤ ‖F b‖ := by have := min_le_right ‖F a‖ ‖F b‖; dsimp [d]; linarith
  let D := F '' segment ℝ (0:ℂ) a
  have hDc : IsCompact D := (segment_isCompact 0 a).image F.continuous
  have hDconn : IsConnected D := (segment_isConnected 0 a).image F F.continuous.continuousOn
  have h0D : (0:ℂ) ∈ D := ⟨0,left_mem_segment ℝ 0 a,hF0⟩
  have hfar : ∃ y ∈ D, d < dist y 0 := ⟨F a,⟨a,right_mem_segment ℝ 0 a,rfl⟩,by simpa using hdA⟩
  obtain ⟨E,hEc,hEconn,hED,h0E,⟨e,heE,he⟩,heB⟩ :=
    CannonContinuum.stop_inside hDc hDconn h0D (by simpa using hd) hfar
  obtain ⟨t,ht,htF⟩ := ray_image_escapes F hb (2*‖F b‖)
  let D' := F '' segment ℝ b (t • b)
  have hD'c : IsCompact D' := (segment_isCompact b (t • b)).image F.continuous
  have hD'conn : IsConnected D' := (segment_isConnected b (t • b)).image F F.continuous.continuousOn
  have hbD' : F b ∈ D' := ⟨b,left_mem_segment ℝ b (t • b),rfl⟩
  have hfar' : ∃ y ∈ D', 2*‖F b‖ < dist y 0 :=
    ⟨F (t • b),⟨t • b,right_mem_segment ℝ b (t • b),rfl⟩,by simpa using htF⟩
  obtain ⟨G,hGc,hGconn,hGD,hbG,⟨g,hgG,hg⟩,hgB⟩ :=
    CannonContinuum.stop_inside hD'c hD'conn hbD' (by simpa using (show ‖F b‖ < 2*‖F b‖ by linarith)) hfar'
  have hEin : ∀ z ∈ E, ‖F.symm z‖ ≤ ‖a‖ := by
    intro z hz
    obtain ⟨w,hw,rfl⟩ := hED hz
    rw [F.symm_apply_apply]
    have hh := (convex_closedBall (0:ℂ) ‖a‖).segment_subset
      (mem_closedBall.mpr (by simp)) (mem_closedBall.mpr (by simp)) hw
    simpa using hh
  have hGout : ∀ z ∈ G, ‖b‖ ≤ ‖F.symm z‖ := by
    intro z hz
    obtain ⟨w,hw,rfl⟩ := hGD hz
    rw [F.symm_apply_apply]
    exact norm_ge_of_mem_radial_segment ht hw
  have hGwide : d ≤ dist (F b) g := by
    have hh := dist_triangle g (F b) 0
    rw [hg,dist_comm g (F b),dist_zero_right] at hh
    linarith
  have hh := annular_condenser_bound F hF hK hD ha0 hab hC0 hC
    (by positivity : 0 < 2*‖F b‖) hd hEconn.isPreconnected hGconn.isPreconnected
    (fun z hz => mem_closedBall.mpr ((heB z hz).trans (by linarith)))
    (fun z hz => mem_closedBall.mpr (hgB z hz)) hEin hGout
    ⟨0,h0E,e,heE,by rw [dist_comm,he]⟩ ⟨F b,hbG,g,hgG,hGwide⟩
  convert hh using 1
  dsimp [d]
  ring

end CannonPlane

namespace CannonPlane

def centeredHomeomorph (F : ℂ ≃ₜ ℂ) (x : ℂ) : ℂ ≃ₜ ℂ where
  toFun z := F (z+x)-F x
  invFun w := F.symm (w+F x)-x
  left_inv z := by simp
  right_inv w := by simp
  continuous_toFun := (F.continuous.comp (continuous_id.add continuous_const)).sub continuous_const
  continuous_invFun := (F.symm.continuous.comp (continuous_id.add continuous_const)).sub continuous_const

@[simp] lemma centeredHomeomorph_apply (F : ℂ ≃ₜ ℂ) (x z : ℂ) :
    centeredHomeomorph F x z = F (z+x)-F x := rfl

@[simp] lemma centeredHomeomorph_symm_apply (F : ℂ ≃ₜ ℂ) (x z : ℂ) :
    (centeredHomeomorph F x).symm z = F.symm (z+F x)-x := rfl

lemma centered_symm_contDiff (F : ℂ ≃ₜ ℂ) (hF : ContDiff ℝ 1 (F.symm : ℂ → ℂ)) (x : ℂ) :
    ContDiff ℝ 1 ((centeredHomeomorph F x).symm : ℂ → ℂ) :=
  (hF.comp (contDiff_id.add contDiff_const)).sub contDiff_const

lemma centered_symm_fderiv (F : ℂ ≃ₜ ℂ) (hF : ContDiff ℝ 1 (F.symm : ℂ → ℂ)) (x z : ℂ) :
    fderiv ℝ ((centeredHomeomorph F x).symm : ℂ → ℂ) z = fderiv ℝ (F.symm : ℂ → ℂ) (z+F x) := by
  have h := ((hF.differentiable (by simp) (z+F x)).hasFDerivAt.comp z
    ((hasFDerivAt_id z).add_const (F x))).sub_const x
  change fderiv ℝ (fun w => F.symm (w+F x)-x) z = _
  simpa only [Function.comp_def,id_eq,ContinuousLinearMap.comp_id] using h.fderiv

theorem annular_ratio_at (F : ℂ ≃ₜ ℂ)
    (hF : ContDiff ℝ 1 (F.symm : ℂ → ℂ)) {K : ℝ} (hK : 0 ≤ K)
    (hD : ∀ z, ‖fderiv ℝ (F.symm : ℂ → ℂ) z‖^2 ≤ K*|(fderiv ℝ (F.symm : ℂ → ℂ) z).det|)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ t, |deriv Real.smoothTransition t| ≤ C)
    {x a b : ℂ} (ha : a ≠ x) (hb : b ≠ x) (hab : 2*dist a x ≤ dist b x) :
    Real.log (dist b x/dist a x) ≤
      128*(16*dist (F b) (F x)/min (dist (F a) (F x)) (dist (F b) (F x))+1)*K*Real.pi*C^2 := by
  have h := annular_ratio (centeredHomeomorph F x) (by simp [centeredHomeomorph])
    (centered_symm_contDiff F hF x) hK
    (by intro z; rw [centered_symm_fderiv F hF]; exact hD _)
    hC0 hC (sub_ne_zero.mpr ha) (sub_ne_zero.mpr hb)
    (by simpa only [dist_eq_norm] using hab)
  simpa only [centeredHomeomorph_apply,sub_add_cancel,dist_eq_norm] using h

theorem smooth_qc_uniform_shrink {K : ℝ} (hK : 0 ≤ K) :
    ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∀ F : ℂ ≃ₜ ℂ,
      ContDiff ℝ 1 (F.symm : ℂ → ℂ) →
      (∀ z, ‖fderiv ℝ (F.symm : ℂ → ℂ) z‖^2 ≤ K*|(fderiv ℝ (F.symm : ℂ → ℂ) z).det|) →
      ∀ x a b : ℂ, b ≠ x → dist a x < η*dist b x →
        dist (F a) (F x) < ε*dist (F b) (F x) := by
  intro ε hε
  obtain ⟨C,hC1,hC⟩ := smoothTransition_deriv_bound
  have hC0 : 0 ≤ C := by linarith
  let e := min ε 1
  have he : 0 < e := lt_min hε (by norm_num)
  have heε : e ≤ ε := min_le_left _ _
  have he1 : e ≤ 1 := min_le_right _ _
  let L := 128*(16/e+1)*K*Real.pi*C^2
  let η := min (1/2:ℝ) (Real.exp (-(L+1)))
  have hη : 0 < η := lt_min (by norm_num) (Real.exp_pos _)
  refine ⟨η,hη,?_⟩
  intro F hF hD x a b hb hab
  have hB : 0 < dist (F b) (F x) := dist_pos.mpr (fun hh => hb (F.injective hh))
  by_cases ha : a=x
  · subst a
    simpa only [dist_self] using mul_pos hε hB
  have hr : 0 < dist a x := dist_pos.mpr ha
  have hR : 0 < dist b x := dist_pos.mpr hb
  have h2 : 2*dist a x ≤ dist b x := by
    have hh := mul_le_mul_of_nonneg_right (min_le_left (1/2:ℝ) (Real.exp (-(L+1)))) hR.le
    dsimp only [η] at hab
    nlinarith
  have hlog := annular_ratio_at F hF hK hD hC0 hC ha hb h2
  by_contra hn
  have hn' : ε*dist (F b) (F x) ≤ dist (F a) (F x) := le_of_not_gt hn
  have hmin : e*dist (F b) (F x) ≤ min (dist (F a) (F x)) (dist (F b) (F x)) := by
    apply le_min
    · exact (mul_le_mul_of_nonneg_right heε hB.le).trans hn'
    · simpa only [one_mul] using mul_le_mul_of_nonneg_right he1 hB.le
  have hminpos : 0 < min (dist (F a) (F x)) (dist (F b) (F x)) := (mul_pos he hB).trans_le hmin
  have hdiv : dist (F b) (F x)/min (dist (F a) (F x)) (dist (F b) (F x)) ≤ 1/e := by
    apply (div_le_div_iff₀ hminpos he).mpr
    simpa only [one_mul,mul_comm] using hmin
  have hupper : 128*(16*dist (F b) (F x)/min (dist (F a) (F x)) (dist (F b) (F x))+1)*K*Real.pi*C^2 ≤ L := by
    dsimp only [L]
    have hh : 16*dist (F b) (F x)/min (dist (F a) (F x)) (dist (F b) (F x)) ≤ 16/e := by
      simpa only [div_eq_mul_inv,mul_assoc,one_mul] using mul_le_mul_of_nonneg_left hdiv (by norm_num : (0:ℝ) ≤ 16)
    gcongr
  have hsource : dist a x/dist b x < Real.exp (-(L+1)) := by
    apply (div_lt_iff₀ hR).mpr
    exact hab.trans_le (mul_le_mul_of_nonneg_right (min_le_right _ _) hR.le)
  have hlogsmall := Real.log_lt_log (div_pos hr hR) hsource
  rw [Real.log_exp] at hlogsmall
  have hlogeq : Real.log (dist b x/dist a x) = -Real.log (dist a x/dist b x) := by
    simpa only [inv_div] using Real.log_inv (dist a x/dist b x)
  rw [hlogeq] at hlog
  linarith [hlog.trans hupper]

end CannonPlane

noncomputable section
open Set Metric Filter Topology

namespace CannonPlane

def UniformRelativeControl {ι : Type*} (F : ι → ℂ → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∀ i x a b, b ≠ x →
    dist a x < η*dist b x → dist (F i a) (F i x) < ε*dist (F i b) (F i x)

theorem normalized_family_pointwise_bound {ι : Type*} (F : ι → ℂ → ℂ)
    (hF0 : ∀ i, F i 0=0) (hF1 : ∀ i, F i 1=1) (hF : UniformRelativeControl F) :
    ∀ z, ∃ B : ℝ, ∀ i, ‖F i z‖ ≤ B := by
  obtain ⟨η,hη,hηF⟩ := hF 1 (by norm_num)
  let P : Set ℂ := {z | ∃ B : ℝ, ∀ i, ‖F i z‖ ≤ B}
  have h0 : (0:ℂ) ∈ P := ⟨0,fun i => by simp [hF0]⟩
  have hnear {z w : ℂ} (hz : z ≠ 0) (hw : dist w z < η*‖z‖) (hzP : z ∈ P) : w ∈ P := by
    obtain ⟨B,hB⟩ := hzP
    refine ⟨2*B,fun i => ?_⟩
    have hs := hηF i z w 0 hz.symm (by simpa only [dist_zero_left] using hw)
    rw [one_mul,hF0,dist_zero_left] at hs
    have ht := dist_triangle (F i w) (F i z) 0
    simp only [dist_zero_right] at ht
    linarith [hB i]
  have ho : IsOpen P := by
    apply Metric.isOpen_iff.mpr
    intro z hz
    by_cases hz0 : z=0
    · subst z
      refine ⟨η,hη,?_⟩
      intro w hw
      refine ⟨1,fun i => ?_⟩
      have hs := hηF i 0 w 1 (by norm_num) (by simpa using hw)
      simpa only [hF0,hF1,dist_zero_right,norm_one,one_mul] using hs.le
    · exact ⟨η*‖z‖,mul_pos hη (norm_pos_iff.mpr hz0),fun w hw => hnear hz0 hw hz⟩
  have hc : IsClosed P := by
    apply closure_subset_iff_isClosed.mp
    intro z hz
    by_cases hz0 : z=0
    · simpa only [hz0] using h0
    have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    obtain ⟨w,hwP,hw⟩ := Metric.mem_closure_iff.mp hz
      (min (‖z‖/2) (η*‖z‖/2)) (by positivity)
    have hw1 := hw.trans_le (min_le_left _ _)
    have hw2 := hw.trans_le (min_le_right _ _)
    have ht := dist_triangle z w 0
    simp only [dist_zero_right] at ht
    have hwpos : 0 < ‖w‖ := by linarith
    have hsmall : dist z w < η*‖w‖ := by nlinarith
    exact hnear (norm_pos_iff.mp hwpos) hsmall hwP
  have hall : P=univ := (show IsClopen P from ⟨hc,ho⟩).eq_univ ⟨0,h0⟩
  intro z
  exact (show z ∈ P by rw [hall]; trivial)

theorem relative_control_equicontinuous {ι : Type*} (F : ι → ℂ → ℂ)
    (hF : UniformRelativeControl F) (hb : ∀ z, ∃ B : ℝ, ∀ i, ‖F i z‖ ≤ B) :
    Equicontinuous F := by
  intro x
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  let b := x+1
  have hbx : b ≠ x := by simp [b]
  have hdist : 0 < dist b x := dist_pos.mpr hbx
  obtain ⟨A,hA⟩ := hb x
  obtain ⟨B,hB⟩ := hb b
  let L := max (A+B) 0+1
  have hL : 0 < L := by dsimp [L]; positivity
  have hble : A+B ≤ L := by dsimp [L]; linarith [le_max_left (A+B) 0]
  obtain ⟨η,hη,hcontrol⟩ := hF (ε/L) (div_pos hε hL)
  refine ⟨η*dist b x,mul_pos hη hdist,fun y hy i => ?_⟩
  have hh := hcontrol i x y b hbx hy
  have hdf : dist (F i b) (F i x) ≤ L := by
    have ht := dist_triangle (F i b) 0 (F i x)
    simp only [dist_zero_left,dist_zero_right] at ht
    linarith [hA i,hB i]
  have hbound := mul_le_mul_of_nonneg_left hdf (div_pos hε hL).le
  rw [div_mul_cancel₀ ε hL.ne'] at hbound
  rw [dist_comm]
  exact hh.trans_le hbound

end CannonPlane

noncomputable section
open Set Filter Topology Metric

namespace CannonPlane

def homeomorphMap (F : ℂ ≃ₜ ℂ) : C(ℂ,ℂ) := ⟨F,F.continuous⟩

lemma complex_map_subsequence (f : ℕ → C(ℂ,ℂ))
    (heq : Equicontinuous (fun n z => f n z))
    (hb : ∀ z, ∃ B, ∀ n, ‖f n z‖ ≤ B) :
    ∃ F : C(ℂ,ℂ), ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (f ∘ φ) atTop (𝓝 F) := by
  classical
  have : T2Space (UniformOnFun ℂ ℂ {K | IsCompact K}) :=
    UniformOnFun.t2Space_of_covering (by
      apply eq_univ_of_forall
      intro x
      exact mem_sUnion_of_mem (mem_singleton x) isCompact_singleton)
  have hcompact : IsCompact (closure (range f)) := by
    apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (F := fun g : C(ℂ,ℂ) => (g : ℂ → ℂ)) (𝔖 := {K | IsCompact K}) (fun _ h => h)
    · exact ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isClosedEmbedding
    · intro K hK
      have hindex : ∀ g : range f, ∃ n, f n=g.val := fun g => g.property
      choose index hindex using hindex
      have heq' := heq.comp index
      have heq'' : Equicontinuous (fun g : range f => (g.val : ℂ → ℂ)) := by
        convert heq' using 1
        funext g x
        exact congrArg (fun h : C(ℂ,ℂ) => h x) (hindex g).symm
      exact heq''.equicontinuousOn K
    · intro K _hK z _hz
      obtain ⟨B,hB⟩ := hb z
      refine ⟨closedBall (0 : ℂ) B,isCompact_closedBall _ _,?_⟩
      rintro g ⟨n,rfl⟩
      simpa only [mem_closedBall,dist_zero_right] using hB n
  obtain ⟨F,_hF,φ,hφ,ht⟩ := hcompact.tendsto_subseq (fun n => subset_closure (mem_range_self n))
  exact ⟨F,φ,hφ,ht⟩

theorem pointwise_bounded_homeomorph_subsequence (F : ℕ → ℂ ≃ₜ ℂ)
    (heq : Equicontinuous (fun n z => F n z))
    (heq' : Equicontinuous (fun n z => (F n).symm z))
    (hb : ∀ z, ∃ B, ∀ n, ‖F n z‖ ≤ B)
    (hb' : ∀ z, ∃ B, ∀ n, ‖(F n).symm z‖ ≤ B) :
    ∃ H : ℂ ≃ₜ ℂ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => homeomorphMap (F (φ n))) atTop (𝓝 (homeomorphMap H)) ∧
      Tendsto (fun n => homeomorphMap (F (φ n)).symm) atTop (𝓝 (homeomorphMap H.symm)) := by
  obtain ⟨f,φ,hφ,ht⟩ := complex_map_subsequence (fun n => homeomorphMap (F n)) heq hb
  obtain ⟨g,ψ,hψ,ht'⟩ := complex_map_subsequence (fun n => homeomorphMap (F (φ n)).symm)
    (heq'.comp φ) (by
      intro z
      obtain ⟨B,hB⟩ := hb' z
      exact ⟨B,fun n => hB (φ n)⟩)
  have htF : Tendsto (fun n => homeomorphMap (F (φ (ψ n)))) atTop (𝓝 f) := ht.comp hψ.tendsto_atTop
  have htG : Tendsto (fun n => homeomorphMap (F (φ (ψ n))).symm) atTop (𝓝 g) := ht'
  have hfg (z : ℂ) : f (g z)=z := by
    have hz : Tendsto (fun n => (F (φ (ψ n))).symm z) atTop (𝓝 (g z)) :=
      (continuous_eval_const z).tendsto g |>.comp htG
    have h := continuous_eval.tendsto (f,g z) |>.comp (htF.prodMk_nhds hz)
    have h' : Tendsto (fun _ : ℕ => z) atTop (𝓝 (f (g z))) := by simpa [Function.comp_def,homeomorphMap] using h
    exact tendsto_nhds_unique h' tendsto_const_nhds
  have hgf (z : ℂ) : g (f z)=z := by
    have hz : Tendsto (fun n => F (φ (ψ n)) z) atTop (𝓝 (f z)) :=
      (continuous_eval_const z).tendsto f |>.comp htF
    have h := continuous_eval.tendsto (g,f z) |>.comp (htG.prodMk_nhds hz)
    have h' : Tendsto (fun _ : ℕ => z) atTop (𝓝 (g (f z))) := by simpa [Function.comp_def,homeomorphMap] using h
    exact tendsto_nhds_unique h' tendsto_const_nhds
  let H : ℂ ≃ₜ ℂ := {
    toFun := f
    invFun := g
    left_inv := hgf
    right_inv := hfg
    continuous_toFun := f.continuous
    continuous_invFun := g.continuous }
  exact ⟨H,φ ∘ ψ,hφ.comp hψ,htF,htG⟩

end CannonPlane

namespace CannonPlane

theorem normalized_smooth_qc_subsequence (F : ℕ → ℂ ≃ₜ ℂ)
    (hF0 : ∀ n, F n 0=0) (hF1 : ∀ n, F n 1=1)
    (hF : ∀ n, ContDiff ℝ 1 (F n : ℂ → ℂ))
    (hF' : ∀ n, ContDiff ℝ 1 ((F n).symm : ℂ → ℂ))
    {K : ℝ} (hK : 0 ≤ K)
    (hD : ∀ n z, ‖fderiv ℝ (F n : ℂ → ℂ) z‖^2 ≤ K*|(fderiv ℝ (F n : ℂ → ℂ) z).det|)
    (hD' : ∀ n z, ‖fderiv ℝ ((F n).symm : ℂ → ℂ) z‖^2 ≤ K*|(fderiv ℝ ((F n).symm : ℂ → ℂ) z).det|) :
    ∃ H : ℂ ≃ₜ ℂ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      H 0=0 ∧ H 1=1 ∧
      Tendsto (fun n => homeomorphMap (F (φ n))) atTop (𝓝 (homeomorphMap H)) ∧
      Tendsto (fun n => homeomorphMap (F (φ n)).symm) atTop (𝓝 (homeomorphMap H.symm)) := by
  have hr : UniformRelativeControl (fun n z => F n z) := by
    intro ε hε
    obtain ⟨η,hη,h⟩ := smooth_qc_uniform_shrink hK ε hε
    exact ⟨η,hη,fun n => h (F n) (hF' n) (hD' n)⟩
  have hr' : UniformRelativeControl (fun n z => (F n).symm z) := by
    intro ε hε
    obtain ⟨η,hη,h⟩ := smooth_qc_uniform_shrink hK ε hε
    exact ⟨η,hη,fun n => h (F n).symm (hF n) (hD n)⟩
  have h0' (n) : (F n).symm 0=0 := by apply (F n).injective; simpa using (hF0 n).symm
  have h1' (n) : (F n).symm 1=1 := by apply (F n).injective; simpa using (hF1 n).symm
  have hb := normalized_family_pointwise_bound _ hF0 hF1 hr
  have hb' := normalized_family_pointwise_bound _ h0' h1' hr'
  obtain ⟨H,φ,hφ,ht,ht'⟩ := pointwise_bounded_homeomorph_subsequence F
    (relative_control_equicontinuous _ hr hb) (relative_control_equicontinuous _ hr' hb') hb hb'
  refine ⟨H,φ,hφ,?_,?_,ht,ht'⟩
  · have h := (continuous_eval_const (0:ℂ)).tendsto (homeomorphMap H) |>.comp ht
    have hh : Tendsto (fun _ : ℕ => (0:ℂ)) atTop (𝓝 (H 0)) := by
      simpa only [Function.comp_def,homeomorphMap,ContinuousMap.coe_mk,hF0] using h
    exact tendsto_nhds_unique hh tendsto_const_nhds
  · have h := (continuous_eval_const (1:ℂ)).tendsto (homeomorphMap H) |>.comp ht
    have hh : Tendsto (fun _ : ℕ => (1:ℂ)) atTop (𝓝 (H 1)) := by
      simpa only [Function.comp_def,homeomorphMap,ContinuousMap.coe_mk,hF1] using h
    exact tendsto_nhds_unique hh tendsto_const_nhds
end CannonPlane

end
end
end
end
end
end
end
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
