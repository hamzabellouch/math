import Mathlib
import OAI.Geometry.BallPacking.Necessity.FramedCompactness

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff

open scoped ContDiff Topology
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity.FramedCR
open HigherDimensionalBallPacking.Rigidity
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
theorem frame_rescale_inverse [FiniteDimensional ℂ E] [CompleteSpace E]
    (S : E ≃L[ℝ] E)
    (p : E) (u : ℂ → E) (c : ℂ) {r : ℝ} (hr : r ≠ 0)
    (h : ContDiffAt ℝ 1 (centeredFrame S p (rescaleMap u c r)) 0) :
    ContDiffAt ℝ 1 u c ∧ fderiv ℝ u c=r⁻¹ • S.symm.toContinuousLinearMap.comp
      (fderiv ℝ (centeredFrame S p (rescaleMap u c r)) 0) := by
  let U := centeredFrame S p (rescaleMap u c r)
  let a : ℂ → ℂ := fun z => r⁻¹ • (z-c)
  have ha0 : a c=0 := by simp [a]
  have ha : ContDiff ℝ ∞ a := (contDiff_id.sub contDiff_const).const_smul r⁻¹
  have hid : (fun z => S.symm (U (a z))+p)=u := by
    funext z
    simp only [U,centeredFrame,rescaleMap,a,smul_smul,mul_inv_cancel₀ hr,one_smul,
      add_sub_cancel,ContinuousLinearEquiv.symm_apply_apply,sub_add_cancel]
  have hh : ContDiffAt ℝ 1 U (a c) := by simpa only [ha0] using h
  have huc : ContDiffAt ℝ 1 u c := by
    rw [←hid]
    exact (S.symm.contDiff.contDiffAt.comp c (hh.comp c (ha.of_le (by simp)).contDiffAt)).add contDiffAt_const
  refine ⟨huc,?_⟩
  have had : HasFDerivAt a (r⁻¹ • ContinuousLinearMap.id ℝ ℂ) c := by
    convert (((hasFDerivAt_id (𝕜 := ℝ) c).sub_const c).const_smul r⁻¹) using 1
    rfl
  have hud := ((S.symm.hasFDerivAt.comp c
    ((hh.differentiableAt (by simp)).hasFDerivAt.comp c had)).add_const p).fderiv
  simp only [Function.comp_def] at hud
  rw [hid] at hud
  rw [ha0] at hud
  simpa only [ContinuousLinearMap.comp_smul,ContinuousLinearMap.comp_id] using hud

theorem field_C0_C1At (H : ℝ × E → E →L[ℝ] E)
    (hH : ∀ y : ℝ × E, y.1 ∈ Icc (0:ℝ) 1 → ContDiffAt ℝ ∞ H y)
    (hHF : ∀ y : ℝ × E, y.1 ∈ Icc (0:ℝ) 1 → HasFrame (H y))
    (t : ℕ → ℝ) (ht : ∀ j, t j ∈ Icc (0:ℝ) 1) {s : ℝ}
    (hts : Tendsto t atTop (𝓝 s))
    (u : ℕ → ℂ → E) (hu : ∀ j, ContDiff ℝ ∞ (u j))
    (hCR : ∀ j z, fderiv ℝ (u j) z Complex.I=H (t j,u j z) (fderiv ℝ (u j) z 1))
    (v : ℂ → E) (hv : TendstoLocallyUniformly u v atTop) (c : ℂ) :
    ContDiffAt ℝ 1 v c ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun j => fderiv ℝ (u (φ j)) c) atTop (𝓝 (fderiv ℝ v c)) := by
  have hs : s ∈ Icc (0:ℝ) 1 := isClosed_Icc.mem_of_tendsto hts (Eventually.of_forall ht)
  have hvc : Continuous v := hv.continuous (Eventually.of_forall (fun j => (hu j).continuous)).frequently
  obtain ⟨L,hL,hLu⟩ := field_C0_gradient_bound H hH hHF t ht hts u hu hCR v hv c
    (by norm_num : (0:ℝ) ≤ 1)
  have hBounded : Bornology.IsBounded
      ((fderiv ℝ H) '' (Icc (0:ℝ) 1 ×ˢ Metric.closedBall (v c) 1)) :=
    ((isCompact_Icc.prod (isCompact_closedBall (v c) 1)).image_of_continuousOn
      (fun y hy => ((hH y hy.1).continuousAt_fderiv (by simp)).continuousWithinAt)).isBounded
  obtain ⟨K,hK,hKb⟩ := hBounded.exists_pos_norm_le
  obtain ⟨S,hS⟩ := hHF (s,v c) hs
  let LS := ‖S.toContinuousLinearMap‖*L
  let KS := ‖frameConjugation S‖*(K*L)
  obtain ⟨δ,hδ,hth⟩ := smallCR_C1_closure_threshold (E := E) LS KS
    (mul_nonneg (norm_nonneg S.toContinuousLinearMap) hL)
    (mul_nonneg (norm_nonneg (frameConjugation S)) (mul_nonneg hK.le hL))
  obtain ⟨ru,hru,hru1,hruv⟩ := locally_uniform_small_ball (c := c) hv hvc.continuousAt hts
    (G := fun y : ℝ × E => S (y.2-v c))
    (S.continuous.continuousAt.comp (continuousAt_snd.sub continuousAt_const))
    (by simp) (by norm_num : (0:ℝ)<1)
  obtain ⟨ra,hra,hra1,hraA⟩ := locally_uniform_small_ball (c := c) hv hvc.continuousAt hts
    (G := fun y : ℝ × E => frameConjugation S (H y-H (s,v c)))
    ((frameConjugation S).continuous.continuousAt.comp
      ((hH (s,v c) hs).continuousAt.sub continuousAt_const)) (by simp) hδ
  obtain ⟨rp,hrp,hrp1,hrpv⟩ := locally_uniform_small_ball (c := c) hv hvc.continuousAt hts
    (G := fun y : ℝ × E => y.2-v c)
    (continuousAt_snd.sub continuousAt_const) (by simp) (by norm_num : (0:ℝ)<1)
  let r := min ru (min ra rp)/3
  have hr : 0 < r := div_pos (lt_min hru (lt_min hra hrp)) (by norm_num)
  have hr3u : 3*r ≤ ru := by dsimp [r]; linarith [min_le_left ru (min ra rp)]
  have hr3a : 3*r ≤ ra := by dsimp [r]; linarith [min_le_right ru (min ra rp),min_le_left ra rp]
  have hr3p : 3*r ≤ rp := by dsimp [r]; linarith [min_le_right ru (min ra rp),min_le_right ra rp]
  have hr1 : r ≤ 1 := by linarith
  let w : ℕ → ℂ → E := fun j => rescaleMap (u j) c r
  let U : ℕ → ℂ → E := fun j => centeredFrame S (v c) (w j)
  let B : ℕ → ℂ → (E →L[ℝ] E) := fun j z => H (t j,w j z)
  let A : ℕ → ℂ → (E →L[ℝ] E) := fun j => frozenCoefficient S (H (s,v c)) (B j)
  let V := centeredFrame S (v c) (rescaleMap v c r)
  have hw (j : ℕ) : ContDiff ℝ ∞ (w j) := rescaleMap_smooth (hu j) c r
  have hU (j : ℕ) : ContDiff ℝ ∞ (U j) := centeredFrame_smooth S (v c) (hw j)
  have hB (j : ℕ) : ContDiff ℝ ∞ (B j) := by
    rw [contDiff_iff_contDiffAt]
    intro z
    exact ContDiffAt.comp (g := H) (f := fun z => (t j,w j z)) z
      (hH (t j,w j z) (ht j)) (contDiffAt_const.prodMk (hw j).contDiffAt)
  have hA (j : ℕ) : ContDiff ℝ ∞ (A j) := frozenCoefficient_smooth S _ (hB j)
  have hmap (z : ℂ) (hz : z ∈ Metric.closedBall (0:ℂ) 3) : dist (c+r • z) c ≤ 3*r := by
    rw [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    nlinarith [show ‖z‖ ≤ 3 by simpa using hz]
  have hb : ∀ᶠ j in atTop, ∀ z ∈ Metric.closedBall (0:ℂ) 3,
      ‖U j z‖ ≤ 1 ∧ ‖fderiv ℝ (U j) z‖ ≤ LS ∧ ‖A j z‖ ≤ δ ∧
      ‖fderiv ℝ (A j) z‖ ≤ KS ∧
      fderiv ℝ (U j) z Complex.I-Complex.I • fderiv ℝ (U j) z 1=
        A j z (fderiv ℝ (U j) z 1) := by
    filter_upwards [hLu,hruv,hraA,hrpv] with j hjD hju hjA hjp
    intro z hz
    have hmem : c+r • z ∈ Metric.closedBall c 1 := (hmap z hz).trans (hr3u.trans hru1)
    have hwD : ‖fderiv ℝ (w j) z‖ ≤ L := by
      rw [show ‖fderiv ℝ (w j) z‖=|r| * ‖fderiv ℝ (u j) (c+r • z)‖ from
        rescaleMap_norm_fderiv ((hu j).differentiable (by simp)) c r z,abs_of_pos hr]
      exact (mul_le_mul_of_nonneg_left (hjD _ hmem) hr.le).trans
        (by simpa using mul_le_mul_of_nonneg_right hr1 hL)
    have hp : w j z ∈ Metric.closedBall (v c) 1 := by
      simpa only [Metric.mem_closedBall,dist_eq_norm,w,rescaleMap] using
        (hjp (c+r • z) ((hmap z hz).trans hr3p))
    have hBD : ‖fderiv ℝ (B j) z‖ ≤ K*L := by
      have hd : HasFDerivAt (fun z => (t j,w j z))
          ((0 : ℂ →L[ℝ] ℝ).prod (fderiv ℝ (w j) z)) z :=
        (hasFDerivAt_const (t j) z).prodMk ((hw j).differentiable (by simp) z).hasFDerivAt
      have he : fderiv ℝ (B j) z=(fderiv ℝ H (t j,w j z)).comp
          ((0 : ℂ →L[ℝ] ℝ).prod (fderiv ℝ (w j) z)) :=
        (HasFDerivAt.comp (g := H) (f := fun z => (t j,w j z)) z
          ((hH (t j,w j z) (ht j)).differentiableAt (by simp)).hasFDerivAt hd).fderiv
      rw [he]
      apply ((fderiv ℝ H (t j,w j z)).opNorm_comp_le _).trans
      have hnorm : ‖(0 : ℂ →L[ℝ] ℝ).prod (fderiv ℝ (w j) z)‖=‖fderiv ℝ (w j) z‖ := by
        rw [ContinuousLinearMap.opNorm_prod,Prod.norm_def,norm_zero,max_eq_right (norm_nonneg _)]
      rw [hnorm]
      exact mul_le_mul (hKb _ ⟨(t j,w j z),⟨ht j,hp⟩,rfl⟩) hwD (norm_nonneg _) hK.le
    refine ⟨hju _ ((hmap z hz).trans hr3u),?_,hjA _ ((hmap z hz).trans hr3a),?_,?_⟩
    · rw [show fderiv ℝ (U j) z=S.toContinuousLinearMap.comp (fderiv ℝ (w j) z) from
        centeredFrame_fderiv S (v c) ((hw j).differentiable (by simp)) z]
      exact (S.toContinuousLinearMap.opNorm_comp_le _).trans
        (mul_le_mul_of_nonneg_left hwD (norm_nonneg _))
    · rw [show fderiv ℝ (A j) z=(frameConjugation S).comp (fderiv ℝ (B j) z) from
        frozenCoefficient_fderiv S _ ((hB j).differentiable (by simp)) z]
      exact ((frameConjugation S).opNorm_comp_le _).trans
        (mul_le_mul_of_nonneg_left hBD (norm_nonneg _))
    · exact frozen_CR_equation S _ hS (v c) ((hw j).differentiable (by simp)) (B j)
        (rescaleMap_CR_I (J := fun x => H (t j,x)) ((hu j).differentiable (by simp)) (hCR j) c r z)
  have hUV : TendstoLocallyUniformly U V atTop := by
    have hf : UniformContinuous (fun x : E => S (x-v c)) :=
      S.toContinuousLinearMap.uniformContinuous.comp (uniformContinuous_id.sub uniformContinuous_const)
    exact hf.comp_tendstoLocallyUniformly
      (hv.comp (fun z : ℂ => c+r • z) (continuous_const.add (continuous_id.const_smul r)))
  obtain ⟨hV,φ,hφ,hφD⟩ := hth U A V hU hA hUV hb
  obtain ⟨hcv,hdv⟩ := frame_rescale_inverse S (v c) v c hr.ne' hV
  refine ⟨hcv,φ,hφ,?_⟩
  have hcont : Continuous (fun T : ℂ →L[ℝ] E => r⁻¹ • S.symm.toContinuousLinearMap.comp T) :=
    (continuous_const.clm_comp continuous_id).const_smul r⁻¹
  have hlim := hcont.continuousAt.tendsto.comp hφD
  convert hlim using 1
  · funext j
    exact (frame_rescale_inverse S (v c) (u (φ j)) c hr.ne' ((hU (φ j)).of_le (by simp)).contDiffAt).2
  · exact congrArg nhds hdv

end HigherDimensionalBallPacking.Rigidity.FramedCR

 

 

 

open scoped ContDiff Topology
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity.FramedCR
open HigherDimensionalBallPacking.Rigidity
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
theorem fderiv_translate [FiniteDimensional ℂ E] [CompleteSpace E]
    (f : ℂ → E) (hf : Differentiable ℝ f) (x z : ℂ) :
    fderiv ℝ (fun w => f (x+w)) z=fderiv ℝ f (x+z) := by
  have hh := ((hf (x+z)).hasFDerivAt.comp z
    ((hasFDerivAt_id (𝕜 := ℝ) z).const_add x)).fderiv
  simpa only [Function.comp_def,ContinuousLinearMap.comp_id] using hh

omit [NormedSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E] in
theorem locally_uniform_translate [NormedSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E]
    {u : ℕ → ℂ → E} {v : ℂ → E}
    (hu : ∀ j, Continuous (u j)) (hv : Continuous v)
    (h : TendstoLocallyUniformly u v atTop) {x : ℕ → ℂ} {c : ℂ}
    (hx : Tendsto x atTop (𝓝 c)) :
    TendstoLocallyUniformly (fun j z => u j (x j+z)) (fun z => v (c+z)) atTop := by
  let U : ℕ → C(ℂ,E) := fun j => ⟨u j,hu j⟩
  let V : C(ℂ,E) := ⟨v,hv⟩
  have hU : Tendsto U atTop (𝓝 V) := ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mpr h
  have hc : Tendsto (fun j => ContinuousMap.const ℂ (x j)) atTop
      (𝓝 (ContinuousMap.const ℂ c)) := ContinuousMap.continuous_const'.continuousAt.tendsto.comp hx
  have ha := hc.add (tendsto_const_nhds (x := ContinuousMap.id ℂ))
  exact ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp (hU.compCM ha)

theorem field_C0_C1_closure (H : ℝ × E → E →L[ℝ] E)
    (hH : ∀ y : ℝ × E, y.1 ∈ Icc (0:ℝ) 1 → ContDiffAt ℝ ∞ H y)
    (hHF : ∀ y : ℝ × E, y.1 ∈ Icc (0:ℝ) 1 → HasFrame (H y))
    (t : ℕ → ℝ) (ht : ∀ j, t j ∈ Icc (0:ℝ) 1) {s : ℝ}
    (hts : Tendsto t atTop (𝓝 s))
    (u : ℕ → ℂ → E) (hu : ∀ j, ContDiff ℝ ∞ (u j))
    (hCR : ∀ j z, fderiv ℝ (u j) z Complex.I=H (t j,u j z) (fderiv ℝ (u j) z 1))
    (v : ℂ → E) (hv : TendstoLocallyUniformly u v atTop) :
    ContDiff ℝ 1 v ∧ TendstoLocallyUniformly (fun j => fderiv ℝ (u j)) (fderiv ℝ v) atTop := by
  have hv1 : ContDiff ℝ 1 v := contDiff_iff_contDiffAt.mpr
    (fun c => (field_C0_C1At H hH hHF t ht hts u hu hCR v hv c).1)
  refine ⟨hv1,?_⟩
  apply tendstoLocallyUniformly_iff_forall_isCompact.mpr
  intro K hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  by_contra hn
  have hfreq : ∃ᶠ j in atTop, ∃ x ∈ K,
      ε ≤ dist (fderiv ℝ v x) (fderiv ℝ (u j) x) := by
    simpa only [Filter.Frequently,not_exists,not_and,not_le] using hn
  obtain ⟨a,hat,ha⟩ := exists_seq_forall_of_frequently hfreq
  choose x hx hbad using ha
  obtain ⟨c,hc,φ,hφ,hφx⟩ := hK.tendsto_subseq hx
  let b : ℕ → ℕ := fun j => a (φ j)
  have hbt : Tendsto b atTop atTop := hat.comp hφ.tendsto_atTop
  let U : ℕ → ℂ → E := fun j z => u (b j) (x (φ j)+z)
  let V : ℂ → E := fun z => v (c+z)
  have hUs (j : ℕ) : ContDiff ℝ ∞ (U j) := (hu (b j)).comp (contDiff_const.add contDiff_id)
  have hUD (j : ℕ) (z : ℂ) : fderiv ℝ (U j) z=fderiv ℝ (u (b j)) (x (φ j)+z) :=
    fderiv_translate _ ((hu (b j)).differentiable (by simp)) _ _
  have hVD (z : ℂ) : fderiv ℝ V z=fderiv ℝ v (c+z) :=
    fderiv_translate _ (hv1.differentiable (by simp)) _ _
  have hUCR (j : ℕ) (z : ℂ) : fderiv ℝ (U j) z Complex.I=
      H (t (b j),U j z) (fderiv ℝ (U j) z 1) := by
    rw [hUD]
    exact hCR (b j) _
  have hlim : TendstoLocallyUniformly U V atTop :=
    locally_uniform_translate (fun j => (hu (b j)).continuous) hv1.continuous
      (locally_uniform_reindex hv hbt) hφx
  obtain ⟨_,ψ,hψ,hψD⟩ := field_C0_C1At H hH hHF (fun j => t (b j))
    (fun j => ht (b j)) (hts.comp hbt) U hUs hUCR V hlim 0
  have hlimD : Tendsto (fun j => fderiv ℝ (u (b (ψ j))) (x (φ (ψ j))))
      atTop (𝓝 (fderiv ℝ v c)) := by
    simpa only [hUD,hVD,add_zero] using hψD
  have hvD := ((hv1.continuous_fderiv (by simp)).continuousAt.tendsto.comp
    (hφx.comp hψ.tendsto_atTop))
  have hdist : Tendsto (fun j => dist (fderiv ℝ v (x (φ (ψ j))))
      (fderiv ℝ (u (b (ψ j))) (x (φ (ψ j))))) atTop (𝓝 0) := by
    convert hvD.dist hlimD using 1 <;> simp only [Function.comp_def,dist_self]
  obtain ⟨j,hj⟩ := (hdist.eventually (gt_mem_nhds hε)).exists
  exact (not_lt_of_ge (hbad (φ (ψ j)))) hj

end HigherDimensionalBallPacking.Rigidity.FramedCR

 

 

 

open scoped ContDiff Topology
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity.FramedCR
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

def tangentMap (J K : E →L[ℝ] E) : (E × E) →L[ℝ] (E × E) :=
  (J.comp (ContinuousLinearMap.fst ℝ E E)).prod
    (K.comp (ContinuousLinearMap.fst ℝ E E)+J.comp (ContinuousLinearMap.snd ℝ E E))

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
@[simp] theorem tangentMap_apply [FiniteDimensional ℂ E] [CompleteSpace E]
    (J K : E →L[ℝ] E) (a b : E) :
    tangentMap J K (a,b)=(J a,K a+J b) := rfl

def shearEquiv (C : E →L[ℝ] E) : (E × E) ≃L[ℝ] (E × E) where
  toFun v := (v.1,v.2+C v.1)
  invFun v := (v.1,v.2-C v.1)
  left_inv := by intro v; simp
  right_inv := by intro v; simp
  map_add' := by intro v w; simp only [Prod.fst_add,Prod.snd_add,map_add,Prod.mk_add_mk];congr 1;abel
  map_smul' := by intro r v; simp only [Prod.smul_fst,Prod.smul_snd,map_smul,smul_add,Prod.smul_mk,RingHom.id_apply]
  continuous_toFun := continuous_fst.prodMk (continuous_snd.add (C.continuous.comp continuous_fst))
  continuous_invFun := continuous_fst.prodMk (continuous_snd.sub (C.continuous.comp continuous_fst))

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
theorem HasFrame.square [FiniteDimensional ℂ E] [CompleteSpace E]
    {J : E →L[ℝ] E} (hJ : HasFrame J) (v : E) : J (J v)=-v := by
  obtain ⟨S,hS⟩ := hJ
  apply S.injective
  simp only [hS,smul_smul,Complex.I_mul_I,neg_one_smul,map_neg]

theorem tangentMap_hasFrame {J K : E →L[ℝ] E} (hJ : HasFrame J)
    (hK : ∀ v, K (J v)+J (K v)=0) : HasFrame (tangentMap J K) := by
  obtain ⟨S,hS⟩ := hJ
  have hJJ : ∀ v, J (J v)=-v := HasFrame.square ⟨S,hS⟩
  let C : E →L[ℝ] E := -(1/2:ℝ) • J.comp K
  have hCJ (a : E) : C (J a)=-(1/2:ℝ) • K a := by
    have hKJ : K (J a)=-J (K a) := eq_neg_of_add_eq_zero_left (hK a)
    simp only [C,smul_apply,ContinuousLinearMap.comp_apply,hKJ,map_neg,hJJ,neg_neg]
  have hJC (a : E) : J (C a)=(1/2:ℝ) • K a := by
    simp only [C,smul_apply,neg_apply,ContinuousLinearMap.comp_apply,map_neg,map_smul,hJJ,smul_neg,neg_smul,neg_neg]
  refine ⟨(shearEquiv C).trans (S.prodCongr S),?_⟩
  rintro ⟨a,b⟩
  change (S (J a),S (K a+J b+C (J a)))=(Complex.I • S a,Complex.I • S (b+C a))
  rw [hS a,←hS (b+C a),map_add J,hCJ a,hJC a]
  congr 2
  module

end HigherDimensionalBallPacking.Rigidity.FramedCR

 

 

open scoped ContDiff Topology
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity.FramedCR
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

def tangentField (H : ℝ × E → E →L[ℝ] E) : ℝ × (E × E) → (E × E) →L[ℝ] (E × E) :=
  fun y => tangentMap (H (y.1,y.2.1)) (fderiv ℝ H (y.1,y.2.1) (0,y.2.2))

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
theorem tangentField_smooth [FiniteDimensional ℂ E] [CompleteSpace E]
    (H : ℝ × E → E →L[ℝ] E)
    (hH : ∀ y : ℝ × E, y.1 ∈ Icc (0:ℝ) 1 → ContDiffAt ℝ ∞ H y)
    (y : ℝ × (E × E)) (hy : y.1 ∈ Icc (0:ℝ) 1) : ContDiffAt ℝ ∞ (tangentField H) y := by
  have hbase : ContDiffAt ℝ ∞ (fun y : ℝ × (E × E) => (y.1,y.2.1)) y :=
    contDiffAt_fst.prodMk (contDiffAt_fst.comp y contDiffAt_snd)
  have hvec : ContDiffAt ℝ ∞ (fun y : ℝ × (E × E) => ((0:ℝ),y.2.2)) y :=
    contDiffAt_const.prodMk (contDiffAt_snd.comp y contDiffAt_snd)
  have hJ := (hH (y.1,y.2.1) hy).comp y hbase
  have hK := (((hH (y.1,y.2.1) hy).fderiv_right (by simp)).comp y hbase).clm_apply hvec
  exact (ContinuousLinearMap.prodₗᵢ (𝕜 := ℝ) (E := E × E) (F := E) (G := E) ℝ).toContinuousLinearEquiv.contDiff.contDiffAt.comp y
    ((hJ.clm_comp contDiffAt_const).prodMk
      ((hK.clm_comp contDiffAt_const).add (hJ.clm_comp contDiffAt_const)))

theorem field_derivative_anticommute (H : ℝ × E → E →L[ℝ] E)
    (hH : ∀ y : ℝ × E, y.1 ∈ Icc (0:ℝ) 1 → ContDiffAt ℝ ∞ H y)
    (hHF : ∀ y : ℝ × E, y.1 ∈ Icc (0:ℝ) 1 → HasFrame (H y))
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (x Y a : E) :
    fderiv ℝ H (t,x) (0,Y) (H (t,x) a)+H (t,x) (fderiv ℝ H (t,x) (0,Y) a)=0 := by
  let B : E → E →L[ℝ] E := fun x => H (t,x)
  let D : E →L[ℝ] (E →L[ℝ] E) := (fderiv ℝ H (t,x)).comp
    ((0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E))
  have hB : HasFDerivAt B D x :=
    ((hH (t,x) ht).differentiableAt (by simp)).hasFDerivAt.comp x
      ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id (𝕜 := ℝ) x))
  have hBB := (hB.clm_apply (hB.clm_apply (hasFDerivAt_const a x))).fderiv
  have he : (fun z => B z (B z a))=fun _ : E => -a := by
    funext z
    exact (hHF (t,z) ht).square a
  rw [he,fderiv_const_apply] at hBB
  have hh := congrArg (fun T : E →L[ℝ] E => T Y) hBB
  simpa [B,D,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,add_comm] using hh.symm

theorem tangentField_hasFrame (H : ℝ × E → E →L[ℝ] E)
    (hH : ∀ y : ℝ × E, y.1 ∈ Icc (0:ℝ) 1 → ContDiffAt ℝ ∞ H y)
    (hHF : ∀ y : ℝ × E, y.1 ∈ Icc (0:ℝ) 1 → HasFrame (H y))
    (y : ℝ × (E × E)) (hy : y.1 ∈ Icc (0:ℝ) 1) : HasFrame (tangentField H y) :=
  tangentMap_hasFrame (hHF (y.1,y.2.1) hy)
    (field_derivative_anticommute H hH hHF hy y.2.1 y.2.2)

end HigherDimensionalBallPacking.Rigidity.FramedCR

 

 

open scoped ContDiff Topology
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity.FramedCR
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

def tangentCurve (u : ℂ → E) : ℂ → E × E := fun z => (u z,fderiv ℝ u z 1)

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
theorem tangentCurve_smooth [FiniteDimensional ℂ E] [CompleteSpace E]
    {u : ℂ → E} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (tangentCurve u) := hu.prodMk ((hu.fderiv_right (by simp)).clm_apply contDiff_const)

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
theorem fderiv_directional [FiniteDimensional ℂ E] [CompleteSpace E]
    {u : ℂ → E} (hu : ContDiff ℝ ∞ u) (z a b : ℂ) :
    fderiv ℝ (fun w => fderiv ℝ u w a) z b=fderiv ℝ (fderiv ℝ u) z b a := by
  rw [fderiv_clm_apply ((hu.fderiv_right (by simp : (∞:WithTop ℕ∞)+1 ≤ ∞)).differentiable (by simp) z)
    (differentiableAt_const a)]
  simp

theorem tangentCurve_fderiv {u : ℂ → E} (hu : ContDiff ℝ ∞ u) (z a : ℂ) :
    fderiv ℝ (tangentCurve u) z a=(fderiv ℝ u z a,fderiv ℝ (fderiv ℝ u) z a 1) := by
  have hDu : Differentiable ℝ (fun w => fderiv ℝ u w 1) :=
    ((hu.fderiv_right (by simp : (∞:WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const).differentiable (by simp)
  have hh := (((hu.differentiable (by simp)) z).hasFDerivAt.prodMk (hDu z).hasFDerivAt).fderiv
  change fderiv ℝ (fun z => (u z,fderiv ℝ u z 1)) z a=_
  rw [hh]
  simp only [ContinuousLinearMap.prod_apply,fderiv_directional hu]

theorem tangentCurve_CR (H : ℝ × E → E →L[ℝ] E)
    (hH : ∀ y : ℝ × E, y.1 ∈ Icc (0:ℝ) 1 → ContDiffAt ℝ ∞ H y)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) {u : ℂ → E} (hu : ContDiff ℝ ∞ u)
    (hCR : ∀ z, fderiv ℝ u z Complex.I=H (t,u z) (fderiv ℝ u z 1)) :
    ∀ z, fderiv ℝ (tangentCurve u) z Complex.I=
      tangentField H (t,tangentCurve u z) (fderiv ℝ (tangentCurve u) z 1) := by
  intro z
  let B : ℂ → E →L[ℝ] E := fun w => H (t,u w)
  let DB : ℂ →L[ℝ] (E →L[ℝ] E) := (fderiv ℝ H (t,u z)).comp
    ((0 : ℂ →L[ℝ] ℝ).prod (fderiv ℝ u z))
  have hB : HasFDerivAt B DB z :=
    ((hH (t,u z) ht).differentiableAt (by simp)).hasFDerivAt.comp z
      ((hasFDerivAt_const t z).prodMk ((hu.differentiable (by simp)) z).hasFDerivAt)
  have hDu : Differentiable ℝ (fun w => fderiv ℝ u w 1) :=
    ((hu.fderiv_right (by simp : (∞:WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const).differentiable (by simp)
  have hR := (hB.clm_apply (hDu z).hasFDerivAt).fderiv
  have he : (fun w => fderiv ℝ u w Complex.I)=(fun w => B w (fderiv ℝ u w 1)) := funext hCR
  have hd := congrArg (fun f : ℂ → E => fderiv ℝ f z 1) he
  rw [fderiv_directional hu,hR] at hd
  have hs := (hu.contDiffAt (x := z)).isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  rw [tangentCurve_fderiv hu,tangentCurve_fderiv hu]
  change (fderiv ℝ u z Complex.I,fderiv ℝ (fderiv ℝ u) z Complex.I 1)=
    (H (t,u z) (fderiv ℝ u z 1),
      fderiv ℝ H (t,u z) (0,fderiv ℝ u z 1) (fderiv ℝ u z 1)+
        H (t,u z) (fderiv ℝ (fderiv ℝ u) z 1 1))
  rw [hCR z,hs Complex.I 1]
  congr 1
  simpa [B,DB,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
    fderiv_directional hu,add_comm] using hd

end HigherDimensionalBallPacking.Rigidity.FramedCR

 

 

open scoped ContDiff Topology
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity.FramedCR
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
theorem field_C1_CR_limit [FiniteDimensional ℂ E] [CompleteSpace E]
    (H : ℝ × E → E →L[ℝ] E)
    (hH : ∀ y : ℝ × E, y.1 ∈ Icc (0:ℝ) 1 → ContDiffAt ℝ ∞ H y)
    (t : ℕ → ℝ) (ht : ∀ j, t j ∈ Icc (0:ℝ) 1) {s : ℝ}
    (hts : Tendsto t atTop (𝓝 s))
    (u : ℕ → ℂ → E)
    (hCR : ∀ j z, fderiv ℝ (u j) z Complex.I=H (t j,u j z) (fderiv ℝ (u j) z 1))
    (v : ℂ → E) (hv : TendstoLocallyUniformly u v atTop)
    (hDv : TendstoLocallyUniformly (fun j => fderiv ℝ (u j)) (fderiv ℝ v) atTop) :
    ∀ z, fderiv ℝ v z Complex.I=H (s,v z) (fderiv ℝ v z 1) := by
  intro z
  have hs : s ∈ Icc (0:ℝ) 1 := isClosed_Icc.mem_of_tendsto hts (Eventually.of_forall ht)
  have hvz := hv.tendstoLocallyUniformlyOn.tendsto_at (mem_univ z)
  have hDz := hDv.tendstoLocallyUniformlyOn.tendsto_at (mem_univ z)
  have hp : Tendsto (fun j => (t j,u j z)) atTop (𝓝 (s,v z)) := hts.prodMk_nhds hvz
  have hJ : Tendsto (fun j => H (t j,u j z)) atTop (𝓝 (H (s,v z))) :=
    (hH (s,v z) hs).continuousAt.tendsto.comp hp
  have happ (a : ℂ) : Continuous (fun T : ℂ →L[ℝ] E => T a) :=
    continuous_id.clm_apply continuous_const
  have hleft : Tendsto (fun j => fderiv ℝ (u j) z Complex.I) atTop
      (𝓝 (fderiv ℝ v z Complex.I)) := (happ Complex.I).continuousAt.tendsto.comp hDz
  have heval : Continuous (fun p : (E →L[ℝ] E) × E => p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  have hright : Tendsto (fun j => H (t j,u j z) (fderiv ℝ (u j) z 1)) atTop
      (𝓝 (H (s,v z) (fderiv ℝ v z 1))) := by
    have hp' : Tendsto (fun j => (H (t j,u j z),fderiv ℝ (u j) z 1)) atTop
        (𝓝 (H (s,v z),fderiv ℝ v z 1)) :=
      hJ.prodMk_nhds ((happ 1).continuousAt.tendsto.comp hDz)
    convert (heval.tendsto (H (s,v z),fderiv ℝ v z 1)).comp hp' using 1
    rfl
  exact tendsto_nhds_unique hleft (hright.congr (fun j => (hCR j z).symm))

end HigherDimensionalBallPacking.Rigidity.FramedCR

 

 

 

open scoped ContDiff Topology
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity.FramedCR

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
theorem realLinear_complex_apply [FiniteDimensional ℂ E] [CompleteSpace E]
    (D : ℂ →L[ℝ] E) (z : ℂ) :
    D z=z.re • D 1+z.im • D Complex.I := by
  have hz : z=z.re • (1:ℂ)+z.im • Complex.I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [hz]
  simp only [map_add,map_smul]

theorem CR_contDiff_succ {m : ℕ} (H : E → E →L[ℝ] E) (hH : ContDiff ℝ ∞ H)
    (v : ℂ → E) (hv1 : ContDiff ℝ 1 v) (hvm : ContDiff ℝ m v)
    (hDx : ContDiff ℝ m (fun z => fderiv ℝ v z 1))
    (hCR : ∀ z, fderiv ℝ v z Complex.I=H (v z) (fderiv ℝ v z 1)) :
    ContDiff ℝ (m+1 : ℕ) v := by
  rw [Nat.cast_add,Nat.cast_one,contDiff_succ_iff_fderiv]
  refine ⟨hv1.differentiable (by simp),by simp,?_⟩
  apply contDiff_clm_apply_iff.mpr
  intro a
  have he : (fun z => fderiv ℝ v z a)=fun z =>
      a.re • fderiv ℝ v z 1+a.im • H (v z) (fderiv ℝ v z 1) := by
    funext z
    rw [realLinear_complex_apply,hCR]
  rw [he]
  have hHm : ContDiff ℝ m H := hH.of_le (by
    change ((m : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  exact (hDx.const_smul a.re).add (((hHm.comp hvm).clm_apply hDx).const_smul a.im)

end HigherDimensionalBallPacking.Rigidity.FramedCR

namespace HigherDimensionalBallPacking.Rigidity.FramedCR

theorem field_C0_contDiff_nat (m : ℕ) :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
      [FiniteDimensional ℂ E] [CompleteSpace E]
      (H : ℝ × E → E →L[ℝ] E)
      (_hH : ∀ y : ℝ × E, y.1 ∈ Icc (0:ℝ) 1 → ContDiffAt ℝ ∞ H y)
      (_hHF : ∀ y : ℝ × E, y.1 ∈ Icc (0:ℝ) 1 → HasFrame (H y))
      (t : ℕ → ℝ) (_ht : ∀ j, t j ∈ Icc (0:ℝ) 1) {s : ℝ}
      (_hts : Tendsto t atTop (𝓝 s))
      (u : ℕ → ℂ → E) (_hu : ∀ j, ContDiff ℝ ∞ (u j))
      (_hCR : ∀ j z, fderiv ℝ (u j) z Complex.I=H (t j,u j z) (fderiv ℝ (u j) z 1))
      (v : ℂ → E) (_hv : TendstoLocallyUniformly u v atTop), ContDiff ℝ m v := by
  induction m with
  | zero =>
    intro E _ _ _ _ H hH hHF t ht s hts u hu hCR v hv
    exact contDiff_zero.mpr
      (hv.continuous (Eventually.of_forall (fun j => (hu j).continuous)).frequently)
  | succ m ih =>
    intro E _ _ _ _ H hH hHF t ht s hts u hu hCR v hv
    have hs : s ∈ Icc (0:ℝ) 1 := isClosed_Icc.mem_of_tendsto hts (Eventually.of_forall ht)
    obtain ⟨hv1,hDv⟩ := field_C0_C1_closure H hH hHF t ht hts u hu hCR v hv
    have hCRv := field_C1_CR_limit H hH t ht hts u hCR v hv hDv
    have happ : UniformContinuous (fun D : ℂ →L[ℝ] E => D 1) :=
      (ContinuousLinearMap.apply ℝ E (1:ℂ)).uniformContinuous
    have hlim : TendstoLocallyUniformly (fun j => tangentCurve (u j)) (tangentCurve v) atTop :=
      hv.prodMk (happ.comp_tendstoLocallyUniformly hDv)
    have hW := ih (E × E) (tangentField H) (tangentField_smooth H hH)
      (tangentField_hasFrame H hH hHF) t ht hts (fun j => tangentCurve (u j))
      (fun j => tangentCurve_smooth (hu j)) (fun j => tangentCurve_CR H hH (ht j) (hu j) (hCR j))
      (tangentCurve v) hlim
    have hHs : ContDiff ℝ ∞ (fun x : E => H (s,x)) := by
      rw [contDiff_iff_contDiffAt]
      intro x
      exact (hH (s,x) hs).comp x (contDiffAt_const.prodMk contDiffAt_id)
    exact CR_contDiff_succ (fun x => H (s,x)) hHs v hv1 hW.fst hW.snd hCRv

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

theorem field_C0_smooth_closure (H : ℝ × E → E →L[ℝ] E)
    (hH : ∀ y : ℝ × E, y.1 ∈ Icc (0:ℝ) 1 → ContDiffAt ℝ ∞ H y)
    (hHF : ∀ y : ℝ × E, y.1 ∈ Icc (0:ℝ) 1 → HasFrame (H y))
    (t : ℕ → ℝ) (ht : ∀ j, t j ∈ Icc (0:ℝ) 1) {s : ℝ}
    (hts : Tendsto t atTop (𝓝 s))
    (u : ℕ → ℂ → E) (hu : ∀ j, ContDiff ℝ ∞ (u j))
    (hCR : ∀ j z, fderiv ℝ (u j) z Complex.I=H (t j,u j z) (fderiv ℝ (u j) z 1))
    (v : ℂ → E) (hv : TendstoLocallyUniformly u v atTop) :
    ContDiff ℝ ∞ v ∧ (∀ z, fderiv ℝ v z Complex.I=H (s,v z) (fderiv ℝ v z 1)) ∧
      TendstoLocallyUniformly (fun j => fderiv ℝ (u j)) (fderiv ℝ v) atTop := by
  obtain ⟨_,hDv⟩ := field_C0_C1_closure H hH hHF t ht hts u hu hCR v hv
  refine ⟨?_,field_C1_CR_limit H hH t ht hts u hCR v hv hDv,hDv⟩
  rw [contDiff_infty]
  intro m
  exact field_C0_contDiff_nat m E H hH hHF t ht hts u hu hCR v hv

end HigherDimensionalBallPacking.Rigidity.FramedCR

 

 

open scoped ContDiff Topology
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity

theorem frame_rescale_inverse {n : ℕ} (S : Phase n ≃L[ℝ] Phase n)
    (p : Phase n) (u : ℂ → Phase n) (c : ℂ) {r : ℝ} (hr : r ≠ 0)
    (h : ContDiffAt ℝ 1 (centeredFrame S p (rescaleMap u c r)) 0) :
    ContDiffAt ℝ 1 u c ∧ fderiv ℝ u c=r⁻¹ • S.symm.toContinuousLinearMap.comp
      (fderiv ℝ (centeredFrame S p (rescaleMap u c r)) 0) := by
  let U := centeredFrame S p (rescaleMap u c r)
  let a : ℂ → ℂ := fun z => r⁻¹ • (z-c)
  have ha0 : a c=0 := by simp [a]
  have ha : ContDiff ℝ ∞ a := (contDiff_id.sub contDiff_const).const_smul r⁻¹
  have hid : (fun z => S.symm (U (a z))+p)=u := by
    funext z
    simp only [U,centeredFrame,rescaleMap,a,smul_smul,mul_inv_cancel₀ hr,one_smul,
      add_sub_cancel,ContinuousLinearEquiv.symm_apply_apply,sub_add_cancel]
  have hh : ContDiffAt ℝ 1 U (a c) := by simpa only [ha0] using h
  have huc : ContDiffAt ℝ 1 u c := by
    rw [←hid]
    exact (S.symm.contDiff.contDiffAt.comp c (hh.comp c (ha.of_le (by simp)).contDiffAt)).add contDiffAt_const
  refine ⟨huc,?_⟩
  have had : HasFDerivAt a (r⁻¹ • ContinuousLinearMap.id ℝ ℂ) c := by
    convert (((hasFDerivAt_id (𝕜 := ℝ) c).sub_const c).const_smul r⁻¹) using 1
    rfl
  have hud := ((S.symm.hasFDerivAt.comp c
    ((hh.differentiableAt (by simp)).hasFDerivAt.comp c had)).add_const p).fderiv
  simp only [Function.comp_def] at hud
  rw [hid] at hud
  rw [ha0] at hud
  simpa only [ContinuousLinearMap.comp_smul,ContinuousLinearMap.comp_id] using hud


 

 

open scoped ContDiff Topology
open Set Filter Function

theorem PseudoHolomorphicAt_limit {n : ℕ} {u : ℕ → ℂ → Phase n}
    {J : ℕ → Phase n → End n} {v : ℂ → Phase n} {B : Phase n → End n} {z : ℂ}
    (hv : DifferentiableAt ℝ v z)
    (hu : ∀ j, PseudoHolomorphicAt (J j) (u j) z)
    (hD : Tendsto (fun j => fderiv ℝ (u j) z) atTop (𝓝 (fderiv ℝ v z)))
    (hJ : Tendsto (fun j => J j (u j z)) atTop (𝓝 (B (v z)))) :
    PseudoHolomorphicAt B v z := by
  refine ⟨hv,?_⟩
  intro w
  have happ (a : ℂ) : Continuous (fun T : ℂ →L[ℝ] Phase n => T a) :=
    continuous_id.clm_apply continuous_const
  have hleft : Tendsto (fun j => fderiv ℝ (u j) z (Complex.I*w)) atTop
      (𝓝 (fderiv ℝ v z (Complex.I*w))) :=
    (happ (Complex.I*w)).continuousAt.tendsto.comp hD
  have hE : Continuous (fun y : End n × Phase n => y.1 y.2) :=
    continuous_fst.clm_apply continuous_snd
  have hright : Tendsto (fun j => J j (u j z) (fderiv ℝ (u j) z w)) atTop
      (𝓝 (B (v z) (fderiv ℝ v z w))) := by
    have hp : Tendsto (fun j => (J j (u j z),fderiv ℝ (u j) z w)) atTop
        (𝓝 (B (v z),fderiv ℝ v z w)) :=
      hJ.prodMk_nhds ((happ w).continuousAt.tendsto.comp hD)
    convert (hE.tendsto (B (v z),fderiv ℝ v z w)).comp hp using 1
    rfl
  apply tendsto_nhds_unique hleft
  exact hright.congr (fun j => (hu j).2 w |>.symm)


 

 

 

open scoped ContDiff Topology
open Set Filter Function
open HigherDimensionalBallPacking.Rigidity

theorem homotopy_C0_C1At {n : ℕ} {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x, Compatible (J x))
    (t : ℕ → ℝ) (ht : ∀ j, t j ∈ Icc (0:ℝ) 1) {s : ℝ}
    (hts : Tendsto t atTop (𝓝 s))
    (u : ℕ → ℂ → Phase n) (hu : ∀ j, ContDiff ℝ ∞ (u j))
    (hCR : ∀ j z, PseudoHolomorphicAt (lineHomotopy J (t j)) (u j) z)
    (v : ℂ → Phase n) (hv : TendstoLocallyUniformly u v atTop) (c : ℂ) :
    ContDiffAt ℝ 1 v c ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun j => fderiv ℝ (u (φ j)) c) atTop (𝓝 (fderiv ℝ v c)) := by
  let H : ℝ × Phase n → End n := fun y => lineHomotopy J y.1 y.2
  have hs : s ∈ Icc (0:ℝ) 1 := isClosed_Icc.mem_of_tendsto hts (Eventually.of_forall ht)
  have hH (y : ℝ × Phase n) (hy : y.1 ∈ Icc (0:ℝ) 1) : ContDiffAt ℝ ∞ H y :=
    lineHomotopy_contDiffAt hJs hJ hy
  have hvc : Continuous v := hv.continuous (Eventually.of_forall (fun j => (hu j).continuous)).frequently
  obtain ⟨L,hL,hLu⟩ := homotopy_C0_gradient_bound hJs hJ t ht hts u hu hCR v hv c
    (by norm_num : (0:ℝ) ≤ 1)
  have hBounded : Bornology.IsBounded
      ((fderiv ℝ H) '' (Icc (0:ℝ) 1 ×ˢ Metric.closedBall (v c) 1)) :=
    ((isCompact_Icc.prod (isCompact_closedBall (v c) 1)).image_of_continuousOn
      (fun y hy => ((hH y hy.1).continuousAt_fderiv (by simp)).continuousWithinAt)).isBounded
  obtain ⟨K,hK,hKb⟩ := hBounded.exists_pos_norm_le
  obtain ⟨S,hS⟩ := compatible_standard_frame (lineHomotopy_compatible hJ hs (v c))
  let LS := ‖S.toContinuousLinearMap‖*L
  let KS := ‖frameConjugation S‖*(K*L)
  obtain ⟨δ,hδ,hth⟩ := smallCR_C1_closure_threshold (E := Phase n) LS KS
    (mul_nonneg (norm_nonneg S.toContinuousLinearMap) hL)
    (mul_nonneg (norm_nonneg (frameConjugation S)) (mul_nonneg hK.le hL))
  obtain ⟨ru,hru,hru1,hruv⟩ := locally_uniform_small_ball (c := c) hv hvc.continuousAt hts
    (G := fun y : ℝ × Phase n => S (y.2-v c))
    (S.continuous.continuousAt.comp (continuousAt_snd.sub continuousAt_const))
    (by simp) (by norm_num : (0:ℝ)<1)
  obtain ⟨ra,hra,hra1,hraA⟩ := locally_uniform_small_ball (c := c) hv hvc.continuousAt hts
    (G := fun y : ℝ × Phase n => frameConjugation S (H y-H (s,v c)))
    ((frameConjugation S).continuous.continuousAt.comp
      ((hH (s,v c) hs).continuousAt.sub continuousAt_const)) (by simp) hδ
  obtain ⟨rp,hrp,hrp1,hrpv⟩ := locally_uniform_small_ball (c := c) hv hvc.continuousAt hts
    (G := fun y : ℝ × Phase n => y.2-v c)
    (continuousAt_snd.sub continuousAt_const) (by simp) (by norm_num : (0:ℝ)<1)
  let r := min ru (min ra rp)/3
  have hr : 0 < r := div_pos (lt_min hru (lt_min hra hrp)) (by norm_num)
  have hr3u : 3*r ≤ ru := by dsimp [r]; linarith [min_le_left ru (min ra rp)]
  have hr3a : 3*r ≤ ra := by dsimp [r]; linarith [min_le_right ru (min ra rp),min_le_left ra rp]
  have hr3p : 3*r ≤ rp := by dsimp [r]; linarith [min_le_right ru (min ra rp),min_le_right ra rp]
  have hr1 : r ≤ 1 := by linarith
  let w : ℕ → ℂ → Phase n := fun j => rescaleMap (u j) c r
  let U : ℕ → ℂ → Phase n := fun j => centeredFrame S (v c) (w j)
  let B : ℕ → ℂ → End n := fun j z => H (t j,w j z)
  let A : ℕ → ℂ → End n := fun j => frozenCoefficient S (H (s,v c)) (B j)
  let V := centeredFrame S (v c) (rescaleMap v c r)
  have hw (j : ℕ) : ContDiff ℝ ∞ (w j) := rescaleMap_smooth (hu j) c r
  have hU (j : ℕ) : ContDiff ℝ ∞ (U j) := centeredFrame_smooth S (v c) (hw j)
  have hB (j : ℕ) : ContDiff ℝ ∞ (B j) := by
    rw [contDiff_iff_contDiffAt]
    intro z
    exact ContDiffAt.comp (g := H) (f := fun z => (t j,w j z)) z
      (hH (t j,w j z) (ht j)) (contDiffAt_const.prodMk (hw j).contDiffAt)
  have hA (j : ℕ) : ContDiff ℝ ∞ (A j) := frozenCoefficient_smooth S _ (hB j)
  have hmap (z : ℂ) (hz : z ∈ Metric.closedBall (0:ℂ) 3) : dist (c+r • z) c ≤ 3*r := by
    rw [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    nlinarith [show ‖z‖ ≤ 3 by simpa using hz]
  have hb : ∀ᶠ j in atTop, ∀ z ∈ Metric.closedBall (0:ℂ) 3,
      ‖U j z‖ ≤ 1 ∧ ‖fderiv ℝ (U j) z‖ ≤ LS ∧ ‖A j z‖ ≤ δ ∧
      ‖fderiv ℝ (A j) z‖ ≤ KS ∧
      fderiv ℝ (U j) z Complex.I-Complex.I • fderiv ℝ (U j) z 1=
        A j z (fderiv ℝ (U j) z 1) := by
    filter_upwards [hLu,hruv,hraA,hrpv] with j hjD hju hjA hjp
    intro z hz
    have hmem : c+r • z ∈ Metric.closedBall c 1 := (hmap z hz).trans (hr3u.trans hru1)
    have hwD : ‖fderiv ℝ (w j) z‖ ≤ L := by
      rw [show ‖fderiv ℝ (w j) z‖=|r| * ‖fderiv ℝ (u j) (c+r • z)‖ from
        rescaleMap_norm_fderiv ((hu j).differentiable (by simp)) c r z,abs_of_pos hr]
      exact (mul_le_mul_of_nonneg_left (hjD _ hmem) hr.le).trans
        (by simpa using mul_le_mul_of_nonneg_right hr1 hL)
    have hp : w j z ∈ Metric.closedBall (v c) 1 := by
      simpa only [Metric.mem_closedBall,dist_eq_norm,w,rescaleMap] using
        (hjp (c+r • z) ((hmap z hz).trans hr3p))
    have hBD : ‖fderiv ℝ (B j) z‖ ≤ K*L := by
      have hd : HasFDerivAt (fun z => (t j,w j z))
          ((0 : ℂ →L[ℝ] ℝ).prod (fderiv ℝ (w j) z)) z :=
        (hasFDerivAt_const (t j) z).prodMk ((hw j).differentiable (by simp) z).hasFDerivAt
      have he : fderiv ℝ (B j) z=(fderiv ℝ H (t j,w j z)).comp
          ((0 : ℂ →L[ℝ] ℝ).prod (fderiv ℝ (w j) z)) :=
        (HasFDerivAt.comp (g := H) (f := fun z => (t j,w j z)) z
          ((hH (t j,w j z) (ht j)).differentiableAt (by simp)).hasFDerivAt hd).fderiv
      rw [he]
      apply ((fderiv ℝ H (t j,w j z)).opNorm_comp_le _).trans
      have hnorm : ‖(0 : ℂ →L[ℝ] ℝ).prod (fderiv ℝ (w j) z)‖=‖fderiv ℝ (w j) z‖ := by
        rw [ContinuousLinearMap.opNorm_prod,Prod.norm_def,norm_zero,max_eq_right (norm_nonneg _)]
      rw [hnorm]
      exact mul_le_mul (hKb _ ⟨(t j,w j z),⟨ht j,hp⟩,rfl⟩) hwD (norm_nonneg _) hK.le
    refine ⟨hju _ ((hmap z hz).trans hr3u),?_,hjA _ ((hmap z hz).trans hr3a),?_,?_⟩
    · rw [show fderiv ℝ (U j) z=S.toContinuousLinearMap.comp (fderiv ℝ (w j) z) from
        centeredFrame_fderiv S (v c) ((hw j).differentiable (by simp)) z]
      exact (S.toContinuousLinearMap.opNorm_comp_le _).trans
        (mul_le_mul_of_nonneg_left hwD (norm_nonneg _))
    · rw [show fderiv ℝ (A j) z=(frameConjugation S).comp (fderiv ℝ (B j) z) from
        frozenCoefficient_fderiv S _ ((hB j).differentiable (by simp)) z]
      exact ((frameConjugation S).opNorm_comp_le _).trans
        (mul_le_mul_of_nonneg_left hBD (norm_nonneg _))
    · exact frozen_CR_equation S _ hS (v c) ((hw j).differentiable (by simp)) (B j)
        (rescaleMap_CR ((hu j).differentiable (by simp)) (hCR j) c r z)
  have hUV : TendstoLocallyUniformly U V atTop := by
    have hf : UniformContinuous (fun x : Phase n => S (x-v c)) :=
      S.toContinuousLinearMap.uniformContinuous.comp (uniformContinuous_id.sub uniformContinuous_const)
    exact hf.comp_tendstoLocallyUniformly
      (hv.comp (fun z : ℂ => c+r • z) (continuous_const.add (continuous_id.const_smul r)))
  obtain ⟨hV,φ,hφ,hφD⟩ := hth U A V hU hA hUV hb
  obtain ⟨hcv,hdv⟩ := frame_rescale_inverse S (v c) v c hr.ne' hV
  refine ⟨hcv,φ,hφ,?_⟩
  have hcont : Continuous (fun T : ℂ →L[ℝ] Phase n => r⁻¹ • S.symm.toContinuousLinearMap.comp T) :=
    (continuous_const.clm_comp continuous_id).const_smul r⁻¹
  have hlim := hcont.continuousAt.tendsto.comp hφD
  convert hlim using 1
  · funext j
    exact (frame_rescale_inverse S (v c) (u (φ j)) c hr.ne' ((hU (φ j)).of_le (by simp)).contDiffAt).2
  · exact congrArg nhds hdv

theorem homotopy_C0_C1_CR {n : ℕ} {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x, Compatible (J x))
    (t : ℕ → ℝ) (ht : ∀ j, t j ∈ Icc (0:ℝ) 1) {s : ℝ}
    (hts : Tendsto t atTop (𝓝 s))
    (u : ℕ → ℂ → Phase n) (hu : ∀ j, ContDiff ℝ ∞ (u j))
    (hCR : ∀ j z, PseudoHolomorphicAt (lineHomotopy J (t j)) (u j) z)
    (v : ℂ → Phase n) (hv : TendstoLocallyUniformly u v atTop) :
    ContDiff ℝ 1 v ∧ ∀ z, PseudoHolomorphicAt (lineHomotopy J s) v z := by
  have hc (z : ℂ) := homotopy_C0_C1At hJs hJ t ht hts u hu hCR v hv z
  refine ⟨contDiff_iff_contDiffAt.mpr (fun z => (hc z).1),?_⟩
  intro z
  obtain ⟨hcz,φ,hφ,hD⟩ := hc z
  have hs : s ∈ Icc (0:ℝ) 1 := isClosed_Icc.mem_of_tendsto hts (Eventually.of_forall ht)
  have hu0 : Tendsto (fun j => u (φ j) z) atTop (𝓝 (v z)) :=
    (hv.tendstoLocallyUniformlyOn.tendsto_at (mem_univ z)).comp hφ.tendsto_atTop
  have hB : Tendsto (fun j => lineHomotopy J (t (φ j)) (u (φ j) z)) atTop
      (𝓝 (lineHomotopy J s (v z))) := by
    have hp : Tendsto (fun j => (t (φ j),u (φ j) z)) atTop (𝓝 (s,v z)) :=
      (hts.comp hφ.tendsto_atTop).prodMk_nhds hu0
    convert (lineHomotopy_contDiffAt hJs hJ (y := (s,v z)) hs).continuousAt.tendsto.comp hp using 1
    rfl
  exact PseudoHolomorphicAt_limit (u := fun j => u (φ j))
    (J := fun j => lineHomotopy J (t (φ j))) (v := v) (B := lineHomotopy J s) (z := z)
    (hcz.differentiableAt (by simp)) (fun j => hCR (φ j) z) hD hB

end HigherDimensionalBallPacking.Rigidity

end

end OAI
