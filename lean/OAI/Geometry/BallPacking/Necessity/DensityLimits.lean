import Mathlib
import OAI.Geometry.BallPacking.Necessity.Properness

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
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

def tangentCurveDir (a : ℂ) (u : ℂ → E) : ℂ → E × E := fun z => (u z,fderiv ℝ u z a)

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
theorem tangentCurveDir_smooth [FiniteDimensional ℂ E] [CompleteSpace E]
    (a : ℂ) {u : ℂ → E} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (tangentCurveDir a u) :=
  hu.prodMk ((hu.fderiv_right (by simp)).clm_apply contDiff_const)

theorem tangentCurveDir_fderiv {u : ℂ → E} (hu : ContDiff ℝ ∞ u) (a z b : ℂ) :
    fderiv ℝ (tangentCurveDir a u) z b=(fderiv ℝ u z b,fderiv ℝ (fderiv ℝ u) z b a) := by
  have hDu : Differentiable ℝ (fun w => fderiv ℝ u w a) :=
    ((hu.fderiv_right (by simp : (∞:WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const).differentiable (by simp)
  have hh := (((hu.differentiable (by simp)) z).hasFDerivAt.prodMk (hDu z).hasFDerivAt).fderiv
  change fderiv ℝ (fun z => (u z,fderiv ℝ u z a)) z b=_
  rw [hh]
  simp only [ContinuousLinearMap.prod_apply,fderiv_directional hu]

theorem tangentCurveDir_CR (a : ℂ) (H : ℝ × E → E →L[ℝ] E)
    (hH : ∀ y : ℝ × E, y.1 ∈ Icc (0:ℝ) 1 → ContDiffAt ℝ ∞ H y)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) {u : ℂ → E} (hu : ContDiff ℝ ∞ u)
    (hCR : ∀ z, fderiv ℝ u z Complex.I=H (t,u z) (fderiv ℝ u z 1)) :
    ∀ z, fderiv ℝ (tangentCurveDir a u) z Complex.I=
      tangentField H (t,tangentCurveDir a u z) (fderiv ℝ (tangentCurveDir a u) z 1) := by
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
  have hd := congrArg (fun f : ℂ → E => fderiv ℝ f z a) he
  rw [fderiv_directional hu,hR] at hd
  have hs := (hu.contDiffAt (x := z)).isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  rw [tangentCurveDir_fderiv hu,tangentCurveDir_fderiv hu]
  change (fderiv ℝ u z Complex.I,fderiv ℝ (fderiv ℝ u) z Complex.I a)=
    (H (t,u z) (fderiv ℝ u z 1),
      fderiv ℝ H (t,u z) (0,fderiv ℝ u z a) (fderiv ℝ u z 1)+
        H (t,u z) (fderiv ℝ (fderiv ℝ u) z 1 a))
  rw [hCR z,hs Complex.I a,hs 1 a]
  congr 1
  simpa [B,DB,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
    fderiv_directional hu,add_comm] using hd

end HigherDimensionalBallPacking.Rigidity.FramedCR

 

 

 

open scoped ContDiff Topology
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity.FramedCR
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

theorem directional_second_convergence (a : ℂ) (H : ℝ × E → E →L[ℝ] E)
    (hH : ∀ y : ℝ × E, y.1 ∈ Icc (0:ℝ) 1 → ContDiffAt ℝ ∞ H y)
    (hHF : ∀ y : ℝ × E, y.1 ∈ Icc (0:ℝ) 1 → HasFrame (H y))
    (t : ℕ → ℝ) (ht : ∀ j, t j ∈ Icc (0:ℝ) 1) {s : ℝ}
    (hts : Tendsto t atTop (𝓝 s))
    (u : ℕ → ℂ → E) (hu : ∀ j, ContDiff ℝ ∞ (u j))
    (hCR : ∀ j z, fderiv ℝ (u j) z Complex.I=H (t j,u j z) (fderiv ℝ (u j) z 1))
    (v : ℂ → E) (hv : TendstoLocallyUniformly u v atTop) :
    TendstoLocallyUniformly (fun j => fderiv ℝ (fun z => fderiv ℝ (u j) z a))
      (fderiv ℝ (fun z => fderiv ℝ v z a)) atTop := by
  obtain ⟨hvs,_,hDv⟩ := field_C0_smooth_closure H hH hHF t ht hts u hu hCR v hv
  have hlim : TendstoLocallyUniformly (fun j => tangentCurveDir a (u j))
      (tangentCurveDir a v) atTop :=
    hv.prodMk ((ContinuousLinearMap.apply ℝ E a).uniformContinuous.comp_tendstoLocallyUniformly hDv)
  obtain ⟨_,_,hDW⟩ := field_C0_smooth_closure (tangentField H)
    (tangentField_smooth H hH) (tangentField_hasFrame H hH hHF) t ht hts
    (fun j => tangentCurveDir a (u j)) (fun j => tangentCurveDir_smooth a (hu j))
    (fun j => tangentCurveDir_CR a H hH (ht j) (hu j) (hCR j)) (tangentCurveDir a v) hlim
  let P : (ℂ →L[ℝ] E × E) →L[ℝ] (ℂ →L[ℝ] E) :=
    (ContinuousLinearMap.compL ℝ ℂ (E × E) E) (ContinuousLinearMap.snd ℝ E E)
  have he (w : ℂ → E) (hw : ContDiff ℝ ∞ w) (z : ℂ) :
      P (fderiv ℝ (tangentCurveDir a w) z)=fderiv ℝ (fun z => fderiv ℝ w z a) z := by
    ext b
    simp only [P,ContinuousLinearMap.compL_apply,ContinuousLinearMap.comp_apply,
      tangentCurveDir_fderiv hw,fderiv_directional hw]
    rfl
  simpa only [Function.comp_def,he _ hvs,he _ (hu _)] using
    P.uniformContinuous.comp_tendstoLocallyUniformly hDW

def standardCurl (u : ℂ → E) (z : ℂ) : E :=
  fderiv ℝ u z Complex.I-Complex.I • fderiv ℝ u z 1

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
theorem standardCurl_smooth [FiniteDimensional ℂ E] [CompleteSpace E]
    {u : ℂ → E} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (standardCurl u) :=
  ((hu.fderiv_right (by simp)).clm_apply contDiff_const).sub
    (((hu.fderiv_right (by simp)).clm_apply contDiff_const).const_smul Complex.I)

def curlLinear : (ℂ →L[ℝ] E) →L[ℝ] E :=
  ContinuousLinearMap.apply ℝ E Complex.I-
    ((Complex.I • ContinuousLinearMap.id ℂ E).restrictScalars ℝ).comp
      (ContinuousLinearMap.apply ℝ E 1)

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
@[simp] theorem curlLinear_apply [FiniteDimensional ℂ E] [CompleteSpace E]
    (D : ℂ →L[ℝ] E) :
    curlLinear D=D Complex.I-Complex.I • D 1 := rfl

theorem standardCurl_convergence (H : ℝ × E → E →L[ℝ] E)
    (hH : ∀ y : ℝ × E, y.1 ∈ Icc (0:ℝ) 1 → ContDiffAt ℝ ∞ H y)
    (hHF : ∀ y : ℝ × E, y.1 ∈ Icc (0:ℝ) 1 → HasFrame (H y))
    (t : ℕ → ℝ) (ht : ∀ j, t j ∈ Icc (0:ℝ) 1) {s : ℝ}
    (hts : Tendsto t atTop (𝓝 s))
    (u : ℕ → ℂ → E) (hu : ∀ j, ContDiff ℝ ∞ (u j))
    (hCR : ∀ j z, fderiv ℝ (u j) z Complex.I=H (t j,u j z) (fderiv ℝ (u j) z 1))
    (v : ℂ → E) (hv : TendstoLocallyUniformly u v atTop) :
    TendstoLocallyUniformly (fun j => standardCurl (u j)) (standardCurl v) atTop ∧
    TendstoLocallyUniformly (fun j => fderiv ℝ (standardCurl (u j)))
      (fderiv ℝ (standardCurl v)) atTop := by
  obtain ⟨hvs,_,hDv⟩ := field_C0_smooth_closure H hH hHF t ht hts u hu hCR v hv
  refine ⟨(curlLinear (E := E)).uniformContinuous.comp_tendstoLocallyUniformly hDv,?_⟩
  have hI := directional_second_convergence Complex.I H hH hHF t ht hts u hu hCR v hv
  have h1 := directional_second_convergence 1 H hH hHF t ht hts u hu hCR v hv
  let M : E →L[ℝ] E := (Complex.I • ContinuousLinearMap.id ℂ E).restrictScalars ℝ
  let L : ((ℂ →L[ℝ] E) × (ℂ →L[ℝ] E)) →L[ℝ] (ℂ →L[ℝ] E) :=
    ContinuousLinearMap.fst ℝ _ _-
      ((ContinuousLinearMap.compL ℝ ℂ E E) M).comp (ContinuousLinearMap.snd ℝ _ _)
  have he (w : ℂ → E) (hw : ContDiff ℝ ∞ w) (z : ℂ) :
      L (fderiv ℝ (fun z => fderiv ℝ w z Complex.I) z,
        fderiv ℝ (fun z => fderiv ℝ w z 1) z)=fderiv ℝ (standardCurl w) z := by
    have hi := (((hw.fderiv_right (by simp : (∞:WithTop ℕ∞)+1 ≤ ∞)).clm_apply
      (contDiff_const (c := Complex.I))).differentiable (by simp) z).hasFDerivAt
    have h1 := (((hw.fderiv_right (by simp : (∞:WithTop ℕ∞)+1 ≤ ∞)).clm_apply
      (contDiff_const (c := (1:ℂ)))).differentiable (by simp) z).hasFDerivAt
    exact (hi.sub (M.hasFDerivAt.comp z h1)).fderiv.symm
  simpa only [Function.comp_def,he _ hvs,he _ (hu _)] using
    L.uniformContinuous.comp_tendstoLocallyUniformly (hI.prodMk h1)

end HigherDimensionalBallPacking.Rigidity.FramedCR

 

 

 

open scoped ContDiff Topology
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem density_tsupport_subset [NormedSpace ℝ E] [CompleteSpace E]
    (R : ℝ) (f : ℂ → E)
    (hf : ∀ z, R < ‖z‖ → f z=0) : tsupport f ⊆ Metric.closedBall (0:ℂ) R := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro z hz
  by_contra hn
  exact hz (hf z (by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hn))

theorem density_compact_support (R : ℝ) (f : ℂ → E)
    (hf : ∀ z, R < ‖z‖ → f z=0) : HasCompactSupport f :=
  (isCompact_closedBall (0:ℂ) R).of_isClosed_subset (isClosed_tsupport _) (density_tsupport_subset R f hf)

def smoothCompactDensity (R : ℝ) (f : ℂ → E) (hf : ContDiff ℝ ∞ f)
    (hs : ∀ z, R < ‖z‖ → f z=0) : CompactHolderSpace E R :=
  ⟨compactSmoothHolder ((1:ℝ)/3) (by norm_num) (by norm_num) f hf
    (density_compact_support R f hs),hs⟩

@[simp] theorem smoothCompactDensity_apply (R : ℝ) (f : ℂ → E) (hf : ContDiff ℝ ∞ f)
    (hs : ∀ z, R < ‖z‖ → f z=0) (z : ℂ) :
    compactHolderValue R (smoothCompactDensity R f hf hs) z=f z := rfl

theorem density_fderiv_zero_exterior (R : ℝ) (f : ℂ → E)
    (hf : ∀ z, R < ‖z‖ → f z=0) (z : ℂ) (hz : R < ‖z‖) :
    fderiv ℝ f z=0 := by
  apply fderiv_of_notMem_tsupport
  intro hh
  have h := density_tsupport_subset R f hf hh
  exact (not_le_of_gt hz) (by simpa only [Metric.mem_closedBall,dist_zero_right] using h)

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem density_locally_uniform_to_uniform [NormedSpace ℝ E] [CompleteSpace E]
    (R : ℝ) (f : ℕ → ℂ → E) (g : ℂ → E)
    (hfs : ∀ j z, R < ‖z‖ → f j z=0) (hgs : ∀ z, R < ‖z‖ → g z=0)
    (h : TendstoLocallyUniformly f g atTop) : TendstoUniformly f g atTop := by
  have hc := tendstoLocallyUniformly_iff_forall_isCompact.mp h
    (Metric.closedBall (0:ℂ) R) (isCompact_closedBall _ _)
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hc ε hε] with j hj z
  by_cases hz : ‖z‖ ≤ R
  · exact hj z (by simpa only [Metric.mem_closedBall,dist_zero_right] using hz)
  · rw [hfs j z (lt_of_not_ge hz),hgs z (lt_of_not_ge hz),dist_self]
    exact hε

theorem smoothCompactDensity_tendsto (R : ℝ) (f : ℕ → ℂ → E)
    (hfs : ∀ j, ContDiff ℝ ∞ (f j)) (hfc : ∀ j z, R < ‖z‖ → f j z=0)
    (g : ℂ → E) (hgs : ContDiff ℝ ∞ g) (hgc : ∀ z, R < ‖z‖ → g z=0)
    (h : TendstoLocallyUniformly f g atTop)
    (hD : TendstoLocallyUniformly (fun j => fderiv ℝ (f j)) (fderiv ℝ g) atTop) :
    Tendsto (fun j => smoothCompactDensity R (f j) (hfs j) (hfc j)) atTop
      (𝓝 (smoothCompactDensity R g hgs hgc)) := by
  have h0 := density_locally_uniform_to_uniform R f g hfc hgc h
  have h1 := density_locally_uniform_to_uniform R (fun j => fderiv ℝ (f j)) (fderiv ℝ g)
    (fun j => density_fderiv_zero_exterior R (f j) (hfc j))
    (density_fderiv_zero_exterior R g hgc) hD
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ,hδ,hδs⟩ := holder_third_small_sup (K := ℂ) (E := E) 1 ε (by norm_num) hε
  filter_upwards [Metric.tendstoUniformly_iff.mp h0 δ hδ,
    Metric.tendstoUniformly_iff.mp h1 1 (by norm_num)] with j hj hjD
  let d : HolderSpace ℂ E ((1:ℝ)/3) := (smoothCompactDensity R (f j) (hfs j) (hfc j)).val-
    (smoothCompactDensity R g hgs hgc).val
  have hd (z : ℂ) : holderValue ((1:ℝ)/3) d z=f j z-g z := rfl
  have hdb (z : ℂ) : ‖fderiv ℝ (fun x => f j x-g x) z‖ ≤ 1 := by
    change ‖fderiv ℝ (f j-g) z‖ ≤ 1
    rw [fderiv_sub ((hfs j).differentiable (by simp) z) (hgs.differentiable (by simp) z)]
    have hb : ‖fderiv ℝ (f j) z-fderiv ℝ g z‖ < 1 := by
      simpa only [dist_eq_norm,norm_sub_rev] using hjD z
    exact hb.le
  have hl : LipschitzWith 1 (fun x => f j x-g x) :=
    lipschitzWith_of_nnnorm_fderiv_le ((hfs j).differentiable (by simp) |>.sub
      (hgs.differentiable (by simp))) (fun z => hdb z)
  have hdn : ‖d‖ < ε := hδs d
    (fun z => by simpa only [hd,dist_eq_norm,norm_sub_rev] using (hj z).le)
    (fun x y => by simpa only [hd,dist_eq_norm,NNReal.coe_one,one_mul] using hl.dist_le_mul x y)
  rw [Subtype.dist_eq,dist_eq_norm]
  exact hdn

end

 

 

 

open scoped ContDiff Topology
open Set Filter Function
section
open HigherDimensionalBallPacking.Rigidity
open FramedCR

def affineHolderModuli {n : ℕ} (J : Phase n → End n) (p q : Phase n) (R : ℝ) :
    Set (ℝ × CompactHolderSpace (Phase n) R) :=
  {y | y.1 ∈ Icc (0:ℝ) 1 ∧ ∃ u : ℂ → Phase n,
    AffineLineCurve (lineHomotopy J y.1) p q u ∧
      ∀ z, compactHolderValue R y.2 z=standardCurl u z}

theorem homotopy_density_common_support (n : ℕ) (hn : 3 ≤ n)
    (J : Phase n → End n) (hJs : ContDiff ℝ ∞ J)
    (hJ : ∀ x, Compatible (J x))
    (hc : HasCompactSupport (fun x => J x-standardJ n))
    (hs : tsupport (fun x => J x-standardJ n) ⊆ openBall n 1)
    (p q : Phase n) (hpq : p ≠ q) :
    ∃ R > 0, ∀ t ∈ Icc (0:ℝ) 1, ∀ u : ℂ → Phase n,
      AffineLineCurve (lineHomotopy J t) p q u →
      ∀ z, R < ‖z‖ → standardCurl u z=0 := by
  obtain ⟨R,hR,he⟩ := homotopy_uniform_holomorphic_exterior n hn J hJs hJ hc hs p q hpq
  refine ⟨R,hR,?_⟩
  intro t ht u hu z hz
  have hopen : IsOpen {z : ℂ | R < ‖z‖} := isOpen_lt continuous_const continuous_norm
  have hd := (he t ht u hu z hz).differentiableAt (hopen.mem_nhds hz)
  exact sub_eq_zero.mpr (differentiableAt_complex_iff_differentiableAt_real.mp hd).2

theorem affineHolderModuli_isCompact (n : ℕ) (hn : 3 ≤ n)
    (J : Phase n → End n) (hJs : ContDiff ℝ ∞ J)
    (hJ : ∀ x, Compatible (J x))
    (hc : HasCompactSupport (fun x => J x-standardJ n))
    (hs : tsupport (fun x => J x-standardJ n) ⊆ openBall n 1)
    (p q : Phase n) (hpq : p ≠ q) (R : ℝ)
    (hR : ∀ t ∈ Icc (0:ℝ) 1, ∀ u : ℂ → Phase n,
      AffineLineCurve (lineHomotopy J t) p q u →
      ∀ z, R < ‖z‖ → standardCurl u z=0) :
    IsCompact (affineHolderModuli J p q R) := by
  apply IsSeqCompact.isCompact
  intro U hU
  choose u hu he using fun j => (hU j).2
  obtain ⟨φ,hφ,τ,hτ,hφt,v,hφv,hv⟩ := homotopy_affine_curve_compactness
    n hn J hJs hJ hc hs p q hpq (fun j => (U j).1) (fun j => (hU j).1) u hu
  have hCR (j : ℕ) (z : ℂ) : fderiv ℝ (u (φ j)) z Complex.I=
      lineHomotopy J (U (φ j)).1 (u (φ j) z) (fderiv ℝ (u (φ j)) z 1) := by
    simpa only [mul_one] using (hu (φ j)).2.1 z |>.2 (1:ℂ)
  have hlim := standardCurl_convergence
    (fun y : ℝ × Phase n => lineHomotopy J y.1 y.2)
    (fun y hy => lineHomotopy_contDiffAt hJs hJ hy)
    (fun y hy => compatible_standard_frame (lineHomotopy_compatible hJ hy y.2))
    (fun j => (U (φ j)).1) (fun j => (hU (φ j)).1) hφt
    (fun j => u (φ j)) (fun j => (hu (φ j)).1) hCR v hφv
  let G : CompactHolderSpace (Phase n) R :=
    smoothCompactDensity R (standardCurl v) (standardCurl_smooth hv.1) (hR τ hτ v hv)
  have hG : Tendsto (fun j => smoothCompactDensity R (standardCurl (u (φ j)))
      (standardCurl_smooth (hu (φ j)).1) (hR _ (hU (φ j)).1 _ (hu (φ j)))) atTop (𝓝 G) :=
    smoothCompactDensity_tendsto R (fun j => standardCurl (u (φ j)))
      (fun j => standardCurl_smooth (hu (φ j)).1)
      (fun j => hR _ (hU (φ j)).1 _ (hu (φ j)))
      (standardCurl v) (standardCurl_smooth hv.1) (hR τ hτ v hv) hlim.1 hlim.2
  have heG (j : ℕ) : smoothCompactDensity R (standardCurl (u (φ j)))
      (standardCurl_smooth (hu (φ j)).1) (hR _ (hU (φ j)).1 _ (hu (φ j)))=(U (φ j)).2 := by
    apply Subtype.ext
    apply holderValue_injective ((1:ℝ)/3)
    apply DFunLike.ext
    intro z
    exact (he (φ j) z).symm
  simp only [heG] at hG
  refine ⟨(τ,G),⟨hτ,v,hv,fun _ => rfl⟩,φ,hφ,?_⟩
  exact hφt.prodMk_nhds hG

theorem homotopy_affine_Holder_compactness (n : ℕ) (hn : 3 ≤ n)
    (J : Phase n → End n) (hJs : ContDiff ℝ ∞ J)
    (hJ : ∀ x, Compatible (J x))
    (hc : HasCompactSupport (fun x => J x-standardJ n))
    (hs : tsupport (fun x => J x-standardJ n) ⊆ openBall n 1)
    (p q : Phase n) (hpq : p ≠ q) :
    ∃ R > 0, IsCompact (affineHolderModuli J p q R) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ u : ℂ → Phase n,
        AffineLineCurve (lineHomotopy J t) p q u →
        ∀ z, R < ‖z‖ → standardCurl u z=0) := by
  obtain ⟨R,hR,hRc⟩ := homotopy_density_common_support n hn J hJs hJ hc hs p q hpq
  exact ⟨R,hR,affineHolderModuli_isCompact n hn J hJs hJ hc hs p q hpq R hRc,hRc⟩

end

 

 

 

open scoped ContDiff Topology
open Set Filter Function

def affineHomotopyModuli {n : ℕ} (J : Phase n → End n) (p q : Phase n) :
    Set (ℝ × C(ℂ,Phase n)) :=
  {y | y.1 ∈ Icc (0:ℝ) 1 ∧ AffineLineCurve (lineHomotopy J y.1) p q y.2}

theorem affineHomotopyModuli_isCompact (n : ℕ) (hn : 3 ≤ n)
    (J : Phase n → End n) (hJs : ContDiff ℝ ∞ J)
    (hJ : ∀ x, Compatible (J x))
    (hc : HasCompactSupport (fun x => J x-standardJ n))
    (hs : tsupport (fun x => J x-standardJ n) ⊆ openBall n 1)
    (p q : Phase n) (hpq : p ≠ q) :
    IsCompact (affineHomotopyModuli J p q) := by
  apply IsSeqCompact.isCompact
  intro U hU
  obtain ⟨φ,hφ,τ,hτ,hφt,v,hφv,hv⟩ := homotopy_affine_curve_compactness
    n hn J hJs hJ hc hs p q hpq (fun j => (U j).1) (fun j => (hU j).1)
    (fun j => (U j).2) (fun j => (hU j).2)
  let V : C(ℂ,Phase n) := ⟨v,hv.1.continuous⟩
  refine ⟨(τ,V),⟨hτ,hv⟩,φ,hφ,?_⟩
  exact hφt.prodMk_nhds (ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mpr hφv)

def affineSolvableTimes {n : ℕ} (J : Phase n → End n) (p q : Phase n) : Set ℝ :=
  {t | t ∈ Icc (0:ℝ) 1 ∧ ∃ u : ℂ → Phase n, AffineLineCurve (lineHomotopy J t) p q u}

theorem affineSolvableTimes_eq_image {n : ℕ} (J : Phase n → End n) (p q : Phase n) :
    affineSolvableTimes J p q = Prod.fst '' affineHomotopyModuli J p q := by
  ext t
  constructor
  · rintro ⟨ht,u,hu⟩
    exact ⟨(t,⟨u,hu.1.continuous⟩),⟨ht,hu⟩,rfl⟩
  · rintro ⟨⟨s,u⟩,⟨hs,hu⟩,rfl⟩
    exact ⟨hs,u,hu⟩

theorem affineSolvableTimes_isCompact (n : ℕ) (hn : 3 ≤ n)
    (J : Phase n → End n) (hJs : ContDiff ℝ ∞ J)
    (hJ : ∀ x, Compatible (J x))
    (hc : HasCompactSupport (fun x => J x-standardJ n))
    (hs : tsupport (fun x => J x-standardJ n) ⊆ openBall n 1)
    (p q : Phase n) (hpq : p ≠ q) :
    IsCompact (affineSolvableTimes J p q) := by
  rw [affineSolvableTimes_eq_image]
  exact (affineHomotopyModuli_isCompact n hn J hJs hJ hc hs p q hpq).image continuous_fst

theorem zero_mem_affineSolvableTimes {n : ℕ} (J : Phase n → End n)
    (hJ : ∀ x, Compatible (J x)) (p q : Phase n) (hpq : p ≠ q) :
    0 ∈ affineSolvableTimes J p q := by
  refine ⟨by norm_num,fun z : ℂ => p+z • (q-p),?_⟩
  convert standard_affine_line p q hpq using 1
  funext x
  exact lineHomotopy_zero hJ x


 

 

 

open scoped ContDiff Topology
open Set Filter Function

theorem standard_affine_line_unique {n : ℕ} {p q : Phase n} {u : ℂ → Phase n}
    (hu : AffineLineCurve (fun _ => standardJ n) p q u) :
    u = fun z : ℂ => p+z • (q-p) := by
  have hd : Differentiable ℂ u := fun z => complex_differentiable_of_CR
    (hu.2.1 z).1 (hu.2.1 z).2
  have hs : Differentiable ℂ (dslope u 0) := by
    rw [←differentiableOn_univ]
    exact (Complex.differentiableOn_dslope (by simp : (univ : Set ℂ) ∈ 𝓝 (0:ℂ))).mpr hd.differentiableOn
  obtain ⟨a,ha,hal⟩ := hu.2.2.2.2
  have hi : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 (0:ℂ)) := by
    rw [←Metric.cobounded_eq_cocompact]
    exact tendsto_inv₀_cobounded
  have hl : Tendsto (dslope u 0) (cocompact ℂ) (𝓝 a) := by
    have he : Tendsto (fun z : ℂ => z⁻¹ • u z-z⁻¹ • u 0) (cocompact ℂ) (𝓝 a) := by
      simpa only [zero_smul,sub_zero] using hal.sub (hi.smul_const (u 0))
    apply he.congr'
    filter_upwards [(isCompact_singleton (x := (0:ℂ))).compl_mem_cocompact] with z hz
    have hz0 : z ≠ 0 := by simpa using hz
    simp only [dslope_of_ne u hz0,slope_def_module,sub_zero,smul_sub]
  have hconst := hs.eq_const_of_tendsto_cocompact hl
  have haq : a=q-p := by
    have h := congrFun hconst (1:ℂ)
    simpa only [dslope_of_ne u one_ne_zero,slope_def_module,sub_zero,inv_one,one_smul,
      hu.2.2.1,hu.2.2.2.1,Function.const_apply] using h.symm
  funext z
  have he := sub_smul_dslope u (0:ℂ) z
  rw [sub_zero,hconst,haq,hu.2.2.1] at he
  have he2 : u z-p=z • (q-p) := by simpa only [Function.const_apply] using he.symm
  exact (sub_eq_iff_eq_add.mp he2).trans (add_comm _ _)

theorem affineHomotopyModuli_zero_fiber {n : ℕ} (J : Phase n → End n)
    (hJ : ∀ x, Compatible (J x)) (p q : Phase n) (hpq : p ≠ q)
    (u : C(ℂ,Phase n)) :
    (0,u) ∈ affineHomotopyModuli J p q ↔
      (u : ℂ → Phase n) = fun z : ℂ => p+z • (q-p) := by
  have he : lineHomotopy J 0=fun _ => standardJ n := funext (lineHomotopy_zero hJ)
  constructor
  · intro hu
    have h := hu.2
    rw [he] at h
    exact standard_affine_line_unique h
  · intro hu
    refine ⟨by norm_num,?_⟩
    rw [he,hu]
    exact standard_affine_line p q hpq

end HigherDimensionalBallPacking.Rigidity

end

end OAI
