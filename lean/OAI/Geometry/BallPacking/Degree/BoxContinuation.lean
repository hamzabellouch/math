import Mathlib
import OAI.Geometry.BallPacking.Degree.ChartFormZeroExtension

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity.Degree

section
open scoped ContDiff Topology
open Set Filter MeasureTheory
variable {m : ℕ}

theorem finite_box_continuation
    {F : CoordinateSpace (m+1) → CoordinateSpace m} (hF : ContDiff ℝ ∞ F)
    {R : ℝ} (hR : 0<R) (hinit : ∀ y,F (timeFace 0 y)=y)
    (hside : ∀ t∈Icc (0:ℝ) 1,∀ y∈spatialBox R,∀ i : Fin m,
      y i= -R ∨ y i=R → F (timeFace t y)≠0) :
    ∃ y∈spatialBox R,F (timeFace 1 y)=0 := by
  by_contra hn
  push Not at hn
  have havoid (v : CoordinateSpace (m+1)) (hv : v∈exitFaces R) : F v≠0 := by
    have ht := time_mem_interval hv.1
    have hy := tail_mem_spatialBox hv.1
    have he : timeFace (v 0) (Fin.tail v)=v := Fin.cons_self_tail v
    rcases hv.2 with hend|hsidev
    · have hh := hn (Fin.tail v) hy
      have he1 : timeFace 1 (Fin.tail v)=v := by rwa [hend] at he
      rwa [he1] at hh
    · obtain ⟨i,hi⟩ := mem_iUnion.mp hsidev
      have hh := hside (v 0) ht (Fin.tail v) hy i hi
      rwa [he] at hh
  let K := F '' exitFaces (m := m) R
  have hK : IsCompact K := (exitFaces_compact R).image hF.continuous
  have h0 : (0:CoordinateSpace m)∉K := by
    rintro ⟨v,hv,he⟩
    exact havoid v hv he
  obtain ⟨b,hb,hbz⟩ := separating_bump hK h0 hR
  have hwb (x : CoordinateSpace m) (hx : x∈K) : weightedVolume b x=0 :=
    weightedVolume_zero (hbz x hx)
  have hboundary : ∀ i : Fin (m+1),i≠0 →
      ∀ y∈Icc (lowerCorner R ∘ i.succAbove) (upperCorner R ∘ i.succAbove),
        weightedVolume b (F (i.insertNth (upperCorner R i) y))=0 ∧
          weightedVolume b (F (i.insertNth (lowerCorner R i) y))=0 := by
    intro i hi y hy
    have hh := sideFace_mem_exit R hR.le i hi hy
    exact ⟨hwb _ (mem_image_of_mem F hh.1),hwb _ (mem_image_of_mem F hh.2)⟩
  have hinitial : (∫ y in Icc (lowerCorner R ∘ (0:Fin (m+1)).succAbove)
      (upperCorner R ∘ (0:Fin (m+1)).succAbove),
      formFlux (pullTopForm F (weightedVolume b)) 0 ((0:Fin (m+1)).insertNth (lowerCorner (m := m) R 0) y))≠0 := by
    simp only [lowerCorner,Fin.cons_zero,initial_weighted_flux hF 0 hinit]
    change (∫ y in spatialBox R,b y)≠0
    exact (bump_initial_integral_pos b hb.le).ne'
  obtain ⟨y,hy,hny⟩ := finite_homotopy_support_endpoint hF
    (weightedVolume_differentiable ((b.contDiff (n := (⊤ : ℕ∞))).differentiable (by simp)))
    (lowerCorner R) (upperCorner R) (corners_le hR.le) hboundary hinitial
  apply hny
  apply hwb
  apply mem_image_of_mem
  have hy' : y∈spatialBox R := (initialFace_box R) ▸ hy
  rw [Fin.insertNth_zero']
  change Fin.cons 1 y∈exitFaces R
  exact ⟨timeFace_mem_box (by constructor <;> norm_num) hy',Or.inl (by simp)⟩


end
section
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
variable {m : ℕ}

lemma compact_smooth_plateau {K U : Set (CoordinateSpace m)} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K⊆U) :
    ∃ χ : CoordinateSpace m → ℝ,ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ⊆U ∧
      (∀ x,0≤χ x ∧ χ x≤1) ∧ ∃ V : Set (CoordinateSpace m),IsOpen V ∧ K⊆V ∧ EqOn χ (fun _ => 1) V := by
  obtain ⟨r,hr,hrU⟩ := hK.exists_cthickening_subset_open hU hKU
  let O := Metric.thickening r K
  let T := Metric.cthickening (r/2) K
  have hTO : T⊆O := Metric.cthickening_subset_thickening (δ₁ := ⟨r/2,(half_pos hr).le⟩) (half_lt_self hr) K
  obtain ⟨χ,hχ,hχr,hχs,hχ1⟩ := exists_contMDiff_support_eq_eq_one_iff
    (I := 𝓘(ℝ,CoordinateSpace m)) (n := (⊤ : ℕ∞)) Metric.isOpen_thickening Metric.isClosed_cthickening hTO
  have hχc : ContDiff ℝ ∞ χ := hχ.contDiff
  have hs : tsupport χ⊆Metric.cthickening r K := by
    rw [tsupport,hχs]
    exact closure_minimal (Metric.thickening_subset_cthickening r K) Metric.isClosed_cthickening
  refine ⟨χ,hχc,(hK.cthickening).of_isClosed_subset (isClosed_tsupport χ) hs,hs.trans hrU,?_,
    Metric.thickening (r/2) K,Metric.isOpen_thickening,Metric.self_subset_thickening (half_pos hr) K,?_⟩
  · intro x
    exact hχr (mem_range_self x)
  · intro x hx
    exact (hχ1 x).mp (Metric.thickening_subset_cthickening (r/2) K hx)

def finiteTimeFreeze (F : CoordinateSpace (m+1) → CoordinateSpace m)
    (v : CoordinateSpace (m+1)) : CoordinateSpace m :=
  F (timeFace (Real.smoothTransition (v 0)) (Fin.tail v))

lemma finiteTimeFreeze_smooth {F : CoordinateSpace (m+1) → CoordinateSpace m}
    (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (finiteTimeFreeze F) := by
  apply hF.comp
  apply contDiff_pi.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact (show ContDiff ℝ ∞ Real.smoothTransition from contDiff_infty.mpr (fun _ => Real.smoothTransition.contDiff)).comp (contDiff_pi.mp contDiff_id 0)
  · exact contDiff_pi.mp contDiff_id j.succ

lemma finiteTimeFreeze_zero {F : CoordinateSpace (m+1) → CoordinateSpace m} (y : CoordinateSpace m) :
    finiteTimeFreeze F (timeFace 0 y)=F (timeFace 0 y) := by
  simp only [finiteTimeFreeze,timeFace,Fin.cons_zero,Fin.tail_cons,Real.smoothTransition.zero]

lemma finiteTimeFreeze_one {F : CoordinateSpace (m+1) → CoordinateSpace m} (y : CoordinateSpace m) :
    finiteTimeFreeze F (timeFace 1 y)=F (timeFace 1 y) := by
  simp only [finiteTimeFreeze,timeFace,Fin.cons_zero,Fin.tail_cons,Real.smoothTransition.one]


end
section
open scoped ContDiff Topology
open Set Filter MeasureTheory
variable {m : ℕ}

def cutoffPullTopForm (χ : CoordinateSpace m → ℝ)
    (F : CoordinateSpace (m+1) → CoordinateSpace m)
    (b : CoordinateSpace m → ℝ) (v : CoordinateSpace (m+1)) :
    CoordinateSpace (m+1) [⋀^Fin m]→L[ℝ] ℝ :=
  χ (Fin.tail v) • pullTopForm F (weightedVolume b) v

lemma tail_smooth : ContDiff ℝ ∞ (Fin.tail : CoordinateSpace (m+1) → CoordinateSpace m) := by
  exact contDiff_pi.mpr (fun i => contDiff_pi.mp contDiff_id i.succ)

lemma cutoffPullTopForm_differentiable {χ : CoordinateSpace m → ℝ}
    {F : CoordinateSpace (m+1) → CoordinateSpace m} {b : CoordinateSpace m → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hF : ContDiff ℝ ∞ F) (hb : ContDiff ℝ ∞ b) :
    Differentiable ℝ (cutoffPullTopForm χ F b) :=
  ((hχ.comp tail_smooth).differentiable (by simp)).smul
    (pullTopForm_differentiable hF (weightedVolume_differentiable (hb.differentiable (by simp))))

lemma extDeriv_constant_zero (v : CoordinateSpace (m+1)) :
    extDeriv (fun _ : CoordinateSpace (m+1) => (0 : CoordinateSpace (m+1) [⋀^Fin m]→L[ℝ] ℝ)) v=0 := by
  ext u
  rw [extDeriv_apply (differentiableAt_const _)]
  simp

lemma cutoffPullTopForm_closed {χ : CoordinateSpace m → ℝ}
    {F : CoordinateSpace (m+1) → CoordinateSpace m} {b : CoordinateSpace m → ℝ}
    (hF : ContDiff ℝ ∞ F) (hb : ContDiff ℝ ∞ b)
    {V : Set (CoordinateSpace m)} (hV : IsOpen V) (hχ1 : EqOn χ (fun _ => 1) V)
    (hcover : ∀ v : CoordinateSpace (m+1),Fin.tail v∈V ∨
      Fin.tail v∉tsupport χ ∨ F v∉tsupport b) (v : CoordinateSpace (m+1)) :
    extDeriv (cutoffPullTopForm χ F b) v=0 := by
  rcases hcover v with h|h|h
  · have he : cutoffPullTopForm χ F b =ᶠ[𝓝 v] pullTopForm F (weightedVolume b) := by
      filter_upwards [tail_smooth.continuous.continuousAt (hV.mem_nhds h)] with y hy
      simp only [cutoffPullTopForm,hχ1 hy,one_smul]
    rw [he.extDeriv_eq]
    exact pullTopForm_closed hF (weightedVolume_differentiable (hb.differentiable (by simp))) v
  · have he : cutoffPullTopForm χ F b =ᶠ[𝓝 v] (fun _ => 0) := by
      filter_upwards [tail_smooth.continuous.continuousAt ((isClosed_tsupport χ).isOpen_compl.mem_nhds h)] with y hy
      simp only [cutoffPullTopForm,image_eq_zero_of_notMem_tsupport hy,zero_smul]
    rw [he.extDeriv_eq]
    exact extDeriv_constant_zero v
  · have he : cutoffPullTopForm χ F b =ᶠ[𝓝 v] (fun _ => 0) := by
      filter_upwards [hF.continuous.continuousAt ((isClosed_tsupport b).isOpen_compl.mem_nhds h)] with y hy
      have hz := pullTopForm_zero (F := F) (weightedVolume_zero (image_eq_zero_of_notMem_tsupport hy))
      simp only [cutoffPullTopForm,hz,smul_zero]
    rw [he.extDeriv_eq]
    exact extDeriv_constant_zero v

lemma separating_bump_support {K : Set (CoordinateSpace m)} (hK : IsCompact K)
    (h0 : (0:CoordinateSpace m)∉K) {R : ℝ} (hR : 0<R) :
    ∃ b : ContDiffBump (0:CoordinateSpace m),b.rOut<R ∧ ∀ x∈K,x∉tsupport (b : CoordinateSpace m → ℝ) := by
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hK.isClosed.isOpen_compl 0 h0
  let r := min ε R/2
  have hr : 0<r := div_pos (lt_min hε hR) (by norm_num)
  let b : ContDiffBump (0:CoordinateSpace m) := ⟨r/2,r,by positivity,by linarith⟩
  have hrε : r<ε := (half_lt_self (lt_min hε hR)).trans_le (min_le_left _ _)
  have hrR : r<R := (half_lt_self (lt_min hε hR)).trans_le (min_le_right _ _)
  refine ⟨b,hrR,?_⟩
  intro x hx hb
  rw [b.tsupport_eq,Metric.mem_closedBall] at hb
  exact hball (show x∈Metric.ball 0 ε from lt_of_le_of_lt hb hrε) hx


end
section
open scoped ContDiff Topology
open Set Function Filter
variable {m : ℕ}

def tailCLM (m : ℕ) : CoordinateSpace (m+1) →L[ℝ] CoordinateSpace m :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj i.succ)
lemma tailCLM_apply (v : CoordinateSpace (m+1)) : tailCLM m v=Fin.tail v := rfl
lemma tail_coordinate_zero : tailCLM m (coordinateVector 0)=0 := by
  ext i
  simp [tailCLM,coordinateVector]
lemma tail_coordinate_succ (i : Fin m) : tailCLM m (coordinateVector i.succ)=coordinateVector i := by
  ext j
  simp [tailCLM,coordinateVector,Pi.single_apply]

def collarVolumeForm (θ : ℝ → ℝ) (ρ : CoordinateSpace m → ℝ) (v : CoordinateSpace (m+1)) :
    CoordinateSpace (m+1) [⋀^Fin m]→L[ℝ] ℝ :=
  (θ (v 0)*ρ (Fin.tail v)) • (coordinateVolume m).compContinuousLinearMap (tailCLM m)

lemma collarVolumeForm_smooth {θ : ℝ → ℝ} {ρ : CoordinateSpace m → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hρ : ContDiff ℝ ∞ ρ) : ContDiff ℝ ∞ (collarVolumeForm θ ρ) :=
  ((hθ.comp (contDiff_pi.mp contDiff_id 0)).mul (hρ.comp tail_smooth)).smul contDiff_const

lemma collarVolumeForm_flux_zero (θ : ℝ → ℝ) (ρ : CoordinateSpace m → ℝ)
    (v : CoordinateSpace (m+1)) :
    formFlux (collarVolumeForm θ ρ) 0 v=θ (v 0)*ρ (Fin.tail v) := by
  change (-1:ℝ)^0 • ((θ (v 0)*ρ (Fin.tail v)) •
    (coordinateVolume m) (fun i => tailCLM m (coordinateVector ((0:Fin (m+1)).succAbove i))))=_
  simp only [Fin.zero_succAbove,tail_coordinate_succ,coordinateVolume_basis,pow_zero,smul_eq_mul,mul_one,one_mul]

lemma collarVolumeForm_flux_other (θ : ℝ → ℝ) (ρ : CoordinateSpace m → ℝ)
    (i : Fin (m+1)) (hi : i≠0) (v : CoordinateSpace (m+1)) :
    formFlux (collarVolumeForm θ ρ) i v=0 := by
  obtain ⟨j,hj⟩ := Fin.exists_succAbove_eq hi.symm
  have hz : (coordinateVolume m) (fun k => tailCLM m (coordinateVector (i.succAbove k)))=0 := by
    apply (coordinateVolume m).toAlternatingMap.map_coord_zero j
    rw [hj,tail_coordinate_zero]
  change (-1:ℝ)^i.val • ((θ (v 0)*ρ (Fin.tail v)) •
    (coordinateVolume m) (fun k => tailCLM m (coordinateVector (i.succAbove k))))=0
  rw [hz,smul_zero,smul_zero]

lemma collarVolumeForm_exterior_basis {θ : ℝ → ℝ} {ρ : CoordinateSpace m → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hρ : ContDiff ℝ ∞ ρ) (v : CoordinateSpace (m+1)) :
    extDeriv (collarVolumeForm θ ρ) v coordinateVector=deriv θ (v 0)*ρ (Fin.tail v) := by
  rw [←formFlux_divergence ((collarVolumeForm_smooth hθ hρ).differentiable (by simp))]
  rw [Finset.sum_eq_single (0:Fin (m+1))]
  · have he : formFlux (collarVolumeForm θ ρ) 0=(fun y => θ (y 0)*ρ (Fin.tail y)) :=
      funext (collarVolumeForm_flux_zero θ ρ)
    rw [he]
    have ht := ((hθ.differentiable (by simp) (v 0)).hasDerivAt.hasFDerivAt).comp v
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (m+1) => ℝ) 0).hasFDerivAt (x := v))
    have hr := ((hρ.differentiable (by simp) (Fin.tail v)).hasFDerivAt).comp v (tailCLM m).hasFDerivAt
    have hh := (ht.mul hr).fderiv
    simp only [Function.comp_def,Pi.mul_def,ContinuousLinearMap.proj_apply] at hh
    rw [hh]
    have hz : tailCLM m (Pi.single 0 1)=0 := tail_coordinate_zero
    simp [coordinateVector,hz,mul_comm]
  · intro i hi hi0
    have he : formFlux (collarVolumeForm θ ρ) i=(fun _ => 0) :=
      funext (collarVolumeForm_flux_other θ ρ i hi0)
    rw [he]
    simp
  · simp

lemma collarVolumeForm_zero_of_time {θ : ℝ → ℝ} {ρ : CoordinateSpace m → ℝ}
    {v : CoordinateSpace (m+1)} (h : θ (v 0)=0) : collarVolumeForm θ ρ v=0 := by
  simp [collarVolumeForm,h]
lemma collarVolumeForm_zero_of_space {θ : ℝ → ℝ} {ρ : CoordinateSpace m → ℝ}
    {v : CoordinateSpace (m+1)} (h : ρ (Fin.tail v)=0) : collarVolumeForm θ ρ v=0 := by
  simp [collarVolumeForm,h]


end
section
open scoped ContDiff Topology
open Set Function Filter

def collarRise (a b t : ℝ) : ℝ := Real.smoothTransition ((t-a)/(b-a))
lemma collarRise_smooth (a b : ℝ) : ContDiff ℝ ∞ (collarRise a b) :=
  (show ContDiff ℝ ∞ Real.smoothTransition from contDiff_infty.mpr (fun _ => Real.smoothTransition.contDiff)).comp
    ((contDiff_id.sub contDiff_const).div_const _)
lemma collarRise_initial {a b t : ℝ} (hab : a<b) (ht : t≤a) : collarRise a b t=0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) (sub_pos.mpr hab).le)
lemma collarRise_final {a b t : ℝ} (hab : a<b) (ht : b≤t) : collarRise a b t=1 :=
  Real.smoothTransition.one_of_one_le ((le_div_iff₀ (sub_pos.mpr hab)).mpr (by linarith))
lemma collarRise_monotone {a b : ℝ} (hab : a<b) : Monotone (collarRise a b) := by
  intro x y hxy
  exact Real.smoothTransition.monotone (div_le_div_of_nonneg_right (sub_le_sub_right hxy _) (sub_pos.mpr hab).le)
lemma collarRise_deriv_nonneg {a b : ℝ} (hab : a<b) (t : ℝ) : 0≤deriv (collarRise a b) t :=
  (collarRise_monotone hab).deriv_nonneg
lemma collarRise_deriv_zero {a b t : ℝ} (hab : a<b) (ht : t∉Icc a b) : deriv (collarRise a b) t=0 := by
  simp only [mem_Icc,not_and_or,not_le] at ht
  rcases ht with ht|ht
  · have he : collarRise a b =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [gt_mem_nhds ht] with s hs
      exact collarRise_initial hab hs.le
    rw [he.deriv_eq]
    simp
  · have he : collarRise a b =ᶠ[𝓝 t] fun _ => 1 := by
      filter_upwards [lt_mem_nhds ht] with s hs
      exact collarRise_final hab hs.le
    rw [he.deriv_eq]
    simp
lemma collarRise_deriv_support {a b : ℝ} (hab : a<b) : tsupport (deriv (collarRise a b))⊆Icc a b := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  by_contra hn
  exact ht (collarRise_deriv_zero hab hn)
lemma collarRise_deriv_positive {a b : ℝ} (hab : a<b) : ∃ t∈Ioo a b,0<deriv (collarRise a b) t := by
  obtain ⟨t,ht,he⟩ := exists_deriv_eq_slope (collarRise a b) hab
    (collarRise_smooth a b).continuous.continuousOn ((collarRise_smooth a b).differentiable (by simp)).differentiableOn
  refine ⟨t,ht,?_⟩
  rw [he,collarRise_initial hab le_rfl,collarRise_final hab le_rfl,sub_zero]
  exact div_pos zero_lt_one (sub_pos.mpr hab)

def collarCutoff (a b c d t : ℝ) : ℝ := collarRise a b t-collarRise c d t
lemma collarCutoff_smooth (a b c d : ℝ) : ContDiff ℝ ∞ (collarCutoff a b c d) :=
  (collarRise_smooth a b).sub (collarRise_smooth c d)
lemma collarCutoff_deriv (a b c d t : ℝ) :
    deriv (collarCutoff a b c d) t=deriv (collarRise a b) t-deriv (collarRise c d) t := by
  exact deriv_sub ((collarRise_smooth a b).differentiable (by simp) t)
    ((collarRise_smooth c d).differentiable (by simp) t)
lemma collarCutoff_zero {a b c d t : ℝ} (hab : a<b) (hbc : b<c) (hcd : c<d)
    (ht : t∉Icc a d) : collarCutoff a b c d t=0 := by
  simp only [mem_Icc,not_and_or,not_le] at ht
  rcases ht with ht|ht
  · rw [collarCutoff,collarRise_initial hab ht.le,collarRise_initial hcd (ht.le.trans (hab.trans hbc).le),sub_self]
  · rw [collarCutoff,collarRise_final hab ((hbc.trans hcd).le.trans ht.le),collarRise_final hcd ht.le,sub_self]
lemma collarCutoff_deriv_initial {a b c d t : ℝ} (hcd : c<d) (ht : t<c) :
    deriv (collarCutoff a b c d) t=deriv (collarRise a b) t := by
  rw [collarCutoff_deriv,collarRise_deriv_zero hcd (fun h => (not_le.mpr ht) h.1),sub_zero]
lemma collarCutoff_deriv_support {a b c d : ℝ} (hab : a<b) (hcd : c<d) :
    tsupport (deriv (collarCutoff a b c d))⊆Icc a b ∪ Icc c d := by
  apply closure_minimal _ (isClosed_Icc.union isClosed_Icc)
  intro t ht
  by_contra hn
  have ha : t∉Icc a b := fun h => hn (Or.inl h)
  have hb : t∉Icc c d := fun h => hn (Or.inr h)
  apply ht
  rw [collarCutoff_deriv,collarRise_deriv_zero hab ha,collarRise_deriv_zero hcd hb,sub_self]


end
section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
variable {m : ℕ}

lemma topForm_eq_zero_of_basis (w : CoordinateSpace m [⋀^Fin m]→L[ℝ] ℝ)
    (hw : w coordinateVector=0) : w=0 := by
  have he := w.toAlternatingMap.eq_smul_basis_det (Pi.basisFun ℝ (Fin m))
  have hb : (coordinateVector : Fin m → CoordinateSpace m)=Pi.basisFun ℝ (Fin m) := by
    funext i
    exact (Pi.basisFun_apply ℝ (Fin m) i).symm
  rw [←hb] at he
  change w.toAlternatingMap coordinateVector=0 at hw
  rw [hw,zero_smul] at he
  ext v
  exact congrArg (fun A : AlternatingMap ℝ (CoordinateSpace m) ℝ (Fin m) => A v) he

lemma collarVolumeForm_exterior_zero {θ : ℝ → ℝ} {ρ : CoordinateSpace m → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hρ : ContDiff ℝ ∞ ρ) {v : CoordinateSpace (m+1)}
    (hz : deriv θ (v 0)=0 ∨ ρ (Fin.tail v)=0) : extDeriv (collarVolumeForm θ ρ) v=0 := by
  apply topForm_eq_zero_of_basis
  rw [collarVolumeForm_exterior_basis hθ hρ]
  exact mul_eq_zero.mpr hz

variable {M I : Type*} [TopologicalSpace M] {a : SignedSmoothAtlas M I (m+1)}
  (f : AtlasSmoothMap a (CoordinateSpace (m+1)))
  {θ : ℝ → ℝ} {ρ : CoordinateSpace m → ℝ}
  (hθ : ContDiff ℝ ∞ θ) (hρ : ContDiff ℝ ∞ ρ)

lemma collar_pullback_density (i : I) {q : CoordinateSpace (m+1)} (hq : q∈(a.chart i).target) :
    (f.pullback (collarVolumeForm θ ρ) (collarVolumeForm_smooth hθ hρ)).exterior.form i q coordinateVector=
      (fderiv ℝ (f.map ∘ (a.chart i).symm) q).det *
        (deriv θ (f.map ((a.chart i).symm q) 0)*ρ (Fin.tail (f.map ((a.chart i).symm q)))) := by
  rw [f.pullback_exterior _ _ i hq]
  change (extDeriv (collarVolumeForm θ ρ) (f.map ((a.chart i).symm q)))
    (fun j => fderiv ℝ (f.map ∘ (a.chart i).symm) q (coordinateVector j))=_
  rw [topForm_evaluation,collarVolumeForm_exterior_basis hθ hρ]

lemma collar_pullback_exterior_supported {K : Set M}
    (hK : ∀ x : M,x∉K →deriv θ (f.map x 0)=0 ∨ ρ (Fin.tail (f.map x))=0) :
    (f.pullback (collarVolumeForm θ ρ) (collarVolumeForm_smooth hθ hρ)).exterior.SupportedIn K := by
  intro i q hq hn
  rw [f.pullback_exterior _ _ i hq,collarVolumeForm_exterior_zero hθ hρ (hK _ hn)]
  ext v
  rfl

lemma collar_pullback_identity_density (i : I)
    (he : EqOn (f.map ∘ (a.chart i).symm) id (a.chart i).target)
    {q : CoordinateSpace (m+1)} (hq : q∈(a.chart i).target) :
    (f.pullback (collarVolumeForm θ ρ) (collarVolumeForm_smooth hθ hρ)).exterior.form i q coordinateVector=
      deriv θ (q 0)*ρ (Fin.tail q) := by
  have heg : (f.map ∘ (a.chart i).symm)=ᶠ[𝓝 q] id :=
    Filter.eventually_of_mem ((a.chart i).open_target.mem_nhds hq) he
  rw [collar_pullback_density f hθ hρ i hq,heg.fderiv_eq]
  have hp : f.map ((a.chart i).symm q)=q := he hq
  rw [hp,fderiv_id]
  simp [ContinuousLinearMap.det,LinearMap.det_id]


end
section
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory Manifold
variable {M I : Type*} [TopologicalSpace M] [T2Space M] [Fintype I] {d : ℕ}
  (a : SignedSmoothAtlas M I d)

@[instance_reducible] def SignedSmoothAtlas.chartedSpace : ChartedSpace (CoordinateSpace d) M where
  atlas := range a.chart
  chartAt x := a.chart (a.cover x).choose
  mem_chart_source x := (a.cover x).choose_spec
  chart_mem_atlas _ := mem_range_self _

omit [T2Space M] [Fintype I] in
lemma SignedSmoothAtlas.isManifold [T2Space M] [Fintype I] :
    @IsManifold ℝ _ (CoordinateSpace d) _ _ (CoordinateSpace d) _
      (𝓘(ℝ,CoordinateSpace d)) ∞ M _ a.chartedSpace := by
  let := a.chartedSpace
  apply isManifold_of_contDiffOn
  rintro e e' ⟨i,rfl⟩ ⟨j,rfl⟩
  simpa only [modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,Function.id_comp,
    Function.comp_id,Set.preimage_id,Set.range_id,Set.inter_univ,OpenPartialHomeomorph.coe_trans] using a.transition_smooth i j

include a in
omit [T2Space M] in
lemma SignedSmoothAtlas.secondCountable [T2Space M] : SecondCountableTopology M := by
  let (i : I) : SecondCountableTopology (a.chart i).source := (a.chart i).secondCountableTopology_source
  apply TopologicalSpace.secondCountableTopology_of_countable_cover (fun i => (a.chart i).open_source)
  exact eq_univ_iff_forall.mpr (fun x => mem_iUnion.mpr (a.cover x))

theorem SignedSmoothAtlas.partition_exists {K : Set M} (hK : IsCompact K) :
    Nonempty (AtlasPartition a K) := by
  let := a.chartedSpace
  let := a.isManifold
  let := a.secondCountable
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (CoordinateSpace d) M
  obtain ⟨p,hp⟩ := SmoothPartitionOfUnity.exists_isSubordinate (𝓘(ℝ,CoordinateSpace d)) hK.isClosed
    (fun i => (a.chart i).source) (fun i => (a.chart i).open_source)
    (fun x hx => mem_iUnion.mpr (a.cover x))
  refine ⟨{weight := fun i => p i,smooth := ?_,sum_one := ?_,subordinate := hp}⟩
  · intro i j
    have hj : a.chart j∈IsManifold.maximalAtlas (𝓘(ℝ,CoordinateSpace d)) ∞ M :=
      IsManifold.subset_maximalAtlas (mem_range_self j)
    exact ((p i).contMDiff.comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas hj)).contDiffOn
  · intro x hx
    simpa only [finsum_eq_sum_of_fintype] using p.sum_eq_one hx


end
open scoped ContDiff Topology Manifold
open Set Function Filter
variable {M I : Type*} [TopologicalSpace M] {d : ℕ}

def SignedSmoothAtlas.restrict (a : SignedSmoothAtlas M I d)
    (J : Set I) (W : TopologicalSpace.Opens M) (hW : Nonempty W)
    (hcover : ∀ x : W,∃ i∈J,x.val∈(a.chart i).source) : SignedSmoothAtlas W J d where
  chart i := (a.chart i.val).subtypeRestr hW
  cover x := by
    obtain ⟨i,hi,hx⟩ := hcover x
    refine ⟨⟨i,hi⟩,?_⟩
    simpa only [OpenPartialHomeomorph.subtypeRestr_source,Set.mem_preimage] using hx
  sign i := a.sign i.val
  sign_sq i := a.sign_sq i.val
  transition_smooth i j := by
    let c := (a.chart i.val).subtypeRestr hW
    let b := (a.chart j.val).subtypeRestr hW
    have hsub : (c.symm ≫ₕ b).source ⊆ ((a.chart i.val).symm ≫ₕ a.chart j.val).source := by
      intro q hq
      refine ⟨(a.chart i.val).subtypeRestr_target_subset hW hq.1,?_⟩
      have he := (a.chart i.val).subtypeRestr_symm_apply hW hq.1
      change ((c.symm q).val)=(a.chart i.val).symm q at he
      change (a.chart i.val).symm q∈(a.chart j.val).source
      rw [←he]
      simpa only [OpenPartialHomeomorph.symm_symm,OpenPartialHomeomorph.subtypeRestr_source,Set.mem_preimage,c,b] using hq.2
    apply ((a.transition_smooth i.val j.val).mono hsub).congr
    intro q hq
    change a.chart j.val (((a.chart i.val).subtypeRestr hW).symm q).val=_
    exact congrArg (a.chart j.val) ((a.chart i.val).subtypeRestr_symm_apply hW hq.1)
  orientation i j q hq := by
    let c := (a.chart i.val).subtypeRestr hW
    let b := (a.chart j.val).subtypeRestr hW
    have he : (b ∘ c.symm) =ᶠ[𝓝 q] (a.chart j.val ∘ (a.chart i.val).symm) := by
      filter_upwards [(c.symm ≫ₕ b).open_source.mem_nhds hq] with r hr
      change a.chart j.val (((a.chart i.val).subtypeRestr hW).symm r).val=_
      exact congrArg (a.chart j.val) ((a.chart i.val).subtypeRestr_symm_apply hW hr.1)
    change a.sign i.val*(fderiv ℝ (b ∘ c.symm) q).det =
      a.sign j.val*|(fderiv ℝ (b ∘ c.symm) q).det|
    rw [he.fderiv_eq]
    apply a.orientation i.val j.val q
    refine ⟨(a.chart i.val).subtypeRestr_target_subset hW hq.1,?_⟩
    have he := (a.chart i.val).subtypeRestr_symm_apply hW hq.1
    change ((c.symm q).val)=(a.chart i.val).symm q at he
    change (a.chart i.val).symm q∈(a.chart j.val).source
    rw [←he]
    simpa only [OpenPartialHomeomorph.symm_symm,OpenPartialHomeomorph.subtypeRestr_source,Set.mem_preimage,c,b] using hq.2

theorem SignedSmoothAtlas.finite_neighborhood (a : SignedSmoothAtlas M I d)
    {K : Set M} (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ W : TopologicalSpace.Opens M,K⊆W ∧
      ∃ J : Finset I,Nonempty (SignedSmoothAtlas W J d) := by
  classical
  obtain ⟨J,hJ⟩ := hK.elim_finite_subcover (fun i => (a.chart i).source)
    (fun i => (a.chart i).open_source) (fun x hx => mem_iUnion.mpr (a.cover x))
  let W : TopologicalSpace.Opens M :=
    ⟨⋃ i∈J,(a.chart i).source,isOpen_biUnion (fun i hi => (a.chart i).open_source)⟩
  have hW : Nonempty W := by
    obtain ⟨x,hx⟩ := hne
    exact ⟨⟨x,hJ hx⟩⟩
  refine ⟨W,hJ,J,⟨a.restrict (J : Set I) W hW ?_⟩⟩
  intro x
  obtain ⟨i,hi,hx⟩ := mem_iUnion₂.mp x.property
  exact ⟨i,hi,hx⟩



end HigherDimensionalBallPacking.Rigidity.Degree
end

end OAI
