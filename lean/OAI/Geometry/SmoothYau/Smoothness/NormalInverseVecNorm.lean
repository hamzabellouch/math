import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.ContDiffSmoothFiniteWave

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem smooth_open_inverse {f : E → F} {s : Set E} (hs : IsOpen s)
    (hf : ContDiffOn ℝ (∞ : WithTop ℕ∞) f s) (hinj : InjOn f s)
    (hd : ∀ x ∈ s, (fderiv ℝ f x).IsInvertible) :
    ∃ e : OpenPartialHomeomorph E F, (e : E → F) = f ∧ e.source = s ∧
      ContDiffOn ℝ (∞ : WithTop ℕ∞) e.symm e.target := by
  have hop : ∀ t : Set E, IsOpen t → t ⊆ s → IsOpen (f '' t) := by
    intro t ht hts
    apply isOpen_iff_mem_nhds.mpr
    rintro _ ⟨x,hx,rfl⟩
    obtain ⟨D,hD⟩ := hd x (hts hx)
    have hfc : ContDiffAt ℝ (∞ : WithTop ℕ∞) f x := (hf x (hts hx)).contDiffAt (hs.mem_nhds (hts hx))
    have hfd : HasFDerivAt f (D : E →L[ℝ] F) x := by
      rw [hD]
      exact (hfc.differentiableAt (by simp)).hasFDerivAt
    let e := hfc.toOpenPartialHomeomorph f hfd (by simp)
    have hxe : x ∈ e.source := hfc.mem_toOpenPartialHomeomorph_source hfd (by simp)
    have hmem : f x ∈ e '' (e.source ∩ t) := ⟨x,⟨hxe,hx⟩,rfl⟩
    apply Filter.mem_of_superset ((e.isOpen_image_source_inter ht).mem_nhds hmem)
    rintro _ ⟨y,hy,rfl⟩
    exact ⟨y,hy.2,rfl⟩
  let p := hinj.toPartialEquiv f s
  have ho : IsOpenMap (s.domRestrict f) := by
    intro t ht
    have hv : IsOpen (Subtype.val '' t : Set E) := hs.isOpenMap_subtype_val t ht
    have hz := hop (Subtype.val '' t) hv (by rintro _ ⟨a,ha,rfl⟩; exact a.property)
    change IsOpen ((fun x : s => f x) '' t)
    simpa only [Set.image_image] using hz
  let e := OpenPartialHomeomorph.ofContinuousOpenRestrict p hf.continuousOn ho hs
  refine ⟨e,rfl,rfl,?_⟩
  intro y hy
  obtain ⟨D,hD⟩ := hd (e.symm y) (e.map_target hy)
  have hfc : ContDiffAt ℝ (∞ : WithTop ℕ∞) f (e.symm y) :=
    (hf _ (e.map_target hy)).contDiffAt (hs.mem_nhds (e.map_target hy))
  have hfd : HasFDerivAt f (D : E →L[ℝ] F) (e.symm y) := by
    rw [hD]
    exact (hfc.differentiableAt (by simp)).hasFDerivAt
  exact (e.contDiffAt_symm hy hfd hfc).contDiffWithinAt
end

section
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma familyTotal_derivative_invertible {f : P × E → E} {q : P} {x : E}
    (hf : DifferentiableAt ℝ f (q,x))
    (hd : (fderiv ℝ (fun y => f (q,y)) x).IsInvertible) :
    (fderiv ℝ (fun a : P × E => (a.1,f a)) (q,x)).IsInvertible := by
  let L := fderiv ℝ f (q,x)
  obtain ⟨D,hD⟩ := hd
  let A : P →L[ℝ] E := L.comp (ContinuousLinearMap.inl ℝ P E)
  let T := (ContinuousLinearEquiv.refl ℝ P).skewProd D A
  have hR : L.comp (ContinuousLinearMap.inr ℝ P E) = D := by
    have h := hf.hasFDerivAt.comp x (hasFDerivAt_prodMk_right q x)
    exact h.fderiv.symm.trans hD.symm
  have hL : (ContinuousLinearMap.fst ℝ P E).prod L = T.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro a
    apply Prod.ext
    · rfl
    · change L a = D a.2 + L (a.1,0)
      have ha : a = (0,a.2) + (a.1,0) := by ext <;> simp
      calc
        L a = L (0,a.2) + L (a.1,0) := by conv_lhs => rw [ha]; rw [L.map_add]
        _ = D a.2 + L (a.1,0) := congrArg (fun v => v + L (a.1,0))
          (congrArg (fun M : E →L[ℝ] E => M a.2) hR)
  refine ⟨T,?_⟩
  exact ((hasFDerivAt_fst.prodMk hf.hasFDerivAt).fderiv.trans hL).symm
end

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma isOpen_continuousLinearMap_isInvertible :
    IsOpen {A : E →L[ℝ] E | A.IsInvertible} := by
  have he : {A : E →L[ℝ] E | A.IsInvertible} = {A : E →L[ℝ] E | IsUnit A} := by
    ext A
    constructor
    · rintro ⟨e,rfl⟩
      exact e.toUnit.isUnit
    · rintro ⟨u,rfl⟩
      exact ⟨ContinuousLinearEquiv.unitsEquiv ℝ E u,rfl⟩
  rw [he]
  exact Units.isOpen

end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
local instance normalInverseVecNorm : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance normalInverseVecSpace : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance normalInverseBiVecNorm : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance normalInverseBiVecSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance

omit [FiniteDimensional ℝ E] in
lemma normalJetMap_injOn_small (p : E) (A : E ≃L[ℝ] E)
    (C : E →L[ℝ] E →L[ℝ] E) :
    InjOn (normalJetMap p A C)
      {x | ‖(A.symm : E →L[ℝ] E)‖ * ‖C‖ * ‖x‖ < 1/2} := by
  intro x hx y hy he
  change ‖(A.symm : E →L[ℝ] E)‖ * ‖C‖ * ‖x‖ < 1/2 at hx
  change ‖(A.symm : E →L[ℝ] E)‖ * ‖C‖ * ‖y‖ < 1/2 at hy
  have hr := normalJetMap_remainder p A C x y
  rw [he,sub_self,zero_sub] at hr
  have hAv : A (x-y) = (1/2 : ℝ) • (C x (x-y) + C (x-y) y) := by
    calc
      _ = -(-(A (x-y))) := (neg_neg _).symm
      _ = _ := by
        change -(-((A : E →L[ℝ] E) (x-y))) = _
        rw [hr]; module
  have hB : ‖x-y‖ ≤
      ((‖(A.symm : E →L[ℝ] E)‖*‖C‖*‖x‖ +
        ‖(A.symm : E →L[ℝ] E)‖*‖C‖*‖y‖)/2) * ‖x-y‖ := by
    calc
      ‖x-y‖ = ‖A.symm (A (x-y))‖ := by rw [A.symm_apply_apply]
      _ ≤ ‖(A.symm : E →L[ℝ] E)‖ * ‖A (x-y)‖ := (A.symm : E →L[ℝ] E).le_opNorm _
      _ = ‖(A.symm : E →L[ℝ] E)‖ * ((1/2 : ℝ)*‖C x (x-y)+C (x-y) y‖) := by
        rw [hAv,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
      _ ≤ ‖(A.symm : E →L[ℝ] E)‖ * ((1/2 : ℝ)*
          ((‖C‖*‖x‖)*‖x-y‖ + (‖C‖*‖x-y‖)*‖y‖)) := by
        gcongr
        calc
          _ ≤ ‖C x (x-y)‖ + ‖C (x-y) y‖ := norm_add_le _ _
          _ ≤ _ := add_le_add ((C x).le_opNorm _ |>.trans
            (mul_le_mul_of_nonneg_right (C.le_opNorm _) (norm_nonneg _)))
            ((C (x-y)).le_opNorm _ |>.trans
            (mul_le_mul_of_nonneg_right (C.le_opNorm _) (norm_nonneg _)))
      _ = _ := by ring
  have hn : ‖x-y‖ = 0 := by nlinarith [norm_nonneg (x-y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

def normalFamilySource (g : SmoothMetric E E) : Set ((E × (E →L[ℝ] E)) × E) :=
  {w | w.1.2.IsInvertible ∧ ‖w.1.2.inverse‖ *
    ‖(metricChristoffel g w.1.1).bilinearComp w.1.2 w.1.2‖ * ‖w.2‖ < 1/2}

def normalFamilyTotal (g : SmoothMetric E E) (w : (E × (E →L[ℝ] E)) × E) :=
  (w.1,normalJetMap w.1.1 w.1.2
    ((metricChristoffel g w.1.1).bilinearComp w.1.2 w.1.2) w.2)

lemma isOpen_normalFamilySource (g : SmoothMetric E E) : IsOpen (normalFamilySource g) := by
  apply isOpen_iff_mem_nhds.mpr
  intro w hw
  have hI := (isOpen_continuousLinearMap_isInvertible.preimage
    (continuous_snd.comp continuous_fst)).mem_nhds hw.1
  have hi : ContinuousAt (fun w : (E × (E →L[ℝ] E)) × E => w.1.2.inverse) w :=
    (hw.1.contDiffAt_map_inverse (n := (∞ : WithTop ℕ∞))).continuousAt.comp
      (f := fun w : (E × (E →L[ℝ] E)) × E => w.1.2)
      (continuous_snd.comp continuous_fst).continuousAt
  have hC : ContinuousAt (fun w : (E × (E →L[ℝ] E)) × E =>
      (metricChristoffel g w.1.1).bilinearComp w.1.2 w.1.2) w :=
    ((contDiff_frameChristoffel g).comp contDiff_fst).continuous.continuousAt
  have hcn : ContinuousAt (fun z : (E × (E →L[ℝ] E)) × E =>
      ‖(metricChristoffel g z.1.1).bilinearComp z.1.2 z.1.2‖) w := by
    exact hC.norm
  have hm : ContinuousAt (fun z : (E × (E →L[ℝ] E)) × E => ‖z.1.2.inverse‖ *
      ‖(metricChristoffel g z.1.1).bilinearComp z.1.2 z.1.2‖) w := by
    exact hi.norm.mul hcn
  have hf : ContinuousAt (fun z : (E × (E →L[ℝ] E)) × E => ‖z.1.2.inverse‖ *
      ‖(metricChristoffel g z.1.1).bilinearComp z.1.2 z.1.2‖ * ‖z.2‖) w := by
    exact hm.mul continuous_snd.continuousAt.norm
  have hh := hf.eventually (gt_mem_nhds hw.2)
  exact inter_mem hI hh

lemma normalFamilyTotal_injOn (g : SmoothMetric E E) :
    InjOn (normalFamilyTotal g) (normalFamilySource g) := by
  rintro ⟨q,x⟩ hx ⟨q',y⟩ hy he
  have hq : q = q' := congrArg Prod.fst he
  subst q'
  refine Prod.ext (by rfl) ?_
  obtain ⟨A,hA⟩ := hx.1
  have hi : (A.symm : E →L[ℝ] E) = q.2.inverse := by
    rw [←hA,ContinuousLinearMap.inverse_equiv]
  have hh := normalJetMap_injOn_small q.1 A
    ((metricChristoffel g q.1).bilinearComp q.2 q.2)
  apply hh
  · simpa only [mem_ofPred_eq,hi] using hx.2
  · simpa only [mem_ofPred_eq,hi] using hy.2
  · simpa only [normalFamilyTotal,hA] using congrArg Prod.snd he

lemma normalFamilyTotal_smooth (g : SmoothMetric E E) : ContDiff ℝ (∞ : WithTop ℕ∞) (normalFamilyTotal g) :=
  contDiff_fst.prodMk (contDiff_normalJetFamily g)

lemma normalFamilyTotal_derivative_invertible (g : SmoothMetric E E)
    {w : (E × (E →L[ℝ] E)) × E} (hw : w ∈ normalFamilySource g) :
    (fderiv ℝ (normalFamilyTotal g) w).IsInvertible := by
  obtain ⟨A,hA⟩ := hw.1
  let C := (metricChristoffel g w.1.1).bilinearComp w.1.2 w.1.2
  have hi : (A.symm : E →L[ℝ] E) = w.1.2.inverse := by
    rw [←hA,ContinuousLinearMap.inverse_equiv]
  have hs : ‖(A.symm : E →L[ℝ] E)‖ * ‖C‖ * ‖w.2‖ < 1 := by
    rw [hi]
    exact hw.2.trans (by norm_num)
  have hCs : ∀ v z, C v z = C z v := by
    intro v z
    exact metricChristoffel_symm g w.1.1 (w.1.2 v) (w.1.2 z)
  have hd : (fderiv ℝ (normalJetMap w.1.1 w.1.2 C) w.2).IsInvertible := by
    rw [fderiv_normalJetMap w.1.1 w.1.2 C hCs]
    have h := normalJetMap_derivative_invertible A C hs
    simpa only [hA] using h
  exact familyTotal_derivative_invertible (f := fun a : (E × (E →L[ℝ] E)) × E =>
    normalJetMap a.1.1 a.1.2 ((metricChristoffel g a.1.1).bilinearComp a.1.2 a.1.2) a.2)
    ((contDiff_normalJetFamily g).differentiable (by simp) w) hd

theorem exists_normal_family_inverse (g : SmoothMetric E E) :
    ∃ e : OpenPartialHomeomorph ((E × (E →L[ℝ] E)) × E) ((E × (E →L[ℝ] E)) × E),
      (e : ((E × (E →L[ℝ] E)) × E) → ((E × (E →L[ℝ] E)) × E)) = normalFamilyTotal g ∧
      e.source = normalFamilySource g ∧ ContDiffOn ℝ (∞ : WithTop ℕ∞) e.symm e.target :=
  smooth_open_inverse (isOpen_normalFamilySource g) (normalFamilyTotal_smooth g).contDiffOn
    (normalFamilyTotal_injOn g) (fun _ h => normalFamilyTotal_derivative_invertible g h)

lemma compact_normal_family_radius (g : SmoothMetric E E) {K : Set E} (hK : IsCompact K) :
    ∃ r > 0, ∀ q ∈ metricFrameSet g K, ∀ x ∈ Metric.closedBall (0 : E) r,
      (q,x) ∈ normalFamilySource g := by
  have hsub : metricFrameSet g K ×ˢ {(0 : E)} ⊆ normalFamilySource g := by
    rintro ⟨q,x⟩ ⟨hq,hx⟩
    have hz : x = 0 := hx
    subst x
    exact ⟨metricFrameSet_equiv g hq,by simp⟩
  obtain ⟨U,V,hU,hV,hKU,h0V,hUV⟩ := generalized_tube_lemma (metricFrameSet_isCompact g hK)
    isCompact_singleton (isOpen_normalFamilySource g) hsub
  obtain ⟨r,hr,hrV⟩ := Metric.isOpen_iff.mp hV 0 (h0V (mem_singleton 0))
  refine ⟨r/2,half_pos hr,?_⟩
  intro q hq x hx
  apply hUV ⟨hKU hq,hrV ?_⟩
  exact (Metric.closedBall_subset_ball (half_lt_self hr)) hx


end YauCounterexamples
end

end OAI
