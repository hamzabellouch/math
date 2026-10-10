import Mathlib
import OAI.Geometry.BallPacking.DiskMaps.SmoothConvexSelection
import OAI.Geometry.BallPacking.DiskMaps.FlatIsotopy

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function
open MeasureTheory
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem scalar_id_isInvertible {a : ℝ} (ha : a ≠ 0) :
    (a • ContinuousLinearMap.id ℝ E).IsInvertible := by
  apply ContinuousLinearMap.IsInvertible.of_inverse (g := a⁻¹ • ContinuousLinearMap.id ℝ E)
  · ext x
    simp [smul_smul,ha]
  · ext x
    simp [smul_smul,ha]

 theorem smul_isInvertible {A : E →L[ℝ] E} (hA : A.IsInvertible)
    {a : ℝ} (ha : a ≠ 0) : (a • A).IsInvertible := by
  have he : a • A = (a • ContinuousLinearMap.id ℝ E).comp A := by ext x; rfl
  rw [he]
  exact (scalar_id_isInvertible ha).comp hA

 theorem isInvertible_injective {A : E →L[ℝ] E} (hA : A.IsInvertible) : Injective A := by
  obtain ⟨e,he⟩ := hA
  rw [← he]
  exact e.injective

variable [CompleteSpace E] [FiniteDimensional ℝ E]

theorem smoothlyAmbientRelated_contraction
    (f : E → E) (hf : ContDiff ℝ ∞ f)
    (U W : Set E) (hU : IsOpen U) (hW : IsOpen W) (hcW : Convex ℝ W)
    (hinj : InjOn f U) (hi : ∀ x ∈ U, (fderiv ℝ f x).IsInvertible)
    (K : Set E) (hK : IsCompact K) (hKU : K ⊆ U) (hKW : MapsTo f K W)
    (c : E) (hc : c ∈ W) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    SmoothlyAmbientRelated W K f (fun x => c + ε • (f x-c)) := by
  let a : ℝ → ℝ := fun t => 1-t+t*ε
  have ha (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : 0 < a t ∧ a t ≤ 1 := by
    dsimp [a]
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) hε.le]
    · nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hε1)]
  let F : ℝ × E → E := fun p => c + a p.1 • (f p.2-c)
  have hF : ContDiff ℝ ∞ F := contDiff_const.add
    (((contDiff_const.sub contDiff_fst).add (contDiff_fst.mul contDiff_const)).smul
      ((hf.comp contDiff_snd).sub contDiff_const))
  have hFi (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : InjOn (fun x => F (t,x)) U := by
    intro x hx y hy he
    apply hinj hx hy
    have hh := (smul_right_injective E (ne_of_gt (ha t ht).1)) (add_left_cancel he)
    exact sub_left_injective hh
  have hFd (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (x : E) (hx : x ∈ U) :
      (fderiv ℝ (fun x => F (t,x)) x).IsInvertible := by
    have hd := (((hf.differentiable (by simp) x).hasFDerivAt.sub_const c).const_smul (a t)).const_add c
    change HasFDerivAt (fun x => F (t,x)) (a t • fderiv ℝ f x) x at hd
    rw [hd.fderiv]
    exact smul_isInvertible (hi x hx) (ne_of_gt (ha t ht).1)
  have htrack (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (x : E) (hx : x ∈ K) : F (t,x) ∈ W := by
    have hh := hcW hc (hKW hx) (sub_nonneg.mpr (ha t ht).2) (ha t ht).1.le
      (show (1-a t)+a t = 1 by ring)
    convert hh using 1
    dsimp [F]
    module
  have hh := smoothlyAmbientRelated_of_path F hF U W hU hW hFi hFd K hK hKU htrack
  simpa [F,a] using hh

theorem exists_compact_planar_embedding_isotopy
    (f : ℂ → ℂ) (hf : ContDiff ℝ ∞ f)
    (U W : Set ℂ) (hU : IsOpen U) (hW : IsOpen W)
    (hcU : Convex ℝ U) (hcW : Convex ℝ W)
    (hinj : InjOn f U) (hi : ∀ x ∈ U, (fderiv ℝ f x).IsInvertible)
    (K : Set ℂ) (hK : IsCompact K) (h0K : (0:ℂ) ∈ K)
    (hKU : K ⊆ U) (hKW : K ⊆ W) (hfKW : MapsTo f K W)
    (hor : 0 < (fderiv ℝ f 0 1).re * (fderiv ℝ f 0 Complex.I).im -
      (fderiv ℝ f 0 1).im * (fderiv ℝ f 0 Complex.I).re) :
    SmoothlyAmbientRelated W K id f := by
  obtain ⟨L,hL,hLi,hL0,hL1,_⟩ := exists_positive_complex_linear_path (fderiv ℝ f 0) hor
  have h0W : (0:ℂ) ∈ W := hKW h0K
  have hf0W : f 0 ∈ W := hfKW h0K
  have h0U : (0:ℂ) ∈ U := hKU h0K
  let T : Set (ℝ × ℂ) := Icc (0:ℝ) 1 ×ˢ K
  have hT : IsCompact T := isCompact_Icc.prod hK
  let F₂ : ℝ × (ℝ × ℂ) → ℂ := fun q => q.2.1 • f 0 + q.1 • L q.2.1 q.2.2
  have hF₂ : ContDiff ℝ ∞ F₂ := (contDiff_snd.fst.smul contDiff_const).add
    (contDiff_fst.smul ((hL.comp contDiff_snd.fst).clm_apply contDiff_snd.snd))
  have hF₂0 (p : ℝ × ℂ) (hp : p ∈ T) : F₂ (0,p) ∈ W := by
    simpa [F₂] using hcW.smul_mem_of_zero_mem h0W hf0W hp.1
  obtain ⟨δ₂,hδ₂,hδ₂W⟩ := exists_small_positive_perturbation hT hF₂.continuous hW hF₂0
  let F₃ : ℝ × (ℝ × ℂ) → ℂ := fun q => f 0 + q.1 • smoothBlowup f q.2
  have hF₃ : ContDiff ℝ ∞ F₃ := contDiff_const.add
    (contDiff_fst.smul ((smoothBlowup_contDiff hf).comp contDiff_snd))
  obtain ⟨δ₃,hδ₃,hδ₃W⟩ := exists_small_positive_perturbation hT hF₃.continuous hW
    (fun _ _ => by simpa [F₃] using hf0W)
  let ε : ℝ := min (min δ₂ δ₃) 1 / 2
  have hε : 0 < ε := div_pos (lt_min (lt_min hδ₂ hδ₃) zero_lt_one) (by norm_num)
  have hε1 : ε ≤ 1 := by
    dsimp [ε]
    linarith [min_le_right (min δ₂ δ₃) 1]
  have hε₂ : |ε| < δ₂ := by
    rw [abs_of_pos hε]
    have hh := (min_le_left (min δ₂ δ₃) 1).trans (min_le_left δ₂ δ₃)
    dsimp [ε] at *
    linarith
  have hε₃ : |ε| < δ₃ := by
    rw [abs_of_pos hε]
    have hh := (min_le_left (min δ₂ δ₃) 1).trans (min_le_right δ₂ δ₃)
    dsimp [ε] at *
    linarith
  have hrel₂ : SmoothlyAmbientRelated W K (fun x => ε • x)
      (fun x => f 0 + ε • fderiv ℝ f 0 x) := by
    have hh := smoothlyAmbientRelated_of_path (fun p => F₂ (ε,p))
      (hF₂.comp (contDiff_const.prodMk contDiff_id)) U W hU hW
      (fun t _ => by
        intro x _ y _ he
        apply isInvertible_injective (hLi t)
        exact (smul_right_injective ℂ (ne_of_gt hε)) (add_left_cancel he))
      (fun t _ x _ => by
        have hd := (((L t).hasFDerivAt (x := x)).const_smul ε).const_add (t • f 0)
        change HasFDerivAt (fun x => F₂ (ε,(t,x))) (ε • L t) x at hd
        rw [hd.fderiv]
        exact smul_isInvertible (hLi t) (ne_of_gt hε)) K hK hKU
      (fun t ht x hx => hδ₂W ε hε₂ (t,x) ⟨ht,hx⟩)
    simpa [F₂,hL0,hL1] using hh
  have hsmulU (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (x : ℂ) (hx : x ∈ U) :
      t • x ∈ U := hcU.smul_mem_of_zero_mem h0U hx ht
  have hrel₃ : SmoothlyAmbientRelated W K (fun x => f 0 + ε • fderiv ℝ f 0 x)
      (fun x => f 0 + ε • (f x-f 0)) := by
    have hh := smoothlyAmbientRelated_of_path (fun p => F₃ (ε,p))
      (hF₃.comp (contDiff_const.prodMk contDiff_id)) U W hU hW
      (fun t ht => by
        intro x hx y hy he
        apply smoothBlowup_injOn hf hinj (isInvertible_injective (hi 0 h0U)) t
          (hsmulU t ht x hx) (hsmulU t ht y hy)
        exact (smul_right_injective ℂ (ne_of_gt hε)) (add_left_cancel he))
      (fun t ht x hx => by
        have hd := ((smoothBlowup_hasFDerivAt hf t x).const_smul ε).const_add (f 0)
        change HasFDerivAt (fun x => F₃ (ε,(t,x))) (ε • fderiv ℝ f (t • x)) x at hd
        rw [hd.fderiv]
        exact smul_isInvertible (hi _ (hsmulU t ht x hx)) (ne_of_gt hε)) K hK hKU
      (fun t ht x hx => hδ₃W ε hε₃ (t,x) ⟨ht,hx⟩)
    have hb (x : ℂ) : smoothBlowup f (1,x) = f x-f 0 := by
      simpa only [one_smul] using smul_smoothBlowup hf 1 x
    simpa only [F₃,smoothBlowup_zero,hb] using hh
  have hshrink : SmoothlyAmbientRelated W K id (fun x => ε • x) := by
    have hh := smoothlyAmbientRelated_contraction id contDiff_id U W hU hW hcW
      (injOn_id U) (fun x _ => by
        rw [fderiv_id]
        exact ⟨ContinuousLinearEquiv.refl ℝ ℂ,rfl⟩)
      K hK hKU hKW 0 h0W ε hε hε1
    simpa only [id_eq,sub_zero,zero_add] using hh
  have hexpand := smoothlyAmbientRelated_contraction f hf U W hU hW hcW hinj hi
    K hK hKU hfKW (f 0) hf0W ε hε hε1
  exact hshrink.trans (hrel₂.trans (hrel₃.trans hexpand.symm))

end
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem homeomorph_fderiv_isInvertible (e : E ≃ₜ E)
    (he : Differentiable ℝ e) (hei : Differentiable ℝ e.symm) (x : E) :
    (fderiv ℝ e x).IsInvertible := by
  apply ContinuousLinearMap.IsInvertible.of_inverse (g := fderiv ℝ e.symm (e x))
  · have hd := ((he (e.symm (e x))).hasFDerivAt.comp (e x) (hei (e x)).hasFDerivAt).fderiv
    simpa only [Function.comp_def,e.apply_symm_apply,e.symm_apply_apply,fderiv_id,fderiv_fun_id] using hd.symm
  · have hd := ((hei (e x)).hasFDerivAt.comp x (he x).hasFDerivAt).fderiv
    simpa only [Function.comp_def,e.symm_apply_apply,fderiv_id,fderiv_fun_id] using hd.symm

namespace SupportedSmoothIsotopy

 theorem map_smooth {W : Set E} (Φ : SupportedSmoothIsotopy W) (t : ℝ) :
    ContDiff ℝ ∞ (Φ.map t) := Φ.smooth.comp (contDiff_const.prodMk contDiff_id)

 theorem symm_smooth {W : Set E} (Φ : SupportedSmoothIsotopy W) (t : ℝ) :
    ContDiff ℝ ∞ (Φ.map t).symm := Φ.inverse_smooth.comp (contDiff_const.prodMk contDiff_id)

 theorem fderiv_isInvertible {W : Set E} (Φ : SupportedSmoothIsotopy W) (t : ℝ) (x : E) :
    (fderiv ℝ (Φ.map t) x).IsInvertible :=
  homeomorph_fderiv_isInvertible (Φ.map t) ((Φ.map_smooth t).differentiable (by simp))
    ((Φ.symm_smooth t).differentiable (by simp)) x

 theorem fderiv_smooth {W : Set E} (Φ : SupportedSmoothIsotopy W) :
    ContDiff ℝ ∞ (fun p : ℝ × E => fderiv ℝ (Φ.map p.1) p.2) := by
  have he (p : ℝ × E) : fderiv ℝ (Φ.map p.1) p.2 =
      (fderiv ℝ (fun p : ℝ × E => Φ.map p.1 p.2) p).comp (ContinuousLinearMap.inr ℝ ℝ E) := by
    have hi : HasFDerivAt (fun x : E => (p.1,x)) (ContinuousLinearMap.inr ℝ ℝ E) p.2 :=
      (hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2)
    exact ((Φ.smooth.differentiable (by simp) p).hasFDerivAt.comp p.2 hi).fderiv
  simp_rw [he]
  exact (Φ.smooth.fderiv_right (by simp)).clm_comp contDiff_const

 theorem det_fderiv_pos {W : Set E} (Φ : SupportedSmoothIsotopy W) (t : ℝ) (x : E) :
    0 < (fderiv ℝ (Φ.map t) x).det := by
  let d : ℝ → ℝ := fun t => (fderiv ℝ (Φ.map t) x).det
  have hd : Continuous d := ContinuousLinearMap.continuous_det.comp
    (Φ.fderiv_smooth.continuous.comp (continuous_id.prodMk continuous_const))
  have hdz (t : ℝ) : d t ≠ 0 := by
    obtain ⟨e,he⟩ := Φ.fderiv_isInvertible t x
    dsimp [d]
    rw [← he]
    exact e.toLinearEquiv.isUnit_det'.ne_zero
  have hd0 : d 0 = 1 := by simp [d,Φ.zero,fderiv_id,ContinuousLinearMap.det]
  by_contra hn
  have ht : d t ≤ 0 := le_of_not_gt hn
  obtain ⟨s,hs⟩ := intermediate_value_univ t 0 hd ⟨ht,by linarith⟩
  exact hdz s hs

end SupportedSmoothIsotopy

 theorem complex_det (A : ℂ →L[ℝ] ℂ) :
    A.det = (A 1).re * (A Complex.I).im - (A 1).im * (A Complex.I).re := by
  rw [ContinuousLinearMap.det,← LinearMap.det_toMatrix Complex.basisOneI,Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply,Complex.coe_basisOneI,Complex.coe_basisOneI_repr]
  ring

 theorem complex_orientation_of_isotopy {W : Set ℂ} (Φ : SupportedSmoothIsotopy W)
    (t : ℝ) (x : ℂ) :
    0 < (fderiv ℝ (Φ.map t) x 1).re * (fderiv ℝ (Φ.map t) x Complex.I).im -
      (fderiv ℝ (Φ.map t) x 1).im * (fderiv ℝ (Φ.map t) x Complex.I).re := by
  rw [← complex_det]
  exact Φ.det_fderiv_pos t x

end
section

variable (P E : Type*) [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

structure SupportedSmoothIsotopyFamily (W : Set E) where
  map : P → ℝ → E ≃ₜ E
  smooth : ContDiff ℝ ∞ (fun p : (P × ℝ) × E => map p.1.1 p.1.2 p.2)
  inverse_smooth : ContDiff ℝ ∞ (fun p : (P × ℝ) × E => (map p.1.1 p.1.2).symm p.2)
  zero : ∀ y, map y 0 = Homeomorph.refl E
  support : Set E
  compact_support : IsCompact support
  support_subset : support ⊆ W
  fixed : ∀ y t x, x ∉ support → map y t x = x

variable {P E}
namespace SupportedSmoothIsotopyFamily

def eval {W : Set E} (Φ : SupportedSmoothIsotopyFamily P E W) (y : P) :
    SupportedSmoothIsotopy W where
  map := Φ.map y
  smooth := Φ.smooth.comp ((contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd)
  inverse_smooth := Φ.inverse_smooth.comp ((contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd)
  zero := Φ.zero y
  support := Φ.support
  compact_support := Φ.compact_support
  support_subset := Φ.support_subset
  fixed := Φ.fixed y

def constant {W : Set E} (Φ : SupportedSmoothIsotopy W) : SupportedSmoothIsotopyFamily P E W where
  map := fun _ => Φ.map
  smooth := Φ.smooth.comp (contDiff_fst.snd.prodMk contDiff_snd)
  inverse_smooth := Φ.inverse_smooth.comp (contDiff_fst.snd.prodMk contDiff_snd)
  zero := fun _ => Φ.zero
  support := Φ.support
  compact_support := Φ.compact_support
  support_subset := Φ.support_subset
  fixed := fun _ => Φ.fixed

def refl (W : Set E) : SupportedSmoothIsotopyFamily P E W := constant (SupportedSmoothIsotopy.refl W)

def trans {W : Set E} (Φ Ψ : SupportedSmoothIsotopyFamily P E W) :
    SupportedSmoothIsotopyFamily P E W where
  map := fun y t => (Φ.map y t).trans (Ψ.map y t)
  smooth := Ψ.smooth.comp (contDiff_fst.prodMk Φ.smooth)
  inverse_smooth := Φ.inverse_smooth.comp (contDiff_fst.prodMk Ψ.inverse_smooth)
  zero := fun y => by rw [Φ.zero y,Ψ.zero y]; rfl
  support := Φ.support ∪ Ψ.support
  compact_support := Φ.compact_support.union Ψ.compact_support
  support_subset := union_subset Φ.support_subset Ψ.support_subset
  fixed := by
    intro y t x hx
    have hx' : x ∉ Φ.support ∧ x ∉ Ψ.support := by simpa only [mem_union,not_or] using hx
    change Ψ.map y t (Φ.map y t x) = x
    rw [Φ.fixed y t x hx'.1,Ψ.fixed y t x hx'.2]

def symm {W : Set E} (Φ : SupportedSmoothIsotopyFamily P E W) :
    SupportedSmoothIsotopyFamily P E W where
  map := fun y t => (Φ.map y t).symm
  smooth := Φ.inverse_smooth
  inverse_smooth := Φ.smooth
  zero := fun y => by rw [Φ.zero y]; rfl
  support := Φ.support
  compact_support := Φ.compact_support
  support_subset := Φ.support_subset
  fixed := by
    intro y t x hx
    apply (Φ.map y t).injective
    rw [(Φ.map y t).apply_symm_apply,Φ.fixed y t x hx]

def mono {U W : Set E} (Φ : SupportedSmoothIsotopyFamily P E U) (hUW : U ⊆ W) :
    SupportedSmoothIsotopyFamily P E W where
  map := Φ.map
  smooth := Φ.smooth
  inverse_smooth := Φ.inverse_smooth
  zero := Φ.zero
  support := Φ.support
  compact_support := Φ.compact_support
  support_subset := Φ.support_subset.trans hUW
  fixed := Φ.fixed

theorem endpoint_smooth {W : Set E} (Φ : SupportedSmoothIsotopyFamily P E W) :
    ContDiff ℝ ∞ (fun p : P × E => Φ.map p.1 1 p.2) :=
  Φ.smooth.comp ((contDiff_fst.prodMk contDiff_const).prodMk contDiff_snd)

theorem endpoint_inverse_smooth {W : Set E} (Φ : SupportedSmoothIsotopyFamily P E W) :
    ContDiff ℝ ∞ (fun p : P × E => (Φ.map p.1 1).symm p.2) :=
  Φ.inverse_smooth.comp ((contDiff_fst.prodMk contDiff_const).prodMk contDiff_snd)

end SupportedSmoothIsotopyFamily

variable [CompleteSpace P] [FiniteDimensional ℝ P]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem exists_embedding_family_transport
    (f : P × E → E) (hf : ContDiff ℝ ∞ f)
    (O : Set P) (hO : IsOpen O) (hcO : Convex ℝ O)
    (U W : Set E) (hU : IsOpen U) (hW : IsOpen W)
    (hinj : ∀ y ∈ O, InjOn (fun x => f (y,x)) U)
    (hi : ∀ y ∈ O, ∀ x ∈ U, (fderiv ℝ (fun x => f (y,x)) x).IsInvertible)
    (Y : Set P) (hY : IsCompact Y) (hcY : Convex ℝ Y) (hYO : Y ⊆ O)
    (y₀ : P) (hy₀ : y₀ ∈ Y) (K : Set E) (hK : IsCompact K) (hKU : K ⊆ U)
    (htrack : ∀ y ∈ Y, ∀ x ∈ K, f (y,x) ∈ W) :
    ∃ Φ : SupportedSmoothIsotopyFamily P E W,
      ∀ y ∈ Y, ∀ x ∈ K, Φ.map y 1 (f (y₀,x)) = f (y,x) := by
  let a : P × ℝ → P := fun p => (1-p.2) • y₀ + p.2 • p.1
  have ha : ContDiff ℝ ∞ a := ((contDiff_const.sub contDiff_snd).smul contDiff_const).add
    (contDiff_snd.smul contDiff_fst)
  have haO (y : P) (hy : y ∈ O) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : a (y,t) ∈ O :=
    hcO (hYO hy₀) hy (sub_nonneg.mpr ht.2) ht.1 (by ring)
  have haY (y : P) (hy : y ∈ Y) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : a (y,t) ∈ Y :=
    hcY hy₀ hy (sub_nonneg.mpr ht.2) ht.1 (by ring)
  let F : (P × ℝ) × E → E := fun p => f (a p.1,p.2)
  have hF : ContDiff ℝ ∞ F := hf.comp ((ha.comp contDiff_fst).prodMk contDiff_snd)
  obtain ⟨S,Φ,hS,hSW,hΦ,hΦi,hΦ0,hΦs,hΦf⟩ := exists_parametric_flat_embedding_extension
    F hF O hO U W hU hW (fun y hy t ht => hinj _ (haO y hy t ht))
    (fun y hy t ht => hi _ (haO y hy t ht)) Y hY hYO K hK hKU
    (fun y hy t ht x hx => htrack _ (haY y hy t ht) x hx)
  refine ⟨⟨Φ,hΦ,hΦi,hΦ0,S,hS,hSW,hΦs⟩,?_⟩
  intro y hy x hx
  simpa only [F,a,sub_zero,one_smul,zero_smul,add_zero,sub_self,zero_add] using hΦf y hy x hx

end
section

variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace SupportedSmoothIsotopyFamily

def conjugate {W : Set E} (Φ : SupportedSmoothIsotopyFamily P E W)
    (e : E ≃L[ℝ] F) : SupportedSmoothIsotopyFamily P F (e '' W) where
  map := fun y t => e.toHomeomorph.symm.trans ((Φ.map y t).trans e.toHomeomorph)
  smooth := e.contDiff.comp (Φ.smooth.comp
    (contDiff_fst.prodMk (e.symm.contDiff.comp contDiff_snd)))
  inverse_smooth := e.contDiff.comp (Φ.inverse_smooth.comp
    (contDiff_fst.prodMk (e.symm.contDiff.comp contDiff_snd)))
  zero := by intro y; ext x; change e (Φ.map y 0 (e.symm x)) = x; rw [Φ.zero]; exact e.apply_symm_apply x
  support := e '' Φ.support
  compact_support := Φ.compact_support.image e.continuous
  support_subset := image_mono Φ.support_subset
  fixed := by
    intro y t x hx
    have hn : e.symm x ∉ Φ.support := fun h => hx ⟨e.symm x,h,e.apply_symm_apply x⟩
    change e (Φ.map y t (e.symm x)) = x
    rw [Φ.fixed y t _ hn,e.apply_symm_apply]

theorem conjugate_image {W : Set E} (Φ : SupportedSmoothIsotopyFamily P E W)
    (e : E ≃L[ℝ] F) (y : P) (t : ℝ) (S : Set E) :
    (Φ.conjugate e).map y t '' (e '' S) = e '' (Φ.map y t '' S) := by
  ext z
  constructor
  · rintro ⟨_,⟨x,hx,rfl⟩,rfl⟩
    refine ⟨Φ.map y t x,⟨x,hx,rfl⟩,?_⟩
    simp [conjugate]
  · rintro ⟨_,⟨x,hx,rfl⟩,rfl⟩
    refine ⟨e x,⟨x,hx,rfl⟩,?_⟩
    simp [conjugate]

end SupportedSmoothIsotopyFamily

theorem complex_plane_image_closedBall {R : ℝ} (hR : 0 ≤ R) :
    Complex.equivRealProdCLM '' Metric.closedBall (0:ℂ) R = closedRoundDisk R := by
  ext x
  constructor
  · rintro ⟨z,hz,rfl⟩
    change z.re^2+z.im^2 ≤ R^2
    have hn : ‖z‖ ≤ R := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz
    have he := Complex.sq_norm z
    rw [Complex.normSq_apply] at he
    nlinarith [pow_le_pow_left₀ (norm_nonneg _) hn 2]
  · intro hx
    change x.1^2+x.2^2 ≤ R^2 at hx
    refine ⟨(⟨x.1,x.2⟩ : ℂ),?_,rfl⟩
    rw [Metric.mem_closedBall,dist_zero_right,← sq_le_sq₀ (norm_nonneg _) hR]
    have he := Complex.sq_norm (⟨x.1,x.2⟩ : ℂ)
    rw [Complex.normSq_apply] at he
    nlinarith

theorem complex_plane_image_ball {R : ℝ} (hR : 0 ≤ R) :
    Complex.equivRealProdCLM '' Metric.ball (0:ℂ) R = roundDisk R := by
  ext x
  constructor
  · rintro ⟨z,hz,rfl⟩
    change z.re^2+z.im^2 < R^2
    have hn : ‖z‖ < R := by simpa only [Metric.mem_ball,dist_zero_right] using hz
    have he := Complex.sq_norm z
    rw [Complex.normSq_apply] at he
    nlinarith [(sq_lt_sq₀ (norm_nonneg _) hR).mpr hn]
  · intro hx
    change x.1^2+x.2^2 < R^2 at hx
    refine ⟨(⟨x.1,x.2⟩ : ℂ),?_,rfl⟩
    rw [Metric.mem_ball,dist_zero_right,← sq_lt_sq₀ (norm_nonneg _) hR]
    have he := Complex.sq_norm (⟨x.1,x.2⟩ : ℂ)
    rw [Complex.normSq_apply] at he
    nlinarith

theorem complex_plane_volume_image (S : Set ℂ) :
    volume (Complex.equivRealProdCLM '' S) = volume S := by
  have hh := Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv
    (Complex.measurableEquivRealProd '' S)
  rw [preimage_image_eq S Complex.measurableEquivRealProd.injective] at hh
  exact hh.symm

end

theorem diagonalScale_injective {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Injective (diagonalScale a b) := by
  intro x y h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  exact Prod.ext (mul_left_cancel₀ ha h1) (mul_left_cancel₀ hb h2)

theorem diagonalScale_inv_image_closedRoundDisk {r : ℝ} (hr : 0 < r) :
    diagonalScale r⁻¹ r⁻¹ '' closedRoundDisk r = closedRoundDisk 1 := by
  ext x
  constructor
  · rintro ⟨z,hz,rfl⟩
    change z.1^2+z.2^2 ≤ r^2 at hz
    change (r⁻¹*z.1)^2+(r⁻¹*z.2)^2 ≤ 1^2
    have hh := mul_le_mul_of_nonneg_left hz (sq_nonneg r⁻¹)
    have he : r⁻¹^2*r^2 = 1 := by field_simp
    nlinarith only [hh,he]
  · intro hx
    change x.1^2+x.2^2 ≤ 1^2 at hx
    refine ⟨(r*x.1,r*x.2),?_,?_⟩
    · change (r*x.1)^2+(r*x.2)^2 ≤ r^2
      nlinarith only [mul_le_mul_of_nonneg_left hx (sq_nonneg r)]
    · ext <;> simp [diagonalScale_apply,hr.ne']

theorem volume_closedRoundDisk {r : ℝ} (hr : 0 ≤ r) :
    volume (closedRoundDisk r) = ENNReal.ofReal (Real.pi*r^2) := by
  rw [←complex_plane_image_closedBall hr,complex_plane_volume_image]
  rw [InnerProductSpace.volume_closedBall_of_dim_even (k := 1) (by simp)]
  simp only [Complex.finrank_real_complex, pow_one, Nat.factorial_one, Nat.cast_one, div_one]
  rw [←ENNReal.ofReal_pow hr,←ENNReal.ofReal_mul (sq_nonneg r),mul_comm]

def radialArea (x : Plane) : ℝ := Real.pi * radiusSq x

def areaRadius (a : ℝ) : ℝ := Real.sqrt (a/Real.pi)

theorem areaRadius_pos {a : ℝ} (ha : 0 < a) : 0 < areaRadius a :=
  Real.sqrt_pos.2 (div_pos ha Real.pi_pos)

theorem areaRadius_sq {a : ℝ} (ha : 0 ≤ a) : (areaRadius a)^2 = a/Real.pi :=
  Real.sq_sqrt (div_nonneg ha Real.pi_pos.le)

theorem areaRadius_strictMono : StrictMonoOn areaRadius (Ici 0) := by
  intro a ha b _ hab
  exact Real.sqrt_lt_sqrt (div_nonneg ha Real.pi_pos.le) ((div_lt_div_iff_of_pos_right Real.pi_pos).2 hab)

theorem mem_closedRoundDisk_areaRadius {a : ℝ} (ha : 0 ≤ a) (x : Plane) :
    x ∈ closedRoundDisk (areaRadius a) ↔ radialArea x ≤ a := by
  change radiusSq x ≤ (areaRadius a)^2 ↔ Real.pi * radiusSq x ≤ a
  rw [areaRadius_sq ha,le_div_iff₀ Real.pi_pos,mul_comm]

theorem mem_roundDisk_areaRadius {a : ℝ} (ha : 0 ≤ a) (x : Plane) :
    x ∈ roundDisk (areaRadius a) ↔ radialArea x < a := by
  change radiusSq x < (areaRadius a)^2 ↔ Real.pi * radiusSq x < a
  rw [areaRadius_sq ha,lt_div_iff₀ Real.pi_pos,mul_comm]

theorem volume_closedRoundDisk_areaRadius {a : ℝ} (ha : 0 ≤ a) :
    volume (closedRoundDisk (areaRadius a)) = ENNReal.ofReal a := by
  rw [volume_closedRoundDisk (show 0 ≤ areaRadius a from Real.sqrt_nonneg _),areaRadius_sq ha]
  congr 1
  exact mul_div_cancel₀ _ Real.pi_ne_zero

def normalizedPolarMap (k : ℝ) (c : Plane) (a b r : ℝ) : Plane → Plane :=
  polarRoundedMap k c a b ∘ diagonalScale r⁻¹ r⁻¹

theorem normalizedPolarMap_injective {k a b r : ℝ} (hk : 0 < k) (ha : 0 < a)
    (hb : 0 < b) (hr : 0 < r) (c : Plane) (hfit : FitsPolar c a b) :
    Injective (normalizedPolarMap k c a b r) :=
  (polarRoundedMap_injective hk ha hb c hfit).comp
    (diagonalScale_injective (inv_ne_zero hr.ne') (inv_ne_zero hr.ne'))

theorem normalizedPolarMap_det_pos {k a b r : ℝ} (hk : 0 < k) (ha : 0 < a)
    (hb : 0 < b) (hr : 0 < r) (c : Plane) (hfit : FitsPolar c a b) (x : Plane) :
    0 < (fderiv ℝ (normalizedPolarMap k c a b r) x).det := by
  rw [normalizedPolarMap,fderiv_comp x
    ((polarRoundedMap_smooth ha hb k c hfit).differentiable (by simp) _)
    ((diagonalScale r⁻¹ r⁻¹).differentiable _), (diagonalScale r⁻¹ r⁻¹).fderiv,
    ContinuousLinearMap.det,ContinuousLinearMap.toLinearMap_comp,LinearMap.det_comp]
  change 0 < (fderiv ℝ (polarRoundedMap k c a b) _).det * (diagonalScale r⁻¹ r⁻¹).det
  rw [diagonalScale_det]
  exact mul_pos (polarRoundedMap_det_pos hk ha hb c hfit _) (mul_pos (inv_pos.mpr hr) (inv_pos.mpr hr))

theorem normalizedPolarMap_image {r : ℝ} (hr : 0 < r) (k : ℝ) (c : Plane) (a b : ℝ) :
    normalizedPolarMap k c a b r '' closedRoundDisk r = polarRoundedDisk k c a b := by
  rw [normalizedPolarMap,image_comp,diagonalScale_inv_image_closedRoundDisk hr]
  rfl

theorem polarRoundedDisk_volume_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (k : ℝ) (c : Plane) (hfit : FitsPolar c a b) :
    volume (polarRoundedDisk k c a b) = ENNReal.ofReal (a*b*squeezedArea k) := by
  have hfin : volume (polarRoundedDisk k c a b) ≠ ⊤ :=
    ((closedRoundDisk_isCompact 1).image (polarRoundedMap_smooth ha hb k c hfit).continuous).measure_ne_top
  exact (ENNReal.toReal_eq_toReal_iff' hfin ENNReal.ofReal_ne_top).mp (by
    rw [polarRoundedDisk_volume ha hb k c hfit,ENNReal.toReal_ofReal
      (mul_nonneg (mul_nonneg ha.le hb.le) (squeezedArea_nonneg k))])

theorem roundedBox_nested_of_margins {k q a b a' b' : ℝ} {c c' : Plane}
    (ha : 0 < a) (hb : 0 < b) (ha' : 0 < a') (hb' : 0 < b')
    (hsquare : Icc (-q) q ×ˢ Icc (-q) q ⊆ squeezedDisk k)
    (hleft : c'.1-q*a' ≤ c.1-a) (hright : c.1+a ≤ c'.1+q*a')
    (hbottom : c'.2-q*b' ≤ c.2-b) (htop : c.2+b ≤ c'.2+q*b') :
    roundedBox k c a b ⊆ interior (roundedBox k c' a' b') := by
  apply Subset.trans _ (openBox_subset_interior_roundedBox ha' hb' hsquare c')
  rintro _ ⟨x,_,rfl⟩
  have hx := roundedMap_mem_openBox ha hb k c x
  exact ⟨⟨hleft.trans_lt hx.1.1,hx.1.2.trans_le hright⟩,
    ⟨hbottom.trans_lt hx.2.1,hx.2.2.trans_le htop⟩⟩

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem normalizedPolarFamily_smoothOn {A : Set P} (hA : IsOpen A)
    (C : P → Plane) (hC : ContDiff ℝ ∞ C) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (k r : ℝ) (hfit : ∀ y ∈ A, FitsPolar (C y) a b) :
    ContDiffOn ℝ ∞ (fun p : P × Plane => normalizedPolarMap k (C p.1) a b r p.2) (A ×ˢ univ) :=
  (polarRoundedFamily_smoothOn hA C hC ha hb k hfit).comp
    (contDiff_fst.prodMk ((diagonalScale r⁻¹ r⁻¹).contDiff.comp contDiff_snd)).contDiffOn
    (by intro p hp; exact ⟨hp.1,mem_univ _⟩)

end PackingSufficiencySupport.Hamiltonian
end

end OAI
