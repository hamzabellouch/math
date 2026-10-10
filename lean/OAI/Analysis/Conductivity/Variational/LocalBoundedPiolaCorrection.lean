import Mathlib
import OAI.Analysis.Conductivity.Geometry.ControlledCorrectionBoxes
import OAI.Analysis.Conductivity.Variational.MetricControlledPiola

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

theorem BoundedPhysicallyCorrectable.piola_local
    (X : OpenPartialHomeomorph Coord3 Coord3)
    (hX : ContDiffOn ℝ (↑(⊤:ℕ∞)) X X.source)
    (hXi : ContDiffOn ℝ (↑(⊤:ℕ∞)) X.symm X.target)
    {u v : Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u)
    (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v)
    {U : Set Coord3} (hUo : IsOpen U) (hU : U⊆X.source)
    (hpot : EqOn u (v∘X.symm) (X '' U)) {C N : ℝ} (hC : 0≤C)
    (hbound : ∀ x∈U,9*|(fderiv ℝ X x).det|⁻¹*‖operatorMatrix (fderiv ℝ X x)‖*
      ‖operatorMatrix (fderiv ℝ X x)‖≤C)
    {r : PhysicalSourcePair} (hr : CompactSmoothPair r) (hs : PairSupported r U)
    (hc : BoundedPhysicallyCorrectable v U r N) :
    BoundedPhysicallyCorrectable u (X '' U) (fun j => localPiolaSource X (r j)) (C*N) := by
  obtain ⟨B,hB,hBc,hBs,hsy,hsrc,hBb⟩ := hc
  have hBs' := hBs.trans hU
  have hsr (j) := (hs j).trans hU
  have hweak (j) (φ : Coord3 → ℝ) (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) :
      (∫ x,fderiv ℝ φ x ((B x*gradientColumns (fderiv ℝ v x)).col j))=-(∫ x,φ x*r j x) := by
    have h := coordinateDivergence_weak (symmetricFlux_smooth hB hv j) (symmetricFlux_compact hBc v j) φ hφ
    change (∫ x,fderiv ℝ φ x ((B x*gradientColumns (fderiv ℝ v x)).col j))=
      -(∫ x,φ x*symmetricSource B v j x) at h
    simpa only [hsrc] using h
  let H := localPiolaTensor X B
  have hH := localPiolaTensor_smooth X hX hXi B hB hBc hBs'
  have hHc := (localPiolaTensor_compact X B hBc hBs').1
  have hHs : tsupport (localPiolaTensor X B)⊆X '' U := by
    have hh : tsupport (localPiolaTensor X B)⊆X '' tsupport B :=
      closure_minimal ((localPiolaTensor_support X B).trans
        (image_mono (fun _ hx => subset_closure hx.1)))
        (hBc.image_of_continuousOn (X.continuousOn.mono hBs')).isClosed
    exact hh.trans (image_mono hBs)
  have hIo : IsOpen (X '' U) := X.isOpen_image_of_subset_source hUo hU
  have hpr : CompactSmoothPair (fun j => localPiolaSource X (r j)) := fun j =>
    ⟨localPiolaSource_smooth X hX hXi (r j) (hr j).1 (hr j).2 (hsr j),
      (localPiolaSource_compact X (r j) (hr j).2 (hsr j)).1⟩
  refine ⟨H,hH,hHc,hHs,localPiolaTensor_isSymm X B hsy,?_,?_⟩
  · apply symmetricSource_eq_of_weak hu hH hHc hpr
    intro j ψ hψ
    have he : (∫ y,fderiv ℝ ψ y ((H y*gradientColumns (fderiv ℝ (v∘X.symm) y)).col j))=
        -(∫ y,ψ y*localPiolaSource X (r j) y) := by
      simp_rw [H,localPiolaTensor_columns X (hX.differentiableOn (by simp))
        (hXi.differentiableOn (by simp)) B v (hv.differentiable (by simp)).differentiableOn]
      have ht := tensorColumn_tsupport B (fun x => gradientColumns (fderiv ℝ v x)) j
      exact localPiolaFlux_weak_source volume X hX hXi _ _
        (hBc.of_isClosed_subset isClosed_closure ht) (hr j).2 (ht.trans hBs') (hsr j) (hweak j) ψ hψ
    refine (integral_congr_ae ?_).trans he
    filter_upwards [] with y
    by_cases hy : y∈X '' U
    · have hf : u =ᶠ[𝓝 y] v∘X.symm :=
        Filter.eventuallyEq_of_mem (hIo.mem_nhds hy) (fun z hz => hpot hz)
      rw [hf.fderiv_eq]
    · have hzero : H y=0 := image_eq_zero_of_notMem_tsupport (fun h => hy (hHs h))
      change (fderiv ℝ ψ y) ((H y*gradientColumns (fderiv ℝ u y)).col j)=_
      simp only [hzero,Matrix.zero_mul]
  · intro y
    exact (localPiolaTensor_bound_of_coefficient X hC hbound B ((subset_tsupport _).trans hBs) y).trans
      (mul_le_mul_of_nonneg_left (hBb _) hC)

theorem physicalSourceMoment_piola_local
    (X : OpenPartialHomeomorph Coord3 Coord3)
    (hX : ContDiffOn ℝ (↑(⊤:ℕ∞)) X X.source)
    (hXi : ContDiffOn ℝ (↑(⊤:ℕ∞)) X.symm X.target)
    {u v : Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u)
    (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v)
    {U : Set Coord3} (hU : U⊆X.source) (hpot : EqOn u (v∘X.symm) (X '' U))
    {r : PhysicalSourcePair} (hr : CompactSmoothPair r) (hs : PairSupported r U) :
    physicalSourceMoment u (fun j => localPiolaSource X (r j))=physicalSourceMoment v r := by
  have hss (j) := (hs j).trans hU
  have hd := hX.differentiableOn (by simp)
  have hdi := hXi.differentiableOn (by simp)
  have hpr : CompactSmoothPair (fun j => localPiolaSource X (r j)) := fun j =>
    ⟨localPiolaSource_smooth X hX hXi (r j) (hr j).1 (hr j).2 (hss j),
      (localPiolaSource_compact X (r j) (hr j).2 (hss j)).1⟩
  have he (j) (φ : Coord3 → ℝ) := localPiolaSource_pairing volume X hd
    (fun _ hx => local_fderiv_det_ne_zero X hd hdi hx) (r j) ((subset_tsupport _).trans (hss j)) φ
  have ht (i j : Fin 2) : (∫ y,u y i*localPiolaSource X (r j) y)=(∫ x,v x i*r j x) := by
    rw [he]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x∈U
    · rw [hpot (mem_image_of_mem X hx),Function.comp_apply,X.left_inv (hU hx)]
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs j h)),mul_zero,mul_zero]
  ext i
  fin_cases i
  · change (∫ y,localPiolaSource X (r 0) y)=(∫ x,r 0 x)
    simpa only [one_mul] using he 0 (fun _ => 1)
  · change (∫ y,localPiolaSource X (r 1) y)=(∫ x,r 1 x)
    simpa only [one_mul] using he 1 (fun _ => 1)
  · change (∫ y,u y 1*localPiolaSource X (r 0) y-u y 0*localPiolaSource X (r 1) y)=
      ∫ x,v x 1*r 0 x-v x 0*r 1 x
    have hi (w : Coord3 → Fin 2 → ℝ) (hw : Continuous w) (s : PhysicalSourcePair)
        (hs : CompactSmoothPair s) (i j : Fin 2) : Integrable (fun x => w x i*s j x) :=
      ((continuous_apply i|>.comp hw).mul (hs j).1.continuous).integrable_of_hasCompactSupport (hs j).2.mul_left
    rw [integral_sub (hi u hu.continuous _ hpr 1 0) (hi u hu.continuous _ hpr 0 1),ht,ht,
      integral_sub (hi v hv.continuous r hr 1 0) (hi v hv.continuous r hr 0 1)]

end ScalarConductivity

end
end

end OAI
