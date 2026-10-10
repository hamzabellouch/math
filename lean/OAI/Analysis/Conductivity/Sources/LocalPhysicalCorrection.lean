import Mathlib
import OAI.Analysis.Conductivity.Geometry.PhysicalBoxCorrection
import OAI.Analysis.Conductivity.Variational.PhysicalOverlapMoments

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

lemma localPiolaSource_tsupport_image
    (X : OpenPartialHomeomorph Coord3 Coord3) (r : Coord3 → ℝ)
    (hc : HasCompactSupport r) (hs : tsupport r⊆X.source) :
    tsupport (localPiolaSource X r)⊆X '' tsupport r := by
  exact closure_minimal ((localPiolaSource_support X r).trans
    (image_mono (fun _ hx => subset_closure hx.1)))
    (hc.image_of_continuousOn (X.continuousOn.mono hs)).isClosed

lemma localPiolaSource_inverse
    (X : OpenPartialHomeomorph Coord3 Coord3)
    (hX : DifferentiableOn ℝ X X.source) (hXi : DifferentiableOn ℝ X.symm X.target)
    (r : Coord3 → ℝ) (hs : Function.support r⊆X.target) :
    localPiolaSource X (localPiolaSource X.symm r)=r := by
  funext y
  by_cases hy : y∈X.target
  · have he := congrArg (fun D : Coord3 →L[ℝ] Coord3 => D.det)
      (local_fderiv_symm_comp X.symm hXi hX hy)
    simp only [OpenPartialHomeomorph.symm_symm,ContinuousLinearMap.det,
      ContinuousLinearMap.toLinearMap_comp,ContinuousLinearMap.coe_id,
      LinearMap.det_comp,LinearMap.det_id] at he
    have habs : |(fderiv ℝ X (X.symm y)).det| * |(fderiv ℝ X.symm y).det|=1 := by
      rw [←abs_mul]
      exact congrArg abs he |>.trans abs_one
    classical
    change (if y∈X.target then |(fderiv ℝ X (X.symm y)).det|⁻¹ *
      (if X.symm y∈X.source then |(fderiv ℝ X.symm (X (X.symm y))).det|⁻¹ *
        r (X (X.symm y)) else 0) else 0) = r y
    rw [ite_eq_left hy,ite_eq_left (X.map_target hy),X.right_inv hy]
    rw [←mul_assoc,←mul_inv,habs,inv_one,one_mul]
  · rw [localPiolaSource,ite_eq_right hy,Function.notMem_support.mp (fun h => hy (hs h))]

def correctionBox (a b : Fin 3 → ℝ) : Set Coord3 :=
  boxCoordinates ⁻¹' ((Ioo (a 0) (b 0) ×ˢ Ioo (a 1) (b 1)) ×ˢ Ioo (a 2) (b 2))

lemma localPiolaSource_inverse_support
    (X : OpenPartialHomeomorph Coord3 Coord3) (r : Coord3 → ℝ)
    (hc : HasCompactSupport r) {V : Set Coord3} (hV : V⊆X.source)
    (hs : tsupport r⊆X '' V) :
    tsupport (localPiolaSource X.symm r)⊆V := by
  have ht : tsupport r⊆X.target := hs.trans (by rintro y ⟨x,hx,rfl⟩; exact X.map_source (hV hx))
  intro x hx
  obtain ⟨y,hy,rfl⟩ := localPiolaSource_tsupport_image X.symm r hc ht hx
  obtain ⟨z,hz,rfl⟩ := hs hy
  simpa only [X.left_inv (hV hz)] using hz

theorem local_physical_symmetric_correction
    (X : OpenPartialHomeomorph Coord3 Coord3)
    (hX : ContDiffOn ℝ (↑(⊤:ℕ∞)) X X.source)
    (hXi : ContDiffOn ℝ (↑(⊤:ℕ∞)) X.symm X.target)
    {a b : Fin 3 → ℝ} (hab : ∀ i,a i<b i) (hbox : correctionBox a b⊆X.source)
    (u : Coord3 → Fin 2 → ℝ) (hu : EqOn u (coordinatePair∘X.symm) X.target)
    (r : Fin 2 → Coord3 → ℝ)
    (hr : ∀ j,ContDiff ℝ (↑(⊤:ℕ∞)) (r j))
    (hc : ∀ j,HasCompactSupport (r j))
    (hs : ∀ j,tsupport (r j)⊆X '' correctionBox a b)
    (hz : ∀ j,(∫ y,r j y)=0)
    (ht : (∫ y,u y 1*r 0 y-u y 0*r 1 y)=0) :
    ∃ H : Coord3 → Mat3,ContDiff ℝ (↑(⊤:ℕ∞)) H ∧ HasCompactSupport H ∧
      tsupport H⊆X.target ∧ (∀ y,(H y).IsSymm) ∧
      ∀ j (ψ : Coord3 → ℝ),ContDiff ℝ (↑(⊤:ℕ∞)) ψ →
        (∫ y,fderiv ℝ ψ y ((H y*gradientColumns (fderiv ℝ u y)).col j))=
          -(∫ y,ψ y*r j y) := by
  let p : Fin 2 → Coord3 → ℝ := fun j => localPiolaSource X.symm (r j)
  have hst (j) : tsupport (r j)⊆X.target :=
    (hs j).trans (by rintro y ⟨x,hx,rfl⟩; exact X.map_source (hbox hx))
  have hp (j) : ContDiff ℝ (↑(⊤:ℕ∞)) (p j) :=
    localPiolaSource_smooth X.symm hXi hX (r j) (hr j) (hc j) (hst j)
  have hpc (j) : HasCompactSupport (p j) :=
    (localPiolaSource_compact X.symm (r j) (hc j) (hst j)).1
  have hps (j) : tsupport (p j)⊆correctionBox a b :=
    localPiolaSource_inverse_support X (r j) (hc j) hbox (hs j)
  let q : Fin 2 → Box3 → ℝ := fun j => p j∘boxCoordinates.symm
  have hq (j) : ContDiff ℝ (↑(⊤:ℕ∞)) (q j) := (hp j).comp boxCoordinates.symm.contDiff
  have hqc (j) : HasCompactSupport (q j) := (hpc j).comp_homeomorph boxCoordinates.symm.toHomeomorph
  have hqs (j) : tsupport (q j)⊆
      (Ioo (a 0) (b 0) ×ˢ Ioo (a 1) (b 1)) ×ˢ Ioo (a 2) (b 2) := by
    intro z hz
    have h := hps j ((tsupport_comp_subset_preimage (p j) boxCoordinates.symm.continuous) hz)
    simpa only [correctionBox,mem_preimage,boxCoordinates.apply_symm_apply] using h
  have hd := hX.differentiableOn (by simp)
  have hdi := hXi.differentiableOn (by simp)
  have hback (j) : localPiolaSource X (p j)=r j :=
    localPiolaSource_inverse X hd hdi (r j) ((subset_tsupport _).trans (hst j))
  have hqz (j) : (∫ z,q j z)=0 := by
    rw [←boxCoordinates_integral (q j)]
    simp only [q,Function.comp_apply,boxCoordinates.symm_apply_apply]
    have he := localPiolaSource_pairing volume X.symm hdi
      (fun _ hy => local_fderiv_det_ne_zero X.symm hdi hd hy) (r j)
      ((subset_tsupport _).trans (hst j)) (fun _ => 1)
    simpa only [one_mul] using he.trans (by simpa only [one_mul] using hz j)
  have hqt : (∫ z : Box3,z.1.2*q 0 z-z.1.1*q 1 z)=0 := by
    rw [←boxCoordinates_integral (fun z : Box3 => z.1.2*q 0 z-z.1.1*q 1 z)]
    have he := localPiolaSource_torque X hd hdi (p 0) (p 1)
      ((subset_tsupport _).trans ((hps 0).trans hbox))
      ((subset_tsupport _).trans ((hps 1).trans hbox))
    rw [hback 0,hback 1] at he
    simp only [q,Function.comp_apply,boxCoordinates.symm_apply_apply]
    change (∫ x,x 1*p 0 x-x 0*p 1 x)=0
    rw [←he]
    refine (integral_congr_ae ?_).trans ht
    filter_upwards [] with y
    by_cases hy : y∈X.target
    · rw [hu hy]; rfl
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hst 0 h)),
        image_eq_zero_of_notMem_tsupport (fun h => hy (hst 1 h)),mul_zero,mul_zero,mul_zero,mul_zero]
  obtain ⟨H,hH,hHc,hHs,hsy,hweak⟩ := physical_box_symmetric_correction X hX hXi hab hbox
    (hq 0) (hq 1) (hqc 0) (hqc 1) (hqs 0) (hqs 1) (hqz 0) (hqz 1) hqt
  refine ⟨H,hH,hHc,hHs,hsy,?_⟩
  intro j ψ hψ
  have he := hweak j ψ hψ
  have hpsource : (fun x => ![q 0 (boxCoordinates x),q 1 (boxCoordinates x)] j)=p j := by
    funext x
    fin_cases j <;> simp [q]
  rw [hpsource,hback j] at he
  refine (integral_congr_ae ?_).trans he
  filter_upwards [] with y
  by_cases hy : y∈X.target
  · have hf : u =ᶠ[𝓝 y] coordinatePair∘X.symm :=
      Filter.eventuallyEq_of_mem (X.open_target.mem_nhds hy) (fun z hz => hu hz)
    rw [hf.fderiv_eq]
  · rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hHs h)),Matrix.zero_mul,Matrix.zero_mul]

end ScalarConductivity

end

end OAI
