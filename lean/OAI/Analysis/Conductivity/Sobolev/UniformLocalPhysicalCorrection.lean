import Mathlib
import OAI.Analysis.Conductivity.Geometry.ControlledCorrectionBoxes
import OAI.Analysis.Conductivity.Geometry.UniformPhysicalBoxCorrection

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

theorem uniform_local_physical_symmetric_correction_C0
    {I : Type*} (Xs : I → OpenPartialHomeomorph Coord3 Coord3)
    (hXs : ∀ i,ContDiffOn ℝ (↑(⊤:ℕ∞)) (Xs i) (Xs i).source)
    (hXis : ∀ i,ContDiffOn ℝ (↑(⊤:ℕ∞)) (Xs i).symm (Xs i).target)
    {a b c d : Coord3} (hab : ∀ i,a i<b i)
    (hca : ∀ i,c i<a i) (hbd : ∀ i,b i<d i)
    (hboxes : ∀ i,closedCorrectionBox c d⊆(Xs i).source)
    {B : ℝ} (hB : 0<B)
    (hmetric : ∀ i x,x∈closedCorrectionBox c d →
      |inverseSourceWeight (Xs i) x|≤B ∧
      ‖fderiv ℝ (inverseSourceWeight (Xs i)) x‖≤B ∧ ‖fderiv ℝ (Xs i) x‖≤B ∧
      9*|(fderiv ℝ (Xs i) x).det|⁻¹*‖operatorMatrix (fderiv ℝ (Xs i) x)‖*
        ‖operatorMatrix (fderiv ℝ (Xs i) x)‖≤B)
    (us : I → Coord3 → Fin 2 → ℝ) (hus : ∀ i,ContDiff ℝ (↑(⊤:ℕ∞)) (us i))
    (hpot : ∀ i,EqOn (us i) (coordinatePair∘(Xs i).symm) (Xs i).target) :
    ∃ L : ℝ,0<L ∧ ∀ i (r : PhysicalSourcePair),
      CompactSmoothPair r → PairSupported r ((Xs i) '' correctionBox a b) →
      physicalSourceMoment (us i) r=0 → ∀ M : ℝ,0≤M →
      (∀ j,UniformC1Bound (r j) M) →
      BoundedPhysicallyCorrectable (us i) (Xs i).target r (L*M) := by
  have hiK := correctionBox_subset_closed (fun i => (hca i).le) (fun i => (hbd i).le)
  let P := B*(B+1)
  have hP : 0<P := by dsimp [P]; positivity
  obtain ⟨L,hL,solve⟩ := uniform_physical_box_symmetric_correction_C0 Xs hXs hXis hab hca hbd hboxes hB
    (fun i x hx => (hmetric i x hx).2.2.2)
  refine ⟨L*P,mul_pos hL hP,?_⟩
  intro i r hrc hs hm M hM hb
  have hr := fun j => (hrc j).1
  have hc := fun j => (hrc j).2
  have hz (j : Fin 2) : (∫ x,r j x)=0 := by
    fin_cases j
    · exact congrFun hm 0
    · exact congrFun hm 1
  have ht : (∫ x,us i x 1*r 0 x-us i x 0*r 1 x)=0 := congrFun hm 2
  let X := Xs i
  let u := us i
  have hX := hXs i
  have hXi := hXis i
  have huu := hus i
  have hu := hpot i
  have houter := hboxes i
  have hbox := hiK.trans houter
  have hPsolve := localPiolaSource_inverse_C1_of_bounds X hX hXi houter hB
    (fun x hx => ⟨(hmetric i x hx).1,(hmetric i x hx).2.1⟩)
    (fun x hx => (hmetric i x hx).2.2.1)

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
  have hpb (j) : UniformC1Bound (p j) (P*M) :=
    hPsolve (r j) (hr j) (hc j) ((hs j).trans (image_mono hiK)) M hM (hb j)
  have hqb (j) : UniformC1Bound (q j) (P*M) :=
    (hpb j).comp_linear ((hp j).differentiable (by simp)) (mul_nonneg hP.le hM)
      boxCoordinates.symm.toContinuousLinearMap boxCoordinates_symm_norm_le
  obtain ⟨H,hH,hHc,hHs,hsy,hweak,hHb⟩ := solve i (q 0) (q 1)
    (hq 0) (hq 1) (hqc 0) (hqc 1) (hqs 0) (hqs 1) (hqz 0) (hqz 1) hqt
    (P*M) (mul_nonneg hP.le hM) (hqb 0) (hqb 1)
  refine ⟨H,hH,hHc,hHs,hsy,?_,fun y => (hHb y).trans_eq (by ring)⟩
  apply symmetricSource_eq_of_weak huu hH hHc (fun j => ⟨hr j,hc j⟩)
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
end

end OAI
