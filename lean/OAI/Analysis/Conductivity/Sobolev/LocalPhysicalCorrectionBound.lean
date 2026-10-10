import Mathlib
import OAI.Analysis.Conductivity.Variational.PhysicalCorrectionC0
import OAI.Analysis.Conductivity.Variational.CompactPhysicalCorrections
import OAI.Analysis.Conductivity.Sources.PhysicalC1Pullback

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

def closedCorrectionBox (a b : Coord3) : Set Coord3 :=
  boxCoordinates ⁻¹' ((Icc (a 0) (b 0) ×ˢ Icc (a 1) (b 1)) ×ˢ Icc (a 2) (b 2))

lemma closedCorrectionBox_compact (a b : Coord3) : IsCompact (closedCorrectionBox a b) := by
  have hc : IsCompact ((Icc (a 0) (b 0) ×ˢ Icc (a 1) (b 1)) ×ˢ Icc (a 2) (b 2)) :=
    (isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc
  convert hc.image boxCoordinates.symm.continuous using 1
  ext x
  constructor
  · intro hx
    exact ⟨boxCoordinates x,hx,boxCoordinates.symm_apply_apply x⟩
  · rintro ⟨p,hp,rfl⟩
    simpa only [closedCorrectionBox,mem_preimage,boxCoordinates.apply_symm_apply] using hp

lemma correctionBox_subset_closed {a b c d : Coord3}
    (hca : ∀ i,c i≤a i) (hbd : ∀ i,b i≤d i) :
    correctionBox a b⊆closedCorrectionBox c d := by
  intro x hx
  have h := mem_correctionBox.mp hx
  exact ⟨⟨⟨(hca 0).trans (h 0).1.le,(h 0).2.le.trans (hbd 0)⟩,
    ⟨(hca 1).trans (h 1).1.le,(h 1).2.le.trans (hbd 1)⟩⟩,
    ⟨(hca 2).trans (h 2).1.le,(h 2).2.le.trans (hbd 2)⟩⟩

lemma boxCoordinates_symm_norm_le : ‖boxCoordinates.symm.toContinuousLinearMap‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro p
  simp only [one_mul]
  apply pi_norm_le_iff_of_nonneg (norm_nonneg p) |>.mpr
  intro i
  fin_cases i
  · exact (norm_fst_le p.1).trans (norm_fst_le p)
  · exact (norm_snd_le p.1).trans (norm_fst_le p)
  · exact norm_snd_le p

theorem local_physical_symmetric_correction_C0
    (X : OpenPartialHomeomorph Coord3 Coord3)
    (hX : ContDiffOn ℝ (↑(⊤:ℕ∞)) X X.source)
    (hXi : ContDiffOn ℝ (↑(⊤:ℕ∞)) X.symm X.target)
    {a b c d : Coord3} (hab : ∀ i,a i<b i)
    (hca : ∀ i,c i<a i) (hbd : ∀ i,b i<d i)
    (houter : closedCorrectionBox c d⊆X.source)
    (u : Coord3 → Fin 2 → ℝ) (huu : ContDiff ℝ (↑(⊤:ℕ∞)) u)
    (hu : EqOn u (coordinatePair∘X.symm) X.target) :
    ∃ L : ℝ,0<L ∧ ∀ r : PhysicalSourcePair,
      (∀ j,ContDiff ℝ (↑(⊤:ℕ∞)) (r j)) → (∀ j,HasCompactSupport (r j)) →
      (∀ j,tsupport (r j)⊆X '' correctionBox a b) →
      (∀ j,(∫ y,r j y)=0) → (∫ y,u y 1*r 0 y-u y 0*r 1 y)=0 →
      ∀ M : ℝ,0≤M → (∀ j,UniformC1Bound (r j) M) →
      ∃ H : Coord3 → Mat3,ContDiff ℝ (↑(⊤:ℕ∞)) H ∧ HasCompactSupport H ∧
        tsupport H⊆X.target ∧ (∀ y,(H y).IsSymm) ∧
        (∀ j,symmetricSource H u j=r j) ∧ (∀ y,‖H y‖≤L*M) := by
  have hiK := correctionBox_subset_closed (fun i => (hca i).le) (fun i => (hbd i).le)
  have hbox := hiK.trans houter
  obtain ⟨P,hP,hPsolve⟩ := localPiolaSource_inverse_C1 X hX hXi
    (closedCorrectionBox_compact c d) houter
  obtain ⟨L,hL,solve⟩ := physical_box_symmetric_correction_C0 X hX hXi hab hca hbd houter
  refine ⟨L*P,mul_pos hL hP,?_⟩
  intro r hr hc hs hz ht M hM hb
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
  obtain ⟨H,hH,hHc,hHs,hsy,hweak,hHb⟩ := solve (q 0) (q 1)
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
