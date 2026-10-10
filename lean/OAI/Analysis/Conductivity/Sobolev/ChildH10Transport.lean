import Mathlib
import OAI.Analysis.Conductivity.Sobolev.ChildCompletionJoin
import OAI.Analysis.Conductivity.Branching.ChildInverse
import OAI.Analysis.Conductivity.Variational.WholeBallJet

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory Filter Topology

lemma gradient_apply_single (f : R3 → ℝ) (x : R3) (i : Fin 3) :
    gradient f x i=fderiv ℝ f x (EuclideanSpace.single i 1) := by
  rw [←toDual_gradient,InnerProductSpace.toDual_apply_apply,EuclideanSpace.inner_single_right]
  simp

lemma sourceChildEuclidean_symm_gradient (σ : ℝ) {f : R3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) (x : R3) (i : Fin 3) :
    gradient (f ∘ (sourceChildEuclidean σ).symm) x i=
      sourceScale⁻¹*gradient f ((sourceChildEuclidean σ).symm x) (childAxis i) := by
  let E : R3 ≃L[ℝ] (Fin 3 → ℝ) := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)
  have hD := E.symm.hasFDerivAt.comp (E x) (sourceChildInverse_hasFDeriv σ (E x))
  have hC := (hf.differentiable (by simp) ((sourceChildEuclidean σ).symm x)).hasFDerivAt.comp x
    (hD.comp x E.hasFDerivAt)
  have hi : E.toContinuousLinearMap (EuclideanSpace.single i 1)=Pi.single i 1 := rfl
  have hj : E.symm.toContinuousLinearMap (Pi.single (childAxis i) 1)=EuclideanSpace.single (childAxis i) 1 := rfl
  rw [gradient_apply_single,gradient_apply_single]
  rw [hC.fderiv,ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply,hi,sourceChildInverse_single,map_smul,hj,map_smul,smul_eq_mul]

def childTransportComponentCLM (k : Fin 2) (i : Fin 4) : JetSpace →L[ℝ]
    Lp ℝ 2 (volume : Measure (Fin 3 → ℝ)) :=
  Fin.cases ((sourceChildPushforwardCLM (actualChildSign k)).comp (ballWholePiComponentCLM 0))
    (fun j => sourceScale⁻¹ • ((sourceChildPushforwardCLM (actualChildSign k)).comp
      (ballWholePiComponentCLM (childAxis j).succ))) i

def childTransportJetCLM (k : Fin 2) : JetSpace →L[ℝ] JetSpace :=
  physicalFourJetCLM.comp (ContinuousLinearMap.pi (childTransportComponentCLM k))

lemma childTransportComponentCLM_smooth_ae (k : Fin 2) (f : R3 → ℝ)
    (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) (hs : tsupport f⊆ball) (i : Fin 4) :
    childTransportComponentCLM k i (smoothH1 f hf).val=ᵐ[volume]
      (fun y => smoothJet (f ∘ (sourceChildEuclidean (actualChildSign k)).symm) (WithLp.toLp 2 y) i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · change sourceChildPushforwardCLM (actualChildSign k) (ballWholePiComponentCLM 0 (smoothH1 f hf).val)=ᵐ[volume] _
    apply (sourceChildPushforwardCLM_ae _ _).trans
    apply ((sourceChildInverse_quasi _).ae_eq_comp (ballWholePiComponentCLM_smooth_ae f hf hs 0)).trans
    exact Filter.Eventually.of_forall (fun y => rfl)
  · simp only [childTransportComponentCLM,Fin.cases_succ,smul_apply,
      ContinuousLinearMap.comp_apply]
    apply (Lp.coeFn_smul _ _).trans
    have he := (sourceChildPushforwardCLM_ae (actualChildSign k)
      (ballWholePiComponentCLM (childAxis j).succ (smoothH1 f hf).val)).trans
      ((sourceChildInverse_quasi _).ae_eq_comp (ballWholePiComponentCLM_smooth_ae f hf hs (childAxis j).succ))
    filter_upwards [he] with y hy
    simp only [Pi.smul_apply,smul_eq_mul,hy,smoothJet,Fin.cases_succ,WithLp.ofLp_toLp]
    exact (sourceChildEuclidean_symm_gradient (actualChildSign k) hf (WithLp.toLp 2 y) j).symm

lemma childTransportJetCLM_smooth (k : Fin 2) (f : R3 → ℝ)
    (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) (hs : tsupport f⊆ball) :
    childTransportJetCLM k (smoothH1 f hf).val=
      (smoothH1 (f ∘ (sourceChildEuclidean (actualChildSign k)).symm)
        (hf.comp (sourceChildEuclidean_symm_contDiff _))).val := by
  apply Lp.ext
  have he (i : Fin 4) := ae_restrict_of_ae (s:=ball)
    ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae_eq_comp
      (childTransportComponentCLM_smooth_ae k f hf hs i))
  filter_upwards [physicalFourJetCLM_ae (fun i => childTransportComponentCLM k i (smoothH1 f hf).val),
    ae_all_iff.mpr he,(smoothJet_memLp (hf.comp (sourceChildEuclidean_symm_contDiff (actualChildSign k)))).coeFn_toLp] with x hx hi hf'
  change physicalFourJetCLM (fun i => childTransportComponentCLM k i (smoothH1 f hf).val) x=_
  change (smoothH1 (f ∘ (sourceChildEuclidean (actualChildSign k)).symm)
    (hf.comp (sourceChildEuclidean_symm_contDiff _))).val x=_ at hf'
  rw [hx,hf']
  ext i
  exact hi i

lemma childTransportJetCLM_H10 (k : Fin 2) {z : JetSpace} (hz : z∈zeroTraceAmbient) :
    childTransportJetCLM k z∈zeroTraceAmbient := by
  let T := zeroTraceAmbient.comap (childTransportJetCLM k).toLinearMap
  have ht : IsClosed (T : Set JetSpace) :=
    (Submodule.isClosed_topologicalClosure (Submodule.span ℝ compactSmoothJets)).preimage
      (childTransportJetCLM k).continuous
  have hs : Submodule.span ℝ compactSmoothJets≤T := by
    apply Submodule.span_le.mpr
    rintro z ⟨f,hf,hc,hs,hL,rfl⟩
    have he : hL.toLp (smoothJet f)=(smoothH1 f hf).val := by apply Lp.ext; exact hL.coeFn_toLp.trans (smoothJet_memLp hf).coeFn_toLp.symm
    change childTransportJetCLM k (hL.toLp (smoothJet f))∈zeroTraceAmbient
    rw [he,childTransportJetCLM_smooth k f hf hs]
    exact smoothH1_mem_H10 _ (hf.comp (sourceChildEuclidean_symm_contDiff _)) (hc.comp_homeomorph (sourceChildEuclidean (actualChildSign k)).symm)
      (sourceChildEuclidean_comp_support k hs)
  exact (Submodule.topologicalClosure_minimal _ hs ht) hz

def childH10Transport (k : Fin 2) : H10 →L[ℝ] H1 :=
  ((childTransportJetCLM k).comp (H1Space.subtypeL.comp H10.subtypeL)).codRestrict H1Space
    (fun u => zeroTraceAmbient_le_H1Space (childTransportJetCLM_H10 k u.property))

lemma childH10Transport_mem_H10 (k : Fin 2) (u : H10) : childH10Transport k u∈H10 :=
  childTransportJetCLM_H10 k u.property

open Set MeasureTheory Filter Topology

variable (s : Fin 3 → ℝ)
  (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
  {a : ℝ} (ha : 0<a) (k : Fin 2)
  {χ : (Fin 3 → ℝ) → ℝ} (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hc : HasCompactSupport χ)
  (hχb : ∀ x,|χ x|≤1)
  (hχs : tsupport χ⊆sourceClosedCollarBand (-2*centralThickness) 0)

def physicalChildCompletionJoin : centralEnergySpace s →L[ℝ] H1 :=
  (childH10Transport k).comp
    ((childCompletionJoin s hs ha k hχ hc hχb hχs).codRestrict H10
      (childCompletionJoin_mem_H10 s hs ha k hχ hc hχb hχs))

lemma physicalChildCompletionJoin_mem_H10 (u : centralEnergySpace s) :
    physicalChildCompletionJoin s hs ha k hχ hc hχb hχs u∈H10 :=
  childH10Transport_mem_H10 k _

lemma physicalChildCompletionJoin_jet (u : centralEnergySpace s) :
    (physicalChildCompletionJoin s hs ha k hχ hc hχb hχs u).val=
      childTransportJetCLM k (childLocalJetCLM s hs ha k hχ hc u.val) := rfl

end

open Set MeasureTheory Filter Topology

variable (s : Fin 3 → ℝ)
  {χ : (Fin 3 → ℝ) → ℝ} (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hc : HasCompactSupport χ)

def centralInteriorComponentCLM (i : Fin 4) : CentralAmbient s →L[ℝ]
    Lp ℝ 2 (volume : Measure (Fin 3 → ℝ)) :=
  Fin.cases ((compactMultiplierCLM hχ.continuous hc).comp
      (centralPhysicalWholeCLM.comp (centralAmbientComponent s 0)))
    (fun j => ((compactMultiplierCLM ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const)
        (hc.fderiv_apply ℝ (Pi.single j 1))).comp
          (centralPhysicalWholeCLM.comp (centralAmbientComponent s 0)))+
      ((compactMultiplierCLM hχ.continuous hc).comp
        (centralPhysicalWholeCLM.comp (centralAmbientComponent s j.succ)))) i

def centralInteriorJetCLM : CentralAmbient s →L[ℝ] JetSpace :=
  physicalFourJetCLM.comp (ContinuousLinearMap.pi (centralInteriorComponentCLM s hχ hc))

lemma centralInteriorComponentCLM_smooth_value
    (hχs : tsupport χ⊆centralPhysical) (f : centralSmoothFunctions) :
    centralInteriorComponentCLM s hχ hc 0 (centralEmbedL s f)=ᵐ[volume]
      (fun y => χ y*f (sourcePairCoordinates y)) := by
  have he := compactMultiplierCLM_ae hχ.continuous hc
    (centralPhysicalWholeCLM (centralSmoothJet f 0))
  filter_upwards [he,centralPhysicalWholeCLM_smooth_ae f 0] with y hy hv
  change (compactMultiplierCLM hχ.continuous hc
    (centralPhysicalWholeCLM (centralSmoothJet f 0))) y=_
  rw [hy,hv]
  by_cases hs : y∈tsupport χ
  · rw [indicator_of_mem (hχs hs)]
    rfl
  · rw [image_eq_zero_of_notMem_tsupport hs]
    simp

lemma centralInteriorComponentCLM_smooth_gradient
    (hχs : tsupport χ⊆centralPhysical) (f : centralSmoothFunctions) (i : Fin 3) :
    centralInteriorComponentCLM s hχ hc i.succ (centralEmbedL s f)=ᵐ[volume]
      (fun y => fderiv ℝ (fun y => χ y*f (sourcePairCoordinates y)) y (Pi.single i 1)) := by
  have hq : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y => f (sourcePairCoordinates y)) :=
    (central_smooth f).comp sourcePairCLE.contDiff
  have he₀ := compactMultiplierCLM_ae ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const)
    (hc.fderiv_apply ℝ (Pi.single i 1)) (centralPhysicalWholeCLM (centralSmoothJet f 0))
  have he₁ := compactMultiplierCLM_ae hχ.continuous hc (centralPhysicalWholeCLM (centralSmoothJet f i.succ))
  apply (Lp.coeFn_add _ _).trans
  filter_upwards [he₀,he₁,centralPhysicalWholeCLM_smooth_ae f 0,
    centralPhysicalWholeCLM_smooth_ae f i.succ] with y h₀ h₁ hv hg
  change (compactMultiplierCLM ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hc.fderiv_apply ℝ (Pi.single i 1)) (centralPhysicalWholeCLM (centralSmoothJet f 0))) y+
    (compactMultiplierCLM hχ.continuous hc (centralPhysicalWholeCLM (centralSmoothJet f i.succ))) y=_
  rw [h₀,h₁,hv,hg]
  change _=fderiv ℝ (χ*(fun y => f (sourcePairCoordinates y))) y (Pi.single i 1)
  rw [fderiv_mul ((hχ.differentiable (by simp)) _) ((hq.differentiable (by simp)) _)]
  simp only [add_apply,smul_apply,smul_eq_mul]
  by_cases hs : y∈tsupport χ
  · rw [indicator_of_mem (hχs hs),indicator_of_mem (hχs hs),central_parent_partial]
    change fderiv ℝ χ y (Pi.single i 1)*f (sourcePairCoordinates y)+χ y*_ =
      χ y*_+f (sourcePairCoordinates y)*fderiv ℝ χ y (Pi.single i 1)
    ring
  · rw [image_eq_zero_of_notMem_tsupport hs,fderiv_of_notMem_tsupport ℝ hs]
    simp

lemma centralInteriorJetCLM_smooth_H10
    (hχs : tsupport χ⊆centralPhysical)
    (hχB : ∀ y∈tsupport χ,WithLp.toLp 2 y∈ball) (f : centralSmoothFunctions) :
    centralInteriorJetCLM s hχ hc (centralEmbedL s f)∈zeroTraceAmbient := by
  let q := fun y => χ y*f (sourcePairCoordinates y)
  let E : R3 ≃L[ℝ] (Fin 3 → ℝ) := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)
  have hq : ContDiff ℝ (↑(⊤:ℕ∞)) q := hχ.mul ((central_smooth f).comp sourcePairCLE.contDiff)
  have hqe : ContDiff ℝ (↑(⊤:ℕ∞)) (q ∘ E) := hq.comp E.contDiff
  have ht : tsupport (q ∘ E)⊆E ⁻¹' tsupport χ :=
    closure_minimal (fun y hy => subset_tsupport χ (fun hc => hy (by simp [q,hc])))
      ((isClosed_tsupport χ).preimage E.continuous)
  have htB : tsupport (q ∘ E)⊆ball := fun x hx => hχB (E x) (ht hx)
  have hmem := smoothH1_mem_H10 (q ∘ E) hqe ((hc.mul_right (f':=fun y => f (sourcePairCoordinates y))).comp_homeomorph E.toHomeomorph) htB
  have he : centralInteriorJetCLM s hχ hc (centralEmbedL s f)=(smoothH1 (q ∘ E) hqe).val := by
    apply Lp.ext
    have ha₀ := ae_restrict_of_ae (s:=ball) ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae_eq_comp
      (centralInteriorComponentCLM_smooth_value s hχ hc hχs f))
    have ha₁ (i : Fin 3) := ae_restrict_of_ae (s:=ball) ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae_eq_comp
      (centralInteriorComponentCLM_smooth_gradient s hχ hc hχs f i))
    filter_upwards [physicalFourJetCLM_ae (fun i => centralInteriorComponentCLM s hχ hc i (centralEmbedL s f)),
      ha₀,ae_all_iff.mpr ha₁,(smoothJet_memLp hqe).coeFn_toLp] with x hj hv hg hs
    change (smoothH1 (q ∘ E) hqe).val x=smoothJet (q ∘ E) x at hs
    rw [hs]
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (congrArg (fun z : JetFiber => z 0) hj).trans hv
    · exact (congrArg (fun z : JetFiber => z j.succ) hj).trans
        ((hg j).trans (gradient_of_pi_function q x j ((hq.differentiable (by simp)) _)).symm)
  rw [he]
  exact hmem

theorem centralInteriorJetCLM_central_H10
    (hχs : tsupport χ⊆centralPhysical)
    (hχB : ∀ y∈tsupport χ,WithLp.toLp 2 y∈ball) (u : centralEnergySpace s) :
    centralInteriorJetCLM s hχ hc u.val∈zeroTraceAmbient := by
  let T := zeroTraceAmbient.comap (centralInteriorJetCLM s hχ hc).toLinearMap
  have ht : IsClosed (T : Set (CentralAmbient s)) :=
    (Submodule.isClosed_topologicalClosure (Submodule.span ℝ compactSmoothJets)).preimage
      (centralInteriorJetCLM s hχ hc).continuous
  have hr : LinearMap.range (centralEmbedL s)≤T := by
    rintro z ⟨f,rfl⟩
    exact centralInteriorJetCLM_smooth_H10 s hχ hc hχs hχB f
  exact (Submodule.topologicalClosure_minimal _ hr ht) u.property

def centralInteriorCompletion (hχs : tsupport χ⊆centralPhysical)
    (hχB : ∀ y∈tsupport χ,WithLp.toLp 2 y∈ball) : centralEnergySpace s →L[ℝ] H1 :=
  ((centralInteriorJetCLM s hχ hc).comp (centralEnergySpace s).subtypeL).codRestrict H1Space
    (fun u => zeroTraceAmbient_le_H1Space (centralInteriorJetCLM_central_H10 s hχ hc hχs hχB u))

lemma centralInteriorCompletion_mem_H10 (hχs : tsupport χ⊆centralPhysical)
    (hχB : ∀ y∈tsupport χ,WithLp.toLp 2 y∈ball) (u : centralEnergySpace s) :
    centralInteriorCompletion s hχ hc hχs hχB u∈H10 :=
  centralInteriorJetCLM_central_H10 s hχ hc hχs hχB u

end ScalarConductivity

end

end OAI
