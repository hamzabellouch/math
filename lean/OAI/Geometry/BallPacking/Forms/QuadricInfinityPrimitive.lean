import Mathlib
import OAI.Geometry.BallPacking.Residues.AreaPolarChart
import OAI.Geometry.BallPacking.Forms.CubicFubiniStudy

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
open Set Function Filter Manifold
open Hamiltonian
variable {m : ℕ} (a : Fin m → ℂ) (ε : Fin m → Bool)

def infinityRegularPhase (y : Plane) : PlanePhase (Option (Fin m)) :=
  affinePhase m (infinityRegularPoint a ε (Complex.equivRealProdCLM.symm y))

def infinityRegularPrimitive (c : ℝ) : Plane → Plane →L[ℝ] ℝ :=
  staticPullbackOneForm (affineFSPrimitive c) (infinityRegularPhase a ε)

theorem infinityRegularPhase_contDiffAt {y : Plane}
    (hy : Complex.equivRealProdCLM.symm y∈infinityRegion a) :
    ContDiffAt ℝ ∞ (infinityRegularPhase a ε) y :=
  (affinePhase m).contDiff.contDiffAt.comp y
    (((infinityRegularPoint_contDiffAt a ε hy).restrict_scalars ℝ).comp y
      Complex.equivRealProdCLM.symm.contDiff.contDiffAt)

theorem infinityRegularPrimitive_contDiffAt (c : ℝ) {y : Plane}
    (hy : Complex.equivRealProdCLM.symm y∈infinityRegion a) :
    ContDiffAt ℝ ∞ (infinityRegularPrimitive a ε c) y :=
  staticPullbackOneForm_smoothAt (affineFSPrimitive_smooth c).contDiffAt
    (infinityRegularPhase_contDiffAt a ε hy)

theorem infinityRegularPrimitive_apply (c : ℝ) {y : Plane}
    (hy : Complex.equivRealProdCLM.symm y∈infinityRegion a) (v : Plane) :
    infinityRegularPrimitive a ε c y v=
      affineFSPrimitive c (affinePhase m (infinityRegularPoint a ε (Complex.equivRealProdCLM.symm y)))
        (affinePhase m (Complex.equivRealProdCLM.symm v,
          fderiv ℂ (infinityRoot a ε) (Complex.equivRealProdCLM.symm y) (Complex.equivRealProdCLM.symm v))) := by
  have hf := realPhaseDerivative_fderiv
    ((infinityRegularPoint_contDiffAt a ε hy).differentiableAt (by simp))
  rw [ContinuousLinearEquiv.apply_symm_apply] at hf
  change affineFSPrimitive c _ (fderiv ℝ (infinityRegularPhase a ε) y v)=_
  change fderiv ℝ (infinityRegularPhase a ε) y = _ at hf
  rw [hf]
  change affineFSPrimitive c _ (affinePhase m
    (fderiv ℂ (infinityRegularPoint a ε) (Complex.equivRealProdCLM.symm y)
      (Complex.equivRealProdCLM.symm v)))=_
  rw [infinityRegularPoint_fderiv a ε hy]
  rfl

variable [Fact (Injective a)] [Fact (∀ j,a j≠0)]

theorem infinityPhase_germ {y : Plane}
    (hy : y∈(infinityDiffeomorph a ε).source) :
    (phaseInclusion a ∘ infinityDiffeomorph a ε)=ᶠ[𝓝 y]
      fun z => affinePhase m (infinityPoint a ε (Complex.equivRealProdCLM.symm z)) := by
  filter_upwards [(infinityDiffeomorph a ε).open_source.mem_nhds hy] with z hz
  have hzD : Complex.equivRealProdCLM.symm z∈infinityDomain a := by
    simpa only [infinityDiffeomorph_source,mem_preimage] using hz
  change affinePhase m ((infinityInverse a ε (Complex.equivRealProdCLM.symm z)).val)=_
  rw [infinityInverse_val a ε hzD.1]

theorem curveFSPrimitive_infinity (c : ℝ) {y : Plane}
    (hy : y∈(infinityDiffeomorph a ε).source) :
    euclideanPullbackOneForm (fun _ => curveFSPrimitive a c) (infinityDiffeomorph a ε) (0,y)=
      infinityRegularPrimitive a ε c y-(c/2) • angularOneForm y := by
  have hD : Complex.equivRealProdCLM.symm y∈infinityDomain a := by
    simpa only [infinityDiffeomorph_source,mem_preimage] using hy
  have hg := infinityPhase_germ a ε hy
  have hd := realPhaseDerivative_fderiv
    ((infinityPoint_contDiffAt a ε hD).differentiableAt (by simp))
  rw [ContinuousLinearEquiv.apply_symm_apply] at hd
  change euclideanPullbackOneForm (fun _ => manifoldPullbackOneForm
    (fun _ => affineFSPrimitive c) (phaseInclusion a) 0) (infinityDiffeomorph a ε) (0,y)=_
  rw [euclideanPullbackOneForm_comp ((phaseInclusion_smooth a).mdifferentiable (by simp) _)
    ((infinityDiffeomorph a ε).mdifferentiableAt (by simp) hy)]
  apply ContinuousLinearMap.ext
  intro v
  change affineFSPrimitive c ((phaseInclusion a ∘ infinityDiffeomorph a ε) y)
    (manifoldMapDifferential (E := PlanePhase (Option (Fin m))) (F := Plane)
      (phaseInclusion a ∘ infinityDiffeomorph a ε) y v)=_
  rw [manifoldMapDifferential,mfderiv_eq_fderiv,hg.eq_of_nhds,hg.fderiv_eq,hd]
  change affineFSPrimitive c (affinePhase m (infinityPoint a ε (Complex.equivRealProdCLM.symm y)))
    (affinePhase m (fderiv ℂ (infinityPoint a ε) (Complex.equivRealProdCLM.symm y)
      (Complex.equivRealProdCLM.symm v)))=_
  rw [infinityPoint_fderiv a ε hD]
  have hp : infinityPoint a ε (Complex.equivRealProdCLM.symm y)=
      ((Complex.equivRealProdCLM.symm y)⁻¹,fun j =>
        infinityRoot a ε (Complex.equivRealProdCLM.symm y) j/(Complex.equivRealProdCLM.symm y)) := by
    simp only [infinityPoint,div_eq_mul_inv,mul_comm]
  rw [hp,affineFSPrimitive_projective_swap c hD.1]
  rw [sub_apply,smul_apply,infinityRegularPrimitive_apply a ε c hD.2]
  have hns : Complex.normSq (Complex.equivRealProdCLM.symm y)=radiusSq y := by
    change y.1*y.1+y.2*y.2=y.1^2+y.2^2
    ring
  have hca : complexArea (Complex.equivRealProdCLM.symm y) (Complex.equivRealProdCLM.symm v)=planarArea y v := by
    rw [complexArea_apply]
    rfl
  simp only [hns,hca,angularOneForm,smul_apply,smul_eq_mul,infinityRegularPoint]
  ring

end PackingSufficiencySupport.DiagonalQuadrics

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff BigOperators
open Set Function
open scoped Manifold Topology
open Manifold
section

variable {ι : Type*} [Fintype ι]

def complexCartesianLinear : (ι → ℂ) ≃ₗ[ℝ] PlanePhase ι where
  toFun z i := ((z i).re,(z i).im)
  invFun z i := ⟨(z i).1,(z i).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a z := by ext i <;> simp [Pi.smul_apply]

def complexCartesian : (ι → ℂ) ≃L[ℝ] PlanePhase ι :=
  complexCartesianLinear.toContinuousLinearEquiv

@[simp] theorem complexCartesian_apply (z : ι → ℂ) (i : ι) :
    complexCartesian z i=((z i).re,(z i).im) := rfl

 def complexPairing (z v : ι → ℂ) : ℂ := ∑ i,star (z i)*v i

theorem complexPairing_re (z v : ι → ℂ) :
    (complexPairing z v).re=phaseDot (complexCartesian z) (complexCartesian v) := by
  simp only [complexPairing,Complex.re_sum,Complex.mul_re,Complex.star_def,
    Complex.conj_re,Complex.conj_im,phaseDot_apply,complexCartesian_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem complexPairing_im (z v : ι → ℂ) :
    (complexPairing z v).im=phaseArea (complexCartesian z) (complexCartesian v) := by
  simp only [complexPairing,Complex.im_sum,Complex.mul_im,Complex.star_def,
    Complex.conj_re,Complex.conj_im,phaseArea_apply,complexCartesian_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem complexCartesian_sq (z : ι → ℂ) :
    phaseSq (complexCartesian z)=∑ i,Complex.normSq (z i) := by
  simp only [phaseSq,phaseDot_apply,complexCartesian_apply,Complex.normSq_apply]

theorem complexPairing_self (z : ι → ℂ) :
    complexPairing z z=(∑ i,Complex.normSq (z i) : ℝ) := by
  simp only [complexPairing,Complex.ofReal_sum,Complex.star_def,← Complex.normSq_eq_conj_mul_self]

theorem complexCartesian_I (z : ι → ℂ) :
    complexCartesian (Complex.I • z)=phaseJ (complexCartesian z) := by
  ext i <;> simp [Pi.smul_apply,Complex.mul_re,Complex.mul_im,phaseJ]

def complexDiagonal (u : ι → ℂ) : (ι → ℂ) →L[ℝ] (ι → ℂ) :=
  ContinuousLinearMap.pi fun i =>
    (u i) • (ContinuousLinearMap.proj i)

omit [Fintype ι] in
@[simp] theorem complexDiagonal_apply (u z : ι → ℂ) (i : ι) :
    complexDiagonal u z i=u i*z i := rfl

def phaseDiagonal (u : ι → ℂ) : PlanePhase ι →L[ℝ] PlanePhase ι :=
  complexCartesian.toContinuousLinearMap.comp
    ((complexDiagonal u).comp complexCartesian.symm.toContinuousLinearMap)

@[simp] theorem phaseDiagonal_cartesian (u z : ι → ℂ) :
    phaseDiagonal u (complexCartesian z)=complexCartesian (complexDiagonal u z) := by
  simp only [phaseDiagonal,ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply]

theorem complexDiagonal_pairing (u z v : ι → ℂ) (hu : ∀ i,Complex.normSq (u i)=1) :
    complexPairing (complexDiagonal u z) (complexDiagonal u v)=complexPairing z v := by
  apply Finset.sum_congr rfl
  intro i _
  simp only [complexDiagonal_apply,star_mul,Complex.star_def]
  calc
    starRingEnd ℂ (z i)*starRingEnd ℂ (u i)*(u i*v i)=
        (starRingEnd ℂ (u i)*u i)*(starRingEnd ℂ (z i)*v i) := by ring
    _=starRingEnd ℂ (z i)*v i := by rw [←Complex.normSq_eq_conj_mul_self,hu]; simp

theorem phaseDiagonal_dot (u : ι → ℂ) (hu : ∀ i,Complex.normSq (u i)=1)
    (z v : PlanePhase ι) : phaseDot (phaseDiagonal u z) (phaseDiagonal u v)=phaseDot z v := by
  obtain ⟨z,rfl⟩ := complexCartesian.surjective z
  obtain ⟨v,rfl⟩ := complexCartesian.surjective v
  rw [phaseDiagonal_cartesian,phaseDiagonal_cartesian,←complexPairing_re,←complexPairing_re,
    complexDiagonal_pairing u z v hu]

theorem phaseDiagonal_area (u : ι → ℂ) (hu : ∀ i,Complex.normSq (u i)=1)
    (z v : PlanePhase ι) : phaseArea (phaseDiagonal u z) (phaseDiagonal u v)=phaseArea z v := by
  obtain ⟨z,rfl⟩ := complexCartesian.surjective z
  obtain ⟨v,rfl⟩ := complexCartesian.surjective v
  rw [phaseDiagonal_cartesian,phaseDiagonal_cartesian,←complexPairing_im,←complexPairing_im,
    complexDiagonal_pairing u z v hu]

def phaseUnitDiagonal (u : ι → ℂ) (hu : ∀ i,Complex.normSq (u i)=1) :
    PlanePhase ι ≃L[ℝ] PlanePhase ι where
  toLinearEquiv :=
    { toLinearMap := (phaseDiagonal u).toLinearMap
      invFun := phaseDiagonal (fun i => star (u i))
      left_inv := by
        intro z
        obtain ⟨z,rfl⟩ := complexCartesian.surjective z
        change phaseDiagonal (fun i => star (u i)) (phaseDiagonal u (complexCartesian z))=complexCartesian z
        simp only [phaseDiagonal_cartesian]
        congr 1
        ext i
        simp only [complexDiagonal_apply,←mul_assoc,←Complex.normSq_eq_conj_mul_self,hu,
          Complex.ofReal_one,one_mul,Complex.star_def]
      right_inv := by
        intro z
        obtain ⟨z,rfl⟩ := complexCartesian.surjective z
        change phaseDiagonal u (phaseDiagonal (fun i => star (u i)) (complexCartesian z))=complexCartesian z
        simp only [phaseDiagonal_cartesian]
        congr 1
        ext i
        simp only [complexDiagonal_apply,←mul_assoc,Complex.star_def]
        rw [mul_comm (u i),←Complex.normSq_eq_conj_mul_self,hu]
        simp only [Complex.ofReal_one,one_mul] }
  continuous_toFun := (phaseDiagonal u).continuous
  continuous_invFun := (phaseDiagonal (fun i => star (u i))).continuous

@[simp] theorem phaseUnitDiagonal_apply (u : ι → ℂ) (hu : ∀ i,Complex.normSq (u i)=1)
    (z : PlanePhase ι) : phaseUnitDiagonal u hu z=phaseDiagonal u z := rfl

def complexAffineLift (z : ι → ℂ) : Option ι → ℂ
  | none => 1
  | some i => z i

def complexAffineQuotient (y : Option ι → ℂ) : ι → ℂ := fun i => y (some i)/y none

def affineSphereScale (z : ι → ℂ) : ℝ := (Real.sqrt (1+phaseSq (complexCartesian z)))⁻¹

def complexSphereLift (z : ι → ℂ) : Option ι → ℂ := affineSphereScale z • complexAffineLift z

omit [Fintype ι] in
@[simp] theorem complexAffineLift_none (z : ι → ℂ) : complexAffineLift z none=1 := rfl
omit [Fintype ι] in
@[simp] theorem complexAffineLift_some (z : ι → ℂ) (i : ι) : complexAffineLift z (some i)=z i := rfl

theorem complexAffineLift_smooth : ContDiff ℝ ∞ (complexAffineLift (ι := ι)) := by
  apply contDiff_pi.mpr
  intro i
  cases i with
  | none => exact contDiff_const
  | some i => exact contDiff_apply ℝ ℂ i

theorem complexAffineLift_sq (z : ι → ℂ) :
    phaseSq (complexCartesian (complexAffineLift z))=1+phaseSq (complexCartesian z) := by
  rw [complexCartesian_sq,complexCartesian_sq]
  simp [Fintype.sum_option]

theorem affineSphereScale_pos (z : ι → ℂ) : 0<affineSphereScale z :=
  inv_pos.mpr (Real.sqrt_pos.mpr (by linarith [phaseSq_nonneg (complexCartesian z)]))

theorem affineSphereScale_smooth : ContDiff ℝ ∞ (affineSphereScale (ι := ι)) := by
  apply ContDiff.inv
  · apply ContDiff.sqrt
    · exact contDiff_const.add (phaseSq_smooth.comp (complexCartesian (ι := ι)).contDiff)
    · intro z
      exact ne_of_gt (by linarith [phaseSq_nonneg (complexCartesian z)])
  · intro z
    exact (Real.sqrt_pos.mpr (by linarith [phaseSq_nonneg (complexCartesian z)])).ne'

theorem complexSphereLift_smooth : ContDiff ℝ ∞ (complexSphereLift (ι := ι)) :=
  affineSphereScale_smooth.smul complexAffineLift_smooth

theorem complexSphereLift_sq (z : ι → ℂ) : phaseSq (complexCartesian (complexSphereLift z))=1 := by
  rw [complexSphereLift,map_smul,phaseSq_smul,complexAffineLift_sq]
  have hp : 0≤1+phaseSq (complexCartesian z) := by linarith [phaseSq_nonneg (complexCartesian z)]
  dsimp [affineSphereScale]
  rw [inv_pow,Real.sq_sqrt hp]
  exact inv_mul_cancel₀ (ne_of_gt (by linarith [phaseSq_nonneg (complexCartesian z)]))

theorem complexSphereLift_none_ne (z : ι → ℂ) : complexSphereLift z none≠0 := by
  change (affineSphereScale z : ℂ)*1≠0
  simpa using Complex.ofReal_ne_zero.mpr (affineSphereScale_pos z).ne'

theorem complexAffineQuotient_smoothAt {y : Option ι → ℂ} (hy : y none≠0) :
    ContDiffAt ℝ ∞ complexAffineQuotient y := by
  apply contDiffAt_pi.mpr
  intro i
  simp only [complexAffineQuotient,div_eq_mul_inv]
  exact (contDiff_apply ℝ ℂ (some i)).contDiffAt.mul
    ((contDiff_apply ℝ ℂ none).contDiffAt.inv hy)

omit [Fintype ι] in
theorem complexAffineQuotient_smul (ζ : ℂ) (hζ : ζ≠0) (y : Option ι → ℂ) :
    complexAffineQuotient (ζ•y)=complexAffineQuotient y := by
  ext i
  simp only [complexAffineQuotient,Pi.smul_apply,smul_eq_mul]
  exact mul_div_mul_left (y (some i)) (y none) hζ

omit [Fintype ι] in
@[simp] theorem complexAffineQuotient_lift (z : ι → ℂ) :
    complexAffineQuotient (complexAffineLift z)=z := by ext i; simp [complexAffineQuotient]

@[simp] theorem complexAffineQuotient_sphereLift (z : ι → ℂ) :
    complexAffineQuotient (complexSphereLift z)=z := by
  change complexAffineQuotient ((affineSphereScale z : ℂ) • complexAffineLift z)=z
  rw [complexAffineQuotient_smul _ (Complex.ofReal_ne_zero.mpr (affineSphereScale_pos z).ne'),
    complexAffineQuotient_lift]

omit [Fintype ι] in
theorem complexAffineLift_quotient {y : Option ι → ℂ} (hy : y none≠0) :
    complexAffineLift (complexAffineQuotient y)=(y none)⁻¹•y := by
  ext i
  cases i with
  | none => simpa only [complexAffineLift_none,Pi.smul_apply,smul_eq_mul] using (inv_mul_cancel₀ hy).symm
  | some i => simp [complexAffineQuotient,div_eq_mul_inv,mul_comm]

theorem complexCartesian_complex_smul_sq (ζ : ℂ) (y : ι → ℂ) :
    phaseSq (complexCartesian (ζ•y))=Complex.normSq ζ*phaseSq (complexCartesian y) := by
  simp only [complexCartesian_sq,Pi.smul_apply,smul_eq_mul,map_mul,Finset.mul_sum]

theorem complexSphereLift_quotient_unit {y : Option ι → ℂ}
    (hy : y none≠0) (hys : phaseSq (complexCartesian y)=1) :
    ∃ ζ : ℂ,Complex.normSq ζ=1 ∧ complexSphereLift (complexAffineQuotient y)=ζ•y := by
  let ζ : ℂ := (affineSphereScale (complexAffineQuotient y) : ℂ)*(y none)⁻¹
  have he : complexSphereLift (complexAffineQuotient y)=ζ•y := by
    change (affineSphereScale (complexAffineQuotient y) : ℂ) •
      complexAffineLift (complexAffineQuotient y)=ζ•y
    rw [complexAffineLift_quotient hy,smul_smul]
  refine ⟨ζ,?_,he⟩
  have h := complexSphereLift_sq (complexAffineQuotient y)
  rw [he,complexCartesian_complex_smul_sq,hys,mul_one] at h
  exact h

end
section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

def parameterPullbackOneForm (α : ℝ → ManifoldOneForm E M) (g : ℝ × N → M)
    (s t : ℝ) : ManifoldOneForm F N :=
  manifoldPullbackOneForm α (fun x => g (s,x)) t

omit [IsManifold 𝓘(ℝ,E) ∞ M] in

theorem chart_parameterPullbackOneForm {α : ℝ → ManifoldOneForm E M} {g : ℝ × N → M}
    (hg : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,F)) 𝓘(ℝ,E) ∞ g)
    (c : N) (s t : ℝ) {y : F} (hy : y ∈ (extChartAt 𝓘(ℝ,F) c).target) :
    chartOneForm (parameterPullbackOneForm α g s t) c y =
      (euclideanPullbackOneForm α
        (fun q : ℝ × F => g (q.1,(extChartAt 𝓘(ℝ,F) c).symm q.2)) (t,(s,y))).comp
          (ContinuousLinearMap.inr ℝ ℝ F) := by
  have hs : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ (fun x => g (s,x)) :=
    hg.comp (contMDiff_const.prodMk contMDiff_id)
  rw [parameterPullbackOneForm,chartOneForm_manifoldPullback (α := α) (p := (t,y)) hs hy]
  let h : ℝ × F → M := fun q => g (q.1,(extChartAt 𝓘(ℝ,F) c).symm q.2)
  have hc := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,F)) (n := ∞) c).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) c).mem_nhds hy)
  have hh : ContMDiffAt 𝓘(ℝ,ℝ × F) 𝓘(ℝ,E) ∞ h (s,y) :=
    hg.contMDiffAt.comp (s,y) (contDiffAt_fst.contMDiffAt.prodMk
      (hc.comp (s,y) contDiffAt_snd.contMDiffAt))
  have hi : HasMFDerivAt 𝓘(ℝ,F) 𝓘(ℝ,ℝ × F) (fun z => (s,z)) y
      (ContinuousLinearMap.inr ℝ ℝ F) := by
    apply hasMFDerivAt_iff_hasFDerivAt.mpr
    convert! ((hasFDerivAt_const (𝕜 := ℝ) s y).prodMk (hasFDerivAt_id (𝕜 := ℝ) y)) using 1
  have hd := ((hh.mdifferentiableAt (by simp)).hasMFDerivAt.comp y hi).mfderiv
  simp only [euclideanPullbackOneForm]
  rw [show mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E)
    ((fun x => g (s,x)) ∘ (extChartAt 𝓘(ℝ,F) c).symm) y = _ from hd]
  ext v
  rfl

theorem parameterPullbackOneForm_smooth
    {α : ℝ → ManifoldOneForm E M} {g : ℝ × N → M}
    (hg : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,F)) 𝓘(ℝ,E) ∞ g)
    (hα : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartOneForm (α q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target)) (c : N) :
    ContDiffOn ℝ ∞ (fun q : ℝ × (ℝ × F) =>
      chartOneForm (parameterPullbackOneForm α g q.1 q.2.1) c q.2.2)
      (univ ×ˢ (univ ×ˢ (extChartAt 𝓘(ℝ,F) c).target)) := by
  intro p hp
  let h : ℝ × F → M := fun q => g (q.1,(extChartAt 𝓘(ℝ,F) c).symm q.2)
  have hc := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,F)) (n := ∞) c).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) c).mem_nhds hp.2.2)
  have hh : ContMDiffAt 𝓘(ℝ,ℝ × F) 𝓘(ℝ,E) ∞ h (p.1,p.2.2) :=
    hg.contMDiffAt.comp (p.1,p.2.2) (contDiffAt_fst.contMDiffAt.prodMk
      (hc.comp (p.1,p.2.2) contDiffAt_snd.contMDiffAt))
  have hs := ((euclideanPullbackOneForm_contDiffAt (p := (p.2.1,(p.1,p.2.2))) hα hh).comp p
    (contDiffAt_snd.fst.prodMk (contDiffAt_fst.prodMk contDiffAt_snd.snd))).clm_comp
      (contDiffAt_const (c := ContinuousLinearMap.inr ℝ ℝ F))
  apply (hs.congr_of_eventuallyEq _).contDiffWithinAt
  have ht := continuousAt_snd.snd.preimage_mem_nhds
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) c).mem_nhds hp.2.2)
  filter_upwards [ht] with q hq
  exact chart_parameterPullbackOneForm hg c q.1 q.2.1 hq

end
section

variable {P Q E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

omit [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
theorem SmoothOneFormFamily.add {α β : P → ManifoldOneForm E M}
    (hα : SmoothOneFormFamily α) (hβ : SmoothOneFormFamily β) :
    SmoothOneFormFamily (fun p => α p+β p) := by
  intro c
  simpa only [chartOneForm_add] using (hα c).add (hβ c)

omit [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
theorem SmoothOneFormFamily.smul {α : P → ManifoldOneForm E M}
    (hα : SmoothOneFormFamily α) {f : P → ℝ} (hf : ContDiff ℝ ∞ f) :
    SmoothOneFormFamily (fun p => f p • α p) := by
  intro c
  simpa only [chartOneForm_smul,Function.comp_apply,Pi.smul_def'] using
    (hf.comp contDiff_fst).contDiffOn.smul (hα c)

theorem SmoothOneFormFamily.comp {α : P → ManifoldOneForm E M}
    (hα : SmoothOneFormFamily α) {f : Q → P} (hf : ContDiff ℝ ∞ f) :
    SmoothOneFormFamily (α ∘ f) := by
  intro c
  have hm : ContDiffOn ℝ ∞ (fun q : Q × E => (f q.1,q.2))
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target) :=
    ((hf.comp contDiff_fst).prodMk contDiff_snd).contDiffOn
  exact (hα c).comp hm (fun _ hq => ⟨mem_univ _,hq.2⟩)

end
section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

 def movingPrimitivePullback (α : F → F →L[ℝ] ℝ) (g : ℝ × M → F)
    (t : ℝ) : ManifoldOneForm E M :=
  manifoldPullbackOneForm (fun _ => α) (fun x => g (t,x)) 0

 theorem movingPrimitivePullback_smooth {α : F → F →L[ℝ] ℝ} {g : ℝ × M → F}
    (hα : ContDiff ℝ ∞ α)
    (hg : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,F) ∞ g) :
    SmoothOneFormFamily (movingPrimitivePullback (E := E) α g) := by
  have hα' : SmoothOneFormFamily (fun _ : ℝ => α) := vector_oneForm_smooth hα
  intro c
  exact (parameterPullbackOneForm_smooth (E := F) (F := E) (M := F) (N := M) (α := fun _ : ℝ => α) hg hα' c).comp
    ((contDiff_fst.prodMk (contDiff_const.prodMk contDiff_snd)).contDiffOn)
    (fun p hp => ⟨mem_univ _,mem_univ _,hp.2⟩)

 theorem movingPrimitivePullback_exterior {α : F → F →L[ℝ] ℝ} {g : ℝ × M → F}
    (hα : ContDiff ℝ ∞ α)
    (hg : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,F) ∞ g) (t : ℝ) (x : M) :
    manifoldExteriorOneForm (movingPrimitivePullback (E := E) α g t) x=
      (euclideanExteriorOneForm α (g (t,x))).bilinearComp
        (manifoldMapDifferential (E := F) (F := E) (fun y => g (t,y)) x)
        (manifoldMapDifferential (E := F) (F := E) (fun y => g (t,y)) x) := by
  have hh := manifold_pullback_exterior (α := α) (g := fun y => g (t,y))
    (fun c => by
      rw [show chartOneForm α c=α from funext (vector_chartOneForm α c)]
      exact hα.contDiffOn)
    (hg.comp (contMDiff_const.prodMk contMDiff_id)) x
  simpa only [movingPrimitivePullback,manifoldPullbackTwoForm,vector_exteriorOneForm] using hh

end

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def extendManifoldOneForm (U : Set M) (α : ManifoldOneForm E M) : ManifoldOneForm E M := by
  classical
  exact U.indicator α

omit [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M] in
@[simp] theorem extendManifoldOneForm_inside {U : Set M} {α : ManifoldOneForm E M}
    {x : M} (hx : x ∈ U) : extendManifoldOneForm U α x=α x := by
  classical
  exact Set.indicator_of_mem hx α

omit [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M] in
@[simp] theorem extendManifoldOneForm_outside {U : Set M} {α : ManifoldOneForm E M}
    {x : M} (hx : x ∉ U) : extendManifoldOneForm U α x=0 := by
  classical
  exact Set.indicator_of_notMem hx α

theorem extendManifoldOneForm_smooth {U K : Set M} (hU : IsOpen U) (hK : IsClosed K)
    (hKU : K ⊆ U) {α : P → ManifoldOneForm E M}
    (hα : ∀ c, ContDiffOn ℝ ∞ (fun q : P × E => chartOneForm (α q.1) c q.2)
      (univ ×ˢ ((extChartAt 𝓘(ℝ,E) c).target ∩ (extChartAt 𝓘(ℝ,E) c).symm ⁻¹' U)))
    (hz : ∀ p x, x ∈ U → x ∉ K → α p x=0) :
    SmoothOneFormFamily (fun p => extendManifoldOneForm U (α p)) := by
  intro c p hp
  let x := (extChartAt 𝓘(ℝ,E) c).symm p.2
  have hi := ((contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) c).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c).mem_nhds hp.2)).continuousAt
  by_cases hx : x ∈ U
  · have hn := (hi.comp continuousAt_snd).preimage_mem_nhds (hU.mem_nhds hx)
    have ht := continuousAt_snd.preimage_mem_nhds
      ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c).mem_nhds hp.2)
    have hnh : univ ×ˢ ((extChartAt 𝓘(ℝ,E) c).target ∩
        (extChartAt 𝓘(ℝ,E) c).symm ⁻¹' U) ∈ 𝓝 p := by
      filter_upwards [hn,ht] with q hq hqt
      exact ⟨mem_univ _,hqt,hq⟩
    apply (((hα c).contDiffAt hnh).congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [hn] with q hq
    change (extendManifoldOneForm U (α q.1) ((extChartAt 𝓘(ℝ,E) c).symm q.2)).comp _ = _
    change (extChartAt 𝓘(ℝ,E) c).symm q.2 ∈ U at hq
    rw [extendManifoldOneForm_inside hq]
    rfl
  · have hxK : x ∉ K := fun hk => hx (hKU hk)
    have hn := (hi.comp continuousAt_snd).preimage_mem_nhds (hK.isOpen_compl.mem_nhds hxK)
    apply ((contDiffAt_const (c := (0 : E →L[ℝ] ℝ))).congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [hn] with q hq
    change (extendManifoldOneForm U (α q.1) ((extChartAt 𝓘(ℝ,E) c).symm q.2)).comp _ = 0
    by_cases hu : (extChartAt 𝓘(ℝ,E) c).symm q.2 ∈ U
    · rw [extendManifoldOneForm_inside hu,hz _ _ hu hq]
      exact ContinuousLinearMap.zero_comp _
    · rw [extendManifoldOneForm_outside hu]
      exact ContinuousLinearMap.zero_comp _

omit [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M] in

theorem extendManifoldOneForm_compact [T2Space M] {U K : Set M} (hK : IsCompact K)
    {α : ManifoldOneForm E M} (hz : ∀ x ∈ U, x ∉ K → α x=0) :
    HasCompactSupport (extendManifoldOneForm U α) := by
  apply HasCompactSupport.intro hK
  intro x hx
  by_cases hu : x ∈ U
  · rw [extendManifoldOneForm_inside hu,hz x hu hx]
  · exact extendManifoldOneForm_outside hu

theorem manifoldExteriorOneForm_congr_of_eventuallyEq {α β : ManifoldOneForm E M}
    {x : M} (he : α =ᶠ[𝓝 x] β) : manifoldExteriorOneForm α x=manifoldExteriorOneForm β x := by
  have hx : x ∈ (extChartAt 𝓘(ℝ,E) x).source := mem_extChartAt_source x
  have hxt := (extChartAt 𝓘(ℝ,E) x).map_source hx
  have hi := ((contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) x).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) x).mem_nhds hxt)).continuousAt
  have hh : chartOneForm α x =ᶠ[𝓝 (extChartAt 𝓘(ℝ,E) x x)] chartOneForm β x := by
    have he' : α =ᶠ[𝓝 ((extChartAt 𝓘(ℝ,E) x).symm (extChartAt 𝓘(ℝ,E) x x))] β := by
      rw [(extChartAt 𝓘(ℝ,E) x).left_inv hx]
      exact he
    have hn := he'.comp_tendsto hi
    filter_upwards [hn] with y hy
    simp only [chartOneForm]
    change α ((extChartAt 𝓘(ℝ,E) x).symm y)=β ((extChartAt 𝓘(ℝ,E) x).symm y) at hy
    rw [hy]
  unfold manifoldExteriorOneForm euclideanExteriorOneForm
  rw [hh.fderiv_eq]

theorem extendManifoldOneForm_exterior_inside {U : Set M} (hU : IsOpen U)
    (α : ManifoldOneForm E M) {x : M} (hx : x ∈ U) :
    manifoldExteriorOneForm (extendManifoldOneForm U α) x=manifoldExteriorOneForm α x := by
  apply manifoldExteriorOneForm_congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds hx] with y hy
  exact extendManifoldOneForm_inside hy

end PackingSufficiencySupport.Hamiltonian
end

end OAI
