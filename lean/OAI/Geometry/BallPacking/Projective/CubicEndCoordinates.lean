import Mathlib
import OAI.Geometry.BallPacking.Projective.AnnularChartHelpers

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Filter Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian

abbrev AffineIndex := Option (Fin 1)
abbrev HomogeneousIndex := Option AffineIndex
abbrev EndIndex := Fin 2 → Bool

def zeroEnd : EndIndex := fun _ => false

def endQuotient (ε : EndIndex) (s : ℂ) : AffineIndex → ℂ
  | none => (infinityRoot (parameters 0) ε s 0-1)/s
  | some _ => (infinityRoot (parameters 0) ε s 1-1)/s

def removableCoordinate (s : ℂ) (j : Fin 2) : ℂ :=
  -(parameters 0 j)*s/(infinityRoot (parameters 0) zeroEnd s j+1)

def endRemovable (s : ℂ) : AffineIndex → ℂ
  | none => removableCoordinate s 0
  | some _ => removableCoordinate s 1

def endHomogeneous (ε : EndIndex) (s : ℂ) : HomogeneousIndex → ℂ
  | none => s
  | some none => infinityRoot (parameters 0) ε s 0-1
  | some (some _) => infinityRoot (parameters 0) ε s 1-1

def endRegular (ε : EndIndex) (s : ℂ) : HomogeneousIndex → ℂ :=
  if ε=zeroEnd then complexAffineLift (endRemovable s) else endHomogeneous ε s

def endRegularRegion : Set ℂ := infinityRegion (parameters 0) ∩
  {s | ∀ j : Fin 2,infinityRoot (parameters 0) zeroEnd s j+1≠0}

 theorem endRegularRegion_open : IsOpen endRegularRegion := by
  apply isOpen_iff_mem_nhds.mpr
  intro s hs
  have hroot (j : Fin 2) : ContinuousAt
      (fun t => infinityRoot (parameters 0) zeroEnd t j+1) s :=
    ((contDiffAt_pi.mp (infinityRoot_contDiffAt _ zeroEnd hs.1) j).add
      contDiffAt_const).continuousAt
  have he : ∀ᶠ t in 𝓝 s, ∀ j : Fin 2,
      infinityRoot (parameters 0) zeroEnd t j+1≠0 := by
    apply Filter.eventually_all.mpr
    intro j
    exact (hroot j).eventually_ne (hs.2 j)
  filter_upwards [(infinityRegion_open _).mem_nhds hs.1,he] with t ht ht'
  exact ⟨ht,ht'⟩

 theorem zero_mem_endRegularRegion : (0:ℂ)∈endRegularRegion := by
  refine ⟨zero_mem_infinityRegion _,?_⟩
  intro j
  simp [infinityRoot,zeroEnd,endSign]

 theorem endHomogeneous_contDiffAt (ε : EndIndex) {s : ℂ}
    (hs : s∈infinityRegion (parameters 0)) : ContDiffAt ℂ ∞ (endHomogeneous ε) s := by
  apply contDiffAt_pi.mpr
  intro j
  cases j with
  | none => exact contDiffAt_id
  | some j =>
    cases j with
    | none => exact (contDiffAt_pi.mp (infinityRoot_contDiffAt _ ε hs) 0).sub contDiffAt_const
    | some _ => exact (contDiffAt_pi.mp (infinityRoot_contDiffAt _ ε hs) 1).sub contDiffAt_const

 theorem endQuotient_contDiffAt (ε : EndIndex) {s : ℂ}
    (hs : s∈infinityDomain (parameters 0)) : ContDiffAt ℂ ∞ (endQuotient ε) s := by
  apply contDiffAt_pi.mpr
  intro j
  cases j with
  | none => exact ((contDiffAt_pi.mp (infinityRoot_contDiffAt _ ε hs.2) 0).sub
      contDiffAt_const).div contDiffAt_id hs.1
  | some _ => exact ((contDiffAt_pi.mp (infinityRoot_contDiffAt _ ε hs.2) 1).sub
      contDiffAt_const).div contDiffAt_id hs.1

 theorem endRemovable_contDiffAt {s : ℂ} (hs : s∈endRegularRegion) :
    ContDiffAt ℂ ∞ endRemovable s := by
  have hd (j : Fin 2) : ContDiffAt ℂ ∞ (fun s => removableCoordinate s j) s := by
    exact (contDiffAt_const.mul contDiffAt_id).div
      ((contDiffAt_pi.mp (infinityRoot_contDiffAt _ zeroEnd hs.1) j).add contDiffAt_const) (hs.2 j)
  apply contDiffAt_pi.mpr
  intro j
  cases j with
  | none => exact hd 0
  | some _ => exact hd 1

 theorem endRegular_contDiffAt (ε : EndIndex) {s : ℂ} (hs : s∈endRegularRegion) :
    ContDiffAt ℂ ∞ (endRegular ε) s := by
  by_cases he : ε=zeroEnd
  · have hh : endRegular ε=fun t => complexAffineLift (endRemovable t) := by
      funext t
      exact ite_eq_left he
    rw [hh]
    apply contDiffAt_pi.mpr
    intro j
    cases j with
    | none => exact contDiffAt_const
    | some j => exact contDiffAt_pi.mp (endRemovable_contDiffAt hs) j
  · have hh : endRegular ε=endHomogeneous ε := by
      funext t
      exact ite_eq_right he
    rw [hh]
    exact endHomogeneous_contDiffAt ε hs.1

 theorem endHomogeneous_ne_zero {ε : EndIndex} (hε : ε≠zeroEnd) (s : ℂ) :
    endHomogeneous ε s≠0 := by
  intro hz
  have hs : s=0 := congrFun hz none
  apply hε
  funext j
  fin_cases j
  · have h := congrFun hz (some none)
    change infinityRoot (parameters 0) ε s 0-1=0 at h
    rw [hs] at h
    cases hh : ε 0
    · exact hh
    · norm_num [infinityRoot,hh,endSign] at h
  · have h := congrFun hz (some (some 0))
    change infinityRoot (parameters 0) ε s 1-1=0 at h
    rw [hs] at h
    cases hh : ε 1
    · exact hh
    · norm_num [infinityRoot,hh,endSign] at h

 theorem endRegular_ne_zero (ε : EndIndex) (s : ℂ) : endRegular ε s≠0 := by
  by_cases he : ε=zeroEnd
  · simp only [endRegular,ite_eq_left he]
    intro h
    have hh := congrFun h none
    exact one_ne_zero hh
  · simpa only [endRegular,ite_eq_right he] using endHomogeneous_ne_zero he s

 theorem endRegular_cartesian_ne_zero (ε : EndIndex) (s : ℂ) :
    complexCartesian (endRegular ε s)≠0 := by
  intro h
  apply endRegular_ne_zero ε s
  exact complexCartesian.injective (by simpa only [map_zero] using h)

 theorem removableCoordinate_eq {s : ℂ} (hs : s≠0) (hR : s∈endRegularRegion) (j : Fin 2) :
    (infinityRoot (parameters 0) zeroEnd s j-1)/s=removableCoordinate s j := by
  have hq := infinityRoot_sq (parameters 0) zeroEnd s j
  dsimp [removableCoordinate]
  apply (div_eq_div_iff hs (hR.2 j)).mpr
  linear_combination hq

 theorem endQuotient_zeroEnd {s : ℂ} (hs : s≠0) (hR : s∈endRegularRegion) :
    endQuotient zeroEnd s=endRemovable s := by
  funext j
  cases j with
  | none => exact removableCoordinate_eq hs hR 0
  | some _ => exact removableCoordinate_eq hs hR 1

 theorem endQuotient_homogeneous {ε : EndIndex} (hε : ε≠zeroEnd) {s : ℂ} (hs : s≠0) :
    complexAffineLift (endQuotient ε s)=s⁻¹•endRegular ε s := by
  funext j
  cases j with
  | none => simp [endRegular,hε,endHomogeneous,Pi.smul_apply,hs]
  | some j =>
    cases j <;> simp [endRegular,hε,endHomogeneous,endQuotient,Pi.smul_apply,div_eq_mul_inv,mul_comm]

 theorem endQuotient_phase (ε : EndIndex) (s : ℂ) :
    complexCartesian (endQuotient ε s)=
      affinePhase 1 (planeAffine (projection (infinityPoint (parameters 0) ε s))) := by
  funext j
  cases j with
  | none =>
    change Complex.equivRealProdCLM ((infinityRoot (parameters 0) ε s 0-1)/s)=
      Complex.equivRealProdCLM (s⁻¹*infinityRoot (parameters 0) ε s 0-s⁻¹)
    congr 1
    simp only [div_eq_mul_inv]
    ring
  | some _ =>
    change Complex.equivRealProdCLM ((infinityRoot (parameters 0) ε s 1-1)/s)=
      Complex.equivRealProdCLM (s⁻¹*infinityRoot (parameters 0) ε s 1-s⁻¹)
    congr 1
    simp only [div_eq_mul_inv]
    ring

 theorem cubic_infinityPhase_germ (ε : EndIndex) {y : Plane}
    (hy : y∈(infinityDiffeomorph (parameters 0) ε).source) :
    (phaseInclusion ∘ infinityDiffeomorph (parameters 0) ε)=ᶠ[𝓝 y]
      fun z => complexCartesian (endQuotient ε (Complex.equivRealProdCLM.symm z)) := by
  filter_upwards [(infinityDiffeomorph (parameters 0) ε).open_source.mem_nhds hy] with z hz
  have hzD : Complex.equivRealProdCLM.symm z∈infinityDomain (parameters 0) := by
    simpa only [infinityDiffeomorph_source,mem_preimage] using hz
  rw [endQuotient_phase]
  change affinePhase 1 (planeAffine (projection ((infinityInverse (parameters 0) ε
    (Complex.equivRealProdCLM.symm z)).val)))=_
  rw [infinityInverse_val _ ε hzD.1]

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff BigOperators

variable {ι : Type*} [Fintype ι]
abbrev VeroneseIndex (ι : Type*) := (Bool×ι) ⊕ (ι×ι)

def veronese (z : ι → ℂ) : VeroneseIndex ι → ℂ
  | .inl i => z i.2
  | .inr i => z i.1*z i.2

def veroneseDerivative (z : ι → ℂ) : (ι → ℂ) →L[ℂ] (VeroneseIndex ι → ℂ) :=
  ContinuousLinearMap.pi fun i => match i with
    | .inl i => ContinuousLinearMap.proj i.2
    | .inr i => z i.1 • ContinuousLinearMap.proj i.2+z i.2 • ContinuousLinearMap.proj i.1

theorem veronese_contDiff : ContDiff ℂ ∞ (veronese : (ι → ℂ) → _) := by
  apply contDiff_pi.mpr
  rintro (⟨b,i⟩|⟨i,j⟩)
  · exact contDiff_apply ℂ ℂ i
  · exact (contDiff_apply ℂ ℂ i).mul (contDiff_apply ℂ ℂ j)

theorem veronese_hasFDerivAt (z : ι → ℂ) :
    HasFDerivAt veronese (veroneseDerivative z) z := by
  apply hasFDerivAt_pi.mpr
  rintro (⟨b,i⟩|⟨i,j⟩)
  · exact (ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).hasFDerivAt
  · convert! ((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).hasFDerivAt.mul
      (ContinuousLinearMap.proj j : (ι → ℂ) →L[ℂ] ℂ).hasFDerivAt) using 1

theorem veronese_pairing (z v : ι → ℂ) :
    complexPairing (veronese z) (veroneseDerivative z v)=
      2*(1+complexPairing z z)*complexPairing z v := by
  classical
  simp only [complexPairing,Fintype.sum_sum_type,Fintype.sum_prod_type,veronese,
    veroneseDerivative,ContinuousLinearMap.pi_apply,add_apply,
    smul_apply,ContinuousLinearMap.proj_apply,smul_eq_mul,
    Fintype.sum_bool,star_mul]
  have hterm (i j : ι) : star (z j)*star (z i)*(z i*v j+z j*v i)=
      (star (z i)*z i)*(star (z j)*v j)+(star (z i)*v i)*(star (z j)*z j) := by ring
  simp_rw [hterm,Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_mul]
  ring

theorem veronese_sq (z : ι → ℂ) :
    1+phaseSq (complexCartesian (veronese z))=(1+phaseSq (complexCartesian z))^2 := by
  rw [complexCartesian_sq,complexCartesian_sq]
  simp only [veronese,Fintype.sum_sum_type,Fintype.sum_prod_type,Fintype.sum_bool,
    Complex.normSq_mul,← Finset.mul_sum,← Finset.sum_mul]
  ring

theorem veronese_phaseArea (z v : ι → ℂ) :
    phaseArea (complexCartesian (veronese z)) (complexCartesian (veroneseDerivative z v))=
      2*(1+phaseSq (complexCartesian z))*phaseArea (complexCartesian z) (complexCartesian v) := by
  rw [← complexPairing_im,veronese_pairing,complexPairing_self,complexCartesian_sq]
  simp [Complex.mul_im,complexPairing_im]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]

theorem holomorphicCartesian_derivative_I {f : E → (ι → ℂ)} {z : E}
    (hf : DifferentiableAt ℂ f z) (v : E) :
    fderiv ℝ (fun x => complexCartesian (f x)) z (Complex.I • v)=
      phaseJ (fderiv ℝ (fun x => complexCartesian (f x)) z v) := by
  have hd := complexCartesian.toContinuousLinearMap.hasFDerivAt.comp z
    (hf.hasFDerivAt.restrictScalars ℝ)
  change HasFDerivAt (fun x => complexCartesian (f x)) _ z at hd
  rw [hd.fderiv]
  change complexCartesian (fderiv ℂ f z (Complex.I • v))=
    phaseJ (complexCartesian (fderiv ℂ f z v))
  rw [map_smul]
  exact complexCartesian_I _

theorem holomorphicFS_nonnegative {f : E → (ι → ℂ)} {z : E}
    (hf : DifferentiableAt ℂ f z) {c : ℝ} (hc : 0<c) (v : E) :
    0≤affineFSForm c (complexCartesian (f z))
      (fderiv ℝ (fun x => complexCartesian (f x)) z v)
      (fderiv ℝ (fun x => complexCartesian (f x)) z (Complex.I • v)) := by
  rw [holomorphicCartesian_derivative_I hf v]
  by_cases hv : fderiv ℝ (fun x => complexCartesian (f x)) z v=0
  · rw [hv,map_zero]
    simp
  · exact (affineFSForm_positive hc _ _ hv).le

theorem holomorphicFS_exterior {f : E → (ι → ℂ)} (hf : ContDiff ℂ ∞ f)
    (c : ℝ) (z : E) :
    euclideanExteriorOneForm
      (primitivePullback (affineFSPrimitive c) (fun x => complexCartesian (f x))) z=
      (affineFSForm c (complexCartesian (f z))).bilinearComp
        (fderiv ℝ (fun x => complexCartesian (f x)) z)
        (fderiv ℝ (fun x => complexCartesian (f x)) z) := by
  have hs : ContDiff ℝ ∞ (fun x => complexCartesian (f x)) :=
    (complexCartesian (ι := ι)).contDiff.comp (hf.restrict_scalars ℝ)
  rw [primitivePullback_exterior (affineFSPrimitive_smooth c) hs,← affineFSForm_eq_exterior]

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff
open Function
open Hamiltonian

variable {m : ℕ}

def affineComplex (m : ℕ) : Affine m →L[ℂ] (Option (Fin m) → ℂ) :=
  ContinuousLinearMap.pi fun j => match j with
    | none => ContinuousLinearMap.fst ℂ ℂ (Fin m → ℂ)
    | some j => (ContinuousLinearMap.proj j).comp (ContinuousLinearMap.snd ℂ ℂ (Fin m → ℂ))

theorem complexCartesian_affineComplex (z : Affine m) :
    complexCartesian (affineComplex m z)=affinePhase m z := by
  ext i <;> cases i <;> rfl

abbrev NormalPolynomialIndex (m : ℕ) := VeroneseIndex (Option (Fin m)) ⊕ Fin m

def normalPolynomial (a : Fin m → ℂ) (t : ℝ) (z : Affine m) : NormalPolynomialIndex m → ℂ
  | .inl i => veronese (affineComplex m z) i
  | .inr j => (t:ℂ)⁻¹*equations a z j

theorem normalPolynomial_smooth (a : Fin m → ℂ) (t : ℝ) :
    ContDiff ℂ ∞ (normalPolynomial a t) := by
  apply contDiff_pi.mpr
  intro i
  cases i with
  | inl i => exact (contDiff_apply ℂ ℂ i).comp (veronese_contDiff.comp (affineComplex m).contDiff)
  | inr j => exact contDiff_const.mul ((contDiff_apply ℂ ℂ j).comp (equations_contDiff a))

theorem normalPolynomialCartesian_smooth (a : Fin m → ℂ) (t : ℝ) :
    ContDiff ℝ ∞ (fun z => complexCartesian (normalPolynomial a t z)) :=
  (complexCartesian (ι := NormalPolynomialIndex m)).contDiff.comp
    ((normalPolynomial_smooth a t).restrict_scalars ℝ)

def ambientFSPrimitive (c : ℝ) (z : Affine m) : Affine m →L[ℝ] ℝ :=
  (affineFSPrimitive c (affinePhase m z)).comp (affinePhase m)

theorem ambientFSPrimitive_smooth (c : ℝ) :
    ContDiff ℝ ∞ (ambientFSPrimitive (m := m) c) :=
  ((affineFSPrimitive_smooth c).comp (affinePhase m).contDiff).clm_comp contDiff_const

theorem ambientFSPrimitive_exterior (c : ℝ) (z : Affine m) :
    euclideanExteriorOneForm (ambientFSPrimitive c) z=
      (affineFSForm c (affinePhase m z)).bilinearComp (affinePhase m) (affinePhase m) := by
  have he : ambientFSPrimitive (m := m) c=primitivePullback (affineFSPrimitive c) (affinePhase m) := by
    funext x
    simp only [ambientFSPrimitive,primitivePullback,(affinePhase m).fderiv]
  rw [he,primitivePullback_exterior (affineFSPrimitive_smooth c) (affinePhase m).contDiff,
    ← affineFSForm_eq_exterior,(affinePhase m).fderiv]

def normalAmbientPrimitive (a : Fin m → ℂ) (c d t : ℝ) : Affine m → Affine m →L[ℝ] ℝ :=
  (1-2*d) • ambientFSPrimitive c+
    d • primitivePullback (affineFSPrimitive c) (fun z => complexCartesian (normalPolynomial a t z))

def normalAmbientForm (a : Fin m → ℂ) (c d t : ℝ) :=
  euclideanExteriorOneForm (normalAmbientPrimitive a c d t)

theorem normalAmbientPrimitive_smooth (a : Fin m → ℂ) (c d t : ℝ) :
    ContDiff ℝ ∞ (normalAmbientPrimitive a c d t) :=
  ((ambientFSPrimitive_smooth c).const_smul (1-2*d)).add
    ((primitivePullback_smooth (affineFSPrimitive_smooth c)
      (normalPolynomialCartesian_smooth a t)).const_smul d)

theorem normalAmbientForm_apply (a : Fin m → ℂ) (c d t : ℝ) (z v w : Affine m) :
    normalAmbientForm a c d t z v w=
      (1-2*d)*affineFSForm c (affinePhase m z) (affinePhase m v) (affinePhase m w)+
      d*affineFSForm c (complexCartesian (normalPolynomial a t z))
        (fderiv ℝ (fun x => complexCartesian (normalPolynomial a t x)) z v)
        (fderiv ℝ (fun x => complexCartesian (normalPolynomial a t x)) z w) := by
  have h₀ := (ambientFSPrimitive_smooth (m := m) c).differentiable (by simp) z
  have h₁ := (primitivePullback_smooth (affineFSPrimitive_smooth c)
    (normalPolynomialCartesian_smooth a t)).differentiable (by simp) z
  rw [normalAmbientForm,normalAmbientPrimitive,euclideanExteriorOneForm_add
    (h₀.const_smul _) (h₁.const_smul _),euclideanExteriorOneForm_smul _ h₀,
    euclideanExteriorOneForm_smul _ h₁,ambientFSPrimitive_exterior,
    holomorphicFS_exterior (normalPolynomial_smooth a t)]
  rfl

theorem normalAmbientForm_positive (a : Fin m → ℂ) {c d : ℝ} (hc : 0<c)
    (hd : 0≤d) (hdhalf : d<1/2) (t : ℝ) (z v : Affine m) (hv : v≠0) :
    0<normalAmbientForm a c d t z v (Complex.I • v) := by
  rw [normalAmbientForm_apply,affinePhase_I]
  have hb := affineFSForm_positive hc (affinePhase m z) (affinePhase m v)
    (fun hz => hv (affinePhase_injective m (hz.trans (map_zero _).symm)))
  have hp := holomorphicFS_nonnegative
    ((normalPolynomial_smooth a t).differentiable (by simp) z) hc v
  exact add_pos_of_pos_of_nonneg (mul_pos (by linarith) hb) (mul_nonneg hd hp)

theorem normalAmbientForm_isInvertible (a : Fin m → ℂ) {c d : ℝ} (hc : 0<c)
    (hd : 0≤d) (hdhalf : d<1/2) (t : ℝ) (z : Affine m) :
    (normalAmbientForm a c d t z).IsInvertible :=
  bilinear_isInvertible_of_taming (normalAmbientForm_positive a hc hd hdhalf t z)

theorem normalAmbientForm_smooth (a : Fin m → ℂ) (c d t : ℝ) :
    ContDiff ℝ ∞ (normalAmbientForm a c d t) :=
  euclideanExteriorOneForm_smooth (normalAmbientPrimitive_smooth a c d t)

theorem normalAmbientForm_closed (a : Fin m → ℂ) (c d t : ℝ) (z u v w : Affine m) :
    fderiv ℝ (normalAmbientForm a c d t) z u v w-
      fderiv ℝ (normalAmbientForm a c d t) z v u w+
      fderiv ℝ (normalAmbientForm a c d t) z w u v=0 :=
  euclideanExteriorOneForm_closed (normalAmbientPrimitive_smooth a c d t) z u v w

end PackingSufficiencySupport.DiagonalQuadrics

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Filter Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian

abbrev WeightedAffineIndex := Option (Fin 3)
abbrev WeightedHomogeneousIndex := Option WeightedAffineIndex

 def five (a b c d e : ℂ) : WeightedHomogeneousIndex → ℂ
  | none => a
  | some none => b
  | some (some j) => ![c,d,e] j

 def weightedEndQuotient (D m : ℕ) (ε : EndIndex) (s : ℂ) : WeightedAffineIndex → ℂ :=
  affineComplex 3 (weightedProjection D m
    (endQuotient ε s none,endQuotient ε s (some 0)))

 def endCoefficient (s : ℂ) (j : Fin 2) : ℂ :=
  -(parameters 0 j)/(infinityRoot (parameters 0) zeroEnd s j+1)

 def endNumerator (ε : EndIndex) (s : ℂ) (j : Fin 2) : ℂ :=
  infinityRoot (parameters 0) ε s j-1

 def weightedEndOrder (D m : ℕ) (ε : EndIndex) : ℕ :=
  if ε 0 then (if ε 1 then D else D-m) else (if ε 1 then D-m else 0)

 def weightedEndRegular (D m : ℕ) (ε : EndIndex) (s : ℂ) : WeightedHomogeneousIndex → ℂ :=
  let L := D-m
  let A := endNumerator ε s
  let C := endCoefficient s
  if ε 0 then
    (if ε 1 then five (s^D) (s^m*A 0^L) (s^m*A 1^L) (A 0^L*A 1^m) (A 0^m*A 1^L)
    else five (s^L) (A 0^L) (s^(2*L)*C 1^L) (s^m*A 0^L*C 1^m) (s^(2*L-m)*A 0^m*C 1^L))
  else
    (if ε 1 then five (s^L) (s^(2*L)*C 0^L) (A 1^L) (s^(2*L-m)*C 0^L*A 1^m) (s^m*C 0^m*A 1^L)
    else complexAffineLift (affineComplex 3 (weightedProjection D m
      (s*C 0,s*C 1))))

 theorem five_contDiffAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {a b c d e : E → ℂ} {x : E} (ha : ContDiffAt ℂ ∞ a x) (hb : ContDiffAt ℂ ∞ b x)
    (hc : ContDiffAt ℂ ∞ c x) (hd : ContDiffAt ℂ ∞ d x) (he : ContDiffAt ℂ ∞ e x) :
    ContDiffAt ℂ ∞ (fun y => five (a y) (b y) (c y) (d y) (e y)) x := by
  apply contDiffAt_pi.mpr
  intro j
  cases j with
  | none => exact ha
  | some j =>
    cases j with
    | none => exact hb
    | some j =>
      fin_cases j
      · exact hc
      · exact hd
      · exact he

 theorem endCoefficient_contDiffAt {s : ℂ} (hs : s∈endRegularRegion) (j : Fin 2) :
    ContDiffAt ℂ ∞ (fun t => endCoefficient t j) s :=
  contDiffAt_const.div
    ((contDiffAt_pi.mp (infinityRoot_contDiffAt _ zeroEnd hs.1) j).add contDiffAt_const) (hs.2 j)

 theorem endNumerator_contDiffAt (ε : EndIndex) {s : ℂ} (hs : s∈endRegularRegion) (j : Fin 2) :
    ContDiffAt ℂ ∞ (fun t => endNumerator ε t j) s :=
  (contDiffAt_pi.mp (infinityRoot_contDiffAt _ ε hs.1) j).sub contDiffAt_const

 theorem complexAffineLift_holomorphic {ι : Type*} [Fintype ι] :
    ContDiff ℂ ∞ (complexAffineLift (ι := ι)) := by
  apply contDiff_pi.mpr
  intro j
  cases j with
  | none => exact contDiff_const
  | some j => exact contDiff_apply ℂ ℂ j

 theorem weightedEndRegular_contDiffAt (D m : ℕ) (ε : EndIndex) {s : ℂ} (hs : s∈endRegularRegion) :
    ContDiffAt ℂ ∞ (weightedEndRegular D m ε) s := by
  change ContDiffAt ℂ ∞ (fun t => weightedEndRegular D m ε t) s
  have hp (n : ℕ) := (contDiffAt_id (𝕜 := ℂ) (x := s) (n := ∞)).pow n
  have hA := endNumerator_contDiffAt ε hs
  have hC := endCoefficient_contDiffAt hs
  cases h0 : ε 0 <;> cases h1 : ε 1
  · simp only [weightedEndRegular,h0,h1,Bool.false_eq_true,↓reduceIte]
    exact complexAffineLift_holomorphic.contDiffAt.comp s ((affineComplex 3).contDiff.contDiffAt.comp s
      ((weightedProjection_contDiff D m).contDiffAt.comp s
        ((contDiffAt_id.mul (hC 0)).prodMk (contDiffAt_id.mul (hC 1)))))
  · simp only [weightedEndRegular,h0,h1,Bool.false_eq_true,↓reduceIte]
    exact five_contDiffAt (hp _) ((hp _).mul ((hC 0).pow _)) ((hA 1).pow _)
      (((hp _).mul ((hC 0).pow _)).mul ((hA 1).pow _))
      (((hp _).mul ((hC 0).pow _)).mul ((hA 1).pow _))
  · simp only [weightedEndRegular,h0,h1,Bool.false_eq_true,↓reduceIte]
    exact five_contDiffAt (hp _) ((hA 0).pow _) ((hp _).mul ((hC 1).pow _))
      (((hp _).mul ((hA 0).pow _)).mul ((hC 1).pow _))
      (((hp _).mul ((hA 0).pow _)).mul ((hC 1).pow _))
  · simp only [weightedEndRegular,h0,h1,↓reduceIte]
    exact five_contDiffAt (hp _) ((hp _).mul ((hA 0).pow _)) ((hp _).mul ((hA 1).pow _))
      (((hA 0).pow _).mul ((hA 1).pow _)) (((hA 0).pow _).mul ((hA 1).pow _))

 theorem endCoordinate_false {ε : EndIndex} {j : Fin 2} (hj : ε j=false)
    {s : ℂ} (hs : s≠0) (hR : s∈endRegularRegion) :
    (infinityRoot (parameters 0) ε s j-1)/s=s*endCoefficient s j := by
  have he : infinityRoot (parameters 0) ε s j=infinityRoot (parameters 0) zeroEnd s j := by
    simp only [infinityRoot,endSign,hj,zeroEnd]
    rfl
  rw [he,removableCoordinate_eq hs hR]
  dsimp [removableCoordinate,endCoefficient]
  ring

 theorem weightedEndQuotient_contDiffAt (D m : ℕ) (ε : EndIndex) {s : ℂ}
    (hs : s∈infinityDomain (parameters 0)) : ContDiffAt ℂ ∞ (weightedEndQuotient D m ε) s :=
  (affineComplex 3).contDiff.contDiffAt.comp s ((weightedProjection_contDiff D m).contDiffAt.comp s
    ((contDiffAt_pi.mp (endQuotient_contDiffAt ε hs) none).prodMk
      (contDiffAt_pi.mp (endQuotient_contDiffAt ε hs) (some 0))))

 theorem weightedEndRegular_none (D m : ℕ) (ε : EndIndex) (s : ℂ) :
    weightedEndRegular D m ε s none=s^(weightedEndOrder D m ε) := by
  cases h0 : ε 0 <;> cases h1 : ε 1 <;>
    simp [weightedEndRegular,weightedEndOrder,h0,h1,five]

 theorem weightedEndRegular_ne_zero (D m : ℕ) (ε : EndIndex) (s : ℂ) :
    weightedEndRegular D m ε s≠0 := by
  intro he
  by_cases hs : s=0
  · subst s
    cases h0 : ε 0 <;> cases h1 : ε 1
    · exact (one_ne_zero : (1:ℂ)≠0) (by simpa [weightedEndRegular,h0,h1,complexAffineLift] using congrFun he none)
    · have hz := congrFun he (some (some 0))
      norm_num [weightedEndRegular,h0,h1,five,endNumerator,infinityRoot,endSign] at hz
    · have hz := congrFun he (some none)
      norm_num [weightedEndRegular,h0,h1,five,endNumerator,infinityRoot,endSign] at hz
    · have hz := congrFun he (some (some 1))
      norm_num [weightedEndRegular,h0,h1,five,endNumerator,infinityRoot,endSign] at hz
  · exact (pow_ne_zero _ hs) (by simpa only [weightedEndRegular_none,Pi.zero_apply] using congrFun he none)

 theorem weightedEndRegular_cartesian_ne_zero (D m : ℕ) (ε : EndIndex) (s : ℂ) :
    complexCartesian (weightedEndRegular D m ε s)≠0 := by
  intro h
  exact weightedEndRegular_ne_zero D m ε s (complexCartesian.injective (by simpa only [map_zero] using h))

 theorem scale_div_pow {s : ℂ} (hs : s≠0) (a : ℂ) (L : ℕ) :
    s^L*(a/s)^L=a^L := by
  rw [←mul_pow,mul_div_cancel₀ a hs]

 theorem scale_complement_pow {s : ℂ} (hs : s≠0) (a : ℂ) {D m : ℕ} (hm : m≤D) :
    s^D*(a/s)^(D-m)=s^m*a^(D-m) := by
  have hD : m+(D-m)=D := Nat.add_sub_of_le hm
  have hp : s^D=s^m*s^(D-m) := by rw [←pow_add,hD]
  calc
    _=s^m*(s^(D-m)*(a/s)^(D-m)) := by rw [hp]; ring
    _=_ := by rw [scale_div_pow hs]

 theorem scale_div_mixed {s : ℂ} (hs : s≠0) (a b : ℂ) (L m : ℕ) :
    s^(L+m)*((a/s)^L*(b/s)^m)=a^L*b^m := by
  calc
    _=(s^L*(a/s)^L)*(s^m*(b/s)^m) := by rw [pow_add]; ring
    _=_ := by rw [scale_div_pow hs,scale_div_pow hs]

 theorem scale_regular_pow (s b : ℂ) (L : ℕ) :
    s^L*(s*b)^L=s^(2*L)*b^L := by
  rw [mul_pow,two_mul,pow_add]
  ring

 theorem scale_onepole_mixed {s : ℂ} (hs : s≠0) (a b : ℂ) (L m : ℕ) :
    s^L*((a/s)^L*(s*b)^m)=s^m*a^L*b^m := by
  calc
    _=(s^L*(a/s)^L)*(s^m*b^m) := by rw [mul_pow]; ring
    _=_ := by rw [scale_div_pow hs]; ring

 theorem scale_onepole_cross {s : ℂ} (hs : s≠0) (a b : ℂ) {L m : ℕ} (hm : m≤2*L) :
    s^L*((a/s)^m*(s*b)^L)=s^(2*L-m)*a^m*b^L := by
  rw [pow_sub₀ s hs hm,two_mul,pow_add,div_pow,mul_pow]
  simp only [div_eq_mul_inv]
  ring

 def weightedLift (D m : ℕ) (v w : ℂ) : WeightedHomogeneousIndex → ℂ :=
  complexAffineLift (affineComplex 3 (weightedProjection D m (v,w)))

 theorem weightedLift_scale_poles {D m : ℕ} (hm : m≤D) {s : ℂ} (hs : s≠0) (a b : ℂ) :
    s^D • weightedLift D m (a/s) (b/s)=
      five (s^D) (s^m*a^(D-m)) (s^m*b^(D-m)) (a^(D-m)*b^m) (a^m*b^(D-m)) := by
  funext j
  cases j with
  | none => change s^D*1=s^D; exact mul_one _
  | some j =>
    cases j with
    | none => exact scale_complement_pow hs a hm
    | some j =>
      fin_cases j
      · exact scale_complement_pow hs b hm
      · change s^D*((a/s)^(D-m)*(b/s)^m)=a^(D-m)*b^m
        simpa only [Nat.sub_add_cancel hm] using scale_div_mixed hs a b (D-m) m
      · change s^D*((a/s)^m*(b/s)^(D-m))=a^m*b^(D-m)
        simpa only [Nat.add_sub_of_le hm] using scale_div_mixed hs a b m (D-m)

 theorem weightedLift_scale_left {D m : ℕ} (hm : m≤2*(D-m)) {s : ℂ} (hs : s≠0) (a b : ℂ) :
    s^(D-m) • weightedLift D m (a/s) (s*b)=
      five (s^(D-m)) (a^(D-m)) (s^(2*(D-m))*b^(D-m))
        (s^m*a^(D-m)*b^m) (s^(2*(D-m)-m)*a^m*b^(D-m)) := by
  funext j
  cases j with
  | none => change s^(D-m)*1=s^(D-m); exact mul_one _
  | some j =>
    cases j with
    | none => exact scale_div_pow hs a (D-m)
    | some j =>
      fin_cases j
      · exact scale_regular_pow s b (D-m)
      · exact scale_onepole_mixed hs a b (D-m) m
      · exact scale_onepole_cross hs a b hm

 theorem weightedLift_scale_right {D m : ℕ} (hm : m≤2*(D-m)) {s : ℂ} (hs : s≠0) (a b : ℂ) :
    s^(D-m) • weightedLift D m (s*a) (b/s)=
      five (s^(D-m)) (s^(2*(D-m))*a^(D-m)) (b^(D-m))
        (s^(2*(D-m)-m)*a^(D-m)*b^m) (s^m*a^m*b^(D-m)) := by
  funext j
  cases j with
  | none => change s^(D-m)*1=s^(D-m); exact mul_one _
  | some j =>
    cases j with
    | none => exact scale_regular_pow s a (D-m)
    | some j =>
      fin_cases j
      · exact scale_div_pow hs b (D-m)
      · change s^(D-m)*((s*a)^(D-m)*(b/s)^m)=s^(2*(D-m)-m)*a^(D-m)*b^m
        calc
          _=s^(D-m)*((b/s)^m*(s*a)^(D-m)) := by ring
          _=s^(2*(D-m)-m)*b^m*a^(D-m) := scale_onepole_cross hs b a hm
          _=_ := by ring
      · change s^(D-m)*((s*a)^m*(b/s)^(D-m))=s^m*a^m*b^(D-m)
        calc
          _=s^(D-m)*((b/s)^(D-m)*(s*a)^m) := by ring
          _=s^m*b^(D-m)*a^m := scale_onepole_mixed hs b a (D-m) m
          _=_ := by ring

 theorem weightedEndRegular_scale {D m : ℕ} (hm : m≤D) (h2 : m≤2*(D-m))
    (ε : EndIndex) {s : ℂ} (hs : s≠0) (hR : s∈endRegularRegion) :
    weightedEndRegular D m ε s=s^(weightedEndOrder D m ε)•complexAffineLift (weightedEndQuotient D m ε s) := by
  cases h0 : ε 0 <;> cases h1 : ε 1
  · have h00 := endCoordinate_false h0 hs hR
    have h11 := endCoordinate_false h1 hs hR
    simp only [weightedEndRegular,weightedEndOrder,h0,h1,Bool.false_eq_true,↓reduceIte,
      weightedEndQuotient,endQuotient,h00,h11,pow_zero,one_smul]
  · have h00 := endCoordinate_false h0 hs hR
    simpa only [weightedEndRegular,weightedEndOrder,h0,h1,Bool.false_eq_true,↓reduceIte,
      weightedEndQuotient,endQuotient,h00,weightedLift,endNumerator] using
      (weightedLift_scale_right h2 hs (endCoefficient s 0) (endNumerator ε s 1)).symm
  · have h11 := endCoordinate_false h1 hs hR
    simpa only [weightedEndRegular,weightedEndOrder,h0,h1,Bool.false_eq_true,↓reduceIte,
      weightedEndQuotient,endQuotient,h11,weightedLift,endNumerator] using
      (weightedLift_scale_left h2 hs (endNumerator ε s 0) (endCoefficient s 1)).symm
  · simpa only [weightedEndRegular,weightedEndOrder,h0,h1,↓reduceIte,
      weightedEndQuotient,endQuotient,weightedLift,endNumerator] using
      (weightedLift_scale_poles hm hs (endNumerator ε s 0) (endNumerator ε s 1)).symm

 theorem weightedEndQuotient_phase (D m : ℕ) (ε : EndIndex) (s : ℂ) :
    complexCartesian (weightedEndQuotient D m ε s)=
      affinePhase 3 (weightedProjection D m (projection (infinityPoint (parameters 0) ε s))) := by
  rw [weightedEndQuotient,complexCartesian_affineComplex]
  congr 2
  apply Prod.ext
  · change (infinityRoot (parameters 0) ε s 0-1)/s=s⁻¹*infinityRoot (parameters 0) ε s 0-s⁻¹
    simp only [div_eq_mul_inv]
    ring
  · change (infinityRoot (parameters 0) ε s 1-1)/s=s⁻¹*infinityRoot (parameters 0) ε s 1-s⁻¹
    simp only [div_eq_mul_inv]
    ring

 theorem weighted_infinityPhase_germ (D m : ℕ) (ε : EndIndex) {y : Plane}
    (hy : y∈(infinityDiffeomorph (parameters 0) ε).source) :
    (weightedPhaseInclusion D m ∘ infinityDiffeomorph (parameters 0) ε)=ᶠ[𝓝 y]
      fun z => complexCartesian (weightedEndQuotient D m ε (Complex.equivRealProdCLM.symm z)) := by
  filter_upwards [(infinityDiffeomorph (parameters 0) ε).open_source.mem_nhds hy] with z hz
  have hzD : Complex.equivRealProdCLM.symm z∈infinityDomain (parameters 0) := by
    simpa only [infinityDiffeomorph_source,mem_preimage] using hz
  rw [weightedEndQuotient_phase]
  change affinePhase 3 (weightedProjection D m (projection ((infinityInverse (parameters 0) ε
    (Complex.equivRealProdCLM.symm z)).val)))=_
  rw [infinityInverse_val _ ε hzD.1]

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff
open DiagonalQuadrics

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem logarithmicDerivative_pow {S : E → ℂ} {x : E} (hS : DifferentiableAt ℝ S x)
    (hSx : S x≠0) (l : ℕ) (v : E) :
    fderiv ℝ (fun y => S y^l) x v/(S x)^l=(l:ℂ)*(fderiv ℝ S x v/S x) := by
  rw [(hS.hasFDerivAt.pow l).fderiv]
  cases l with
  | zero => simp
  | succ l =>
    simp only [Nat.succ_sub_one,smul_apply,nsmul_eq_mul,smul_eq_mul,pow_succ]
    field_simp

 theorem hopfPrimitive_variable_power_gauge {S : E → ℂ} {G : E → (ι → ℂ)} {x : E}
    (hS : DifferentiableAt ℝ S x) (hG : DifferentiableAt ℝ G x)
    (hSx : S x≠0) (hGx : complexCartesian (G x)≠0) (l : ℕ) (c : ℝ) (v : E) :
    hopfPrimitive c (complexCartesian (S x^l•G x))
      (fderiv ℝ (fun y => complexCartesian (S y^l•G y)) x v)=
    hopfPrimitive c (complexCartesian (G x))
      (fderiv ℝ (fun y => complexCartesian (G y)) x v)+
        (l:ℝ)*c/(2*Complex.normSq (S x))*complexArea (S x) (fderiv ℝ S x v) := by
  rw [hopfPrimitive_variable_gauge (S := fun y => S y^l) (hS.pow l) hG (pow_ne_zero l hSx) hGx c v]
  congr 1
  have hd := congrArg Complex.im (logarithmicDerivative_pow hS hSx l v)
  rw [complex_div_im] at hd
  simp only [Complex.mul_im,Complex.natCast_re,Complex.natCast_im,zero_mul,add_zero,
    complex_div_im] at hd
  calc
    _=c/2*(complexArea (S x^l) (fderiv ℝ (fun y => S y^l) x v)/Complex.normSq (S x^l)) := by ring
    _=c/2*((l:ℝ)*(complexArea (S x) (fderiv ℝ S x v)/Complex.normSq (S x))) := by rw [hd]
    _=_ := by ring

 theorem planar_power_gauge {G : Plane → (ι → ℂ)} {y : Plane}
    (hG : DifferentiableAt ℝ G y) (hy : Complex.equivRealProdCLM.symm y≠0)
    (hGy : complexCartesian (G y)≠0) (l : ℕ) (c : ℝ) (v : Plane) :
    hopfPrimitive c (complexCartesian ((Complex.equivRealProdCLM.symm y)^l•G y))
      (fderiv ℝ (fun z => complexCartesian ((Complex.equivRealProdCLM.symm z)^l•G z)) y v)=
    hopfPrimitive c (complexCartesian (G y))
      (fderiv ℝ (fun z => complexCartesian (G z)) y v)+
        ((l:ℝ)*c/2)*angularOneForm y v := by
  rw [hopfPrimitive_variable_power_gauge Complex.equivRealProdCLM.symm.differentiableAt
    hG hy hGy l c v,ContinuousLinearEquiv.fderiv]
  simp only [ContinuousLinearEquiv.coe_coe]
  have hns : Complex.normSq (Complex.equivRealProdCLM.symm y)=radiusSq y := by
    change y.1*y.1+y.2*y.2=y.1^2+y.2^2
    ring
  have hca : complexArea (Complex.equivRealProdCLM.symm y)
      (Complex.equivRealProdCLM.symm v)=planarArea y v := by
    rw [complexArea_apply]
    rfl
  rw [hns,hca]
  simp only [angularOneForm,smul_apply,smul_eq_mul]
  ring

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Filter Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian

 def weightedRegularEndPhase (D m : ℕ) (ε : EndIndex) (y : Plane) : PlanePhase WeightedHomogeneousIndex :=
  complexCartesian (weightedEndRegular D m ε (Complex.equivRealProdCLM.symm y))

 def weightedRegularEndPrimitive (D m : ℕ) (ε : EndIndex) (c : ℝ) : Plane → Plane →L[ℝ] ℝ :=
  staticPullbackOneForm (hopfPrimitive c) (weightedRegularEndPhase D m ε)

 def weightedEndResidue (D m : ℕ) (ε : EndIndex) (c : ℝ) : ℝ := (weightedEndOrder D m ε:ℝ)*c

 theorem weightedRegularEndPhase_contDiffAt (D m : ℕ) (ε : EndIndex) {y : Plane}
    (hy : Complex.equivRealProdCLM.symm y∈endRegularRegion) :
    ContDiffAt ℝ ∞ (weightedRegularEndPhase D m ε) y :=
  (complexCartesian (ι := WeightedHomogeneousIndex)).contDiff.contDiffAt.comp y
    (((weightedEndRegular_contDiffAt D m ε hy).restrict_scalars ℝ).comp y
      Complex.equivRealProdCLM.symm.contDiff.contDiffAt)

 theorem weightedRegularEndPrimitive_contDiffAt (D m : ℕ) (ε : EndIndex) (c : ℝ) {y : Plane}
    (hy : Complex.equivRealProdCLM.symm y∈endRegularRegion) :
    ContDiffAt ℝ ∞ (weightedRegularEndPrimitive D m ε c) y :=
  staticPullbackOneForm_smoothAt
    (hopfPrimitive_smoothAt c (weightedEndRegular_cartesian_ne_zero D m ε _))
    (weightedRegularEndPhase_contDiffAt D m ε hy)

 theorem weightedEndQuotientPrimitive_residue {D m : ℕ} (hm : m≤D) (h2 : m≤2*(D-m))
    (ε : EndIndex) (c : ℝ) {y : Plane}
    (hy : Complex.equivRealProdCLM.symm y∈endRegularRegion)
    (h0 : Complex.equivRealProdCLM.symm y≠0) (v : Plane) :
    affineFSPrimitive c (complexCartesian (weightedEndQuotient D m ε (Complex.equivRealProdCLM.symm y)))
      (fderiv ℝ (fun z : Plane => complexCartesian
        (weightedEndQuotient D m ε (Complex.equivRealProdCLM.symm z))) y v)=
      weightedRegularEndPrimitive D m ε c y v-(weightedEndResidue D m ε c/2)*angularOneForm y v := by
  let Q : Plane → WeightedAffineIndex → ℂ := fun z => weightedEndQuotient D m ε (Complex.equivRealProdCLM.symm z)
  have hQ : DifferentiableAt ℝ Q y :=
    (((weightedEndQuotient_contDiffAt D m ε ⟨h0,hy.1⟩).restrict_scalars ℝ).differentiableAt (by simp)).comp y
      Complex.equivRealProdCLM.symm.differentiableAt
  have hp := affineFSPrimitive_hopf_pullback hQ c v
  have hN : complexCartesian (complexAffineLift (Q y))≠0 := by
    intro hz
    have hf : complexAffineLift (Q y)=0 := by
      apply (complexCartesian (ι := WeightedHomogeneousIndex)).injective
      simpa only [map_zero] using hz
    exact one_ne_zero (congrFun hf none)
  have he : weightedRegularEndPhase D m ε=ᶠ[𝓝 y] fun z => complexCartesian
      ((Complex.equivRealProdCLM.symm z)^(weightedEndOrder D m ε)•complexAffineLift (Q z)) := by
    have hR := endRegularRegion_open.preimage Complex.equivRealProdCLM.symm.continuous
    filter_upwards [(isOpen_ne_fun Complex.equivRealProdCLM.symm.continuous continuous_const).mem_nhds h0,
      hR.mem_nhds hy] with z hz hzR
    exact congrArg complexCartesian (weightedEndRegular_scale hm h2 ε hz hzR)
  have hG : DifferentiableAt ℝ (fun z => complexAffineLift (Q z)) y :=
    (complexAffineLift_smooth.differentiable (by simp) _).comp y hQ
  have hg := planar_power_gauge hG h0 hN (weightedEndOrder D m ε) c v
  change _=hopfPrimitive c (weightedRegularEndPhase D m ε y) (fderiv ℝ (weightedRegularEndPhase D m ε) y v)-_
  rw [he.eq_of_nhds,he.fderiv_eq,hg,hp]
  dsimp [weightedEndResidue]
  ring

 theorem weightedFSPrimitive_infinity {D m : ℕ} (hm : m≤D) (h2 : m≤2*(D-m))
    (ε : EndIndex) (c : ℝ) {y : Plane}
    (hy : y∈(infinityDiffeomorph (parameters 0) ε).source)
    (hR : Complex.equivRealProdCLM.symm y∈endRegularRegion) :
    euclideanPullbackOneForm (fun _ => weightedFSPrimitive D m c)
      (infinityDiffeomorph (parameters 0) ε) (0,y)=
      weightedRegularEndPrimitive D m ε c y-(weightedEndResidue D m ε c/2) • angularOneForm y := by
  have hD : Complex.equivRealProdCLM.symm y∈infinityDomain (parameters 0) := by
    simpa only [infinityDiffeomorph_source,mem_preimage] using hy
  have hg := weighted_infinityPhase_germ D m ε hy
  change euclideanPullbackOneForm (fun _ => manifoldPullbackOneForm
    (fun _ => affineFSPrimitive c) (weightedPhaseInclusion D m) 0) (infinityDiffeomorph (parameters 0) ε) (0,y)=_
  rw [euclideanPullbackOneForm_comp ((weightedPhaseInclusion_smooth D m).mdifferentiable (by simp) _)
    ((infinityDiffeomorph (parameters 0) ε).mdifferentiableAt (by simp) hy)]
  apply ContinuousLinearMap.ext
  intro v
  change affineFSPrimitive c ((weightedPhaseInclusion D m ∘ infinityDiffeomorph (parameters 0) ε) y)
    (manifoldMapDifferential (E := PlanePhase WeightedAffineIndex) (F := Plane)
      (weightedPhaseInclusion D m ∘ infinityDiffeomorph (parameters 0) ε) y v)=_
  rw [manifoldMapDifferential,mfderiv_eq_fderiv,hg.eq_of_nhds,hg.fderiv_eq]
  exact weightedEndQuotientPrimitive_residue hm h2 ε c hR hD.1 v

 theorem sum_weightedEndResidue {D m : ℕ} (hm : m≤D) (c : ℝ) :
    (∑ ε : EndIndex,weightedEndResidue D m ε c)=(3*(D:ℝ)-2*(m:ℝ))*c := by
  have hfin (b : Bool × Bool) : (finTwoArrowEquiv Bool).symm b = ![b.1,b.2] := by
    simpa only [finTwoArrowEquiv] using congrFun (finTwoArrowEquiv_symm_apply Bool) b
  rw [← (finTwoArrowEquiv Bool).symm.sum_comp (fun ε => weightedEndResidue D m ε c)]
  simp only [Fintype.sum_prod_type,Fintype.sum_bool,weightedEndResidue,weightedEndOrder,
    hfin,Matrix.cons_val_zero,Matrix.cons_val_one,
    Bool.false_eq_true,↓reduceIte,Nat.cast_zero,zero_mul,Nat.cast_sub hm]
  ring

end PackingSufficiencySupport.CubicModel
end

end OAI
