import Mathlib
import OAI.Geometry.BallPacking.Toric.SixModelComparisonData

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.FiniteMoment.Radial
open scoped BigOperators Topology ContDiff
open Set Filter Function

variable {ι : Type*} [Fintype ι]

theorem diskForward_contDiffAt {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (h0 : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) (z : DiskPair) :
    ContDiffAt ℝ ∞ (fun q : (ι → ℝ) × DiskPair => diskForward k q.1 q.2) (a,z) := by
  have hp := polynomial_pos ha h0 (squaredRadii_nonneg z)
  have hs := slope_contDiffAt hp.ne'
  have hm : ContDiff ℝ ∞ (fun q : (ι → ℝ) × DiskPair => (q.1,squaredRadii q.2)) :=
    contDiff_fst.prodMk (squaredRadii_contDiff.comp contDiff_snd)
  have hc := hs.comp (a,z) hm.contDiffAt
  have hpos := slope_pos ha h0 he0 he1 (squaredRadii_nonneg z)
  exact (hc.fst.sqrt hpos.1.ne').smul contDiffAt_snd.fst |>.prodMk
    ((hc.snd.sqrt hpos.2.ne').smul contDiffAt_snd.snd)

theorem diskForward_contDiff {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (h0 : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) :
    ContDiff ℝ ∞ (diskForward k a) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  exact (diskForward_contDiffAt ha h0 he0 he1 z).comp z
    (contDiffAt_const.prodMk contDiffAt_id)

theorem diskRadius_contDiffAt {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    {a : TrapezoidWeight A B → ℝ} (ha : ∀ i,0<a i) {z : DiskPair}
    (hz : z∈diskDomain A B) :
    ContDiffAt ℝ ∞
      (fun q : (TrapezoidWeight A B → ℝ) × DiskPair => nonnegativeInverse latticeIndex q.1 (squaredRadii q.2)) (a,z) := by
  let U : Set ((TrapezoidWeight A B → ℝ) × DiskPair) :=
    {q | (∀ i,0<q.1 i) ∧ q.2∈diskDomain A B}
  have hU : IsOpen U := positiveCoefficients_isOpen.prod (diskDomain_isOpen A B)
  have hs := trapezoid_inverse_contDiffWithinAt hA hAB ha (squaredRadii_mem_lower hz)
  have hm : ContDiff ℝ ∞
      (fun q : (TrapezoidWeight A B → ℝ) × DiskPair => (q.1,squaredRadii q.2)) :=
    contDiff_fst.prodMk (squaredRadii_contDiff.comp contDiff_snd)
  have hmaps : MapsTo (fun q : (TrapezoidWeight A B → ℝ) × DiskPair => (q.1,squaredRadii q.2))
      U {q | (∀ i,0<q.1 i) ∧ q.2∈lowerTrapezoid A B} :=
    fun q hq => ⟨hq.1,squaredRadii_mem_lower hq.2⟩
  have hc := hs.comp (a,z) (hm.contDiffWithinAt (s:=U)) hmaps
  exact hc.contDiffAt (hU.mem_nhds ⟨ha,hz⟩)

theorem diskInverse_contDiffAt {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    {a : TrapezoidWeight A B → ℝ} (ha : ∀ i,0<a i) {z : DiskPair}
    (hz : z∈diskDomain A B) :
    ContDiffAt ℝ ∞
      (fun q : (TrapezoidWeight A B → ℝ) × DiskPair => diskInverse latticeIndex q.1 q.2) (a,z) := by
  have hr := nonnegativeInverse_nonneg (latticeIndex (A:=A) (B:=B)) a (squaredRadii z)
  have hs := diskRadius_contDiffAt hA hAB ha hz
  have hmap := contDiffAt_fst.prodMk hs
  have hsl := slope_contDiffAt (polynomial_pos ha (lattice_zero A B) hr).ne'
  have hc := hsl.comp (a,z) hmap
  have hpos := slope_pos ha (lattice_zero A B) (lattice_unit_fst hA hAB) (lattice_unit_snd hA hAB) hr
  exact ((hc.fst.sqrt hpos.1.ne').inv (Real.sqrt_pos.mpr hpos.1).ne').smul contDiffAt_snd.fst |>.prodMk
    (((hc.snd.sqrt hpos.2.ne').inv (Real.sqrt_pos.mpr hpos.2).ne').smul contDiffAt_snd.snd)

theorem diskInverse_contDiffOn {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    {a : TrapezoidWeight A B → ℝ} (ha : ∀ i,0<a i) :
    ContDiffOn ℝ ∞ (diskInverse latticeIndex a) (diskDomain A B) := by
  intro z hz
  exact ((diskInverse_contDiffAt hA hAB ha hz).comp z
    (contDiffAt_const.prodMk contDiffAt_id)).contDiffWithinAt

theorem diskInverse_isEmbedding {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    {a : TrapezoidWeight A B → ℝ} (ha : ∀ i,0<a i) :
    Topology.IsEmbedding (fun z : diskDomain A B => diskInverse latticeIndex a z.val) := by
  have hi := (diskInverse_contDiffOn hA hAB ha).continuousOn.domRestrict
  have hf := (diskForward_contDiff ha (lattice_zero A B)
    (lattice_unit_fst hA hAB) (lattice_unit_snd hA hAB)).continuous
  have he : diskForward (latticeIndex (A:=A) (B:=B)) a ∘
      (fun z : diskDomain A B => diskInverse latticeIndex a z.val)=Subtype.val := by
    funext z
    exact diskForward_inverse ha (lattice_zero A B) (lattice_unit_fst hA hAB) (lattice_unit_snd hA hAB)
      (trapezoid_radial_surjective hAB ha (squaredRadii_mem_lower z.property))
  apply Topology.IsEmbedding.of_comp hi hf
  change Topology.IsEmbedding (diskForward (latticeIndex (A:=A) (B:=B)) a ∘
    (fun z : diskDomain A B => diskInverse latticeIndex a z.val))
  rw [he]
  exact Topology.IsEmbedding.subtypeVal

end PackingSufficiencySupport.FiniteMoment.Radial

namespace PackingSufficiencySupport.Hamiltonian
open scoped BigOperators ContDiff ComplexConjugate
open DiagonalQuadrics FiniteMoment.Radial

theorem complexArea_scaled_derivative (r s : ℝ) (z v : ℂ) :
    complexArea (r • z) (s • z+r • v)=r^2*complexArea z v := by
  simp only [complexArea_apply,Complex.smul_re,Complex.smul_im,Complex.add_re,Complex.add_im,smul_eq_mul]
  ring

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
theorem complexArea_fderiv_real_smul {r : X → ℝ} {z : X → ℂ} {x : X}
    (hr : DifferentiableAt ℝ r x) (hz : DifferentiableAt ℝ z x) (v : X) :
    complexArea (r x • z x) (fderiv ℝ (fun q => r q • z q) x v)=
      (r x)^2*complexArea (z x) (fderiv ℝ z x v) := by
  rw [fderiv_fun_smul hr hz]
  simp only [add_apply,smul_apply,ContinuousLinearMap.smulRight_apply]
  rw [add_comm]
  exact complexArea_scaled_derivative _ _ _ _

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.FiniteMoment.Radial
open scoped BigOperators ContDiff ComplexConjugate
open Hamiltonian DiagonalQuadrics

theorem inverseDiskScale_contDiffAt {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    {a : TrapezoidWeight A B → ℝ} (ha : ∀ i,0<a i) {z : DiskPair}
    (hz : z∈diskDomain A B) :
    ContDiffAt ℝ ∞ (fun q : (TrapezoidWeight A B → ℝ) × DiskPair =>
      ((Real.sqrt (slope latticeIndex q.1 (nonnegativeInverse latticeIndex q.1 (squaredRadii q.2))).1)⁻¹,
       (Real.sqrt (slope latticeIndex q.1 (nonnegativeInverse latticeIndex q.1 (squaredRadii q.2))).2)⁻¹)) (a,z) := by
  have hr := nonnegativeInverse_nonneg (latticeIndex (A:=A) (B:=B)) a (squaredRadii z)
  have hs := diskRadius_contDiffAt hA hAB ha hz
  have hc := (slope_contDiffAt (polynomial_pos ha (lattice_zero A B) hr).ne').comp (a,z)
    (contDiffAt_fst.prodMk hs)
  have hpos := slope_pos ha (lattice_zero A B) (lattice_unit_fst hA hAB) (lattice_unit_snd hA hAB) hr
  exact ((hc.fst.sqrt hpos.1.ne').inv (Real.sqrt_pos.mpr hpos.1).ne').prodMk
    ((hc.snd.sqrt hpos.2.ne').inv (Real.sqrt_pos.mpr hpos.2).ne')

theorem diskInverse_angular_fst {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    {a : TrapezoidWeight A B → ℝ} (ha : ∀ i,0<a i) {z : DiskPair}
    (hz : z∈diskDomain A B) (v : (TrapezoidWeight A B → ℝ) × DiskPair) :
    (slope latticeIndex a (squaredRadii (diskInverse latticeIndex a z))).1*
      complexArea (diskInverse latticeIndex a z).1
        ((fderiv ℝ (fun q : (TrapezoidWeight A B → ℝ) × DiskPair => diskInverse latticeIndex q.1 q.2) (a,z) v).1)=
      complexArea z.1 v.2.1 := by
  have hs := (inverseDiskScale_contDiffAt hA hAB ha hz).fst.differentiableAt (by simp)
  have hz' : DifferentiableAt ℝ (fun q : (TrapezoidWeight A B → ℝ) × DiskPair => q.2.1) (a,z) :=
    differentiableAt_snd.fst
  have hd := (diskInverse_contDiffAt hA hAB ha hz).differentiableAt (by simp)
  have he := complexArea_fderiv_real_smul hs hz' v
  have hpos := (slope_pos ha (lattice_zero A B) (lattice_unit_fst hA hAB) (lattice_unit_snd hA hAB)
    (nonnegativeInverse_nonneg (latticeIndex (A:=A) (B:=B)) a (squaredRadii z))).1
  have hrad := squaredRadii_inverse ha (lattice_zero A B) (lattice_unit_fst hA hAB)
    (lattice_unit_snd hA hAB) (trapezoid_radial_surjective hAB ha (squaredRadii_mem_lower hz))
  rw [hrad]
  rw [show (fderiv ℝ (fun q : (TrapezoidWeight A B → ℝ) × DiskPair => diskInverse latticeIndex q.1 q.2) (a,z) v).1=
      fderiv ℝ (fun q : (TrapezoidWeight A B → ℝ) × DiskPair => (diskInverse latticeIndex q.1 q.2).1) (a,z) v from
      (congrArg (fun L => L v) hd.hasFDerivAt.fst.fderiv).symm]
  change _*complexArea (_ • _) (fderiv ℝ (fun q => _ • q.2.1) (a,z) v)=_
  rw [he]
  have hp : HasFDerivAt (fun q : (TrapezoidWeight A B → ℝ) × DiskPair => q.2.1)
      ((ContinuousLinearMap.fst ℝ ℂ ℂ).comp
        (ContinuousLinearMap.snd ℝ (TrapezoidWeight A B → ℝ) DiskPair)) (a,z) := by
    convert! ((ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt (x := z)).comp (a,z)
      ((ContinuousLinearMap.snd ℝ (TrapezoidWeight A B → ℝ) DiskPair).hasFDerivAt (x := (a,z))) using 1
  rw [hp.fderiv]
  change _*((Real.sqrt _)⁻¹^2*complexArea z.1 v.2.1)=_
  rw [inv_pow,Real.sq_sqrt hpos.le]
  field_simp

theorem diskInverse_angular_snd {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    {a : TrapezoidWeight A B → ℝ} (ha : ∀ i,0<a i) {z : DiskPair}
    (hz : z∈diskDomain A B) (v : (TrapezoidWeight A B → ℝ) × DiskPair) :
    (slope latticeIndex a (squaredRadii (diskInverse latticeIndex a z))).2*
      complexArea (diskInverse latticeIndex a z).2
        ((fderiv ℝ (fun q : (TrapezoidWeight A B → ℝ) × DiskPair => diskInverse latticeIndex q.1 q.2) (a,z) v).2)=
      complexArea z.2 v.2.2 := by
  have hs := (inverseDiskScale_contDiffAt hA hAB ha hz).snd.differentiableAt (by simp)
  have hz' : DifferentiableAt ℝ (fun q : (TrapezoidWeight A B → ℝ) × DiskPair => q.2.2) (a,z) :=
    differentiableAt_snd.snd
  have hd := (diskInverse_contDiffAt hA hAB ha hz).differentiableAt (by simp)
  have he := complexArea_fderiv_real_smul hs hz' v
  have hpos := (slope_pos ha (lattice_zero A B) (lattice_unit_fst hA hAB) (lattice_unit_snd hA hAB)
    (nonnegativeInverse_nonneg (latticeIndex (A:=A) (B:=B)) a (squaredRadii z))).2
  have hrad := squaredRadii_inverse ha (lattice_zero A B) (lattice_unit_fst hA hAB)
    (lattice_unit_snd hA hAB) (trapezoid_radial_surjective hAB ha (squaredRadii_mem_lower hz))
  rw [hrad]
  rw [show (fderiv ℝ (fun q : (TrapezoidWeight A B → ℝ) × DiskPair => diskInverse latticeIndex q.1 q.2) (a,z) v).2=
      fderiv ℝ (fun q : (TrapezoidWeight A B → ℝ) × DiskPair => (diskInverse latticeIndex q.1 q.2).2) (a,z) v from
      (congrArg (fun L => L v) hd.hasFDerivAt.snd.fderiv).symm]
  change _*complexArea (_ • _) (fderiv ℝ (fun q => _ • q.2.2) (a,z) v)=_
  rw [he]
  have hp : HasFDerivAt (fun q : (TrapezoidWeight A B → ℝ) × DiskPair => q.2.2)
      ((ContinuousLinearMap.snd ℝ ℂ ℂ).comp
        (ContinuousLinearMap.snd ℝ (TrapezoidWeight A B → ℝ) DiskPair)) (a,z) := by
    convert! ((ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt (x := z)).comp (a,z)
      ((ContinuousLinearMap.snd ℝ (TrapezoidWeight A B → ℝ) DiskPair).hasFDerivAt (x := (a,z))) using 1
  rw [hp.fderiv]
  change _*((Real.sqrt _)⁻¹^2*complexArea z.2 v.2.2)=_
  rw [inv_pow,Real.sq_sqrt hpos.le]
  field_simp

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem diskInverse_angular_comp {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    {a : X → TrapezoidWeight A B → ℝ} {z : X → DiskPair} {x : X}
    (ha : DifferentiableAt ℝ a x) (hz : DifferentiableAt ℝ z x)
    (hpos : ∀ i,0<a x i) (hdom : z x∈diskDomain A B) (v : X) :
    ((slope latticeIndex (a x) (squaredRadii (diskInverse latticeIndex (a x) (z x)))).1*
      complexArea (diskInverse latticeIndex (a x) (z x)).1
        (fderiv ℝ (fun q => diskInverse latticeIndex (a q) (z q)) x v).1 =
      complexArea (z x).1 (fderiv ℝ z x v).1) ∧
    ((slope latticeIndex (a x) (squaredRadii (diskInverse latticeIndex (a x) (z x)))).2*
      complexArea (diskInverse latticeIndex (a x) (z x)).2
        (fderiv ℝ (fun q => diskInverse latticeIndex (a q) (z q)) x v).2 =
      complexArea (z x).2 (fderiv ℝ z x v).2) := by
  have hi := (diskInverse_contDiffAt hA hAB hpos hdom).differentiableAt (by simp)
  have he : fderiv ℝ (fun q => diskInverse latticeIndex (a q) (z q)) x=
      (fderiv ℝ (fun q : (TrapezoidWeight A B → ℝ) × DiskPair => diskInverse latticeIndex q.1 q.2) (a x,z x)).comp
        ((fderiv ℝ a x).prod (fderiv ℝ z x)) := by
    convert! (hi.hasFDerivAt.comp x (ha.hasFDerivAt.prodMk hz.hasFDerivAt)).fderiv using 1
  rw [he]
  exact ⟨diskInverse_angular_fst hA hAB hpos hdom (fderiv ℝ a x v,fderiv ℝ z x v),
    diskInverse_angular_snd hA hAB hpos hdom (fderiv ℝ a x v,fderiv ℝ z x v)⟩

end PackingSufficiencySupport.FiniteMoment.Radial

namespace PackingSufficiencySupport.Hamiltonian
open scoped BigOperators ContDiff ComplexConjugate
open DiagonalQuadrics FiniteMoment FiniteMoment.Radial

variable {ι κ X : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

def coefficientSquares (G : ι → κ → ℂ) : ι → ℝ := fun i => phaseSq (complexCartesian (G i))

theorem coefficientSquares_contDiff : ContDiff ℝ ∞ (coefficientSquares (ι := ι) (κ := κ)) := by
  apply contDiff_pi.mpr
  intro i
  exact phaseSq_smooth.comp ((complexCartesian (ι := κ)).contDiff.comp (contDiff_apply ℝ (κ → ℂ) i))

def normalizedToricLift (k : ι → ℕ × ℕ) (G : ι → κ → ℂ) (z : DiskPair) : ι × κ → ℂ :=
  toricLift k G (diskInverse k (coefficientSquares G) z)

theorem coefficient_diskInverse_contDiffAt {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    {G : TrapezoidWeight A B → κ → ℂ} (hG : ∀ i,complexCartesian (G i)≠0)
    {z : DiskPair} (hz : z∈diskDomain A B) :
    ContDiffAt ℝ ∞ (fun q : (TrapezoidWeight A B → κ → ℂ) × DiskPair =>
      diskInverse latticeIndex (coefficientSquares q.1) q.2) (G,z) := by
  have hf : ContDiff ℝ ∞ (fun q : (TrapezoidWeight A B → κ → ℂ) × DiskPair =>
      (coefficientSquares q.1,q.2)) :=
    (coefficientSquares_contDiff.comp contDiff_fst).prodMk contDiff_snd
  exact (diskInverse_contDiffAt hA hAB (fun i => phaseSq_pos (hG i)) hz).comp (G,z) hf.contDiffAt

theorem normalizedToricLift_contDiffAt {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    {G : TrapezoidWeight A B → κ → ℂ} (hG : ∀ i,complexCartesian (G i)≠0)
    {z : DiskPair} (hz : z∈diskDomain A B) :
    ContDiffAt ℝ ∞ (fun q : (TrapezoidWeight A B → κ → ℂ) × DiskPair =>
      normalizedToricLift latticeIndex q.1 q.2) (G,z) := by
  have hi := coefficient_diskInverse_contDiffAt hA hAB hG hz
  apply contDiffAt_pi.mpr
  intro ij
  change ContDiffAt ℝ ∞ (fun q : (TrapezoidWeight A B → κ → ℂ) × DiskPair =>
    (diskInverse latticeIndex (coefficientSquares q.1) q.2).1 ^ (latticeIndex ij.1).1 *
    (diskInverse latticeIndex (coefficientSquares q.1) q.2).2 ^ (latticeIndex ij.1).2 * q.1 ij.1 ij.2) (G,z)
  have hg : ContDiffAt ℝ ∞ (fun q : (TrapezoidWeight A B → κ → ℂ) × DiskPair => q.1 ij.1 ij.2) (G,z) := by
    fun_prop
  exact ((hi.fst.pow _).mul (hi.snd.pow _)).mul hg

 theorem normalizedToricLift_pullback_primitive {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    {G : X → TrapezoidWeight A B → κ → ℂ} {z : X → DiskPair} {x : X}
    (hG : DifferentiableAt ℝ G x) (hz : DifferentiableAt ℝ z x)
    (hne : ∀ i,complexCartesian (G x i)≠0) (hdom : z x∈diskDomain A B) (v : X) (c : ℝ) :
    hopfPrimitive c (complexCartesian (normalizedToricLift latticeIndex (G x) (z x)))
      (complexCartesian (fderiv ℝ (fun q => normalizedToricLift latticeIndex (G q) (z q)) x v))=
    (∑ i,selected latticeIndex (coefficientSquares (G x)) (squaredRadii (z x)) i *
      hopfPrimitive c (complexCartesian (G x i)) (complexCartesian (fderiv ℝ G x v i)))+
    c/2*(complexArea (z x).1 (fderiv ℝ z x v).1+complexArea (z x).2 (fderiv ℝ z x v).2) := by
  have ha : DifferentiableAt ℝ (fun q => coefficientSquares (G q)) x := by
    convert! (coefficientSquares_contDiff.differentiable (by simp) (G x)).comp x hG using 1
  have hpos : ∀ i,0<coefficientSquares (G x) i := fun i => phaseSq_pos (hne i)
  have hi : DifferentiableAt ℝ (fun q => diskInverse latticeIndex (coefficientSquares (G q)) (z q)) x := by
    convert! ((diskInverse_contDiffAt hA hAB hpos hdom).differentiableAt (by simp)).comp x (ha.prodMk hz) using 1
  have hang := diskInverse_angular_comp hA hAB ha hz hpos hdom v
  have hrad := squaredRadii_inverse hpos (lattice_zero A B) (lattice_unit_fst hA hAB)
    (lattice_unit_snd hA hAB) (trapezoid_radial_surjective hAB hpos (squaredRadii_mem_lower hdom))
  unfold normalizedToricLift
  rw [toricLift_pullback_primitive hG hi hne v c]
  change (∑ i,probability latticeIndex (coefficientSquares (G x)) _ i*_)+c/2*(_+_)=_
  erw [hang.1,hang.2]
  rw [hrad]
  rfl

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff BigOperators
open Set Function
open Hamiltonian FiniteMoment FiniteMoment.Radial DiagonalQuadrics

def physicalDiskCoordinates (L : ℝ) : PlanePhase (Fin 2) →L[ℝ] DiskPair :=
  Real.sqrt (L*Real.pi) •
    (((ContinuousLinearMap.proj (0 : Fin 2)).comp (complexCartesian (ι := Fin 2)).symm.toContinuousLinearMap).prod
      ((ContinuousLinearMap.proj (1 : Fin 2)).comp (complexCartesian (ι := Fin 2)).symm.toContinuousLinearMap))

theorem physicalDiskCoordinates_apply (L : ℝ) (z : PlanePhase (Fin 2)) :
    physicalDiskCoordinates L z=(Real.sqrt (L*Real.pi) • (Complex.mk (z 0).1 (z 0).2),
      Real.sqrt (L*Real.pi) • (Complex.mk (z 1).1 (z 1).2)) := rfl

theorem physicalDiskCoordinates_squared {L : ℝ} (hL : 0≤L) (z : PlanePhase (Fin 2)) :
    squaredRadii (physicalDiskCoordinates L z)=physicalParameter L (planeMoments z) := by
  have hsq := Real.sq_sqrt (mul_nonneg hL Real.pi_pos.le)
  apply Prod.ext <;>
    simp only [physicalDiskCoordinates_apply,squaredRadii,Complex.normSq_apply,Complex.smul_re,
      Complex.smul_im,smul_eq_mul,physicalParameter,planeMoments,radialArea,radiusSq]
  all_goals nlinarith [sq_nonneg (z 0).1,sq_nonneg (z 0).2,sq_nonneg (z 1).1,sq_nonneg (z 1).2]

theorem physicalDiskCoordinates_mem {A B : ℕ} {L : ℝ} (hL : 0≤L) (z : PlanePhase (Fin 2)) :
    physicalDiskCoordinates L z∈diskDomain A B ↔
      physicalParameter L (planeMoments z)∈lowerTrapezoid A B := by
  rw [← physicalDiskCoordinates_squared hL z]
  exact ⟨squaredRadii_mem_lower,fun h => ⟨h.2.1,h.2.2.2⟩⟩

theorem complexArea_real_smul_both (r : ℝ) (z v : ℂ) :
    complexArea (r • z) (r • v)=r^2*complexArea z v := by
  simp only [complexArea_apply,Complex.smul_re,Complex.smul_im,smul_eq_mul]
  ring

theorem physicalDiskCoordinates_area {L : ℝ} (hL : 0≤L) (z v : PlanePhase (Fin 2)) :
    complexArea (physicalDiskCoordinates L z).1 (physicalDiskCoordinates L v).1+
      complexArea (physicalDiskCoordinates L z).2 (physicalDiskCoordinates L v).2=
      (L*Real.pi)*phaseArea z v := by
  change complexArea (Real.sqrt (L*Real.pi) • (Complex.mk (z 0).1 (z 0).2))
      (Real.sqrt (L*Real.pi) • (Complex.mk (v 0).1 (v 0).2))+
    complexArea (Real.sqrt (L*Real.pi) • (Complex.mk (z 1).1 (z 1).2))
      (Real.sqrt (L*Real.pi) • (Complex.mk (v 1).1 (v 1).2))=_
  rw [complexArea_real_smul_both,complexArea_real_smul_both,Real.sq_sqrt (mul_nonneg hL Real.pi_pos.le)]
  simp only [phaseArea_apply,Fin.sum_univ_two,complexArea_apply]
  ring

theorem physicalDiskCoordinates_primitive {L : ℝ} (hL : 0<L) (z v : PlanePhase (Fin 2)) :
    (1/(L*Real.pi))/2*(complexArea (physicalDiskCoordinates L z).1 (physicalDiskCoordinates L v).1+
      complexArea (physicalDiskCoordinates L z).2 (physicalDiskCoordinates L v).2)=
      (1/2:ℝ)*phaseArea z v := by
  rw [physicalDiskCoordinates_area hL.le]
  field_simp [hL.ne',Real.pi_ne_zero]

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold BigOperators
open FiniteMoment FiniteMoment.Radial DiagonalQuadrics
section

variable {κ E M : Type*} [Fintype κ] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

 theorem normalizedToricLift_manifold_primitive {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    {G : M → TrapezoidWeight A B → κ → ℂ} {z : M → DiskPair} {x : M}
    (hG : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,TrapezoidWeight A B → κ → ℂ) G x)
    (hz : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,DiskPair) z x)
    (hne : ∀ i,complexCartesian (G x i)≠0) (hdom : z x∈diskDomain A B) (v : E) (c : ℝ) :
    hopfPrimitive c (complexCartesian (normalizedToricLift latticeIndex (G x) (z x)))
      (complexCartesian (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,TrapezoidWeight A B × κ → ℂ)
        (fun q => normalizedToricLift latticeIndex (G q) (z q)) x v))=
    (∑ i,selected latticeIndex (coefficientSquares (G x)) (squaredRadii (z x)) i *
      hopfPrimitive c (complexCartesian (G x i))
        (complexCartesian (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,TrapezoidWeight A B → κ → ℂ) G x v i)))+
      c/2*(complexArea (z x).1 (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,DiskPair) z x v).1+
        complexArea (z x).2 (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,DiskPair) z x v).2) := by
  let f : M → (TrapezoidWeight A B → κ → ℂ) × DiskPair := fun q => (G q,z q)
  have hf : HasMFDerivAt 𝓘(ℝ,E) 𝓘(ℝ,(TrapezoidWeight A B → κ → ℂ) × DiskPair) f x
      ((mfderiv 𝓘(ℝ,E) 𝓘(ℝ,TrapezoidWeight A B → κ → ℂ) G x).prod
        (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,DiskPair) z x)) :=
    ⟨hG.hasMFDerivAt.1.prodMk hz.hasMFDerivAt.1,
      hG.hasMFDerivAt.2.prodMk hz.hasMFDerivAt.2⟩
  have ht := (normalizedToricLift_contDiffAt hA hAB hne hdom).differentiableAt (by simp)
  have hd := ht.hasFDerivAt.hasMFDerivAt.comp x hf
  rw [show mfderiv 𝓘(ℝ,E) 𝓘(ℝ,TrapezoidWeight A B × κ → ℂ)
      (fun q => normalizedToricLift latticeIndex (G q) (z q)) x=_ from hd.mfderiv]
  convert! normalizedToricLift_pullback_primitive
      (X := (TrapezoidWeight A B → κ → ℂ) × DiskPair) hA hAB
      (differentiableAt_fst (p := (G x,z x))) (differentiableAt_snd (p := (G x,z x))) hne hdom
      ((mfderiv 𝓘(ℝ,E) 𝓘(ℝ,TrapezoidWeight A B → κ → ℂ) G x v),
        (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,DiskPair) z x v)) c using 1
  simp only [fderiv_fst,fderiv_snd]
  rfl

end

variable {ι E M : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

 theorem affineFSPrimitive_hopf_manifold {G : M → ι → ℂ} {x : M}
    (hG : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,ι → ℂ) G x) (c : ℝ) (v : E) :
    hopfPrimitive c (complexCartesian (complexAffineLift (G x)))
      (complexCartesian (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,Option ι → ℂ)
        (fun y => complexAffineLift (G y)) x v))=
    affineFSPrimitive c (complexCartesian (G x))
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,PlanePhase ι) (fun y => complexCartesian (G y)) x v) := by
  have hL := complexAffineLift_smooth.differentiable (by simp) (G x)
  have hd := hL.hasFDerivAt.hasMFDerivAt.comp x hG.hasMFDerivAt
  have hd' := (complexCartesian (ι := ι)).hasFDerivAt.hasMFDerivAt.comp x hG.hasMFDerivAt
  rw [show mfderiv 𝓘(ℝ,E) 𝓘(ℝ,Option ι → ℂ)
      (fun y => complexAffineLift (G y)) x=_ from hd.mfderiv,
    show mfderiv 𝓘(ℝ,E) 𝓘(ℝ,PlanePhase ι) (fun y => complexCartesian (G y)) x=_ from hd'.mfderiv]
  exact affineFSPrimitive_hopf c (G x) (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ι → ℂ) G x v)

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment FiniteMoment.Radial

 def weightedCoefficient (D m : ℕ) (x : BaseCurve) : WeightedHomogeneousIndex → ℂ :=
  complexAffineLift ((complexCartesian (ι := Option (Fin 3))).symm (weightedPhaseInclusion D m x))

 theorem weightedCoefficient_smooth (D m : ℕ) :
    ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,WeightedHomogeneousIndex → ℂ) ∞ (weightedCoefficient D m) :=
  complexAffineLift_smooth.contMDiff.comp
    ((complexCartesian (ι := Option (Fin 3))).symm.contDiff.contMDiff.comp
      (weightedPhaseInclusion_smooth D m))

 theorem weightedCoefficient_nonzero (D m : ℕ) (x : BaseCurve) :
    complexCartesian (weightedCoefficient D m x)≠0 := by
  intro h
  have he := congrFun (complexCartesian.injective (h.trans (map_zero _).symm)) none
  exact one_ne_zero (by simpa only [weightedCoefficient,complexAffineLift_none,Pi.zero_apply] using he)

 theorem weightedCoefficient_norm (D m : ℕ) (x : BaseCurve) :
    phaseSq (complexCartesian (weightedCoefficient D m x))=coefficientNorm D m x := by
  rw [weightedCoefficient,complexAffineLift_sq,ContinuousLinearEquiv.apply_symm_apply]
  rfl

 theorem weightedCoefficient_hopf (D m : ℕ) (x : BaseCurve) (v : RealModel) (c : ℝ) :
    hopfPrimitive c (complexCartesian (weightedCoefficient D m x))
      (complexCartesian (mfderiv 𝓘(ℝ,RealModel) 𝓘(ℝ,WeightedHomogeneousIndex → ℂ)
        (weightedCoefficient D m) x v))=weightedFSPrimitive D m c x v := by
  have hG := ((complexCartesian (ι := Option (Fin 3))).symm.contDiff.contMDiff.comp
      (weightedPhaseInclusion_smooth D m)).mdifferentiable (by simp) x
  have he : (fun y : BaseCurve => complexCartesian
      ((complexCartesian (ι := Option (Fin 3))).symm (weightedPhaseInclusion D m y)))=
      weightedPhaseInclusion D m := by
    funext y
    exact (complexCartesian (ι := Option (Fin 3))).apply_symm_apply _
  have hh := affineFSPrimitive_hopf_manifold hG c v
  simp only [Function.comp_apply] at hh
  rw [he,ContinuousLinearEquiv.apply_symm_apply] at hh
  exact hh

 def cubicCoefficients {A B : ℕ} (D S : ℕ) (x : BaseCurve)
    (i : TrapezoidWeight A B) : WeightedHomogeneousIndex → ℂ :=
  weightedCoefficient (cubicDegree D i) (cubicMarkedOrder S i) x

 theorem cubicCoefficients_smooth {A B : ℕ} (D S : ℕ) :
    ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,TrapezoidWeight A B → WeightedHomogeneousIndex → ℂ)
      ∞ (cubicCoefficients (A := A) (B := B) D S) :=
  contMDiff_pi_space.mpr (fun _ => weightedCoefficient_smooth _ _)

 theorem cubicCoefficients_squares {A B : ℕ} (D S : ℕ) (x : BaseCurve) :
    coefficientSquares (cubicCoefficients (A := A) (B := B) D S x)=
      fun i => coefficientNorm (cubicDegree D i) (cubicMarkedOrder S i) x := by
  funext i
  exact weightedCoefficient_norm _ _ _

 def physicalPolynomialLift {A B : ℕ} (D S : ℕ) (L : ℝ)
    (x : BaseCurve × PlanePhase (Fin 2)) : TrapezoidWeight A B × WeightedHomogeneousIndex → ℂ :=
  normalizedToricLift latticeIndex (cubicCoefficients D S x.1) (physicalDiskCoordinates L x.2)

 theorem physicalPolynomialLift_smoothAt {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    (D S : ℕ) {L : ℝ} (hL : 0≤L) {x : BaseCurve × PlanePhase (Fin 2)}
    (hx : physicalParameter L (planeMoments x.2)∈lowerTrapezoid A B) :
    ContMDiffAt 𝓘(ℝ,RealModel × PlanePhase (Fin 2))
      𝓘(ℝ,TrapezoidWeight A B × WeightedHomogeneousIndex → ℂ) ∞
        (physicalPolynomialLift (A := A) (B := B) D S L) x := by
  have hG := (cubicCoefficients_smooth (A := A) (B := B) D S).comp (flatProduct_fst_smooth (V := PlanePhase (Fin 2)))
  have hz := (physicalDiskCoordinates L).contDiff.contMDiff.comp
    (flatProduct_snd_smooth (E := RealModel) (M := BaseCurve) (V := PlanePhase (Fin 2)))
  exact (normalizedToricLift_contDiffAt hA hAB (fun _ => weightedCoefficient_nonzero _ _ _)
    ((physicalDiskCoordinates_mem hL x.2).mpr hx)).contMDiffAt.comp x (hG.prodMk_space hz).contMDiffAt

 theorem physicalPolynomialLift_primitive {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    (D S : ℕ) {L : ℝ} (hL : 0<L) {x : BaseCurve × PlanePhase (Fin 2)}
    (hx : physicalParameter L (planeMoments x.2)∈lowerTrapezoid A B)
    (v : RealModel × PlanePhase (Fin 2)) :
    hopfPrimitive (1/(L*Real.pi)) (complexCartesian (physicalPolynomialLift (A := A) (B := B) D S L x))
      (complexCartesian (mfderiv 𝓘(ℝ,RealModel × PlanePhase (Fin 2))
        𝓘(ℝ,TrapezoidWeight A B × WeightedHomogeneousIndex → ℂ)
          (physicalPolynomialLift (A := A) (B := B) D S L) x v))=
    (productHorizontalLift (E := RealModel) (M := BaseCurve) (V := PlanePhase (Fin 2)) (physicalPrimitive (A := A) (B := B) D S (1/(L*Real.pi)) L ∘ planeMoments)+
      (verticalLiouville : ManifoldOneForm (RealModel × PlanePhase (Fin 2)) (BaseCurve × PlanePhase (Fin 2)))) x v := by
  let G : BaseCurve × PlanePhase (Fin 2) → TrapezoidWeight A B → WeightedHomogeneousIndex → ℂ :=
    fun q => cubicCoefficients D S q.1
  let z : BaseCurve × PlanePhase (Fin 2) → DiskPair := fun q => physicalDiskCoordinates L q.2
  have hG := (cubicCoefficients_smooth (A := A) (B := B) D S).comp (flatProduct_fst_smooth (V := PlanePhase (Fin 2)))
  have hz := (physicalDiskCoordinates L).contDiff.contMDiff.comp
    (flatProduct_snd_smooth (E := RealModel) (M := BaseCurve) (V := PlanePhase (Fin 2)))
  have hdG (i : TrapezoidWeight A B) :
      mfderiv 𝓘(ℝ,RealModel × PlanePhase (Fin 2))
        𝓘(ℝ,TrapezoidWeight A B → WeightedHomogeneousIndex → ℂ) G x v i=
      mfderiv 𝓘(ℝ,RealModel) 𝓘(ℝ,WeightedHomogeneousIndex → ℂ)
        (weightedCoefficient (cubicDegree D i) (cubicMarkedOrder S i)) x.1 v.1 := by
    have hi := (ContinuousLinearMap.proj i :
      (TrapezoidWeight A B → WeightedHomogeneousIndex → ℂ) →L[ℝ] (WeightedHomogeneousIndex → ℂ)).hasFDerivAt.hasMFDerivAt.comp x
          (hG.mdifferentiable (by simp) x).hasMFDerivAt
    have hf := manifoldMapDifferential_comp
      ((weightedCoefficient_smooth (cubicDegree D i) (cubicMarkedOrder S i)).mdifferentiable (by simp) x.1)
      ((flatProduct_fst_smooth (V := PlanePhase (Fin 2))).mdifferentiable (by simp) x)
    have he : mfderiv 𝓘(ℝ,RealModel × PlanePhase (Fin 2)) 𝓘(ℝ,WeightedHomogeneousIndex → ℂ)
        (fun q : BaseCurve × PlanePhase (Fin 2) => G q i) x=
      (ContinuousLinearMap.proj i).comp
        (mfderiv 𝓘(ℝ,RealModel × PlanePhase (Fin 2))
          𝓘(ℝ,TrapezoidWeight A B → WeightedHomogeneousIndex → ℂ) G x) := hi.mfderiv
    have hev := congrArg (fun T => T v) he
    have hfv := congrArg (fun T => T v) hf
    simp only [manifoldMapDifferential] at hfv
    erw [flatProduct_fst_derivative] at hfv
    exact hev.symm.trans hfv
  have hdz : mfderiv 𝓘(ℝ,RealModel × PlanePhase (Fin 2)) 𝓘(ℝ,DiskPair) z x v=
      physicalDiskCoordinates L v.2 := by
    have he := (physicalDiskCoordinates L).hasFDerivAt.hasMFDerivAt.comp x
      ((flatProduct_snd_smooth (E := RealModel) (M := BaseCurve) (V := PlanePhase (Fin 2))).mdifferentiable (by simp) x).hasMFDerivAt
    rw [show mfderiv 𝓘(ℝ,RealModel × PlanePhase (Fin 2)) 𝓘(ℝ,DiskPair) z x=_ from he.mfderiv,
      flatProduct_snd_derivative]
    rfl
  have hh := normalizedToricLift_manifold_primitive hA hAB
    (hG.mdifferentiable (by simp) x) (hz.mdifferentiable (by simp) x)
    (fun _ => weightedCoefficient_nonzero _ _ _) ((physicalDiskCoordinates_mem hL.le x.2).mpr hx) v (1/(L*Real.pi))
  change hopfPrimitive _ _ (complexCartesian (mfderiv _ _ (fun q => normalizedToricLift latticeIndex (G q) (z q)) x v))=_
  erw [hh]
  change (∑ i,selected latticeIndex (coefficientSquares (cubicCoefficients D S x.1))
      (squaredRadii (physicalDiskCoordinates L x.2)) i *
      hopfPrimitive _ (complexCartesian (weightedCoefficient (cubicDegree D i) (cubicMarkedOrder S i) x.1))
        (complexCartesian (mfderiv 𝓘(ℝ,RealModel × PlanePhase (Fin 2)) 𝓘(ℝ,TrapezoidWeight A B → WeightedHomogeneousIndex → ℂ) G x v i)))+_= _
  simp_rw [hdG,weightedCoefficient_hopf]
  erw [hdz]
  simp only [Function.comp_apply]
  erw [physicalDiskCoordinates_primitive hL]
  rw [cubicCoefficients_squares,physicalDiskCoordinates_squared hL.le]
  simp only [Pi.add_apply,add_apply,productHorizontalLift,physicalPrimitive,radialPrimitive,radialProbability,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_fst',sum_apply,smul_apply,smul_eq_mul,
    verticalLiouville_apply,Function.comp_apply]

end PackingSufficiencySupport.CubicModel
end

end OAI
