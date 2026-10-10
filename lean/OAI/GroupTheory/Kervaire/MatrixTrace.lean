import OAI.GroupTheory.Kervaire.RegularOperators

namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate

namespace KervaireMatrix

section
open KervaireRegular
variable {D A : Type*} [Group A]
abbrev Space (D A : Type*) := ℓ²(D × A, ℂ)
abbrev Operator (D A : Type*) := Space D A →L[ℂ] Space D A

/-- Diagonal right translations on the finite multiple of the regular Hilbert space. -/
def right (a : A) : Space D A ≃ₗᵢ[ℂ] Space D A :=
  reindex (Equiv.prodCongr (Equiv.refl D) (Equiv.mulRight a⁻¹))

@[simp] theorem right_apply (a : A) (f : Space D A) (j : D) (x : A) :
    right a f (j,x) = f (j,x*a) := by simp [right]

@[simp] theorem right_delta (a x : A) (j : D) :
    right a (delta (j,x)) = delta (j,x*a⁻¹) := by simp [right]

@[simp] theorem right_star (a : A) :
    star (right (D := D) a : Operator D A) = (right (D := D) a⁻¹ : Operator D A) := by
  rw [ContinuousLinearMap.star_eq_adjoint, LinearIsometryEquiv.adjoint_eq_symm]
  ext f ⟨j,x⟩
  simp [right, reindex_symm, reindex_apply]

/-- The finite matrix group von Neumann algebra, before bundling. -/
def InCommutant (T : Operator D A) : Prop := ∀ a : A, Commute T (right (D := D) a : Operator D A)

/-- Matrix equivariance with no countability restriction. -/
theorem matrix_coefficient {T : Operator D A} (hT : InCommutant T)
    (i j : D) (x y : A) : T (delta (j,y)) (i,x) = T (delta (j,1)) (i,x*y⁻¹) := by
  have he : T (delta (j,y)) = right y⁻¹ (T (delta (j,1))) := by
    have h := DFunLike.congr_fun (hT y⁻¹).eq (delta (j,1))
    simpa using h
  rw [he, right_apply]

/-- The reflected matrix coefficient identity for adjoints. -/
theorem star_coefficient {T : Operator D A} (hT : InCommutant T)
    (i j : D) (x : A) :
    star (star T (delta (i,1)) (j,x)) = T (delta (j,1)) (i,x⁻¹) := by
  calc
    star (star T (delta (i,1)) (j,x)) =
        inner ℂ (star T (delta (i,1))) (delta (j,x)) :=
      (inner_delta_right _ _).symm
    _ = inner ℂ (delta (i,1)) (T (delta (j,x))) := by
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
    _ = T (delta (j,x)) (i,1) := inner_delta_left _ _
    _ = T (delta (j,1)) (i,x⁻¹) := by simpa using matrix_coefficient hT i j 1 x

variable [Fintype D]

def trace : Operator D A →L[ℂ] ℂ :=
  ∑ i : D, (innerSL ℂ (delta (i,(1 : A)))).comp
    (ContinuousLinearMap.apply ℂ (Space D A) (delta (i,1)))

@[simp] theorem trace_apply (T : Operator D A) :
    trace T = ∑ i : D, inner ℂ (delta (i,1)) (T (delta (i,1))) := by simp [trace]

@[simp] theorem trace_eq_coefficient (T : Operator D A) :
    trace T = ∑ i : D, T (delta (i,1)) (i,1) := by simp

@[simp] theorem trace_one : trace (1 : Operator D A) = Fintype.card D := by
  classical
  simp [delta]

omit [Fintype D] in
/-- All double series below are absolutely summable, even for an uncountable group. -/
theorem summable_product_coefficients {S T : Operator D A} (hS : InCommutant S) (i : D) :
    Summable (fun p : D × A => S (delta (p.1,1)) (i,p.2⁻¹) * T (delta (i,1)) p) := by
  have h := lp.summable_inner (𝕜 := ℂ) (star S (delta (i,1))) (T (delta (i,1)))
  apply h.congr
  rintro ⟨j,x⟩
  rw [RCLike.inner_apply, mul_comm]
  change star (star S (delta (i,1)) (j,x)) * _ = _
  rw [star_coefficient hS]

/-- Trace multiplication expressed by regular matrix coefficients. -/
theorem trace_mul_eq_sum_tsum {S T : Operator D A} (hS : InCommutant S) :
    trace (S*T) = ∑ i : D, ∑ j : D, ∑' x : A,
      S (delta (j,1)) (i,x⁻¹) * T (delta (i,1)) (j,x) := by
  rw [trace_apply]
  apply Finset.sum_congr rfl
  intro i _
  change inner ℂ (delta (i,1)) (S (T (delta (i,1)))) = _
  rw [← ContinuousLinearMap.adjoint_inner_left, lp.inner_eq_tsum]
  simp only [← ContinuousLinearMap.star_eq_adjoint]
  have he : (∑' p : D × A, inner ℂ (star S (delta (i,1)) p) (T (delta (i,1)) p)) =
      ∑' p : D × A, S (delta (p.1,1)) (i,p.2⁻¹) * T (delta (i,1)) p := by
    apply tsum_congr
    rintro ⟨j,x⟩
    rw [RCLike.inner_apply, mul_comm]
    change star (star S (delta (i,1)) (j,x)) * _ = _
    rw [star_coefficient hS]
  rw [he, (summable_product_coefficients hS i).tsum_prod, tsum_fintype]

/-- Full cyclicity of the finite matrix regular trace. -/
theorem trace_mul_comm {S T : Operator D A} (hS : InCommutant S) (hT : InCommutant T) :
    trace (S*T) = trace (T*S) := by
  rw [trace_mul_eq_sum_tsum hS, trace_mul_eq_sum_tsum hT, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  calc
    (∑' x : A, S (delta (i,1)) (j,x⁻¹) * T (delta (j,1)) (i,x)) =
        ∑' x : A, S (delta (i,1)) (j,x) * T (delta (j,1)) (i,x⁻¹) := by
      simpa using (Equiv.inv A).tsum_eq
        (fun x : A => S (delta (i,1)) (j,x) * T (delta (j,1)) (i,x⁻¹))
    _ = _ := tsum_congr fun _ => mul_comm _ _

end

section
open KervaireRegular
variable {D A : Type*} [Fintype D] [Group A]

omit [Fintype D] in
/-- The complete finite frame is separating for the right regular commutant. -/
theorem eq_zero_of_frame {T : Operator D A} (hT : InCommutant T)
    (h : ∀ i : D, T (delta (i,1)) = 0) : T = 0 := by
  classical
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ENNReal) ≠ ⊤)
  rintro ⟨j,x⟩
  apply ContinuousLinearMap.ext
  intro c
  simp only [ContinuousLinearMap.comp_apply, lp.singleContinuousLinearMap_apply, zero_apply]
  have hi : T (delta (j,x)) = 0 := by
    ext ⟨i,y⟩
    rw [matrix_coefficient hT, h]
    rfl
  have hc : lp.single 2 (j,x) c = c • delta (j,x) := by
    ext p
    simp [delta, Pi.single_apply]
  rw [hc, map_smul, hi, smul_zero]

/-- The real trace of a positive square is the sum of squared column norms. -/
theorem re_trace_star_mul_self (T : Operator D A) :
    (trace (star T*T)).re = ∑ i : D, ‖T (delta (i,1))‖^2 := by
  rw [trace_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  change (inner ℂ (delta (i,1)) (star T (T (delta (i,1))))).re = _
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  change RCLike.re (inner ℂ (T (delta (i,1))) (T (delta (i,1)))) = _
  exact inner_self_eq_norm_sq _

/-- Faithfulness of the real matrix trace, in positive-square form. -/
theorem re_trace_star_mul_self_eq_zero_iff {T : Operator D A} (hT : InCommutant T) :
    (trace (star T*T)).re = 0 ↔ T = 0 := by
  rw [re_trace_star_mul_self]
  constructor
  · intro h
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖T (delta (i,1))‖)).mp h
    apply eq_zero_of_frame hT
    intro i
    apply norm_eq_zero.mp
    exact (pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp (hi i (Finset.mem_univ i))
  · rintro rfl
    simp

local instance : ContinuousFunctionalCalculus ℝ (Operator D A) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus (A := Operator D A)

omit [Fintype D] in
/-- Square roots preserve the matrix commutant. -/
theorem InCommutant.sqrt {T : Operator D A} (hT : InCommutant T) :
    InCommutant (CFC.sqrt T) := fun a => (hT a).cfcₙ_nnreal NNReal.sqrt

theorem re_trace_eq_zero_iff_of_nonneg {T : Operator D A} (hT : InCommutant T)
    (hpos : 0 ≤ T) : (trace T).re = 0 ↔ T = 0 := by
  have hs : star (CFC.sqrt T) = CFC.sqrt T :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg T)).star_eq
  constructor
  · intro ht
    have hz : (trace (star (CFC.sqrt T)*CFC.sqrt T)).re = 0 := by
      rwa [hs, CFC.sqrt_mul_sqrt_self T hpos]
    have hz' := (re_trace_star_mul_self_eq_zero_iff hT.sqrt).mp hz
    exact (CFC.sqrt_eq_zero_iff T hpos).mp hz'
  · rintro rfl
    simp

end

section
open KervaireRegular KervaireSpectral
variable {D A : Type*} [Group A]

/-- The closed algebra `M_D(M_A)` represented on the arbitrary-group Hilbert space. -/
def algebra : StarSubalgebra ℂ (Operator D A) :=
  KervaireCentralizer.algebra (Set.range (fun a : A => (right (D := D) a : Operator D A)))

theorem mem_algebra (T : Operator D A) : T ∈ algebra ↔ InCommutant T := by
  rw [algebra, KervaireCentralizer.algebra, StarSubalgebra.mem_centralizer_iff]
  constructor
  · intro h a
    exact ((h (right (D := D) a) ⟨a,rfl⟩).1).symm
  · intro h R hR
    obtain ⟨a,rfl⟩ := hR
    rw [right_star]
    exact ⟨(h a).symm, (h a⁻¹).symm⟩

variable [Fintype D]

/-- The vector family agrees exactly with the unnormalized matrix trace. -/
theorem trace_eq_vectorSum : (trace : Operator D A →L[ℂ] ℂ) =
    vectorSum (fun i : D => (delta (i,(1 : A)))) := rfl

/-- The regular Hilbert space is nonzero whenever the finite index set is inhabited. -/
instance [Nonempty D] : Nontrivial (Space D A) := by
  classical
  let i : D := Classical.choice inferInstance
  refine ⟨⟨delta (i,(1 : A)), 0, ?_⟩⟩
  intro h
  have hh := congrArg (fun f : Space D A => f (i,1)) h
  simp [delta] at hh

def phase (U : Operator D A) [IsStarNormal U] : ℝ :=
  sumPhase U (fun i : D => delta (i,(1 : A)))

/-- Subadditivity for the full arbitrary-group matrix algebra, with no approximation hypothesis. -/
theorem phase_mul_le [Nonempty D] (U V : algebra (D := D) (A := A))
    (hU : U ∈ unitary (algebra (D := D) (A := A)))
    (hV : V ∈ unitary (algebra (D := D) (A := A))) :
    let _ := isStarNormal_of_mem_unitary ((KervaireCentralizer.unitary_iff _ U).mp hU)
    let _ := isStarNormal_of_mem_unitary ((KervaireCentralizer.unitary_iff _ V).mp hV)
    let _ := isStarNormal_of_mem_unitary ((KervaireCentralizer.unitary_iff _ (U*V)).mp
      ((unitary _).mul_mem hU hV))
    phase ((U*V : algebra (D := D) (A := A)) : Operator D A) ≤
      phase (U : Operator D A) + phase (V : Operator D A) := by
  apply KervaireCentralizer.phase_subadditive _ _ _ U V hU hV
  intro X Y
  change vectorSum _ ((X : Operator D A)*(Y : Operator D A)) =
    vectorSum _ ((Y : Operator D A)*(X : Operator D A))
  rw [← trace_eq_vectorSum]
  exact trace_mul_comm ((mem_algebra _).mp X.property) ((mem_algebra _).mp Y.property)

/-- Phase is nonnegative. -/
theorem phase_nonneg (U : Operator D A) (hU : U ∈ unitary (Operator D A)) :
    let _ := isStarNormal_of_mem_unitary hU
    0 ≤ phase U := by
  let _ := isStarNormal_of_mem_unitary hU
  obtain ⟨B,hB,_,_,_,hvec,_⟩ := exists_phaseOperator U hU
  apply Finset.sum_nonneg
  intro i _
  rw [← hvec]
  exact (ContinuousLinearMap.nonneg_iff_isPositive.mp hB).re_inner_nonneg_right _

/-- The scalar identity has zero phase, including the precise cut convention. -/
theorem phase_one [Nonempty D] : phase (1 : Operator D A) = 0 := by
  unfold phase sumPhase vectorPhase
  apply Finset.sum_eq_zero
  intro i _
  have hf : (fun z : spectrum ℂ (1 : Operator D A) => KervaireSpectral.phase z) = 0 := by
    funext z
    have hz : (z : ℂ) = 1 := by simpa using z.property
    simp [hz]
  simp [hf]

/-- Vanishing of the phase detects the identity in the faithful regular algebra. -/
theorem phase_eq_zero_iff [Nonempty D] (U : algebra (D := D) (A := A))
    (hU : U ∈ unitary (algebra (D := D) (A := A))) :
    let _ := isStarNormal_of_mem_unitary ((KervaireCentralizer.unitary_iff _ U).mp hU)
    phase (U : Operator D A) = 0 ↔ U = 1 := by
  have hU' := (KervaireCentralizer.unitary_iff _ U).mp hU
  let _ := isStarNormal_of_mem_unitary hU'
  obtain ⟨B,hB,hBU,hvec⟩ := KervaireCentralizer.exists_phaseOperator_mem _ U hU
  have he : (trace (B : Operator D A)).re = phase (U : Operator D A) := by
    rw [trace_eq_vectorSum, vectorSum_apply, Complex.re_sum]
    exact Finset.sum_congr rfl (fun i _ => hvec (delta (i,1)))
  constructor
  · intro h
    have hz : (B : Operator D A) = 0 :=
      (re_trace_eq_zero_iff_of_nonneg ((mem_algebra _).mp B.property) hB).mp (he.trans h)
    have hz' : B = 0 := Subtype.ext hz
    rw [hz'] at hBU
    apply Subtype.ext
    have hh := congrArg Subtype.val hBU
    simpa [KervaireTraceCalculus.phaseVelocity] using hh.symm
  · rintro rfl
    exact phase_one

end

open KervaireRegular KervaireSpectral
variable {D A : Type*} [Fintype D] [Group A]

omit [Fintype D] in
theorem InCommutant.mul {S T : Operator D A} (hS : InCommutant S) (hT : InCommutant T) :
    InCommutant (S*T) := fun a => (hS a).mul_left (hT a)

omit [Fintype D] in
theorem InCommutant.pow {S : Operator D A} (hS : InCommutant S) (n : ℕ) :
    InCommutant (S^n) := fun a => (hS a).pow_left n

omit [Fintype D] in
theorem InCommutant.star {S : Operator D A} (hS : InCommutant S) :
    InCommutant (star S) :=
  (mem_algebra _).mp (star_mem ((mem_algebra S).mpr hS))

omit [Fintype D] [Group A] in
/-- Telescope powers without a finite-dimensional restriction on the Hilbert space. -/
theorem conjugate_pow (U Q : Operator D A) (hQ : Q ∈ unitary (Operator D A)) (n : ℕ) :
    (Q*U*star Q)^n = Q*U^n*star Q := by
  induction n with
  | zero => simpa using (Unitary.mem_iff.mp hQ).2.symm
  | succ n ih =>
    rw [pow_succ, ih, pow_succ]
    calc (Q * U^n * star Q) * (Q * U * star Q) =
        Q * U^n * (star Q * Q) * U * star Q := by noncomm_ring
         _ = Q * (U^n * U) * star Q := by rw [(Unitary.mem_iff.mp hQ).1]; noncomm_ring

/-- Conjugation invariance of the exact phase in the arbitrary-group regular algebra. -/
theorem phase_conjugate (U Q : Operator D A)
    (hU : U ∈ unitary (Operator D A)) (hQ : Q ∈ unitary (Operator D A))
    (hUc : InCommutant U) (hQc : InCommutant Q) :
    let _ := isStarNormal_of_mem_unitary hU
    let _ := isStarNormal_of_mem_unitary (mul_mem (mul_mem hQ hU) (Unitary.star_mem hQ))
    KervaireMatrix.phase (Q*U*star Q) = KervaireMatrix.phase U := by
  apply sumPhase_eq_of_moments _ _
    (mul_mem (mul_mem hQ hU) (Unitary.star_mem hQ)) hU
    (fun i : D => delta (i,(1 : A))) (fun i : D => delta (i,(1 : A)))
  intro n
  rw [← trace_eq_vectorSum, conjugate_pow U Q hQ n,
    trace_mul_comm (hQc.mul (hUc.pow n)) hQc.star, ← mul_assoc,
    (Unitary.mem_iff.mp hQ).1, one_mul]

/-- Matrix trace of the root-grid phase identity, retaining the unnormalized dimension. -/
theorem phase_grid (U : Operator D A) (hU : U ∈ unitary (Operator D A))
    (d : ℕ) (hd : 0 < d) :
    let _ := isStarNormal_of_mem_unitary hU
    let _ := isStarNormal_of_mem_unitary (pow_mem hU d)
    let _ := fun j : Fin d => isStarNormal_of_mem_unitary
      (Unitary.smul_mem ⟨scalarRotation ((j.val : ℝ)/d), scalarRotation_unitary _⟩ hU)
    (∑ j : Fin d, KervaireMatrix.phase (scalarRotation ((j.val : ℝ)/d) • U)) =
      (Fintype.card D : ℝ) * ((d : ℝ)-1)/2 + KervaireMatrix.phase (U^d) := by
  let _ := isStarNormal_of_mem_unitary hU
  let _ := isStarNormal_of_mem_unitary (pow_mem hU d)
  change (∑ j : Fin d, ∑ i : D,
    vectorPhase (scalarRotation ((j.val : ℝ)/d) • U) (delta (i,(1 : A)))) = _
  rw [Finset.sum_comm]
  simp_rw [sum_vectorPhase_grid U hU d hd]
  rw [Finset.sum_add_distrib]
  congr 1
  have hn (i : D) : ‖delta (i,(1 : A))‖ = 1 := by
    simp [delta, lp.norm_single]
  simp_rw [hn]
  simp
  ring

end KervaireMatrix

end

end OAI
