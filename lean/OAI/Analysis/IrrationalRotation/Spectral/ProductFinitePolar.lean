import OAI.Analysis.IrrationalRotation.Model.Product
import OAI.Analysis.IrrationalRotation.Model.ConcreteSpectral
import OAI.Analysis.IrrationalRotation.Rotation.FieldDiagonal
import OAI.Analysis.IrrationalRotation.Analysis.FiniteOrbitAtomic

namespace OAI

noncomputable section
open MeasureTheory Filter

namespace Invariant233.ProductModel

theorem rotationIterate_measurePreserving_polar (θ : ℕ → ℝ) (k : ℤ) :
    MeasurePreserving (rotationIterate θ k) baseMeasure baseMeasure := by
  let : circleMeasure.IsAddRightInvariant := by
    unfold circleMeasure
    infer_instance
  constructor
  · apply Measurable.of_eval
    intro i
    exact (measurable_pi_apply i).add_const _
  · unfold baseMeasure rotationIterate
    rw [Measure.infinitePi_map_pi (fun _ : ℕ => circleMeasure)
      (f := fun i (x : Circle) => x + (((k : ℝ) * θ i : ℝ) : Circle))
      (fun i => measurable_id.add_const _)]
    congr 1
    funext i
    exact (measurePreserving_add_right circleMeasure (((k : ℝ) * θ i : ℝ) : Circle)).map_eq

private abbrev signedShift (m : ℤ) : Hilbert →L[ℂ] Hilbert :=
  (WeightedShift.shift m).toLinearIsometry.toContinuousLinearMap.compLpL 2 baseMeasure

theorem shiftOperator_star_eq : star shiftOperator = signedShift (-1) := by
  have hu := WeightedShift.fieldShift_mem_unitary (μ := baseMeasure) 1
  have hleft : star shiftOperator * shiftOperator = 1 := (Unitary.mem_iff.mp hu).1
  have hright : shiftOperator * signedShift (-1) = 1 := by
    change signedShift 1 * signedShift (-1) = 1
    rw [← WeightedShift.fieldShift_add]
    simpa using (WeightedShift.fieldShift_zero (μ := baseMeasure))
  calc
    star shiftOperator = star shiftOperator * 1 := (mul_one _).symm
    _ = star shiftOperator * (shiftOperator * signedShift (-1)) := by rw [hright]
    _ = signedShift (-1) := by rw [← mul_assoc, hleft, one_mul]

theorem shiftOperator_pow_eq (n : ℕ) : shiftOperator ^ n = signedShift n := by
  induction n with
  | zero => simpa only [pow_zero, Nat.cast_zero] using
      (WeightedShift.fieldShift_zero (μ := baseMeasure)).symm
  | succ n ih =>
      rw [pow_succ, ih]
      change signedShift (n : ℤ) * signedShift 1 = signedShift (n + 1 : ℕ)
      rw [← WeightedShift.fieldShift_add]
      simp only [Nat.cast_add, Nat.cast_one]

theorem star_shiftOperator_pow_eq (n : ℕ) : star shiftOperator ^ n = signedShift (-(n : ℤ)) := by
  induction n with
  | zero => simpa only [pow_zero, Nat.cast_zero, neg_zero] using
      (WeightedShift.fieldShift_zero (μ := baseMeasure)).symm
  | succ n ih =>
      rw [pow_succ, ih, shiftOperator_star_eq]
      rw [← WeightedShift.fieldShift_add]
      rw [show -(n : ℤ) + -1 = -((n + 1 : ℕ) : ℤ) by omega]

theorem polarConjugate_eq_signedShift (B : Hilbert →L[ℂ] Hilbert) (n : ℤ) :
    polarConjugate shiftOperator B n = signedShift n * B * signedShift (-n) := by
  unfold polarConjugate
  split_ifs with hn
  · rw [shiftOperator_pow_eq, star_shiftOperator_pow_eq, Int.toNat_of_nonneg hn]
  · rw [shiftOperator_pow_eq, star_shiftOperator_pow_eq, Int.toNat_of_nonneg (by omega : 0 ≤ -n)]
    simp only [neg_neg]

theorem multiplier_coordinate_ae (θ : ℕ → ℝ) (g : Base → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hg : Measurable g) (hb : ∀ x, ‖g x‖ ≤ C) (v : Hilbert) :
    ∀ᵐ x ∂baseMeasure, ∀ k : ℤ,
      multiplier θ g C hC hg hb v x k = g (rotationIterate θ k x) * v x k := by
  exact WeightedShift.fieldDiagonal_coordinate_ae _ _ _ _ _ v

theorem polarConjugate_multiplier_coordinate_ae
    (θ : ℕ → ℝ) (g : Base → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hg : Measurable g) (hb : ∀ x, ‖g x‖ ≤ C) (n : ℤ) (v : Hilbert) :
    ∀ᵐ x ∂baseMeasure, ∀ k : ℤ,
      polarConjugate shiftOperator (multiplier θ g C hC hg hb) n v x k =
        g (rotationIterate θ (k - n) x) * v x k := by
  rw [polarConjugate_eq_signedShift]
  let B := multiplier θ g C hC hg hb
  filter_upwards [WeightedShift.fieldShift_ae n (B (signedShift (-n) v)),
    multiplier_coordinate_ae θ g C hC hg hb (signedShift (-n) v),
    WeightedShift.fieldShift_ae (-n) v] with x hs hbval ht k
  change signedShift n (B (signedShift (-n) v)) x k = _
  rw [hs, WeightedShift.shift_apply, hbval, ht, WeightedShift.shift_apply]
  simp only [sub_neg_eq_add, sub_add_cancel]

theorem finitePolarAlgebra_multiplier_atomic
    (θ : ℕ → ℝ) (f : Base → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : Measurable f) (hb : ∀ x, ‖(f x : ℂ)‖ ≤ C)
    (hcount : ∃ R : Set ℝ, R.Countable ∧ ∀ᵐ x ∂baseMeasure, f x ∈ R)
    (F : Finset ℤ) :
    IsAbelianVonNeumannAlgebra
      (finitePolarAlgebra shiftOperator (multiplier θ (fun x => (f x : ℂ)) C hC hf.complex_ofReal hb) F) ∧
    IsAtomicVonNeumannAlgebra
      (finitePolarAlgebra shiftOperator (multiplier θ (fun x => (f x : ℂ)) C hC hf.complex_ofReal hb) F) := by
  let B := multiplier θ (fun x => (f x : ℂ)) C hC hf.complex_ofReal hb
  let D : F → Hilbert →L[ℂ] Hilbert := fun j => polarConjugate shiftOperator B j.val
  have hD : ∀ j (v : Hilbert) k, ∀ᵐ x ∂baseMeasure,
      D j v x k = (f (rotationIterate θ (k - j.val) x) : ℂ) * v x k := by
    intro j v k
    exact (polarConjugate_multiplier_coordinate_ae θ _ C hC hf.complex_ofReal hb j.val v).mono
      (fun x hx => hx k)
  obtain ⟨hat, hab⟩ := finite_orbit_diagonal_algebra_atomic_and_commutative
    (fun j : F => j.val) (rotationIterate θ) (rotationIterate_measurePreserving_polar θ)
    f hf hcount D hD
  have hgen : {A | ∃ n ∈ F, A = polarConjugate shiftOperator B n} = Set.range D := by
    ext A
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨⟨n, hn⟩, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨j.val, j.property, rfl⟩
  change IsAbelianVonNeumannAlgebra (vonNeumannGenerated _) ∧
    IsAtomicVonNeumannAlgebra (vonNeumannGenerated _)
  rw [hgen]
  exact ⟨fun S T hS hT => hab S hS T hT, hat⟩

theorem fullPolarAlgebra_multiplier_abelian
    (θ : ℕ → ℝ) (f : Base → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : Measurable f) (hb : ∀ x, ‖(f x : ℂ)‖ ≤ C) :
    IsAbelianVonNeumannAlgebra
      (fullPolarAlgebra shiftOperator (multiplier θ (fun x => (f x : ℂ)) C hC hf.complex_ofReal hb)) := by
  let D := polarConjugate shiftOperator (multiplier θ (fun x => (f x : ℂ)) C hC hf.complex_ofReal hb)
  have hD (n : ℤ) (v : Hilbert) (k : ℤ) : ∀ᵐ x ∂baseMeasure,
      D n v x k = (f (rotationIterate θ (k - n) x) : ℂ) * v x k :=
    (polarConjugate_multiplier_coordinate_ae θ _ C hC hf.complex_ofReal hb n v).mono
      (fun x hx => hx k)
  have hself (n : ℤ) : IsSelfAdjoint (D n) :=
    isSelfAdjoint_of_real_sequence_diagonal _ _ (hD n)
  have hcomm (m n : ℤ) : Commute (D m) (D n) :=
    commute_of_sequence_diagonal _ _ _ _ (hD m) (hD n)
  intro S T hS hT
  exact commute_of_mem_generated_selfAdjoint_family D hself hcomm hS hT

theorem multiplier_hasCountablyAtomicSpectralType
    (θ : ℕ → ℝ) (f : Base → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : Measurable f) (hb : ∀ x, ‖(f x : ℂ)‖ ≤ C)
    (hcount : ∃ R : Set ℝ, R.Countable ∧ ∀ᵐ x ∂baseMeasure, f x ∈ R) :
    HasCountablyAtomicSpectralType
      (multiplier θ (fun x => (f x : ℂ)) C hC hf.complex_ofReal hb) := by
  obtain ⟨R, hR, hmem⟩ := hcount
  let S : Set ℂ := Complex.ofReal '' R
  have hS : S.Countable := hR.image _
  refine ⟨S, hS, ?_⟩
  let b : HilbertBasis ℤ ℂ Fiber :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)
  have hbasis (v : Fiber) (k : ℤ) : inner ℂ (b k) v = v k :=
    (b.repr_apply_apply v k).symm
  have hmeas (k : ℤ) : Measurable (fun x => (f (rotationIterate θ k x) : ℂ)) := by
    exact hf.complex_ofReal.comp (rotationIterate_measurePreserving_polar θ k).measurable
  have hrange (k : ℤ) : ∀ᵐ x ∂baseMeasure, (f (rotationIterate θ k x) : ℂ) ∈ S := by
    filter_upwards [(rotationIterate_measurePreserving_polar θ k).quasiMeasurePreserving.ae hmem]
      with x hx
    exact Set.mem_image_of_mem Complex.ofReal hx
  apply MultiplicationPurePoint.topologicalClosure_iSup_eigenspace_eq_top_of_basis b
    (fun k x => (f (rotationIterate θ k x) : ℂ)) hmeas hS hrange
  intro v k
  simpa only [hbasis] using
    (multiplier_coordinate_ae θ _ C hC hf.complex_ofReal hb v).mono (fun x hx => hx k)

theorem multiplier_injective_of_ae_ne_zero
    (θ : ℕ → ℝ) (g : Base → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hg : Measurable g) (hb : ∀ x, ‖g x‖ ≤ C)
    (hne : ∀ᵐ x ∂baseMeasure, g x ≠ 0) :
    Function.Injective (multiplier θ g C hC hg hb) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  apply Lp.ext
  have hcoord : ∀ᵐ x ∂baseMeasure, ∀ k, g (rotationIterate θ k x) ≠ 0 :=
    ae_all_iff.mpr fun k => (rotationIterate_measurePreserving_polar θ k).quasiMeasurePreserving.ae hne
  have hout : (multiplier θ g C hC hg hb v : Base → Fiber) =ᵐ[baseMeasure] 0 := by
    rw [hv]
    exact Lp.coeFn_zero _ _ _
  filter_upwards [multiplier_coordinate_ae θ g C hC hg hb v, hcoord, hout,
    Lp.coeFn_zero Fiber 2 baseMeasure] with x hx hn hz hzero
  rw [hzero]
  apply lp.ext
  funext k
  have hprod : g (rotationIterate θ k x) * v x k = 0 := by
    rw [← hx k, hz]
    rfl
  exact (mul_eq_zero.mp hprod).resolve_left (hn k)

end Invariant233.ProductModel

end

end OAI
