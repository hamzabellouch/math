import Mathlib
import OAI.Computability.MaxCut.Games.KMSInjectionCountBounds

namespace OAI

/-!
The dependent branches in the KMS fixed-character recursion inject into the
lower-rank restricted Fourier sum. The new coordinate value is kept fixed,
so no multiplicity or ambient-dimension loss is introduced here.
-/

namespace MaxCutGames.Inverse.KMSAnalytic
noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Fourier.MatrixFourier

variable {E B J K : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup B] [Module F2 B]
  [AddCommGroup J] [Module F2 J] [AddCommGroup K] [Module F2 K]

/-- Fixing the new coordinate still allows recovery of the entire old map. -/
theorem hyperplaneExtend_old_injective (w : J) :
    Function.Injective (fun z : B →ₗ[F2] J => hyperplaneExtend z w) := by
  intro z z' h
  have hc := congrArg
    (fun T : (B × F2) →ₗ[F2] J => T.comp (LinearMap.inl F2 B F2)) h
  simpa only [hyperplaneExtend_comp_inl] using hc

/-- A surjective old frequency stays surjective after any new coordinate. -/
theorem hyperplaneExtend_surjective {z : B →ₗ[F2] J}
    (hz : Function.Surjective z) (w : J) :
    Function.Surjective (hyperplaneExtend z w) := by
  intro y
  obtain ⟨b, hb⟩ := hz y
  refine ⟨(b, 0), ?_⟩
  simpa using hb

/-- The fixed partial frequency extends by its actual projected new value. -/
theorem comp_hyperplaneExtend (π : J →ₗ[F2] K) (z : B →ₗ[F2] J) (w : J) :
    π.comp (hyperplaneExtend z w) = hyperplaneExtend (π.comp z) (π w) := by
  apply LinearMap.ext
  rintro ⟨b, c⟩
  simp [LinearMap.comp_apply]

variable [FiniteDimensional F2 E] [FiniteDimensional F2 B] [FiniteDimensional F2 J]
  [Fintype (E →ₗ[F2] (B × F2))] [Fintype ((B × F2) →ₗ[F2] E)]
  [Fintype (J →ₗ[F2] (B × F2))] [Fintype ((B × F2) →ₗ[F2] J)]
  [Fintype (B →ₗ[F2] J)]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 B] [FiniteDimensional F2 J]
  [Fintype ((B × F2) →ₗ[F2] E)] [Fintype (J →ₗ[F2] (B × F2))] in
/-- Each fixed dependent extension branch is bounded by the genuine restricted
small-component energy. There is no hidden cardinality factor. -/
theorem dependent_extension_energy_le
    (ι : J →ₗ[F2] E) (f : (E →ₗ[F2] (B × F2)) → ℝ)
    (π : J →ₗ[F2] K) (A0 : B →ₗ[F2] K) (w : J) :
    (∑ z : B →ₗ[F2] J with π.comp z = A0 ∧ Function.Surjective z,
      linearCoeff f (ι.comp (hyperplaneExtend z w)) ^ 2) ≤
        fixedFrequencyEnergy ι f π (hyperplaneExtend A0 (π w)) := by
  let P : Finset (B →ₗ[F2] J) :=
    Finset.univ.filter fun z => π.comp z = A0 ∧ Function.Surjective z
  let Q : Finset ((B × F2) →ₗ[F2] J) :=
    Finset.univ.filter fun T =>
      π.comp T = hyperplaneExtend A0 (π w) ∧ Function.Surjective T
  have hsub : P.image (fun z => hyperplaneExtend z w) ⊆ Q := by
    intro T hT
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hT
    have hp := (Finset.mem_filter.mp hz).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, hyperplaneExtend_surjective hp.2 w⟩
    rw [comp_hyperplaneExtend, hp.1]
  rw [fixedFrequencyEnergy_eq]
  change (∑ z ∈ P, linearCoeff f (ι.comp (hyperplaneExtend z w)) ^ 2) ≤
    ∑ T ∈ Q, linearCoeff f (ι.comp T) ^ 2
  calc
    _ = ∑ T ∈ P.image (fun z => hyperplaneExtend z w),
        linearCoeff f (ι.comp T) ^ 2 := by
      rw [Finset.sum_image]
      exact fun z _ z' _ h => hyperplaneExtend_old_injective w h
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun T _ _ => sq_nonneg _)

end

/-! A denominator-cleared fixed-character induction step. Its right side
contains only the actual smaller restricted Fourier energies, obtained from
the exact zoom-out identity and injective reindexing of each dependent branch.
-/

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Fourier.MatrixFourier
open MaxCutGames.Inverse.KMSBasisInvariant

variable {E B J K : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup B] [Module F2 B]
  [AddCommGroup J] [Module F2 J] [AddCommGroup K] [Module F2 K]
  [FiniteDimensional F2 E] [FiniteDimensional F2 B] [FiniteDimensional F2 J]
  [Fintype E] [Fintype J]
  [Fintype (E →ₗ[F2] (B × F2))] [Fintype ((B × F2) →ₗ[F2] E)]
  [Fintype (E →ₗ[F2] B)] [Fintype (B →ₗ[F2] E)]
  [Fintype (J →ₗ[F2] (B × F2))] [Fintype ((B × F2) →ₗ[F2] J)]
  [Fintype (J →ₗ[F2] B)] [Fintype (B →ₗ[F2] J)]

omit [FiniteDimensional F2 J] [Fintype (J →ₗ[F2] B × F2)] [Fintype (B × F2 →ₗ[F2] J)]
  [Fintype (J →ₗ[F2] B)] [Fintype (B →ₗ[F2] J)] [Fintype (B →ₗ[F2] E)] in
/-- The exact zoom-out square bound after embedding the small frequency
space; the dependent sum is indexed by that small space itself. -/
theorem coefficient_lifted_zoomOut_sq_bound
    (ι : (J × F2) →ₗ[F2] E) (hι : Function.Injective ι)
    (f : (E →ₗ[F2] (B × F2)) → ℝ) (hf : IsBasisInvariant f)
    (z : B →ₗ[F2] J) (hz : Function.Surjective z) :
    (((Fintype.card E - Fintype.card J : ℕ) : ℝ) ^ 2) *
        linearCoeff f (hyperplaneExtend ((leftEmbedding ι).comp z) (ι (0, 1))) ^ 2 ≤
      ((Fintype.card J : ℝ) + 1) *
        (linearCoeff (fun X => f ((LinearMap.inl F2 B F2).comp X))
            ((leftEmbedding ι).comp z) ^ 2 +
          ∑ w : J, linearCoeff f ((leftEmbedding ι).comp (hyperplaneExtend z w)) ^ 2) := by
  have hv : ι (0, 1) ∉ ((leftEmbedding ι).comp z).range := by
    rw [range_left_comp_of_surjective ι z hz]
    exact lastVector_not_mem_left_range ι hι
  have h := coefficient_zoomOut_sq_bound f hf ((leftEmbedding ι).comp z) hv
  rw [card_lifted_range ι hι z hz,
    sum_lifted_range ι hι z hz
      (fun u => linearCoeff f (hyperplaneExtend ((leftEmbedding ι).comp z) u) ^ 2)] at h
  simpa only [hyperplaneExtend_left_comp] using h

omit [Fintype (J →ₗ[F2] B)] [FiniteDimensional F2 J] [Fintype (B →ₗ[F2] E)]
  [Fintype (J →ₗ[F2] (B × F2))] in
/-- Summing the genuine pointwise recurrence bounds every dependent branch
by an actual lower-rank fixed-character energy, with no missing multiplicity. -/
theorem fixedCharacter_step_sum
    (ι : (J × F2) →ₗ[F2] E) (hι : Function.Injective ι)
    (f : (E →ₗ[F2] (B × F2)) → ℝ) (hf : IsBasisInvariant f)
    (π : J →ₗ[F2] K) (A : B →ₗ[F2] K) :
    (((Fintype.card E - Fintype.card J : ℕ) : ℝ) ^ 2) *
        (∑ z ∈ Finset.univ.filter (fun z : B →ₗ[F2] J =>
            π.comp z = A ∧ Function.Surjective z),
          linearCoeff f (hyperplaneExtend ((leftEmbedding ι).comp z) (ι (0, 1))) ^ 2) ≤
      ((Fintype.card J : ℝ) + 1) *
        (fixedFrequencyEnergy (leftEmbedding ι)
          (fun X : E →ₗ[F2] B => f ((LinearMap.inl F2 B F2).comp X)) π A +
        ∑ w : J, fixedFrequencyEnergy (leftEmbedding ι) f π (hyperplaneExtend A (π w))) := by
  let P : Finset (B →ₗ[F2] J) :=
    Finset.univ.filter fun z => π.comp z = A ∧ Function.Surjective z
  change _ * (∑ z ∈ P, _) ≤ _
  calc
    _ ≤ ∑ z ∈ P, ((Fintype.card J : ℝ) + 1) *
        (linearCoeff (fun X => f ((LinearMap.inl F2 B F2).comp X))
            ((leftEmbedding ι).comp z) ^ 2 +
          ∑ w : J, linearCoeff f ((leftEmbedding ι).comp (hyperplaneExtend z w)) ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro z hz
      exact coefficient_lifted_zoomOut_sq_bound ι hι f hf z
        (Finset.mem_filter.mp hz).2.2
    _ = ((Fintype.card J : ℝ) + 1) *
        ((∑ z ∈ P, linearCoeff
          (fun X => f ((LinearMap.inl F2 B F2).comp X)) ((leftEmbedding ι).comp z) ^ 2) +
        ∑ w : J, ∑ z ∈ P,
          linearCoeff f ((leftEmbedding ι).comp (hyperplaneExtend z w)) ^ 2) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_comm]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply add_le_add
      · rw [fixedFrequencyEnergy_eq]
      · apply Finset.sum_le_sum
        intro w _
        exact dependent_extension_energy_le (leftEmbedding ι) f π A w

end

/-!
# Compatible block frequencies

A compatible surjection on `B × F2` has a unique old surjection and a new
vector in the kernel of the partial projection. The new vector does not
change its kernel. Consequently actual basis-invariant Fourier coefficients
are constant along this fiber, yielding its exact energy multiplicity.
-/

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Fourier.MatrixFourier

variable {B J K E : Type*}
  [AddCommGroup B] [Module F2 B] [AddCommGroup J] [Module F2 J]
  [AddCommGroup K] [Module F2 K] [AddCommGroup E] [Module F2 E]

/-- Adjoin a new identity coordinate and an arbitrary off-diagonal vector. -/
def blockFrequency (z : B →ₗ[F2] J) (w : J) : (B × F2) →ₗ[F2] (J × F2) :=
  (hyperplaneExtend z w).prod (LinearMap.snd F2 B F2)

@[simp] theorem blockFrequency_apply (z : B →ₗ[F2] J) (w : J) (b : B) (c : F2) :
    blockFrequency z w (b, c) = (z b + c • w, c) := rfl

theorem blockFrequency_surjective_iff (z : B →ₗ[F2] J) (w : J) :
    Function.Surjective (blockFrequency z w) ↔ Function.Surjective z := by
  constructor
  · intro h y
    obtain ⟨⟨b, c⟩, hx⟩ := h (y, 0)
    have hc : c = 0 := congrArg Prod.snd hx
    refine ⟨b, ?_⟩
    simpa only [blockFrequency_apply, hc, zero_smul, add_zero] using congrArg Prod.fst hx
  · intro h x
    obtain ⟨b, hb⟩ := h (x.1 - x.2 • w)
    refine ⟨(b, x.2), ?_⟩
    simp only [blockFrequency_apply, hb, sub_add_cancel, Prod.eta]

/-- The kernel is independent of the off-diagonal vector, without any
surjectivity assumption. -/
theorem ker_blockFrequency (z : B →ₗ[F2] J) (w : J) :
    (blockFrequency z w).ker = z.ker.prod (⊥ : Submodule F2 F2) := by
  ext ⟨b, c⟩
  change ((z b + c • w, c) = (0, 0)) ↔ (z b = 0 ∧ c = 0)
  rw [Prod.mk.injEq]
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨by simpa using h, rfl⟩
  · rintro ⟨h, rfl⟩
    simpa using h

theorem blockFrequency_compatible_iff (π : J →ₗ[F2] K) (A : B →ₗ[F2] K)
    (z : B →ₗ[F2] J) (w : J) :
    (π.prodMap (LinearMap.id : F2 →ₗ[F2] F2)).comp (blockFrequency z w) =
      A.prodMap (LinearMap.id : F2 →ₗ[F2] F2) ↔ π.comp z = A ∧ π w = 0 := by
  constructor
  · intro h
    constructor
    · apply LinearMap.ext
      intro b
      simpa using congrArg (fun T : (B × F2) →ₗ[F2] (K × F2) => (T (b, 0)).1) h
    · simpa using congrArg (fun T : (B × F2) →ₗ[F2] (K × F2) => (T (0, 1)).1) h
  · rintro ⟨hz, hw⟩
    apply LinearMap.ext
    rintro ⟨b, c⟩
    have hb : π (z b) = A b := congrArg (fun T : B →ₗ[F2] K => T b) hz
    simp [hb, hw]

def blockOld (T : (B × F2) →ₗ[F2] (J × F2)) : B →ₗ[F2] J :=
  ((LinearMap.fst F2 J F2).comp T).comp (LinearMap.inl F2 B F2)

def blockNew (T : (B × F2) →ₗ[F2] (J × F2)) : J := (T (0, 1)).1

@[simp] theorem blockOld_blockFrequency (z : B →ₗ[F2] J) (w : J) :
    blockOld (blockFrequency z w) = z := by
  ext b
  simp [blockOld]

@[simp] theorem blockNew_blockFrequency (z : B →ₗ[F2] J) (w : J) :
    blockNew (blockFrequency z w) = w := by simp [blockNew]

theorem blockFrequency_recover (π : J →ₗ[F2] K) (A : B →ₗ[F2] K)
    (T : (B × F2) →ₗ[F2] (J × F2))
    (hT : (π.prodMap (LinearMap.id : F2 →ₗ[F2] F2)).comp T =
      A.prodMap (LinearMap.id : F2 →ₗ[F2] F2)) :
    blockFrequency (blockOld T) (blockNew T) = T := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · exact congrArg (fun R : (B × F2) →ₗ[F2] J => R x)
      (hyperplaneExtend_recover ((LinearMap.fst F2 J F2).comp T))
  · have h := congrArg (fun R : (B × F2) →ₗ[F2] (K × F2) => (R x).2) hT
    exact h.symm

abbrev CompatibleBlockFrequency (π : J →ₗ[F2] K) (A : B →ₗ[F2] K) :=
  {T : (B × F2) →ₗ[F2] (J × F2) // Function.Surjective T ∧
    (π.prodMap (LinearMap.id : F2 →ₗ[F2] F2)).comp T =
      A.prodMap (LinearMap.id : F2 →ₗ[F2] F2)}

abbrev CompatibleOldFrequency (π : J →ₗ[F2] K) (A : B →ₗ[F2] K) :=
  {z : B →ₗ[F2] J // Function.Surjective z ∧ π.comp z = A}

/-- The actual compatible frequency fiber, with its exact kernel-vector parameter. -/
def compatibleBlockFrequencyEquiv (π : J →ₗ[F2] K) (A : B →ₗ[F2] K) :
    CompatibleBlockFrequency π A ≃ CompatibleOldFrequency π A × π.ker where
  toFun T := by
    have hr := blockFrequency_recover π A T.val T.property.2
    have hc : π.comp (blockOld T.val) = A ∧ π (blockNew T.val) = 0 :=
      (blockFrequency_compatible_iff π A _ _).mp (by rw [hr]; exact T.property.2)
    refine (⟨blockOld T.val, ?_, hc.1⟩, ⟨blockNew T.val, hc.2⟩)
    apply (blockFrequency_surjective_iff (blockOld T.val) (blockNew T.val)).mp
    rw [hr]
    exact T.property.1
  invFun p := ⟨blockFrequency p.1.val p.2.val,
    (blockFrequency_surjective_iff _ _).mpr p.1.property.1,
    (blockFrequency_compatible_iff π A _ _).mpr ⟨p.1.property.2, p.2.property⟩⟩
  left_inv T := by
    apply Subtype.ext
    exact blockFrequency_recover π A T.val T.property.2
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      exact blockOld_blockFrequency _ _
    · apply Subtype.ext
      exact blockNew_blockFrequency _ _

variable [FiniteDimensional F2 E] [Fintype (E →ₗ[F2] (B × F2))]

/-- Actual lifted coefficients are independent of the block vector. -/
theorem coefficient_blockFrequency_eq (ι : (J × F2) →ₗ[F2] E)
    (hι : Function.Injective ι) (f : (E →ₗ[F2] (B × F2)) → ℝ)
    (hf : KMSBasisInvariant.IsBasisInvariant f) (z : B →ₗ[F2] J) (u v : J) :
    linearCoeff f (ι.comp (blockFrequency z u)) =
      linearCoeff f (ι.comp (blockFrequency z v)) := by
  apply KMSKernelOrbitsFourier.coefficient_eq_of_ker_eq f hf
  rw [LinearMap.ker_comp_of_ker_eq_bot _ (LinearMap.ker_eq_bot.mpr hι),
    LinearMap.ker_comp_of_ker_eq_bot _ (LinearMap.ker_eq_bot.mpr hι),
    ker_blockFrequency, ker_blockFrequency]

variable [FiniteDimensional F2 B] [FiniteDimensional F2 J] [Fintype J]
  [Fintype ((B × F2) →ₗ[F2] E)] [Fintype (B →ₗ[F2] J)]
  [Fintype ((J × F2) →ₗ[F2] (B × F2))]
  [Fintype ((B × F2) →ₗ[F2] (J × F2))]

omit [FiniteDimensional F2 B] [FiniteDimensional F2 J] [Fintype (B × F2 →ₗ[F2] E)] [Fintype (J × F2 →ₗ[F2] B × F2)] in
/-- Exact collapse of the new-coordinate fiber in the prescribed-frequency
energy. The multiplier is the actual number of vectors in `ker π`. -/
theorem fixedFrequencyEnergy_block (ι : (J × F2) →ₗ[F2] E)
    (hι : Function.Injective ι) (f : (E →ₗ[F2] (B × F2)) → ℝ)
    (hf : KMSBasisInvariant.IsBasisInvariant f) (π : J →ₗ[F2] K) (A : B →ₗ[F2] K) :
    fixedFrequencyEnergy ι f (π.prodMap (LinearMap.id : F2 →ₗ[F2] F2))
      (A.prodMap (LinearMap.id : F2 →ₗ[F2] F2)) =
      (Fintype.card π.ker : ℝ) * ∑ z : CompatibleOldFrequency π A,
        linearCoeff f (ι.comp (blockFrequency z.val 0)) ^ 2 := by
  let e := compatibleBlockFrequencyEquiv π A
  calc
    _ = ∑ T : CompatibleBlockFrequency π A, linearCoeff f (ι.comp T.val) ^ 2 := by
      unfold fixedFrequencyEnergy
      rw [← Finset.sum_subtype (Finset.univ.filter (fun T : (B × F2) →ₗ[F2] (J × F2) =>
          Function.Surjective T ∧
            (π.prodMap (LinearMap.id : F2 →ₗ[F2] F2)).comp T =
              A.prodMap (LinearMap.id : F2 →ₗ[F2] F2))) (by simp)
          (fun T => linearCoeff f (ι.comp T) ^ 2),
        Finset.sum_filter, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro T _
      by_cases hs : Function.Surjective T <;>
        by_cases hp : (π.prodMap (LinearMap.id : F2 →ₗ[F2] F2)).comp T =
            A.prodMap (LinearMap.id : F2 →ₗ[F2] F2) <;> simp [smallCoeff, hs, hp]
    _ = ∑ p : CompatibleOldFrequency π A × π.ker,
        linearCoeff f (ι.comp (blockFrequency p.1.val p.2.val)) ^ 2 := by
      apply Fintype.sum_equiv e
      intro T
      exact congrArg (fun R : (B × F2) →ₗ[F2] (J × F2) =>
        linearCoeff f (ι.comp R) ^ 2) (congrArg Subtype.val (e.symm_apply_apply T)).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp_rw [coefficient_blockFrequency_eq ι hι f hf _ _ 0]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [Finset.mul_sum]

end

/-! The complete product-coordinate fixed-character recurrence, with the
actual new-coordinate multiplicity. This joins the block-frequency bijection
to the genuine Fourier zoom-out energy inequality. -/

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Fourier.MatrixFourier
open MaxCutGames.Inverse.KMSBasisInvariant

variable {E B J K : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup B] [Module F2 B]
  [AddCommGroup J] [Module F2 J] [AddCommGroup K] [Module F2 K]

theorem comp_blockFrequency_zero (ι : (J × F2) →ₗ[F2] E) (z : B →ₗ[F2] J) :
    ι.comp (blockFrequency z 0) =
      hyperplaneExtend ((leftEmbedding ι).comp z) (ι (0, 1)) := by
  apply LinearMap.ext
  rintro ⟨b, c⟩
  change ι (z b + c • 0, c) = ι (z b, 0) + c • ι (0, 1)
  simp only [smul_zero, add_zero]
  rw [← map_smul, ← map_add]
  congr 1
  simp

variable [FiniteDimensional F2 E] [FiniteDimensional F2 B] [FiniteDimensional F2 J]
  [Fintype E] [Fintype J]
  [Fintype (E →ₗ[F2] (B × F2))] [Fintype ((B × F2) →ₗ[F2] E)]
  [Fintype (E →ₗ[F2] B)] [Fintype (B →ₗ[F2] E)]
  [Fintype (J →ₗ[F2] (B × F2))] [Fintype ((B × F2) →ₗ[F2] J)]
  [Fintype (J →ₗ[F2] B)] [Fintype (B →ₗ[F2] J)]
  [Fintype ((J × F2) →ₗ[F2] (B × F2))]
  [Fintype ((B × F2) →ₗ[F2] (J × F2))]

omit [Fintype ((J × F2) →ₗ[F2] (B × F2))] [Fintype (J →ₗ[F2] B)]
  [FiniteDimensional F2 J] [Fintype (B →ₗ[F2] E)] [Fintype (J →ₗ[F2] (B × F2))] in
/-- A genuine one-step recurrence in the actual restricted Fourier energy.
Every term on the right has one fewer small-space dimension and one fewer
fixed character. -/
theorem fixedFrequencyEnergy_product_step
    (ι : (J × F2) →ₗ[F2] E) (hι : Function.Injective ι)
    (f : (E →ₗ[F2] (B × F2)) → ℝ) (hf : IsBasisInvariant f)
    (π : J →ₗ[F2] K) (A : B →ₗ[F2] K) :
    (((Fintype.card E - Fintype.card J : ℕ) : ℝ) ^ 2) *
        fixedFrequencyEnergy ι f (π.prodMap (LinearMap.id : F2 →ₗ[F2] F2))
          (A.prodMap (LinearMap.id : F2 →ₗ[F2] F2)) ≤
      (Fintype.card π.ker : ℝ) * (((Fintype.card J : ℝ) + 1) *
        (fixedFrequencyEnergy (leftEmbedding ι)
          (fun X : E →ₗ[F2] B => f ((LinearMap.inl F2 B F2).comp X)) π A +
        ∑ w : J, fixedFrequencyEnergy (leftEmbedding ι) f π (hyperplaneExtend A (π w)))) := by
  let P : Finset (B →ₗ[F2] J) :=
    Finset.univ.filter fun z => π.comp z = A ∧ Function.Surjective z
  have hsum : (∑ z : CompatibleOldFrequency π A,
      linearCoeff f (ι.comp (blockFrequency z.val 0)) ^ 2) =
      ∑ z ∈ P,
        linearCoeff f (hyperplaneExtend ((leftEmbedding ι).comp z) (ι (0, 1))) ^ 2 := by
    rw [← Finset.sum_subtype (p := fun z : B →ₗ[F2] J =>
      Function.Surjective z ∧ π.comp z = A) P (by intro z; simp [P, and_comm])
      (fun z => linearCoeff f (ι.comp (blockFrequency z 0)) ^ 2)]
    apply Finset.sum_congr rfl
    intro z _
    rw [comp_blockFrequency_zero]
  rw [fixedFrequencyEnergy_block ι hι f hf π A, hsum]
  calc
    _ = (Fintype.card π.ker : ℝ) *
        ((((Fintype.card E - Fintype.card J : ℕ) : ℝ) ^ 2) *
          ∑ z ∈ P, linearCoeff f
            (hyperplaneExtend ((leftEmbedding ι).comp z) (ι (0, 1))) ^ 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (fixedCharacter_step_sum ι hι f hf π A)
      (Nat.cast_nonneg _)

end

/-! Scalar closure of the genuine KMS fixed-character induction. The three
combinatorial losses are absorbed by the explicit quadratic exponent; no
Fourier estimate is asserted or assumed in this arithmetic lemma. -/

/-- The recurrence cost in Lemma 3.19 is absorbed by `2^(4 i²)`. The proof only
needs `n < ell`, weaker than the usual `2*(n+1) ≤ ell` induction hypothesis. -/
theorem fixedCharacter_constant_step (n m ell : ℕ) (hnell : n < ell) :
    (2 : ℝ) ^ n * ((2 : ℝ) ^ n + 1) ^ 2 * (2 : ℝ) ^ (4 * n * n) /
        ((((2 : ℝ) ^ ell - (2 : ℝ) ^ n) ^ 2) * (2 : ℝ) ^ ((n + m) * ell)) ≤
      (2 : ℝ) ^ (4 * (n + 1) * (n + 1)) /
        (2 : ℝ) ^ (((n + 1) + (m + 1)) * ell) := by
  let A : ℝ := (2 : ℝ) ^ ell
  let B : ℝ := (2 : ℝ) ^ n
  let C : ℝ := (2 : ℝ) ^ (4 * n * n)
  let C' : ℝ := (2 : ℝ) ^ (4 * (n + 1) * (n + 1))
  let P : ℝ := (2 : ℝ) ^ ((n + m) * ell)
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hP : 0 < P := by dsimp [P]; positivity
  have hB1 : 1 ≤ B := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hAB : 2 * B ≤ A := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hnell
    simpa only [pow_succ, mul_comm] using h
  have hdiff : 0 < A - B := by linarith
  have hplus : (B + 1) ^ 2 ≤ 4 * B ^ 2 := by
    have hs := mul_self_le_mul_self (show 0 ≤ B + 1 by positivity)
      (show B + 1 ≤ 2 * B by linarith)
    nlinarith only [hs]
  have hsquare : A ^ 2 ≤ 4 * (A - B) ^ 2 := by
    have hs := mul_self_le_mul_self (show 0 ≤ A / 2 by positivity)
      (show A / 2 ≤ A - B by linarith)
    nlinarith only [hs]
  have hcoeff : B * (B + 1) ^ 2 * C ≤ 4 * B ^ 3 * C := by
    calc
      _ ≤ B * (4 * B ^ 2) * C := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hplus hB.le) hC.le
      _ = _ := by ring
  have hconst : 16 * B ^ 3 * C ≤ C' := by
    calc
      _ = (2 : ℝ) ^ (4 + 3 * n + 4 * n * n) := by
        dsimp [B, C]
        rw [show (16 : ℝ) = 2 ^ 4 by norm_num, ← pow_mul, ← pow_add, ← pow_add]
        congr 1
        ring
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by nlinarith)
  have hmain : B * (B + 1) ^ 2 * C * A ^ 2 ≤ C' * (A - B) ^ 2 := by
    calc
      _ ≤ (4 * B ^ 3 * C) * A ^ 2 :=
        mul_le_mul_of_nonneg_right hcoeff (sq_nonneg A)
      _ ≤ (4 * B ^ 3 * C) * (4 * (A - B) ^ 2) :=
        mul_le_mul_of_nonneg_left hsquare (by positivity)
      _ = (16 * B ^ 3 * C) * (A - B) ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hconst (sq_nonneg _)
  have hpower : (2 : ℝ) ^ (((n + 1) + (m + 1)) * ell) = A ^ 2 * P := by
    dsimp [A, P]
    rw [← pow_mul, ← pow_add]
    congr 1
    ring
  change B * (B + 1) ^ 2 * C / ((A - B) ^ 2 * P) ≤
    C' / (2 : ℝ) ^ (((n + 1) + (m + 1)) * ell)
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  rw [hpower]
  calc
    _ = (B * (B + 1) ^ 2 * C * A ^ 2) * P := by ring
    _ ≤ (C' * (A - B) ^ 2) * P := mul_le_mul_of_nonneg_right hmain hP.le
    _ = _ := by ring

end MaxCutGames.Inverse.KMSAnalytic

/-! Quantitative closure of the genuine fixed-character product recurrence.
The hypotheses are the actual two smaller restricted energies. The proof
accounts for the kernel multiplicity and all dependent extensions explicitly.
-/

namespace MaxCutGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Inverse.KMSBasisInvariant

variable {E B J K : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup B] [Module F2 B]
  [AddCommGroup J] [Module F2 J] [AddCommGroup K] [Module F2 K]
  [FiniteDimensional F2 E] [FiniteDimensional F2 B]
  [FiniteDimensional F2 J] [FiniteDimensional F2 K]
  [Fintype E] [Fintype J]
  [Fintype (E →ₗ[F2] (B × F2))] [Fintype ((B × F2) →ₗ[F2] E)]
  [Fintype (E →ₗ[F2] B)] [Fintype (B →ₗ[F2] E)]
  [Fintype (J →ₗ[F2] (B × F2))] [Fintype ((B × F2) →ₗ[F2] J)]
  [Fintype (J →ₗ[F2] B)] [Fintype (B →ₗ[F2] J)]
  [Fintype ((J × F2) →ₗ[F2] (B × F2))]
  [Fintype ((B × F2) →ₗ[F2] (J × F2))]

omit [Fintype ((J × F2) →ₗ[F2] (B × F2))] [Fintype (J →ₗ[F2] B)]
  [Fintype (B →ₗ[F2] E)] [Fintype (J →ₗ[F2] (B × F2))] in
/-- The fixed-character recurrence preserves the explicit quadratic constant.
No local-density or Fourier bound is hidden in the scalar accounting. -/
theorem fixedFrequencyEnergy_product_bound
    (ι : (J × F2) →ₗ[F2] E) (hι : Function.Injective ι)
    (f : (E →ₗ[F2] (B × F2)) → ℝ) (hf : IsBasisInvariant f)
    (π : J →ₗ[F2] K) (A : B →ₗ[F2] K) (ε : ℝ) (hε : 0 ≤ ε)
    (hfirst : (2 : ℝ) ^ ((Module.finrank F2 J + Module.finrank F2 K) *
        Module.finrank F2 E) * fixedFrequencyEnergy (leftEmbedding ι)
        (fun X : E →ₗ[F2] B => f ((LinearMap.inl F2 B F2).comp X)) π A ≤
      (2 : ℝ) ^ (4 * Module.finrank F2 J * Module.finrank F2 J) * ε)
    (hlower : ∀ w : J, (2 : ℝ) ^ ((Module.finrank F2 J + Module.finrank F2 K) *
        Module.finrank F2 E) * fixedFrequencyEnergy (leftEmbedding ι) f π
        (hyperplaneExtend A (π w)) ≤
      (2 : ℝ) ^ (4 * Module.finrank F2 J * Module.finrank F2 J) * ε) :
    (2 : ℝ) ^ ((Module.finrank F2 (J × F2) + Module.finrank F2 (K × F2)) *
        Module.finrank F2 E) * fixedFrequencyEnergy ι f
        (π.prodMap (LinearMap.id : F2 →ₗ[F2] F2))
        (A.prodMap (LinearMap.id : F2 →ₗ[F2] F2)) ≤
      (2 : ℝ) ^ (4 * Module.finrank F2 (J × F2) * Module.finrank F2 (J × F2)) * ε := by
  let n := Module.finrank F2 J
  let m := Module.finrank F2 K
  let ell := Module.finrank F2 E
  let P : ℝ := 2 ^ ((n + m) * ell)
  let C : ℝ := 2 ^ (4 * n * n)
  let N : ℝ := 2 ^ n
  let D : ℝ := 2 ^ ell - 2 ^ n
  let a := fixedFrequencyEnergy (leftEmbedding ι)
    (fun X : E →ₗ[F2] B => f ((LinearMap.inl F2 B F2).comp X)) π A
  let b := fun w : J => fixedFrequencyEnergy (leftEmbedding ι) f π
    (hyperplaneExtend A (π w))
  let t := fixedFrequencyEnergy ι f
    (π.prodMap (LinearMap.id : F2 →ₗ[F2] F2))
    (A.prodMap (LinearMap.id : F2 →ₗ[F2] F2))
  have hnell : n < ell := by
    have hdim := LinearMap.finrank_le_finrank_of_injective hι
    rw [Module.finrank_prod, Module.finrank_self] at hdim
    exact hdim
  have hcardE : Fintype.card E = 2 ^ ell := by
    rw [Module.card_eq_pow_finrank (K := F2)]
    simp only [F2, ZMod.card, ell]
  have hcardJ : Fintype.card J = 2 ^ n := by
    rw [Module.card_eq_pow_finrank (K := F2)]
    simp only [F2, ZMod.card, n]
  have hcardle : Fintype.card J ≤ Fintype.card E := by
    rw [hcardJ, hcardE]
    exact Nat.pow_le_pow_right (by decide) hnell.le
  have hcardJR : (Fintype.card J : ℝ) = N := by
    rw [hcardJ]
    simp only [Nat.cast_pow, Nat.cast_ofNat, N]
  have hdiff : ((Fintype.card E - Fintype.card J : ℕ) : ℝ) = D := by
    rw [Nat.cast_sub hcardle, hcardE, hcardJ]
    simp only [Nat.cast_pow, Nat.cast_ofNat, D]
  have hker : (Fintype.card π.ker : ℝ) ≤ N := by
    rw [← hcardJR]
    exact_mod_cast Fintype.card_le_of_injective (fun x : π.ker => (x : J))
      Subtype.val_injective
  have hP : 0 < P := by dsimp [P]; positivity
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hD : 0 < D := by
    dsimp [D]
    exact sub_pos.mpr (pow_lt_pow_right₀ (by norm_num : (1 : ℝ) < 2) hnell)
  have ha : 0 ≤ a := fixedFrequencyEnergy_nonneg _ _ _ _
  have hb : 0 ≤ ∑ w : J, b w :=
    Finset.sum_nonneg (fun w _ => fixedFrequencyEnergy_nonneg _ _ _ _)
  have hsum : P * (a + ∑ w : J, b w) ≤ (N + 1) * (C * ε) := by
    calc
      _ = P * a + ∑ w : J, P * b w := by rw [mul_add, Finset.mul_sum]
      _ ≤ C * ε + ∑ _w : J, C * ε :=
        add_le_add hfirst (Finset.sum_le_sum (fun w _ => hlower w))
      _ = (N + 1) * (C * ε) := by simp only [Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, hcardJR]; ring
  have hrec : D ^ 2 * t ≤ (Fintype.card π.ker : ℝ) * ((N + 1) * (a + ∑ w : J, b w)) := by
    simpa only [hdiff, hcardJR] using fixedFrequencyEnergy_product_step ι hι f hf π A
  have hweighted : (D ^ 2 * P) * t ≤ N * (N + 1) ^ 2 * C * ε := by
    calc
      _ = P * (D ^ 2 * t) := by ring
      _ ≤ P * ((Fintype.card π.ker : ℝ) * ((N + 1) * (a + ∑ w : J, b w))) :=
        mul_le_mul_of_nonneg_left hrec hP.le
      _ ≤ P * (N * ((N + 1) * (a + ∑ w : J, b w))) := by
        apply mul_le_mul_of_nonneg_left _ hP.le
        exact mul_le_mul_of_nonneg_right hker (mul_nonneg (by positivity) (add_nonneg ha hb))
      _ = (N * (N + 1)) * (P * (a + ∑ w : J, b w)) := by ring
      _ ≤ (N * (N + 1)) * ((N + 1) * (C * ε)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = _ := by ring
  have ht : t ≤ (N * (N + 1) ^ 2 * C / (D ^ 2 * P)) * ε := by
    calc
      t ≤ (N * (N + 1) ^ 2 * C * ε) / (D ^ 2 * P) :=
        (le_div_iff₀ (show 0 < D ^ 2 * P by positivity)).mpr
          (by simpa only [mul_comm] using hweighted)
      _ = _ := by ring
  have hc := fixedCharacter_constant_step n m ell hnell
  change N * (N + 1) ^ 2 * C / (D ^ 2 * P) ≤
    (2 : ℝ) ^ (4 * (n + 1) * (n + 1)) /
      (2 : ℝ) ^ (((n + 1) + (m + 1)) * ell) at hc
  have hfinal := ht.trans (mul_le_mul_of_nonneg_right hc hε)
  rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_self]
  change (2 : ℝ) ^ (((n + 1) + (m + 1)) * ell) * t ≤
    (2 : ℝ) ^ (4 * (n + 1) * (n + 1)) * ε
  have hresult := (le_div_iff₀
    (show 0 < (2 : ℝ) ^ (((n + 1) + (m + 1)) * ell) by positivity)).mp
      (show t ≤ ((2 : ℝ) ^ (4 * (n + 1) * (n + 1)) * ε) /
        (2 : ℝ) ^ (((n + 1) + (m + 1)) * ell) from hfinal.trans_eq (by ring))
  simpa only [mul_comm] using hresult

end

/-!
# Transport of the primal codomain

An equivalence of primal codomains gives a unique frequency in the Fourier
pullback fiber. The resulting exact coefficient identity transports both
the small component and its prescribed-frequency energy. No invariance or
analytic estimate is needed for these identities.
-/

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Fourier.MatrixFourier

variable {E F F' I J : Type*}
  [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F] [AddCommGroup F'] [Module F2 F']
  [AddCommGroup I] [Module F2 I] [AddCommGroup J] [Module F2 J]

def codomainTransport (e : F ≃ₗ[F2] F') (f : (E →ₗ[F2] F) → ℝ) :
    (E →ₗ[F2] F') → ℝ := fun X => f (e.symm.toLinearMap.comp X)

/-- Actual dual frequencies are reindexed by precomposition with the inverse. -/
def codomainFrequencyEquiv (e : F ≃ₗ[F2] F') : (F →ₗ[F2] I) ≃ (F' →ₗ[F2] I) where
  toFun T := T.comp e.symm.toLinearMap
  invFun T := T.comp e.toLinearMap
  left_inv T := by ext x; simp
  right_inv T := by ext x; simp

@[simp] theorem codomainFrequencyEquiv_apply (e : F ≃ₗ[F2] F') (T : F →ₗ[F2] I) :
    codomainFrequencyEquiv e T = T.comp e.symm.toLinearMap := rfl

@[simp] theorem codomainFrequency_cancel (e : F ≃ₗ[F2] F') (T : F →ₗ[F2] I) :
    (T.comp e.symm.toLinearMap).comp e.toLinearMap = T := by ext x; simp

theorem surjective_comp_codomainEquiv_iff (e : F ≃ₗ[F2] F') (T : F' →ₗ[F2] I) :
    Function.Surjective (T.comp e.toLinearMap) ↔ Function.Surjective T := by
  constructor
  · intro h y
    obtain ⟨x, hx⟩ := h y
    exact ⟨e x, hx⟩
  · intro h y
    obtain ⟨x, hx⟩ := h y
    refine ⟨e.symm x, ?_⟩
    simpa using hx

variable [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 F']
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (E →ₗ[F2] F')] [Fintype (F' →ₗ[F2] E)]

omit [Fintype (F' →ₗ[F2] E)] in
/-- The Fourier pullback fiber of a codomain equivalence has a single term. -/
theorem linearCoeff_codomainTransport (e : F ≃ₗ[F2] F')
    (f : (E →ₗ[F2] F) → ℝ) (S' : F' →ₗ[F2] E) :
    linearCoeff (codomainTransport e f) S' = linearCoeff f (S'.comp e.toLinearMap) := by
  unfold codomainTransport
  rw [KMSFourthMoment.coefficient_codomain_pullback]
  have hc : (S'.comp e.toLinearMap).comp e.symm.toLinearMap = S' := by ext x; simp
  rw [Finset.sum_eq_single (S'.comp e.toLinearMap)]
  · rw [ite_eq_left hc]
  · intro S _ hS
    apply ite_eq_right
    intro h
    apply hS
    apply LinearMap.ext
    intro x
    simpa using congrArg (fun R : F' →ₗ[F2] E => R (e x)) h
  · intro h
    exact (h (Finset.mem_univ _)).elim

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 F'] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] [Fintype (E →ₗ[F2] F')] [Fintype (F' →ₗ[F2] E)] in
/-- Codomain transport preserves the original basis invariance. -/
theorem basisInvariant_codomainTransport (e : F ≃ₗ[F2] F')
    (f : (E →ₗ[F2] F) → ℝ) (hf : KMSBasisInvariant.IsBasisInvariant f) :
    KMSBasisInvariant.IsBasisInvariant (codomainTransport e f) := by
  intro g X
  change f (e.symm.toLinearMap.comp (X.comp g.toLinearMap)) =
    f (e.symm.toLinearMap.comp X)
  rw [← LinearMap.comp_assoc]
  exact hf g (e.symm.toLinearMap.comp X)

variable [FiniteDimensional F2 I]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)]
  [Fintype (I →ₗ[F2] F')] [Fintype (F' →ₗ[F2] I)]

omit [FiniteDimensional F2 I] [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)]
  [Fintype (I →ₗ[F2] F')] [Fintype (F' →ₗ[F2] I)] [Fintype (F' →ₗ[F2] E)] in
theorem smallCoeff_codomainTransport (e : F ≃ₗ[F2] F') (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (T : F' →ₗ[F2] I) :
    smallCoeff ι (codomainTransport e f) T =
      smallCoeff ι f (T.comp e.toLinearMap) := by
  unfold smallCoeff
  rw [surjective_comp_codomainEquiv_iff]
  split_ifs
  · rw [linearCoeff_codomainTransport, LinearMap.comp_assoc]
  · rfl

omit [Fintype (F' →ₗ[F2] E)] in
/-- The synthesized small component itself commutes with codomain transport. -/
theorem smallComponent_codomainTransport (e : F ≃ₗ[F2] F') (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) :
    smallComponent ι (codomainTransport e f) =
      codomainTransport e (smallComponent ι f) := by
  apply eq_of_coeff_eq
  intro T
  rw [coeff_smallComponent, linearCoeff_codomainTransport, coeff_smallComponent,
    smallCoeff_codomainTransport]

omit [FiniteDimensional F2 I] [Fintype (I →ₗ[F2] F)] [Fintype (I →ₗ[F2] F')]
  [Fintype (F' →ₗ[F2] E)] in
/-- Transport the prescribed partial frequency together with the primal
codomain; the normalized energy remains exactly unchanged. -/
theorem fixedFrequencyEnergy_codomainTransport (e : F ≃ₗ[F2] F') (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (π : I →ₗ[F2] J) (A : F →ₗ[F2] J) :
    fixedFrequencyEnergy ι (codomainTransport e f) π (A.comp e.symm.toLinearMap) =
      fixedFrequencyEnergy ι f π A := by
  unfold fixedFrequencyEnergy
  rw [Finset.sum_filter, Finset.sum_filter]
  symm
  apply Fintype.sum_equiv (codomainFrequencyEquiv (I := I) e)
  intro T
  have hp : π.comp (T.comp e.symm.toLinearMap) = A.comp e.symm.toLinearMap ↔
      π.comp T = A := by
    rw [← LinearMap.comp_assoc]
    exact (codomainFrequencyEquiv (I := J) e).injective.eq_iff
  simp only [codomainFrequencyEquiv_apply, smallCoeff_codomainTransport,
    codomainFrequency_cancel, hp]

end
end MaxCutGames.Inverse.KMSAnalytic

end OAI
