import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Logic.Equiv.Sum
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import OAI.Computability.UniqueGames.Inverse.KMSAffineRestrictionComplementLemmas
import OAI.Computability.UniqueGames.Inverse.KMSAnalyticHybridCoordinatesConditions

namespace OAI

section

/-! The exact injection/surjection factorization of the adapted coordinates. -/

namespace UniqueGamesTheorem.Inverse.KMSAnalyticHybridCoordinates

variable {R A W D B C : Type*} [Ring R]
  [AddCommGroup A] [Module R A] [AddCommGroup W] [Module R W]
  [AddCommGroup D] [Module R D] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]

/-- The small frequency map before its last coordinate is embedded into `D`. -/
def fullCoordinates {z : B →ₗ[R] W}
    (p : Coordinates (A := A) (D := D) (C := C) z) :
    (B × C) →ₗ[R] (A × (W × C)) :=
  p.alpha.prod (p.psi.prod (LinearMap.snd R B C))

/-- The injection chosen by the last block, keeping the first two blocks fixed. -/
def embedLast (v : C →ₗ[R] D) : (A × (W × C)) →ₗ[R] (A × (W × D)) :=
  (LinearMap.id : A →ₗ[R] A).prodMap ((LinearMap.id : W →ₗ[R] W).prodMap v)

@[simp] theorem embedLast_apply (v : C →ₗ[R] D) (x : A × (W × C)) :
    embedLast v x = (x.1, x.2.1, v x.2.2) := rfl

theorem embedLast_injective (v : C →ₗ[R] D) (hv : Function.Injective v) :
    Function.Injective (embedLast (A := A) (W := W) v) := by
  intro x y h
  apply Prod.ext
  · exact congrArg (fun u : A × (W × D) => u.1) h
  · apply Prod.ext
    · exact congrArg (fun u : A × (W × D) => u.2.1) h
    · apply hv
      exact congrArg (fun u : A × (W × D) => u.2.2) h

theorem assemble_eq_embedLast_comp {z : B →ₗ[R] W}
    (p : Coordinates (A := A) (D := D) (C := C) z) :
    assemble p = (embedLast p.v).comp (fullCoordinates p) := by
  apply LinearMap.ext
  intro x
  rfl

theorem range_assemble_of_fullCoordinates_surjective {z : B →ₗ[R] W}
    (p : Coordinates (A := A) (D := D) (C := C) z)
    (hp : Function.Surjective (fullCoordinates p)) :
    (assemble p).range = (embedLast (A := A) (W := W) p.v).range := by
  rw [assemble_eq_embedLast_comp, LinearMap.range_comp,
    LinearMap.range_eq_top.mpr hp, Submodule.map_top]

theorem finrank_assemble {z : B →ₗ[R] W}
    (p : Coordinates (A := A) (D := D) (C := C) z)
    (hv : Function.Injective p.v) (hp : Function.Surjective (fullCoordinates p)) :
    Module.finrank R (assemble p).range = Module.finrank R (A × (W × C)) := by
  rw [range_assemble_of_fullCoordinates_surjective p hp]
  exact LinearMap.finrank_range_of_inj (embedLast_injective p.v hv)

theorem ker_assemble {z : B →ₗ[R] W}
    (p : Coordinates (A := A) (D := D) (C := C) z)
    (hv : Function.Injective p.v) :
    (assemble p).ker = (fullCoordinates p).ker := by
  rw [assemble_eq_embedLast_comp]
  exact LinearMap.ker_comp_of_ker_eq_bot _
    (LinearMap.ker_eq_bot.mpr (embedLast_injective p.v hv))

end UniqueGamesTheorem.Inverse.KMSAnalyticHybridCoordinates

end

section

/-! The actual hybrid compressed fiber, with no coordinate multiplicity. -/

namespace UniqueGamesTheorem.Inverse.KMSAnalyticHybridCoordinates

variable {R A W D B C : Type*} [Field R]
  [AddCommGroup A] [Module R A] [AddCommGroup W] [Module R W]
  [AddCommGroup D] [Module R D] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]

open UniqueGamesTheorem.Appendix

/-- The exact coordinate parametrization after imposing the genuine hybrid
selector. The two remaining conditions are ordinary injectivity and
surjectivity of displayed linear maps. -/
def hybridFiberEquiv (z : B →ₗ[R] W) (hz : Function.Surjective z) :
    {S : (B × C) →ₗ[R] (A × (W × D)) //
      compressBlock S = z.prod (0 : B →ₗ[R] D) ∧
        LinearIdentities.Hybrid S
          (LinearMap.range (LinearMap.inl R A (W × D)))
          (LinearMap.range (LinearMap.inl R B C))} ≃
      {p : Coordinates (A := A) (D := D) (C := C) z //
        Function.Injective p.v ∧ Function.Surjective (fullCoordinates p)} where
  toFun S := ⟨extract z ⟨S.val, S.property.1⟩, by
    apply (hybrid_assemble_iff _ hz).mp
    rw [assemble_extract]
    exact S.property.2⟩
  invFun p := ⟨assemble p.val, compressBlock_assemble p.val,
    (hybrid_assemble_iff p.val hz).mpr p.property⟩
  left_inv S := by
    apply Subtype.ext
    exact assemble_extract z ⟨S.val, S.property.1⟩
  right_inv p := by
    apply Subtype.ext
    exact extract_assemble p.val

/-- Every map in the actual fiber has the prescribed small rank. -/
theorem hybridFiber_finrank (z : B →ₗ[R] W) (hz : Function.Surjective z)
    (S : (B × C) →ₗ[R] (A × (W × D)))
    (hc : compressBlock S = z.prod (0 : B →ₗ[R] D))
    (hh : LinearIdentities.Hybrid S
      (LinearMap.range (LinearMap.inl R A (W × D)))
      (LinearMap.range (LinearMap.inl R B C))) :
    Module.finrank R S.range = Module.finrank R (A × (W × C)) := by
  let p := (hybridFiberEquiv (A := A) (D := D) (C := C) z hz) ⟨S, hc, hh⟩
  have he : assemble p.val = S := assemble_extract z ⟨S, hc⟩
  rw [← he]
  exact finrank_assemble p.val p.property.1 p.property.2

end UniqueGamesTheorem.Inverse.KMSAnalyticHybridCoordinates

end

section

/-!
# Cauchy--Schwarz for the hybrid coefficient fibers

The complementary-vector phase sum contributes the square of its number
of terms. Merging extensions with the same restriction contributes their
largest fiber size. Both factors come from finite Cauchy--Schwarz; summing
the disjoint fibers preserves the unnormalized coefficient energy.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

noncomputable section
open scoped BigOperators Classical

/-- Unit-bounded squared phases cost at most the number of summands in the
finite Cauchy--Schwarz inequality. -/
theorem phase_weighted_sum_sq_le {Ψ : Type*} (s : Finset Ψ)
    (b H : Ψ → ℝ) (hb : ∀ ψ ∈ s, b ψ ^ 2 ≤ 1) :
    (∑ ψ ∈ s, b ψ * H ψ) ^ 2 ≤ (s.card : ℝ) * ∑ ψ ∈ s, H ψ ^ 2 := by
  have hphase : (∑ ψ ∈ s, b ψ ^ 2) ≤ (s.card : ℝ) := by
    calc
      _ ≤ ∑ _ψ ∈ s, (1 : ℝ) := Finset.sum_le_sum hb
      _ = _ := by simp
  exact (Finset.sum_mul_sq_le_sq_mul_sq s b H).trans
    (mul_le_mul_of_nonneg_right hphase (Finset.sum_nonneg (fun ψ _ => sq_nonneg (H ψ))))

/-- A finite sum of phases has square at most the squared cardinality.
The statement also covers an empty indexing type. -/
theorem phase_sum_sq_le_card_sq {V : Type*} [Fintype V]
    (a : V → ℝ) (ha : ∀ v, a v ^ 2 ≤ 1) :
    (∑ v, a v) ^ 2 ≤ (Fintype.card V : ℝ) ^ 2 := by
  have h := phase_weighted_sum_sq_le Finset.univ a (fun _ => (1 : ℝ))
    (fun v _ => ha v)
  simpa only [mul_one, one_pow, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, pow_two] using h

/-- Summing the Cauchy--Schwarz bounds over the disjoint restriction fibers
loses only the largest fiber cardinality. -/
theorem sum_fiber_phase_sq_le {Ψ Z : Type*} [Fintype Ψ] [Fintype Z]
    (r : Ψ → Z) (b H : Ψ → ℝ) (maxFiber : ℕ)
    (hb : ∀ ψ, b ψ ^ 2 ≤ 1)
    (hcard : ∀ z, (Finset.univ.filter (fun ψ => r ψ = z)).card ≤ maxFiber) :
    (∑ z, (∑ ψ with r ψ = z, b ψ * H ψ) ^ 2) ≤
      (maxFiber : ℝ) * ∑ ψ, H ψ ^ 2 := by
  have hlocal (z : Z) :
      (∑ ψ with r ψ = z, b ψ * H ψ) ^ 2 ≤
        (maxFiber : ℝ) * ∑ ψ with r ψ = z, H ψ ^ 2 := by
    have hc : ((Finset.univ.filter (fun ψ => r ψ = z)).card : ℝ) ≤
        (maxFiber : ℝ) := Nat.cast_le.mpr (hcard z)
    exact (phase_weighted_sum_sq_le (Finset.univ.filter (fun ψ => r ψ = z))
      b H (fun ψ _ => hb ψ)).trans
      (mul_le_mul_of_nonneg_right hc (Finset.sum_nonneg (fun ψ _ => sq_nonneg (H ψ))))
  calc
    _ ≤ ∑ z, (maxFiber : ℝ) * ∑ ψ with r ψ = z, H ψ ^ 2 :=
      Finset.sum_le_sum (fun z _ => hlocal z)
    _ = (maxFiber : ℝ) * ∑ ψ, H ψ ^ 2 := by
      rw [← Finset.mul_sum]
      exact congrArg (fun t : ℝ => (maxFiber : ℝ) * t)
        (Finset.sum_fiberwise Finset.univ r (fun ψ => H ψ ^ 2))

/-- The hybrid coefficient factorization has energy bounded by the squared
number of complementary choices times the extension-fiber size and the
original mixed coefficient energy. No phase cancellation is assumed. -/
theorem sum_fiber_product_sq_le {V Ψ Z : Type*}
    [Fintype V] [Fintype Ψ] [Fintype Z]
    (r : Ψ → Z) (a : V → ℝ) (b H : Ψ → ℝ) (maxFiber : ℕ)
    (ha : ∀ v, a v ^ 2 ≤ 1) (hb : ∀ ψ, b ψ ^ 2 ≤ 1)
    (hcard : ∀ z, (Finset.univ.filter (fun ψ => r ψ = z)).card ≤ maxFiber) :
    (∑ z, ((∑ v, a v) * (∑ ψ with r ψ = z, b ψ * H ψ)) ^ 2) ≤
      (Fintype.card V : ℝ) ^ 2 * (maxFiber : ℝ) * ∑ ψ, H ψ ^ 2 := by
  have haSum := phase_sum_sq_le_card_sq a ha
  have hmerged := sum_fiber_phase_sq_le r b H maxFiber hb hcard
  calc
    _ = (∑ v, a v) ^ 2 * ∑ z, (∑ ψ with r ψ = z, b ψ * H ψ) ^ 2 := by
      simp_rw [mul_pow]
      rw [Finset.mul_sum]
    _ ≤ (Fintype.card V : ℝ) ^ 2 *
        ∑ z, (∑ ψ with r ψ = z, b ψ * H ψ) ^ 2 :=
      mul_le_mul_of_nonneg_right haSum (Finset.sum_nonneg (fun z _ => sq_nonneg _))
    _ ≤ (Fintype.card V : ℝ) ^ 2 * ((maxFiber : ℝ) * ∑ ψ, H ψ ^ 2) :=
      mul_le_mul_of_nonneg_left hmerged (sq_nonneg _)
    _ = _ := (mul_assoc _ _ _).symm

end
end UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

end

section

/-!
# Partition frequencies by their actual image

A map with image `W` is uniquely a surjection onto `W`, followed by the
subspace inclusion. Consequently a sum over rank-`q` frequencies splits
exactly over dimension-`q` image subspaces and surjections onto each image.
The identities hold for arbitrary real weights and use no analytic estimate.
-/

noncomputable section

namespace UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical

variable {R B U : Type*} [Ring R]
  [AddCommGroup B] [Module R B] [AddCommGroup U] [Module R U]

/-- The inclusion of the target subspace preserves the prescribed image of
a surjective map. -/
theorem range_subtype_comp_of_surjective (W : Submodule R U)
    (z : B →ₗ[R] W) (hz : Function.Surjective z) :
    (W.subtype.comp z).range = W := by
  ext u
  constructor
  · rintro ⟨b, rfl⟩
    exact (z b).property
  · intro hu
    obtain ⟨b, hb⟩ := hz ⟨u, hu⟩
    exact ⟨b, congrArg Subtype.val hb⟩

/-- The full fixed-image fiber, with its canonical surjective coordinates. -/
def fixedImageEquivSurjection (W : Submodule R U) :
    {z : B →ₗ[R] U // z.range = W} ≃
      {z : B →ₗ[R] W // Function.Surjective z} where
  toFun z := ⟨z.val.codRestrict W (fun b => z.property.le (LinearMap.mem_range_self z.val b)), by
    intro w
    have hw : w.val ∈ z.val.range := z.property.symm ▸ w.property
    obtain ⟨b, hb⟩ := hw
    exact ⟨b, Subtype.ext hb⟩⟩
  invFun z := ⟨W.subtype.comp z.val, range_subtype_comp_of_surjective W z.val z.property⟩
  left_inv z := by
    apply Subtype.ext
    apply LinearMap.ext
    intro b
    rfl
  right_inv z := by
    apply Subtype.ext
    apply LinearMap.ext
    intro b
    apply Subtype.ext
    rfl

@[simp] theorem fixedImageEquivSurjection_symm_val (W : Submodule R U)
    (z : {z : B →ₗ[R] W // Function.Surjective z}) :
    ((fixedImageEquivSurjection W).symm z).val = W.subtype.comp z.val := rfl

@[simp] theorem fixedImageEquivSurjection_apply_coe (W : Submodule R U)
    (z : {z : B →ₗ[R] U // z.range = W}) (b : B) :
    ((fixedImageEquivSurjection W z).val b : U) = z.val b := rfl

/-- Frequencies of an exact rank. -/
abbrev ImageRankFrequency (q : ℕ) :=
  {z : B →ₗ[R] U // Module.finrank R z.range = q}

/-- Actual image subspaces of the required dimension. -/
abbrev RankImage (R U : Type*) [Ring R] [AddCommGroup U] [Module R U] (q : ℕ) :=
  {W : Submodule R U // Module.finrank R W = q}

/-- The image classification of an exact-rank frequency. -/
def frequencyImage (q : ℕ) (z : ImageRankFrequency (R := R) (B := B) (U := U) q) :
    RankImage R U q := ⟨z.val.range, z.property⟩

/-- Removing the redundant rank certificate from a fixed-image fiber. -/
def frequencyImageFiberEquiv (q : ℕ) (W : RankImage R U q) :
    {z : ImageRankFrequency (R := R) (B := B) (U := U) q // frequencyImage q z = W} ≃
      {z : B →ₗ[R] U // z.range = W.val} where
  toFun z := ⟨z.val.val, congrArg Subtype.val z.property⟩
  invFun z := ⟨⟨z.val, by rw [z.property]; exact W.property⟩, Subtype.ext z.property⟩
  left_inv z := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv z := by apply Subtype.ext; rfl

/-- Exact rank frequencies are in bijection with a choice of actual image
and a surjective map onto it. -/
def rankFrequencyImageEquiv (q : ℕ) :
    ImageRankFrequency (R := R) (B := B) (U := U) q ≃
      Σ W : RankImage R U q, {z : B →ₗ[R] W.val // Function.Surjective z} :=
  (Equiv.sigmaFiberEquiv (frequencyImage (R := R) (B := B) (U := U) q)).symm.trans
    (Equiv.sigmaCongrRight fun W =>
      (frequencyImageFiberEquiv q W).trans (fixedImageEquivSurjection W.val))

@[simp] theorem rankFrequencyImageEquiv_symm_val (q : ℕ)
    (p : Σ W : RankImage R U q, {z : B →ₗ[R] W.val // Function.Surjective z}) :
    ((rankFrequencyImageEquiv q).symm p).val = p.1.val.subtype.comp p.2.val := rfl

section Sums

variable [Fintype (B →ₗ[R] U)] [Fintype (Submodule R U)]
  [∀ W : Submodule R U, Fintype (B →ₗ[R] W)]

omit [Fintype (Submodule R U)] in
/-- Exact fixed-image reindexing for arbitrary real weights. -/
theorem sum_fixedImage_eq_sum_surjection (W : Submodule R U)
    (weight : (B →ₗ[R] U) → ℝ) :
    (∑ z : {z : B →ₗ[R] U // z.range = W}, weight z.val) =
      ∑ z : {z : B →ₗ[R] W // Function.Surjective z}, weight (W.subtype.comp z.val) := by
  symm
  apply Fintype.sum_equiv (fixedImageEquivSurjection W).symm
  intro z
  rfl

/-- Partition the exact-rank frequency sum by the actual image subspace. -/
theorem sum_rankFrequency_eq_sum_image (q : ℕ) (weight : (B →ₗ[R] U) → ℝ) :
    (∑ z : ImageRankFrequency (R := R) (B := B) (U := U) q, weight z.val) =
      ∑ W : RankImage R U q,
        ∑ z : {z : B →ₗ[R] W.val // Function.Surjective z},
          weight (W.val.subtype.comp z.val) := by
  calc
    _ = ∑ p : Σ W : RankImage R U q,
        {z : B →ₗ[R] W.val // Function.Surjective z},
        weight (p.1.val.subtype.comp p.2.val) := by
      symm
      apply Fintype.sum_equiv (rankFrequencyImageEquiv q).symm
      intro p
      rfl
    _ = _ := Fintype.sum_sigma _

/-- The same partition in filtered-sum form, convenient for Fourier support
conditions that are expressed as vanishing away from one rank. -/
theorem sum_filter_rank_eq_sum_image (q : ℕ) (weight : (B →ₗ[R] U) → ℝ) :
    (∑ z : B →ₗ[R] U with Module.finrank R z.range = q, weight z) =
      ∑ W : RankImage R U q,
        ∑ z : {z : B →ₗ[R] W.val // Function.Surjective z},
          weight (W.val.subtype.comp z.val) := by
  rw [Finset.sum_subtype (p := fun z : B →ₗ[R] U => Module.finrank R z.range = q)
    (Finset.univ.filter fun z : B →ₗ[R] U =>
    Module.finrank R z.range = q) (by simp) weight]
  exact sum_rankFrequency_eq_sum_image q weight

/-- If a weight vanishes outside rank `q`, the full sum has the same exact
image partition. No positivity assumption on the weight is needed. -/
theorem sum_eq_sum_image_of_rank_support (q : ℕ) (weight : (B →ₗ[R] U) → ℝ)
    (hsupport : ∀ z, Module.finrank R z.range ≠ q → weight z = 0) :
    (∑ z : B →ₗ[R] U, weight z) =
      ∑ W : RankImage R U q,
        ∑ z : {z : B →ₗ[R] W.val // Function.Surjective z},
          weight (W.val.subtype.comp z.val) := by
  rw [← sum_filter_rank_eq_sum_image, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : Module.finrank R z.range = q
  · simp [hz]
  · simp [hz, hsupport z hz]

end Sums

section ImageCoordinates

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Coordinates adapted to a prescribed image and any chosen complement. -/
def imageCoordinates (W D : Submodule K V) (h : IsCompl W D) : V ≃ₗ[K] (W × D) :=
  (Submodule.prodEquivOfIsCompl W D h).symm

/-- Vectors in the prescribed image have zero complementary coordinate. -/
@[simp] theorem imageCoordinates_subtype (W D : Submodule K V) (h : IsCompl W D)
    (w : W) : imageCoordinates W D h (w : V) = (w, 0) :=
  Submodule.prodEquivOfIsCompl_symm_apply_left W D h w

/-- Each fixed-image frequency has exactly the block form used by the
compressed Hybrid-coordinate parametrization. -/
theorem imageCoordinates_frequency {X : Type*} [AddCommGroup X] [Module K X]
    (W D : Submodule K V) (h : IsCompl W D) (z : X →ₗ[K] W) :
    (imageCoordinates W D h).toLinearMap.comp (W.subtype.comp z) =
      z.prod (0 : X →ₗ[K] D) := by
  apply LinearMap.ext
  intro x
  exact imageCoordinates_subtype W D h (z x)

/-- A complement contributes exactly the remaining ambient dimension. -/
theorem imageCoordinates_finrank [FiniteDimensional K V]
    (W D : Submodule K V) (h : IsCompl W D) :
    Module.finrank K W + Module.finrank K D = Module.finrank K V := by
  simpa only [Module.finrank_prod] using (Submodule.prodEquivOfIsCompl W D h).finrank_eq

/-- Every image subspace admits the required product coordinates. -/
theorem exists_imageCoordinates (W : Submodule K V) :
    ∃ D : Submodule K V, ∃ e : V ≃ₗ[K] (W × D), ∀ w : W, e (w : V) = (w, 0) := by
  obtain ⟨D, h⟩ := W.exists_isCompl
  exact ⟨D, imageCoordinates W D h, imageCoordinates_subtype W D h⟩

end ImageCoordinates
end UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

end

end

section

/-!
# Fixed kernels and injective quotient maps

Linear maps with a prescribed kernel are in explicit bijection with injective
maps from the corresponding quotient. This elementary counting foundation
works over any ring, and in particular over the binary field used by KMS.
No expansion or rank-level estimate is assumed.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalyticKernelCount

noncomputable section

variable {R E F : Type*} [Ring R]
  [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]

/-- Composing an injective map with the quotient projection has exactly the
prescribed kernel. -/
theorem ker_comp_mkQ (K : Submodule R F) (J : (F ⧸ K) →ₗ[R] E)
    (hJ : Function.Injective J) : (J.comp K.mkQ).ker = K := by
  rw [LinearMap.ker_comp_of_ker_eq_bot K.mkQ (LinearMap.ker_eq_bot.mpr hJ),
    Submodule.ker_mkQ]

/-- Every map with kernel `K` factors uniquely through an injective quotient
map; the inverse sends that quotient map to its composition with `K.mkQ`. -/
def fixedKernelEquivQuotientInjection (K : Submodule R F) :
    {S : F →ₗ[R] E // S.ker = K} ≃
      {J : (F ⧸ K) →ₗ[R] E // Function.Injective J} where
  toFun S := ⟨K.liftQ S.val S.property.symm.le,
    LinearMap.ker_eq_bot.mp (K.ker_liftQ_eq_bot S.val _ S.property.le)⟩
  invFun J := ⟨J.val.comp K.mkQ, ker_comp_mkQ K J.val J.property⟩
  left_inv S := by
    apply Subtype.ext
    exact K.liftQ_mkQ S.val _
  right_inv J := by
    apply Subtype.ext
    apply LinearMap.ext
    intro q
    obtain ⟨x, rfl⟩ := K.mkQ_surjective q
    rfl

@[simp]
theorem fixedKernelEquiv_apply_mkQ (K : Submodule R F)
    (S : {S : F →ₗ[R] E // S.ker = K}) (x : F) :
    (fixedKernelEquivQuotientInjection K S).val (K.mkQ x) = S.val x := rfl

@[simp]
theorem fixedKernelEquiv_symm_apply (K : Submodule R F)
    (J : {J : (F ⧸ K) →ₗ[R] E // Function.Injective J}) :
    ((fixedKernelEquivQuotientInjection K).symm J).val = J.val.comp K.mkQ := rfl

/-- Quotient factorization leaves the image subspace unchanged. -/
theorem range_forward (K : Submodule R F)
    (S : {S : F →ₗ[R] E // S.ker = K}) :
    (fixedKernelEquivQuotientInjection K S).val.range = S.val.range :=
  K.range_liftQ S.val _

/-- The quotient lift has the same rank as the original map. -/
theorem finrank_range_forward (K : Submodule R F)
    (S : {S : F →ₗ[R] E // S.ker = K}) :
    Module.finrank R (fixedKernelEquivQuotientInjection K S).val.range =
      Module.finrank R S.val.range := by
  rw [range_forward]

/-- A prescribed kernel fixes the rank to the dimension of its quotient. -/
theorem fixedKernel_finrank_eq_quotient (K : Submodule R F)
    (S : {S : F →ₗ[R] E // S.ker = K}) :
    Module.finrank R S.val.range = Module.finrank R (F ⧸ K) := by
  rw [← range_forward K S]
  exact LinearMap.finrank_range_of_inj (fixedKernelEquivQuotientInjection K S).property

/-- Surjectivity of the quotient projection preserves the range of any map
defined on the quotient. -/
theorem range_comp_mkQ (K : Submodule R F) (J : (F ⧸ K) →ₗ[R] E) :
    (J.comp K.mkQ).range = J.range := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨K.mkQ x, rfl⟩
  · rintro ⟨q, rfl⟩
    obtain ⟨x, rfl⟩ := K.mkQ_surjective q
    exact ⟨x, rfl⟩

/-- The inverse factorization of an injection has quotient dimension as its
rank. In the finite-dimensional binary case this is the ordinary finite rank. -/
theorem quotientInjection_comp_finrank (K : Submodule R F)
    (J : (F ⧸ K) →ₗ[R] E) (hJ : Function.Injective J) :
    Module.finrank R (J.comp K.mkQ).range = Module.finrank R (F ⧸ K) := by
  rw [range_comp_mkQ]
  exact LinearMap.finrank_range_of_inj hJ

/-- Exact fixed-kernel count, stated without requiring a chosen enumeration. -/
theorem natCard_fixedKernel_eq_injectiveQuotient (K : Submodule R F) :
    Nat.card {S : F →ₗ[R] E // S.ker = K} =
      Nat.card {J : (F ⧸ K) →ₗ[R] E // Function.Injective J} :=
  Nat.card_congr (fixedKernelEquivQuotientInjection K)

/-- The same counting equality for any finite enumerations of the two sides. -/
theorem card_fixedKernel_eq_injectiveQuotient (K : Submodule R F)
    [Fintype {S : F →ₗ[R] E // S.ker = K}]
    [Fintype {J : (F ⧸ K) →ₗ[R] E // Function.Injective J}] :
    Fintype.card {S : F →ₗ[R] E // S.ker = K} =
      Fintype.card {J : (F ⧸ K) →ₗ[R] E // Function.Injective J} :=
  Fintype.card_congr (fixedKernelEquivQuotientInjection K)

end
end UniqueGamesTheorem.Inverse.KMSAnalyticKernelCount

end

section

/-! Scalar closure of the genuine KMS fixed-character induction. The three
combinatorial losses are absorbed by the explicit quadratic exponent; no
Fourier estimate is asserted or assumed in this arithmetic lemma. -/

namespace UniqueGamesTheorem.Inverse.KMSAnalytic

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

end UniqueGamesTheorem.Inverse.KMSAnalytic

end

section

/-! Exact finite conditioning error for bounded functions. These identities
keep the rejected mass visible when comparing all maps with independent bases.
-/

namespace UniqueGamesTheorem.Inverse.KMSBasisComparison

noncomputable section
open scoped BigOperators Classical

variable {Ω : Type*} [Fintype Ω]

omit [Fintype Ω] in
/-- Finset conditioning and uniform sampling from its membership subtype are
the same normalized finite sum, including the empty event. -/
theorem expect_coe_eq (s : Finset Ω) (f : Ω → ℝ) :
    (𝔼 x : s, f x.val) = s.expect f := by
  simp only [Finset.expect_eq_sum_div_card, Finset.card_univ,
    Fintype.card_coe, Finset.sum_coe_sort]

omit [Fintype Ω] in
theorem expect_unit_interval (s : Finset Ω) (f : Ω → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    0 ≤ s.expect f ∧ s.expect f ≤ 1 := by
  refine ⟨Finset.expect_nonneg (fun x _ => hf0 x), ?_⟩
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  · exact Finset.expect_le hs (fun x _ => hf1 x)

/-- The weighted conditional expectation is the unnormalized sum divided by
the ambient cardinality, also for an empty conditioning event. -/
theorem mass_mul_expect (s : Finset Ω) (f : Ω → ℝ) :
    (s.card : ℝ) / Fintype.card Ω * s.expect f =
      (∑ x ∈ s, f x) / Fintype.card Ω := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  · rw [Finset.expect_eq_sum_div_card]
    have hn : (s.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hs.card_ne_zero
    by_cases hN : (Fintype.card Ω : ℝ) = 0
    · simp [hN]
    · field_simp

/-- Exact two-event total expectation, with the same zero convention on both
conditional expectations as mathlib's finite expectation. -/
theorem expect_partition (s : Finset Ω) (f : Ω → ℝ) :
    (𝔼 x, f x) =
      (s.card : ℝ) / Fintype.card Ω * s.expect f +
      ((Finset.univ \ s).card : ℝ) / Fintype.card Ω *
        (Finset.univ \ s).expect f := by
  rw [mass_mul_expect, mass_mul_expect, ← add_div, Fintype.expect_eq_sum_div_card]
  congr 1
  exact (Finset.sum_sdiff (Finset.subset_univ s)).symm.trans (add_comm _ _)

/-- Conditioning a bounded function changes its expectation by at most the
discarded probability mass. No independence assumption is used here. -/
theorem abs_expect_sub_restrict_le [Nonempty Ω] (s : Finset Ω) (f : Ω → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    |(𝔼 x, f x) - s.expect f| ≤
      ((Finset.univ \ s).card : ℝ) / Fintype.card Ω := by
  have hB := expect_unit_interval s f hf0 hf1
  have hC := expect_unit_interval (Finset.univ \ s) f hf0 hf1
  have hN : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hsum : (s.card : ℝ) / Fintype.card Ω +
      ((Finset.univ \ s).card : ℝ) / Fintype.card Ω = 1 := by
    rw [← add_div]
    have hc := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ s)
    have hcast : ((Finset.univ \ s).card : ℝ) + (s.card : ℝ) =
        Fintype.card Ω := by exact_mod_cast hc.trans (Finset.card_univ)
    rw [add_comm, hcast, div_self hN]
  have hq : 0 ≤ ((Finset.univ \ s).card : ℝ) / Fintype.card Ω := by positivity
  have hp : (s.card : ℝ) / Fintype.card Ω =
      1 - ((Finset.univ \ s).card : ℝ) / Fintype.card Ω := by linarith
  rw [expect_partition]
  rw [hp]
  apply abs_le.mpr
  constructor
  · nlinarith [mul_nonneg hq hB.1, mul_nonneg hq hC.1,
      mul_nonneg hq (sub_nonneg.mpr hB.2)]
  · nlinarith [mul_nonneg hq hB.1, mul_nonneg hq hC.1,
      mul_nonneg hq (sub_nonneg.mpr hC.2)]

end
end UniqueGamesTheorem.Inverse.KMSBasisComparison

end

section

/-!
Binary linear functionals are determined by their kernels. The statement
includes the zero functional; no choice of a nonzero normalization is needed.
Injective linear images retain the same uniqueness property.
-/

namespace UniqueGamesTheorem.Inverse.KMSBasisComparison

variable {E F : Type*}
  [AddCommGroup E] [Module (ZMod 2) E]
  [AddCommGroup F] [Module (ZMod 2) F]

/-- A binary functional is determined by its zero set. -/
theorem binary_functional_eq_of_ker_eq
    {a b : E →ₗ[ZMod 2] ZMod 2} (h : a.ker = b.ker) : a = b := by
  have scalar_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  apply LinearMap.ext
  intro x
  have hzero : a x = 0 ↔ b x = 0 := by
    change x ∈ a.ker ↔ x ∈ b.ker
    rw [h]
  rcases scalar_cases (a x) with ha | ha
  · exact ha.trans (hzero.mp ha).symm
  · rcases scalar_cases (b x) with hb | hb
    · exact False.elim (zero_ne_one ((hzero.mpr hb).symm.trans ha))
    · exact ha.trans hb.symm

/-- The image of a binary functional's kernel under an injective linear map
still determines that functional uniquely. -/
theorem binary_functional_eq_of_map_ker_eq
    (X : E →ₗ[ZMod 2] F) (hX : Function.Injective X)
    {a b : E →ₗ[ZMod 2] ZMod 2}
    (h : a.ker.map X = b.ker.map X) : a = b := by
  exact binary_functional_eq_of_ker_eq (Submodule.map_injective_of_injective hX h)

end UniqueGamesTheorem.Inverse.KMSBasisComparison

end

section

/-!
# Equal fibers for restricted basis completion

A fixed independent tuple may have vectors outside the restricting submodule.
Nevertheless, any two nonempty fibers of independent completions inside that
submodule are equivalent. The change of basis fixes the fixed tuple, and its
difference from the identity has image in the restricting submodule.
-/

namespace UniqueGamesTheorem.Inverse.KMSBasisComparisonPseudorandom

noncomputable section
open scoped Classical

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {q t : ℕ}

/-- Ordered completions in `W` of `Q` to an independent spanning tuple for `L`. -/
def RestrictedCompletion (Q : Fin q → V) (W L : Submodule K V) :=
  {z : Fin t → W //
    LinearIndependent K (Sum.elim Q (fun i => (z i : V))) ∧
      Submodule.span K (Set.range (Sum.elim Q (fun i => (z i : V)))) = L}

variable {Q : Fin q → V} {W L M N : Submodule K V}

/-- A completion, regarded as a basis of the resulting subspace. -/
def completionBasis (z : RestrictedCompletion (t := t) Q W L) :
    Module.Basis (Fin q ⊕ Fin t) K L :=
  (Module.Basis.span z.property.1).map (LinearEquiv.ofEq _ _ z.property.2)

@[simp] theorem completionBasis_coe
    (z : RestrictedCompletion (t := t) Q W L) (i : Fin q ⊕ Fin t) :
    (completionBasis z i : V) = Sum.elim Q (fun j => (z.val j : V)) i := by
  simp [completionBasis]

/-- Recover a restricted completion from a basis having the prescribed prefix. -/
def completionOfBasis (b : Module.Basis (Fin q ⊕ Fin t) K L)
    (hQ : ∀ i, (b (Sum.inl i) : V) = Q i)
    (hW : ∀ i, (b (Sum.inr i) : V) ∈ W) :
    RestrictedCompletion (t := t) Q W L := by
  have hb : Sum.elim Q (fun i => ((⟨b (Sum.inr i), hW i⟩ : W) : V)) =
      fun i => (b i : V) := by
    funext i
    cases i with
    | inl i => exact (hQ i).symm
    | inr i => rfl
  refine ⟨fun i => ⟨b (Sum.inr i), hW i⟩, ?_, ?_⟩
  · rw [hb]
    exact b.linearIndependent.map' L.subtype (by simp)
  · rw [hb]
    calc
      Submodule.span K (Set.range fun i => (b i : V)) =
          (Submodule.span K (Set.range b)).map L.subtype := by
        rw [Submodule.map_span, ← Set.range_comp]
        rfl
      _ = L := by rw [b.span_eq]; simp

/-- The unique basis change carrying the first completion to the second. -/
def completionSpanEquiv
    (x : RestrictedCompletion (t := t) Q W L)
    (y : RestrictedCompletion (t := t) Q W M) : L ≃ₗ[K] M :=
  (completionBasis x).equiv (completionBasis y) (Equiv.refl _)

@[simp] theorem completionSpanEquiv_basis
    (x : RestrictedCompletion (t := t) Q W L)
    (y : RestrictedCompletion (t := t) Q W M) (i : Fin q ⊕ Fin t) :
    completionSpanEquiv x y (completionBasis x i) = completionBasis y i := by
  simp [completionSpanEquiv]

@[simp] theorem completionSpanEquiv_symm
    (x : RestrictedCompletion (t := t) Q W L)
    (y : RestrictedCompletion (t := t) Q W M) :
    (completionSpanEquiv x y).symm = completionSpanEquiv y x := by
  simp [completionSpanEquiv]

/-- Changing the completion changes every vector by an element of `W`. -/
theorem completionSpanEquiv_sub_mem
    (x : RestrictedCompletion (t := t) Q W L)
    (y : RestrictedCompletion (t := t) Q W M) (v : L) :
    (completionSpanEquiv x y v : V) - (v : V) ∈ W := by
  let d : L →ₗ[K] V := M.subtype.comp (completionSpanEquiv x y).toLinearMap - L.subtype
  have hd : (⊤ : Submodule K L) ≤ W.comap d := by
    rw [← (completionBasis x).span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change d (completionBasis x i) ∈ W
    change (completionSpanEquiv x y (completionBasis x i) : V) -
      (completionBasis x i : V) ∈ W
    rw [completionSpanEquiv_basis]
    cases i with
    | inl i => simp
    | inr i =>
      simpa only [completionBasis_coe, Sum.elim_inr] using
        W.sub_mem (y.val i).property (x.val i).property
  exact hd (Submodule.mem_top : v ∈ (⊤ : Submodule K L))

/-- The basis change preserves membership in `W`, without requiring `Q ⊆ W`. -/
theorem completionSpanEquiv_mem_iff
    (x : RestrictedCompletion (t := t) Q W L)
    (y : RestrictedCompletion (t := t) Q W M) (v : L) :
    (completionSpanEquiv x y v : V) ∈ W ↔ (v : V) ∈ W := by
  have hd := completionSpanEquiv_sub_mem x y v
  constructor
  · intro hv
    exact (W.sub_mem_iff_right hv).mp hd
  · intro hv
    exact (W.sub_mem_iff_left hv).mp hd

/-- Transport every restricted completion along one fixed basis change. -/
def transportCompletion
    (x : RestrictedCompletion (t := t) Q W L)
    (y : RestrictedCompletion (t := t) Q W M)
    (z : RestrictedCompletion (t := t) Q W L) :
    RestrictedCompletion (t := t) Q W M :=
  completionOfBasis ((completionBasis z).map (completionSpanEquiv x y))
    (by
      intro i
      have h : completionBasis z (Sum.inl i) = completionBasis x (Sum.inl i) := by
        apply Subtype.ext
        simp
      simp [Module.Basis.map_apply, h])
    (by
      intro i
      change (completionSpanEquiv x y (completionBasis z (Sum.inr i)) : V) ∈ W
      apply (completionSpanEquiv_mem_iff x y _).mpr
      simp)

@[simp] theorem transportCompletion_coe
    (x : RestrictedCompletion (t := t) Q W L)
    (y : RestrictedCompletion (t := t) Q W M)
    (z : RestrictedCompletion (t := t) Q W L) (i : Fin t) :
    ((transportCompletion x y z).val i : V) =
      (completionSpanEquiv x y (completionBasis z (Sum.inr i)) : V) := rfl

theorem transportCompletion_inverse
    (x : RestrictedCompletion (t := t) Q W L)
    (y : RestrictedCompletion (t := t) Q W M)
    (z : RestrictedCompletion (t := t) Q W L) :
    transportCompletion y x (transportCompletion x y z) = z := by
  apply Subtype.ext
  funext i
  apply Subtype.ext
  rw [transportCompletion_coe]
  have hb : completionBasis (transportCompletion x y z) (Sum.inr i) =
      completionSpanEquiv x y (completionBasis z (Sum.inr i)) := by
    apply Subtype.ext
    simp
  rw [hb, ← completionSpanEquiv_symm, LinearEquiv.symm_apply_apply]
  simp

/-- All nonempty restricted-completion fibers are equivalent. -/
def restrictedCompletionEquiv
    (x : RestrictedCompletion (t := t) Q W L)
    (y : RestrictedCompletion (t := t) Q W M) :
    RestrictedCompletion (t := t) Q W L ≃ RestrictedCompletion (t := t) Q W M where
  toFun := transportCompletion x y
  invFun := transportCompletion y x
  left_inv := transportCompletion_inverse x y
  right_inv := transportCompletion_inverse y x

/-- Equal fiber cardinality follows from the explicit completion equivalence. -/
theorem restrictedCompletionCard_eq
    (x : RestrictedCompletion (t := t) Q W L)
    (y : RestrictedCompletion (t := t) Q W M) :
    Nat.card (RestrictedCompletion (t := t) Q W L) =
      Nat.card (RestrictedCompletion (t := t) Q W M) :=
  Nat.card_congr (restrictedCompletionEquiv x y)

end
end UniqueGamesTheorem.Inverse.KMSBasisComparisonPseudorandom

end

end OAI
