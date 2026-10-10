import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Localization.AtPrime.Basic

namespace OAI

/-!
# Affine maximal ideals, local rings, and multiplicity predicates
-/

section

/-!
# Affine polynomial multiplicity lower bounds
-/

namespace Nagata.AffineMultiplicity

variable {σ K : Type*} [CommRing K]

/-- The ideal of polynomials vanishing at an affine point. -/
noncomputable def pointIdeal (p : σ → K) : Ideal (MvPolynomial σ K) :=
  RingHom.ker (MvPolynomial.eval p)

/-- A polynomial vanishes to order at least `m` when it belongs to the
`m`th power of the point's evaluation ideal. -/
def orderAtLeast (p : σ → K) (m : ℕ) (f : MvPolynomial σ K) : Prop :=
  f ∈ pointIdeal p ^ m

theorem pointIdeal_mem_iff (p : σ → K) (f : MvPolynomial σ K) :
    f ∈ pointIdeal p ↔ MvPolynomial.eval p f = 0 := by
  exact RingHom.mem_ker

theorem coordinate_difference_mem (p : σ → K) (i : σ) :
    MvPolynomial.X i - MvPolynomial.C (p i) ∈ pointIdeal p := by
  rw [pointIdeal_mem_iff]
  simp

@[simp] theorem orderAtLeast_zero (p : σ → K) (f : MvPolynomial σ K) :
    orderAtLeast p 0 f := by
  simp [orderAtLeast]

@[simp] theorem zero_orderAtLeast (p : σ → K) (m : ℕ) :
    orderAtLeast p m 0 := (pointIdeal p ^ m).zero_mem

theorem orderAtLeast_one_iff (p : σ → K) (f : MvPolynomial σ K) :
    orderAtLeast p 1 f ↔ MvPolynomial.eval p f = 0 := by
  simp only [orderAtLeast, pow_one, pointIdeal_mem_iff]

theorem orderAtLeast_mono {p : σ → K} {m n : ℕ} {f : MvPolynomial σ K}
    (h : orderAtLeast p n f) (hmn : m ≤ n) : orderAtLeast p m f :=
  Ideal.pow_le_pow_right hmn h

theorem orderAtLeast_add {p : σ → K} {m : ℕ} {f g : MvPolynomial σ K}
    (hf : orderAtLeast p m f) (hg : orderAtLeast p m g) :
    orderAtLeast p m (f + g) := (pointIdeal p ^ m).add_mem hf hg

/-- Multiplication by a polynomial unit does not change the order condition. -/
theorem orderAtLeast_unit_mul_iff (p : σ → K) (m : ℕ)
    (u : (MvPolynomial σ K)ˣ) (f : MvPolynomial σ K) :
    orderAtLeast p m ((u : MvPolynomial σ K) * f) ↔ orderAtLeast p m f :=
  Ideal.unit_mul_mem_iff_mem (pointIdeal p ^ m) u.isUnit

/-- Multiplication adds lower bounds for affine vanishing order. -/
theorem orderAtLeast_mul {p : σ → K} {m n : ℕ} {f g : MvPolynomial σ K}
    (hf : orderAtLeast p m f) (hg : orderAtLeast p n g) :
    orderAtLeast p (m + n) (f * g) := by
  change f * g ∈ pointIdeal p ^ (m + n)
  rw [pow_add]
  exact Ideal.mul_mem_mul hf hg

/-- Taking a power scales every affine multiplicity lower bound. -/
theorem orderAtLeast_pow {p : σ → K} {m : ℕ} {f : MvPolynomial σ K}
    (hf : orderAtLeast p m f) (N : ℕ) : orderAtLeast p (m * N) (f ^ N) := by
  change f ^ N ∈ pointIdeal p ^ (m * N)
  rw [pow_mul]
  exact Ideal.pow_mem_pow hf N

/-- Product form used by the permutation reduction, with unequal bounds. -/
theorem orderAtLeast_prod {ι : Type*} (s : Finset ι) (p : σ → K)
    (m : ι → ℕ) (f : ι → MvPolynomial σ K)
    (h : ∀ i ∈ s, orderAtLeast p (m i) (f i)) :
    orderAtLeast p (∑ i ∈ s, m i) (∏ i ∈ s, f i) := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty => intro h; simp
  | @insert a s ha ih =>
      intro h
      simp only [Finset.sum_insert ha, Finset.prod_insert ha]
      exact orderAtLeast_mul (h a (Finset.mem_insert_self a s))
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- An isomorphism of polynomial coordinate rings carrying evaluation at `q`
to evaluation at `p` carries the actual point ideal to the actual point ideal. -/
theorem pointIdeal_map_of_eval_compatible {τ : Type*}
    (p : σ → K) (q : τ → K)
    (e : MvPolynomial σ K ≃+* MvPolynomial τ K)
    (h : ∀ f, MvPolynomial.eval q (e f) = MvPolynomial.eval p f) :
    Ideal.map e (pointIdeal p) = pointIdeal q := by
  ext g
  rw [Ideal.mem_map_of_equiv]
  constructor
  · rintro ⟨f, hf, rfl⟩
    rw [pointIdeal_mem_iff, h]
    exact (pointIdeal_mem_iff p f).mp hf
  · intro hg
    refine ⟨e.symm g, ?_, e.apply_symm_apply g⟩
    rw [pointIdeal_mem_iff, ← h, e.apply_symm_apply]
    exact (pointIdeal_mem_iff q g).mp hg

/-- Algebraic coordinate-ring isomorphisms preserve ideal-power multiplicity.
The compatibility hypothesis concerns evaluation, not any order bound. -/
theorem orderAtLeast_equiv_iff {τ : Type*}
    (p : σ → K) (q : τ → K)
    (e : MvPolynomial σ K ≃+* MvPolynomial τ K)
    (h : ∀ f, MvPolynomial.eval q (e f) = MvPolynomial.eval p f)
    (m : ℕ) (f : MvPolynomial σ K) :
    orderAtLeast q m (e f) ↔ orderAtLeast p m f := by
  unfold orderAtLeast
  rw [← pointIdeal_map_of_eval_compatible p q e h, ← Ideal.map_pow]
  exact Ideal.apply_mem_of_equiv_iff

section Field

variable {F : Type*} [Field F]

/-- Over a field, the ideal used by `orderAtLeast` really is maximal. -/
theorem pointIdeal_isMaximal (p : σ → F) : (pointIdeal p).IsMaximal := by
  apply RingHom.ker_isMaximal_of_surjective (MvPolynomial.eval p)
  intro a
  exact ⟨MvPolynomial.C a, MvPolynomial.eval_C a⟩

end Field

end Nagata.AffineMultiplicity

end

section

/-!
# Affine polynomial order and the actual local ring

The crucial contraction statement uses primary powers of a maximal ideal.
It is false for arbitrary powers of a prime ideal. All required maximality
hypotheses are proved for the evaluation ideals used here.
-/

namespace Nagata.AffineMultiplicity

section MaximalIdeal

variable {R : Type*} [CommRing R] (I : Ideal R) (hI : I.IsMaximal)

include hI

theorem maximalIdeal_power_radical {m : ℕ} (hm : m ≠ 0) :
    (I ^ m).radical = I := by
  rw [Ideal.radical_pow I hm, hI.isPrime.radical]

theorem maximalIdeal_power_isPrimary {m : ℕ} (hm : m ≠ 0) :
    (I ^ m).IsPrimary := by
  apply Ideal.isPrimary_of_isMaximal_radical
  rwa [maximalIdeal_power_radical I hI hm]

/-- Elements outside a maximal ideal cancel from membership in every power. -/
theorem maximalIdeal_power_mul_iff (m : ℕ) (f g : R) (hg : g ∉ I) :
    g * f ∈ I ^ m ↔ f ∈ I ^ m := by
  by_cases hm : m = 0
  · simp [hm]
  constructor
  · intro h
    have hfg : f * g ∈ I ^ m := by simpa only [mul_comm] using h
    rcases (Ideal.isPrimary_iff.mp (maximalIdeal_power_isPrimary I hI hm)).2 hfg
      with hf | hg'
    · exact hf
    · rw [maximalIdeal_power_radical I hI hm] at hg'
      exact (hg hg').elim
  · exact (I ^ m).mul_mem_left g

theorem maximalIdeal_power_comap_map
    [I.IsPrime] (S : Type*) [CommRing S] [Algebra R S]
    [IsLocalization.AtPrime S I] (m : ℕ) :
    Ideal.comap (algebraMap R S) (Ideal.map (algebraMap R S) (I ^ m)) = I ^ m := by
  by_cases hm : m = 0
  · simp [hm, Ideal.map_top]
  apply IsLocalization.under_map_of_isPrimary_disjoint I.primeCompl S
    (maximalIdeal_power_isPrimary I hI hm)
  apply Set.disjoint_left.mpr
  intro x hx hxm
  exact hx (Ideal.pow_le_self hm hxm)

/-- Affine maximal-ideal power membership equals membership after passing to
the actual local ring at that ideal. -/
theorem maximalIdeal_power_localization_iff
    [I.IsPrime] (S : Type*) [CommRing S] [Algebra R S]
    [IsLocalization.AtPrime S I] [IsLocalRing S] (m : ℕ) (f : R) :
    algebraMap R S f ∈ IsLocalRing.maximalIdeal S ^ m ↔ f ∈ I ^ m := by
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal I S, ← Ideal.map_pow]
  change f ∈ Ideal.comap (algebraMap R S) (Ideal.map (algebraMap R S) (I ^ m)) ↔ _
  rw [maximalIdeal_power_comap_map I hI S m]

end MaximalIdeal

section AffinePoint

variable {σ F : Type*} [Field F]

/-- Cancellation by an affine polynomial nonvanishing at the point. This
applies in particular to the denominators on projective chart overlaps. -/
theorem orderAtLeast_nonvanishing_mul_iff (p : σ → F) (m : ℕ)
    (f g : MvPolynomial σ F) (hg : MvPolynomial.eval p g ≠ 0) :
    orderAtLeast p m (g * f) ↔ orderAtLeast p m f := by
  apply maximalIdeal_power_mul_iff (pointIdeal p) (pointIdeal_isMaximal p)
  intro h
  exact hg ((pointIdeal_mem_iff p g).mp h)

instance pointIdeal_isPrime (p : σ → F) : (pointIdeal p).IsPrime :=
  (pointIdeal_isMaximal p).isPrime

/-- The genuine local ring of affine space at the indicated rational point. -/
abbrev PointLocalRing (p : σ → F) := Localization.AtPrime (pointIdeal p)

/-- Evaluation at the point extends to its actual local ring, because the
allowed denominators have nonzero values in the coefficient field. -/
noncomputable def residueEval (p : σ → F) : PointLocalRing p →+* F :=
  IsLocalization.lift (M := (pointIdeal p).primeCompl)
    (S := PointLocalRing p) (g := MvPolynomial.eval p) (fun s => by
      apply isUnit_iff_ne_zero.mpr
      intro hs
      exact s.property ((pointIdeal_mem_iff p s).mpr hs))

@[simp] theorem residueEval_algebraMap (p : σ → F) (f : MvPolynomial σ F) :
    residueEval p (algebraMap (MvPolynomial σ F) (PointLocalRing p) f) =
      MvPolynomial.eval p f := by
  exact IsLocalization.lift_eq _ f

theorem residueEval_surjective (p : σ → F) : Function.Surjective (residueEval p) := by
  intro a
  refine ⟨algebraMap (MvPolynomial σ F) (PointLocalRing p) (MvPolynomial.C a), ?_⟩
  simp

/-- The kernel of residue evaluation is the actual local maximal ideal. -/
theorem ker_residueEval (p : σ → F) :
    RingHom.ker (residueEval p) = IsLocalRing.maximalIdeal (PointLocalRing p) :=
  IsLocalRing.ker_eq_maximalIdeal (residueEval p) (residueEval_surjective p)

theorem residueEval_isUnit (p : σ → F) (x : PointLocalRing p) :
    IsUnit x ↔ residueEval p x ≠ 0 := by
  have h : residueEval p x = 0 ↔ ¬ IsUnit x := by
    rw [← RingHom.mem_ker, ker_residueEval, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff]
  simpa only [not_not] using (not_congr h).symm

/-- Multiplicity in the actual local ring uses its maximal ideal. -/
def localOrderAtLeast (p : σ → F) (m : ℕ) (f : MvPolynomial σ F) : Prop :=
  algebraMap (MvPolynomial σ F) (PointLocalRing p) f ∈
    IsLocalRing.maximalIdeal (PointLocalRing p) ^ m

/-- The affine ideal-power definition is faithfully identified with local
maximal-ideal power membership; no extra geometric assumption is used. -/
theorem localOrderAtLeast_iff (p : σ → F) (m : ℕ) (f : MvPolynomial σ F) :
    localOrderAtLeast p m f ↔ orderAtLeast p m f :=
  maximalIdeal_power_localization_iff (pointIdeal p) (pointIdeal_isMaximal p)
    (PointLocalRing p) m f

/-- A fraction with a denominator invertible at the point has the same
local order lower bounds as its numerator. -/
theorem local_fraction_order_iff (p : σ → F) (m : ℕ)
    (f : MvPolynomial σ F) (s : (pointIdeal p).primeCompl) :
    IsLocalization.mk' (PointLocalRing p) f s ∈
      IsLocalRing.maximalIdeal (PointLocalRing p) ^ m ↔ orderAtLeast p m f := by
  rw [IsLocalization.mk'_mem_iff]
  exact localOrderAtLeast_iff p m f

end AffinePoint

end Nagata.AffineMultiplicity

end

end OAI
