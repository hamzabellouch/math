import OAI.LinearAlgebra.CirculantHadamard.CyclicEvaluation
import OAI.LinearAlgebra.CirculantHadamard.CyclicPolynomial
import OAI.LinearAlgebra.CirculantHadamard.PrimeComponents
import OAI.LinearAlgebra.CirculantHadamard.CyclotomicRings
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Tactic.Linarith

namespace OAI

universe uR uS uT uA

/-!
# Actual prime-component character evaluations

The partial-evaluation homomorphism retains one cyclic coordinate and evaluates
the others. Its multiplication and subsequent evaluation laws follow from its
construction, rather than assumptions attached to the factors of a norm equation.
-/

noncomputable section

namespace CirculantHadamard.PrimeCharacterEvaluations

open scoped BigOperators
open CyclicRing

section WeightedProjection

variable {R : Type uR} {S : Type uS} {T : Type uT} [Semiring R] [CommSemiring S] [CommSemiring T]
variable {n m : ℕ}

/-- A character with values in the actual residual cyclic group algebra. -/
def weightedCharacter (f : ZMod n →+ ZMod m)
    (χ : Multiplicative (ZMod n) →* S) :
    Multiplicative (ZMod n) →* Elem S m where
  toFun g := AddMonoidAlgebra.single (f g.toAdd) (χ g)
  map_one' := by
    change AddMonoidAlgebra.single (f 0) (χ 1) = 1
    simp only [map_zero, map_one, AddMonoidAlgebra.one_def]
  map_mul' g h := by
    change AddMonoidAlgebra.single (f (g.toAdd + h.toAdd)) (χ (g * h)) = _
    simp only [map_add, map_mul, AddMonoidAlgebra.single_mul_single]

@[simp] theorem weightedCharacter_apply (f : ZMod n →+ ZMod m)
    (χ : Multiplicative (ZMod n) →* S) (g : ZMod n) :
    weightedCharacter f χ (Multiplicative.ofAdd g) =
      AddMonoidAlgebra.single (f g) (χ (Multiplicative.ofAdd g)) := rfl

/-- Coefficients are mapped by `φ`, the coordinate `f` is kept as a variable,
and all other character values become coefficients. -/
def weightedProjection (φ : R →+* S) (f : ZMod n →+ ZMod m)
    (χ : Multiplicative (ZMod n) →* S) : Elem R n →+* Elem S m :=
  evaluate (AddMonoidAlgebra.singleZeroRingHom.comp φ) (weightedCharacter f χ)

@[simp] theorem weightedProjection_single (φ : R →+* S)
    (f : ZMod n →+ ZMod m) (χ : Multiplicative (ZMod n) →* S)
    (g : ZMod n) (r : R) :
    weightedProjection φ f χ (AddMonoidAlgebra.single g r) =
      AddMonoidAlgebra.single (f g) (φ r * χ (Multiplicative.ofAdd g)) := by
  simp only [weightedProjection, evaluate_single, RingHom.comp_apply,
    AddMonoidAlgebra.singleZeroRingHom_apply, AddMonoidAlgebra.singleAddHom,
    weightedCharacter_apply,
    AddMonoidAlgebra.single_mul_single, zero_add]

@[simp] theorem weightedProjection_scalar (φ : R →+* S)
    (f : ZMod n →+ ZMod m) (χ : Multiplicative (ZMod n) →* S) (r : R) :
    weightedProjection φ f χ (scalar n r) = scalar m (φ r) := by
  rw [scalar, weightedProjection_single, map_zero]
  change AddMonoidAlgebra.single 0 (φ r * χ 1) = _
  simp only [map_one, mul_one, scalar]

private theorem toMultiplicative_apply (f : ZMod n →+ ZMod m) (a : ZMod n) :
    f.toMultiplicative (Multiplicative.ofAdd a) = Multiplicative.ofAdd (f a) := rfl

/-- Subsequent evaluation is exactly the product of the evaluated coefficients
and the character of the retained coordinate. -/
theorem evaluate_weightedProjection (φ : R →+* S) (ψ : S →+* T)
    (f : ZMod n →+ ZMod m) (χ : Multiplicative (ZMod n) →* S)
    (θ : Multiplicative (ZMod m) →* T) :
    (evaluate ψ θ).comp (weightedProjection φ f χ) =
      evaluate (ψ.comp φ)
        ((ψ.toMonoidHom.comp χ) * (θ.comp f.toMultiplicative)) := by
  apply AddMonoidAlgebra.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, weightedProjection_single, evaluate_single,
      map_zero, map_mul, MonoidHom.mul_apply, MonoidHom.comp_apply,
      toMultiplicative_apply, RingHom.toMonoidHom_eq_coe]
    simp
  · intro g
    simp only [RingHom.comp_apply, weightedProjection_single, evaluate_single,
      map_one, one_mul, MonoidHom.mul_apply, MonoidHom.comp_apply,
      toMultiplicative_apply, RingHom.toMonoidHom_eq_coe]
    rfl

/-- Norm preservation is a consequence of the constructed ring homomorphism.
In particular it does not require the residual group algebra to be a domain. -/
theorem weightedProjection_product (φ : R →+* S) (f : ZMod n →+ ZMod m)
    (χ : Multiplicative (ZMod n) →* S) (x y : Elem R n) (r : R)
    (hxy : x * y = scalar n r) :
    weightedProjection φ f χ x * weightedProjection φ f χ y = scalar m (φ r) := by
  rw [← map_mul, hxy, weightedProjection_scalar]

end WeightedProjection

open PrimeComponents CyclotomicRings

/-- The actual CRT coordinate, without a chosen-decomposition hypothesis. -/
def coordinate (u : ℕ) (hu : 0 < u) (p : PrimeIndex u) :
    ZMod (u ^ 2) →+ Component u p where
  toFun a := crt u hu a p
  map_zero' := by simp
  map_add' a b := by simp

@[simp] theorem coordinate_generator (u : ℕ) (hu : 0 < u) (p : PrimeIndex u) :
    coordinate u hu p (primaryGenerator u hu p) = 1 :=
  crt_primaryGenerator_same u hu p

@[simp] theorem coordinate_generator_ne (u : ℕ) (hu : 0 < u)
    (p q : PrimeIndex u) (h : q ≠ p) :
    coordinate u hu q (primaryGenerator u hu p) = 0 :=
  crt_primaryGenerator_ne u hu p q h

section RootCharacters
variable {A : Type uA} [CommMonoid A]

theorem root_order_pow (u : ℕ) (hu : 0 < u) (p : PrimeIndex u)
    (r : A) (hr : r ^ p.val = 1) : r ^ order u p.val = 1 := by
  obtain ⟨t, ht⟩ := prime_dvd_order hu p.property
  rw [ht, pow_mul, hr, one_pow]

def componentCharacter (u : ℕ) (hu : 0 < u) (p : PrimeIndex u)
    (r : A) (hr : r ^ p.val = 1) : Multiplicative (ZMod (u ^ 2)) →* A :=
  (CyclicPolynomial.powerCharacter (order u p.val) r (root_order_pow u hu p r hr)).comp
    (coordinate u hu p).toMultiplicative

@[simp] theorem componentCharacter_apply (u : ℕ) (hu : 0 < u) (p : PrimeIndex u)
    (r : A) (hr : r ^ p.val = 1) (a : ZMod (u ^ 2)) :
    componentCharacter u hu p r hr (Multiplicative.ofAdd a) =
      r ^ (coordinate u hu p a).val := rfl

@[simp] theorem componentCharacter_generator (u : ℕ) (hu : 0 < u)
    (p : PrimeIndex u) (r : A) (hr : r ^ p.val = 1) :
    componentCharacter u hu p r hr (Multiplicative.ofAdd (primaryGenerator u hu p)) = r := by
  change CyclicPolynomial.powerCharacter (order u p.val) r (root_order_pow u hu p r hr) (Multiplicative.ofAdd
    (coordinate u hu p (primaryGenerator u hu p))) = r
  rw [coordinate_generator, CyclicPolynomial.powerCharacter_generator]

@[simp] theorem componentCharacter_generator_ne (u : ℕ) (hu : 0 < u)
    (p q : PrimeIndex u) (h : q ≠ p) (r : A) (hr : r ^ q.val = 1) :
    componentCharacter u hu q r hr (Multiplicative.ofAdd (primaryGenerator u hu p)) = 1 := by
  rw [componentCharacter_apply, coordinate_generator_ne u hu p q h]
  simp

/-- A finite product of the actual primary-coordinate characters. -/
def rootsCharacter (u : ℕ) (hu : 0 < u) (r : PrimeIndex u → A)
    (hr : ∀ p, r p ^ p.val = 1) (S : Finset (PrimeIndex u)) :
    Multiplicative (ZMod (u ^ 2)) →* A :=
  ∏ p ∈ S, componentCharacter u hu p (r p) (hr p)

@[simp] theorem rootsCharacter_apply (u : ℕ) (hu : 0 < u) (r : PrimeIndex u → A)
    (hr : ∀ p, r p ^ p.val = 1) (S : Finset (PrimeIndex u)) (a : ZMod (u ^ 2)) :
    rootsCharacter u hu r hr S (Multiplicative.ofAdd a) =
      ∏ p ∈ S, r p ^ (coordinate u hu p a).val := by
  simp [rootsCharacter]

@[simp] theorem rootsCharacter_empty (u : ℕ) (hu : 0 < u) (r : PrimeIndex u → A)
    (hr : ∀ p, r p ^ p.val = 1) : rootsCharacter u hu r hr ∅ = 1 := by
  simp [rootsCharacter]

theorem rootsCharacter_generator (u : ℕ) (hu : 0 < u) (r : PrimeIndex u → A)
    (hr : ∀ p, r p ^ p.val = 1) (S : Finset (PrimeIndex u)) (p : PrimeIndex u) :
    rootsCharacter u hu r hr S (Multiplicative.ofAdd (primaryGenerator u hu p)) =
      if p ∈ S then r p else 1 := by
  classical
  simp only [rootsCharacter, MonoidHom.finsetProd_apply]
  have heq : ∀ q ∈ S, componentCharacter u hu q (r q) (hr q)
      (Multiplicative.ofAdd (primaryGenerator u hu p)) = if q = p then r p else 1 := by
    intro q _
    by_cases h : q = p
    · subst q
      simp only [componentCharacter_generator, ite_true]
    · simp [h, componentCharacter_generator_ne u hu p q h]
  rw [Finset.prod_congr rfl heq]
  simp

end RootCharacters

/-- The chosen primitive prime root in the literal global coefficient ring. -/
def rhoB (u : ℕ) (p : PrimeIndex u) : B u :=
  ⟨rho p.val, rho_mem_B u p.val p.property⟩

@[simp] theorem coe_rhoB (u : ℕ) (p : PrimeIndex u) :
    (rhoB u p : ℂ) = rho p.val := rfl

theorem rhoB_pow (u : ℕ) (p : PrimeIndex u) : rhoB u p ^ p.val = 1 :=
  Subtype.ext (rho_pow p.val (prime_of_mem p.property).ne_zero)

theorem rhoB_ne_one (u : ℕ) (p : PrimeIndex u) : rhoB u p ≠ 1 := by
  intro h
  exact (rho_isPrimitiveRoot p.val (prime_of_mem p.property).ne_zero).ne_one
    (prime_of_mem p.property).one_lt (congrArg Subtype.val h)

def subsetCharacter (u : ℕ) (hu : 0 < u) (S : Finset (PrimeIndex u)) :
    Multiplicative (ZMod (u ^ 2)) →* B u :=
  rootsCharacter u hu (rhoB u) (rhoB_pow u) S

@[simp] theorem subsetCharacter_empty (u : ℕ) (hu : 0 < u) :
    subsetCharacter u hu ∅ = 1 := rootsCharacter_empty _ _ _ _

theorem subsetCharacter_generator (u : ℕ) (hu : 0 < u)
    (S : Finset (PrimeIndex u)) (p : PrimeIndex u) :
    subsetCharacter u hu S (Multiplicative.ofAdd (primaryGenerator u hu p)) =
      if p ∈ S then rhoB u p else 1 := rootsCharacter_generator _ _ _ _ _ _

theorem subsetCharacter_nonempty (u : ℕ) (hu : 0 < u)
    (S : Finset (PrimeIndex u)) (hS : S.Nonempty) :
    ∃ a : ZMod (u ^ 2), subsetCharacter u hu S (Multiplicative.ofAdd a) ≠ 1 := by
  obtain ⟨p, hp⟩ := hS
  refine ⟨primaryGenerator u hu p, ?_⟩
  rw [subsetCharacter_generator, ite_eq_left hp]
  exact rhoB_ne_one u p

def subsetEvaluation (u : ℕ) (hu : 0 < u) (S : Finset (PrimeIndex u)) :
    Elem GaussianRing (u ^ 2) →+* B u :=
  evaluate (gaussianToB u).toRingHom (subsetCharacter u hu S)

/-- The omitted root is replaced by one; all remaining roots lie in the actual away ring. -/
def rhoAway (u : ℕ) (p q : PrimeIndex u) : awayRing u p.val := by
  classical
  exact if h : q = p then 1 else
    ⟨rho q.val, rho_mem_awayRing u p.val q.val q.property
      (fun he => h (Subtype.ext he))⟩

theorem rhoAway_pow (u : ℕ) (p q : PrimeIndex u) : rhoAway u p q ^ q.val = 1 := by
  classical
  by_cases h : q = p
  · simp [rhoAway, h]
  · apply Subtype.ext
    simpa [rhoAway, h] using rho_pow q.val (prime_of_mem q.property).ne_zero

def awayCharacter (u : ℕ) (hu : 0 < u) (p : PrimeIndex u)
    (S : Finset (PrimeIndex u)) : Multiplicative (ZMod (u ^ 2)) →* awayRing u p.val :=
  rootsCharacter u hu (rhoAway u p) (rhoAway_pow u p) (S.erase p)

/-- Leave precisely the full p-primary cyclic coordinate unevaluated. -/
def partialEvaluation (u : ℕ) (hu : 0 < u) (p : PrimeIndex u)
    (S : Finset (PrimeIndex u)) :
    Elem GaussianRing (u ^ 2) →+* Elem (awayRing u p.val) (order u p.val) :=
  weightedProjection (gaussianToAway u p.val).toRingHom (coordinate u hu p)
    (awayCharacter u hu p S)

theorem partialEvaluation_product (u : ℕ) (hu : 0 < u) (p : PrimeIndex u)
    (S : Finset (PrimeIndex u)) (x y : Elem GaussianRing (u ^ 2))
    (hxy : x * y = scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing)) :
    partialEvaluation u hu p S x * partialEvaluation u hu p S y =
      scalar (order u p.val) ((u ^ 2 : ℕ) : awayRing u p.val) := by
  unfold partialEvaluation
  simpa only [map_natCast] using weightedProjection_product
    (gaussianToAway u p.val).toRingHom (coordinate u hu p) (awayCharacter u hu p S)
    x y ((u ^ 2 : ℕ) : GaussianRing) hxy

theorem awayCharacter_map (u : ℕ) (hu : 0 < u) (p : PrimeIndex u)
    (S : Finset (PrimeIndex u)) :
    (awayInclusion u p.val).toMonoidHom.comp (awayCharacter u hu p S) =
      subsetCharacter u hu (S.erase p) := by
  classical
  apply MonoidHom.ext
  intro a
  change awayInclusion u p.val
    (rootsCharacter u hu (rhoAway u p) (rhoAway_pow u p) (S.erase p)
      (Multiplicative.ofAdd a.toAdd)) =
    rootsCharacter u hu (rhoB u) (rhoB_pow u) (S.erase p)
      (Multiplicative.ofAdd a.toAdd)
  simp only [rootsCharacter_apply, map_prod, map_pow]
  apply Finset.prod_congr rfl
  intro q hq
  have hqp := (Finset.mem_erase.mp hq).1
  congr 1
  apply Subtype.ext
  simp [rhoAway, hqp, rhoB]

theorem subsetCharacter_insert (u : ℕ) (hu : 0 < u) (p : PrimeIndex u)
    (S : Finset (PrimeIndex u)) :
    subsetCharacter u hu (insert p S) =
      subsetCharacter u hu (S.erase p) * componentCharacter u hu p (rhoB u p) (rhoB_pow u p) := by
  classical
  have hi : insert p (S.erase p) = insert p S := by
    ext q
    by_cases h : q = p <;> simp [h]
  calc
    subsetCharacter u hu (insert p S) = subsetCharacter u hu (insert p (S.erase p)) :=
      congrArg (subsetCharacter u hu) hi.symm
    _ = _ := by
      simp only [subsetCharacter, rootsCharacter, Finset.prod_insert (Finset.notMem_erase p S),
        mul_comm]

/-- Evaluate the remaining p-primary variable at one. -/
def partialAtOne (u : ℕ) (p : PrimeIndex u) :
    Elem (awayRing u p.val) (order u p.val) →+* B u :=
  evaluate (awayInclusion u p.val).toRingHom 1

/-- Evaluate the remaining full p-primary variable at the selected pth root. -/
def partialAtRoot (u : ℕ) (hu : 0 < u) (p : PrimeIndex u) :
    Elem (awayRing u p.val) (order u p.val) →+* B u :=
  evaluate (awayInclusion u p.val).toRingHom
    (CyclicPolynomial.powerCharacter (order u p.val) (rhoB u p)
      (root_order_pow u hu p (rhoB u p) (rhoB_pow u p)))

private theorem gaussian_away_comp (u p : ℕ) :
    (awayInclusion u p).toRingHom.comp (gaussianToAway u p).toRingHom =
      (gaussianToB u).toRingHom := by
  apply RingHom.ext
  intro r
  apply Subtype.ext
  exact (coe_awayInclusion u p (gaussianToAway u p r)).trans
    ((coe_gaussianToAway u p r).trans (coe_gaussianToB u r).symm)

theorem partialEvaluation_at_one (u : ℕ) (hu : 0 < u) (p : PrimeIndex u)
    (S : Finset (PrimeIndex u)) :
    (partialAtOne u p).comp (partialEvaluation u hu p S) =
      subsetEvaluation u hu (S.erase p) := by
  unfold partialAtOne partialEvaluation
  rw [evaluate_weightedProjection]
  rw [gaussian_away_comp]
  have ht : (1 : Multiplicative (Component u p) →* B u).comp
      (coordinate u hu p).toMultiplicative = 1 := by ext; rfl
  rw [ht, mul_one]
  exact congrArg (evaluate (gaussianToB u).toRingHom) (awayCharacter_map u hu p S)

theorem partialEvaluation_at_root (u : ℕ) (hu : 0 < u) (p : PrimeIndex u)
    (S : Finset (PrimeIndex u)) :
    (partialAtRoot u hu p).comp (partialEvaluation u hu p S) =
      subsetEvaluation u hu (insert p S) := by
  unfold partialAtRoot partialEvaluation
  rw [evaluate_weightedProjection]
  rw [gaussian_away_comp]
  change evaluate (gaussianToB u).toRingHom
    (((awayInclusion u p.val).toMonoidHom.comp (awayCharacter u hu p S)) *
      componentCharacter u hu p (rhoB u p) (rhoB_pow u p)) = _
  rw [awayCharacter_map, ← subsetCharacter_insert]
  rfl

@[simp] theorem partialEvaluation_at_one_apply (u : ℕ) (hu : 0 < u) (p : PrimeIndex u)
    (S : Finset (PrimeIndex u)) (hp : p ∉ S) (x : Elem GaussianRing (u ^ 2)) :
    partialAtOne u p (partialEvaluation u hu p S x) = subsetEvaluation u hu S x := by
  have h := congrArg (fun f : Elem GaussianRing (u ^ 2) →+* B u => f x)
    (partialEvaluation_at_one u hu p S)
  simpa only [RingHom.comp_apply, Finset.erase_eq_of_notMem hp] using h

@[simp] theorem partialEvaluation_at_root_apply (u : ℕ) (hu : 0 < u) (p : PrimeIndex u)
    (S : Finset (PrimeIndex u)) (x : Elem GaussianRing (u ^ 2)) :
    partialAtRoot u hu p (partialEvaluation u hu p S x) =
      subsetEvaluation u hu (insert p S) x :=
  congrArg (fun f : Elem GaussianRing (u ^ 2) →+* B u => f x)
    (partialEvaluation_at_root u hu p S)

theorem rhoB_mul_star (u : ℕ) (p : PrimeIndex u) : rhoB u p * star (rhoB u p) = 1 :=
  Subtype.ext (rho_mul_star p.val)

theorem subsetCharacter_mul_star (u : ℕ) (hu : 0 < u)
    (S : Finset (PrimeIndex u)) (a : ZMod (u ^ 2)) :
    subsetCharacter u hu S (Multiplicative.ofAdd a) *
      star (subsetCharacter u hu S (Multiplicative.ofAdd a)) = 1 := by
  unfold subsetCharacter
  rw [rootsCharacter_apply, star_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro p _
  rw [star_pow, ← mul_pow, rhoB_mul_star, one_pow]

theorem subsetCharacter_neg (u : ℕ) (hu : 0 < u)
    (S : Finset (PrimeIndex u)) (a : ZMod (u ^ 2)) :
    subsetCharacter u hu S (Multiplicative.ofAdd (-a)) =
      star (subsetCharacter u hu S (Multiplicative.ofAdd a)) := by
  let χ := subsetCharacter u hu S
  have hi : χ (Multiplicative.ofAdd (-a)) * χ (Multiplicative.ofAdd a) = 1 := by
    rw [← map_mul]
    change χ (Multiplicative.ofAdd (-a + a)) = 1
    simp
  have hs := subsetCharacter_mul_star u hu S a
  change χ (Multiplicative.ofAdd a) * star (χ (Multiplicative.ofAdd a)) = 1 at hs
  calc
    χ (Multiplicative.ofAdd (-a)) = χ (Multiplicative.ofAdd (-a)) * 1 := (mul_one _).symm
    _ = χ (Multiplicative.ofAdd (-a)) *
        (χ (Multiplicative.ofAdd a) * star (χ (Multiplicative.ofAdd a))) := by rw [hs]
    _ = star (χ (Multiplicative.ofAdd a)) := by rw [← mul_assoc, hi, one_mul]

theorem subsetEvaluation_star (u : ℕ) [NeZero (u ^ 2)] (hu : 0 < u)
    (S : Finset (PrimeIndex u)) (x : Elem GaussianRing (u ^ 2)) :
    subsetEvaluation u hu S (ringStar x) = star (subsetEvaluation u hu S x) := by
  exact evaluate_ringStar (gaussianToB u).toRingHom (subsetCharacter u hu S)
    (gaussianToB_star u) (subsetCharacter_neg u hu S) x

theorem subsetEvaluation_norm (u : ℕ) [NeZero (u ^ 2)] (hu : 0 < u)
    (S : Finset (PrimeIndex u)) (x : Elem GaussianRing (u ^ 2))
    (hx : x * ringStar x = scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing)) :
    subsetEvaluation u hu S x * star (subsetEvaluation u hu S x) = ((u ^ 2 : ℕ) : B u) := by
  simpa only [subsetEvaluation, map_natCast] using evaluate_norm_eq
    (gaussianToB u).toRingHom (subsetCharacter u hu S)
    (gaussianToB_star u) (subsetCharacter_neg u hu S) x ((u ^ 2 : ℕ) : GaussianRing) hx

theorem subsetEvaluation_ne_zero (u : ℕ) [NeZero (u ^ 2)] (hu : 0 < u)
    (S : Finset (PrimeIndex u)) (x : Elem GaussianRing (u ^ 2))
    (hx : x * ringStar x = scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing)) :
    subsetEvaluation u hu S x ≠ 0 := by
  intro h
  have hn := subsetEvaluation_norm u hu S x hx
  rw [h, zero_mul] at hn
  exact (Nat.cast_ne_zero.mpr (pow_ne_zero 2 hu.ne')) hn.symm

/-- Every complex embedding has the required norm. Compatibility with conjugation
is derived from the actual adjoined roots in `map_star_B`. -/
theorem subsetEvaluation_map_norm (u : ℕ) [NeZero (u ^ 2)] (hu : 0 < u)
    (S : Finset (PrimeIndex u)) (x : Elem GaussianRing (u ^ 2))
    (hx : x * ringStar x = scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing))
    (σ : B u →+* ℂ) : ‖σ (subsetEvaluation u hu S x)‖ = (u : ℝ) := by
  have hn := congrArg (fun z : B u => ‖σ z‖) (subsetEvaluation_norm u hu S x hx)
  simp only [map_mul, map_star_B, norm_mul, norm_star, map_natCast] at hn
  rw [RCLike.norm_natCast, Nat.cast_pow] at hn
  nlinarith [norm_nonneg (σ (subsetEvaluation u hu S x)), (show (0 : ℝ) ≤ (u : ℝ) from Nat.cast_nonneg u)]

end CirculantHadamard.PrimeCharacterEvaluations

end

end OAI
