import OAI.NumberTheory.PiExponent.Cohomology.LocalIntersectionEulerFiltration
import OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionDimensionOne
import OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterKilledFiniteLength

namespace OAI

namespace PiExponentJets.W28.LocalIntersection

open scoped BigOperators Classical

variable {A : Type*} [CommRing A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]

theorem regular_cut_length_ne_top (x : A) (hx : x ∈ nonZeroDivisors A) (I : Ideal A) :
    Module.length A (A ⧸ (I ⊔ Ideal.span {x})) ≠ ⊤ := by
  rw [← cokernel_length_eq_cut]
  exact Module.length_ne_top_iff.mpr
    (W06.isFiniteLength_coker_parameter_mul (M := A ⧸ I) hx)

theorem regular_colon_length_ne_top (x : A) (hx : x ∈ nonZeroDivisors A) (I : Ideal A) :
    Module.length A ((I.colon {x}) ⧸ I.submoduleOf (I.colon {x})) ≠ ⊤ := by
  rw [← kernel_length_eq_colon]
  exact Module.length_ne_top_iff.mpr
    (W06.isFiniteLength_ker_parameter_mul (M := A ⧸ I) hx)

omit [IsNoetherianRing A] [Ring.KrullDimLE 1 A] in
theorem regular_colon_bot (x : A) (hx : x ∈ nonZeroDivisors A) :
    (⊥ : Ideal A).colon {x} = ⊥ := by
  ext a
  simp only [Submodule.mem_colon_singleton, smul_eq_mul, Submodule.mem_bot]
  exact mul_right_mem_nonZeroDivisors_eq_zero_iff hx

omit [IsNoetherianRing A] [Ring.KrullDimLE 1 A] in
theorem cutEuler_bot_regular (x : A) (hx : x ∈ nonZeroDivisors A) :
    cutEuler (⊥ : Ideal A) x =
      ((Module.length A (A ⧸ Ideal.span {x})).toNat : ℤ) := by
  have hz : Module.length A
      (((⊥ : Ideal A).colon {x}) ⧸ (⊥ : Ideal A).submoduleOf ((⊥ : Ideal A).colon {x})) = 0 := by
    rw [regular_colon_bot x hx]
    exact Module.length_eq_zero
  have hlen : Module.length A (A ⧸ ((⊥ : Ideal A) ⊔ Ideal.span {x})) =
      Module.length A (A ⧸ Ideal.span {x}) :=
    (Submodule.quotEquivOfEq _ _ (bot_sup_eq (Ideal.span {x}))).length_eq
  simp only [cutEuler, hz, ENat.toNat_zero, Nat.cast_zero, sub_zero]
  exact congrArg (fun n : ℕ∞ => (n.toNat : ℤ)) hlen

omit [IsNoetherianRing A] in
theorem cutEuler_prime_regular [IsLocalRing A]
    (x : A) (hx : x ∈ nonZeroDivisors A) (P : Ideal A) [P.IsPrime] :
    cutEuler P x = if P ∈ minimalPrimes A then
      ((Module.length A (A ⧸ (P ⊔ Ideal.span {x}))).toNat : ℤ) else 0 := by
  classical
  by_cases hp : P ∈ minimalPrimes A
  · have hz := prime_colon_length_zero P x (regular_not_mem_minimalPrime x hx P hp)
    simp [cutEuler, hp, hz]
  · rcases dimension_one_prime_factor_dichotomy x hx P with hmin | hmax
    · exact False.elim (hp hmin.1)
    · simp only [hp, ↓reduceIte, cutEuler, hmax.2, sub_self]

theorem exists_regular_onecut_sum_and_local_counts [IsLocalRing A]
    (x : A) (hx : x ∈ nonZeroDivisors A) :
    ∃ (n : ℕ) (J : ℕ → Ideal A) (f : ℕ → A),
      (∀ i < n, ((J i).colon {f i}).IsPrime) ∧
      (((Module.length A (A ⧸ Ideal.span {x})).toNat : ℤ) =
        ∑ i ∈ Finset.range n, if (J i).colon {f i} ∈ minimalPrimes A then
          ((Module.length A (A ⧸ ((J i).colon {f i} ⊔ Ideal.span {x}))).toNat : ℤ) else 0) ∧
      ∀ (P : Ideal A) [P.IsPrime], P ∈ minimalPrimes A →
        Module.length (Localization.AtPrime P)
          (Localization.AtPrime P ⧸ (⊥ : Ideal A).map
            (algebraMap A (Localization.AtPrime P))) =
          ∑ i ∈ Finset.range n, if (J i).colon {f i} = P then 1 else 0 := by
  classical
  obtain ⟨n, J, f, hm, h0, hn, hs, hcounts⟩ :=
    exists_cyclic_filtration_all_local_counts (A := A)
  refine ⟨n, J, f, (fun i hi => (hs i hi).1), ?_, hcounts⟩
  have he := cutEuler_filtration J f x n (fun i hi => (hs i hi).2)
    (regular_cut_length_ne_top x hx) (regular_colon_length_ne_top x hx)
  rw [h0, hn, cutEuler_top, add_zero, cutEuler_bot_regular x hx] at he
  refine he.trans (Finset.sum_congr rfl ?_)
  intro i hi
  let : ((J i).colon {f i}).IsPrime := (hs i (Finset.mem_range.mp hi)).1
  exact cutEuler_prime_regular x hx ((J i).colon {f i})

end PiExponentJets.W28.LocalIntersection

end OAI
