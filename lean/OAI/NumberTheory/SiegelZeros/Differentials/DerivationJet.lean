import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Structure.RectangleThreshold

namespace OAI

namespace SiegelZeros

open scoped BigOperators
open scoped BigOperators
namespace WeightedTorusJets.Geometry

theorem mixed_iterate_add {A : Type*} (D : Fin 3 → A → A)
    (h01 : Function.Commute (D 0) (D 1))
    (h02 : Function.Commute (D 0) (D 2))
    (h12 : Function.Commute (D 1) (D 2))
    (a b : Fin 3 → ℕ) (x : A) :
    (D 0)^[a 0 + b 0] ((D 1)^[a 1 + b 1] ((D 2)^[a 2 + b 2] x)) =
      (D 0)^[a 0] ((D 1)^[a 1] ((D 2)^[a 2]
        ((D 0)^[b 0] ((D 1)^[b 1] ((D 2)^[b 2] x))))) := by
  simp only [Function.iterate_add_apply]
  rw [(h01.iterate_iterate (b 0) (a 1)).eq,
    (h12.iterate_iterate (b 1) (a 2)).eq,
    (h02.iterate_iterate (b 0) (a 2)).eq]

theorem mixed_derivation_pow_add {R A : Type*} [CommSemiring R] [CommSemiring A]
    [Algebra R A] (D : Fin 3 → Derivation R A A)
    (h01 : Function.Commute (D 0) (D 1))
    (h02 : Function.Commute (D 0) (D 2))
    (h12 : Function.Commute (D 1) (D 2))
    (a b : Fin 3 → ℕ) (x : A) :
    ((D 0).toLinearMap ^ (a 0 + b 0))
      (((D 1).toLinearMap ^ (a 1 + b 1)) (((D 2).toLinearMap ^ (a 2 + b 2)) x)) =
      ((D 0).toLinearMap ^ a 0) (((D 1).toLinearMap ^ a 1) (((D 2).toLinearMap ^ a 2)
        (((D 0).toLinearMap ^ b 0) (((D 1).toLinearMap ^ b 1)
          (((D 2).toLinearMap ^ b 2) x))))) := by
  simpa only [Module.End.pow_apply, Derivation.coeFn_coe] using mixed_iterate_add
    (fun i => (D i : A → A)) h01 h02 h12 a b x

theorem derivation_pow_mixed_derivation_pow {R A : Type*}
    [CommSemiring R] [CommSemiring A] [Algebra R A]
    (D : Fin 3 → Derivation R A A)
    (h01 : Function.Commute (D 0) (D 1))
    (h02 : Function.Commute (D 0) (D 2))
    (h12 : Function.Commute (D 1) (D 2))
    (j : Fin 3) (n : ℕ) (b : Fin 3 → ℕ) (x : A) :
    ((D j).toLinearMap ^ n)
      (((D 0).toLinearMap ^ b 0) (((D 1).toLinearMap ^ b 1)
        (((D 2).toLinearMap ^ b 2) x))) =
    ((D 0).toLinearMap ^ ((b + (Pi.single j n : Fin 3 → ℕ)) 0))
      (((D 1).toLinearMap ^ ((b + (Pi.single j n : Fin 3 → ℕ)) 1))
        (((D 2).toLinearMap ^ ((b + (Pi.single j n : Fin 3 → ℕ)) 2)) x)) := by
  have h := mixed_derivation_pow_add D h01 h02 h12 (Pi.single j n) b x
  fin_cases j <;> simpa [Pi.single_apply, add_comm] using h.symm

end WeightedTorusJets.Geometry

open scoped BigOperators

namespace WeightedTorusJets.Geometry

lemma extend_selectedIndex_eq_zero (I : Finset (Fin 3)) (α : I → ℕ) {j : Fin 3}
    (hj : j ∉ I) : Function.extend (Subtype.val : I → Fin 3) α 0 j = 0 := by
  apply Function.extend_apply'
  rintro ⟨i, rfl⟩
  exact hj i.property

lemma extend_selectedIndex_le (I : Finset (Fin 3)) (α : I → ℕ) (t : Fin 3 → ℕ)
    (hα : ∀ i, α i ≤ t i) :
    ∀ j, Function.extend (Subtype.val : I → Fin 3) α 0 j ≤ t j := by
  intro j
  by_cases hj : j ∈ I
  · rw [Subtype.val_injective.extend_apply α 0 ⟨j, hj⟩]
    exact hα ⟨j, hj⟩
  · rw [extend_selectedIndex_eq_zero I α hj]
    exact Nat.zero_le _

lemma extend_selectedIndex_single (I : Finset (Fin 3)) (i : I) (n : ℕ) :
    Function.extend (Subtype.val : I → Fin 3) (Pi.single i n) 0 = Pi.single (i : Fin 3) n := by
  funext j
  by_cases hj : j ∈ I
  · rw [Subtype.val_injective.extend_apply (Pi.single i n) 0 ⟨j, hj⟩]
    simp only [Pi.single_apply, Subtype.ext_iff]
  · rw [extend_selectedIndex_eq_zero I _ hj]
    have hne : j ≠ (i : Fin 3) := by
      intro he
      exact hj (he.symm ▸ i.property)
    rw [Pi.single_eq_of_ne hne]

theorem add_jet_indices_le_next_stage {σ : Type*} (a α t : σ → ℕ) (b : ℕ)
    (ha : ∀ j, a j ≤ b * t j) (hα : ∀ j, α j ≤ t j) :
    ∀ j, (a + α) j ≤ (b + 1) * t j := by
  intro j
  simpa [Pi.add_apply, Nat.add_mul] using Nat.add_le_add (ha j) (hα j)

theorem selectedIndex_add_stage_bound (I : Finset (Fin 3)) (α : I → ℕ)
    (a t : Fin 3 → ℕ) (b : ℕ) (ha : ∀ j, a j ≤ b * t j) (hα : ∀ i, α i ≤ t i) :
    ∀ j, (a + Function.extend (Subtype.val : I → Fin 3) α 0) j ≤ (b + 1) * t j :=
  add_jet_indices_le_next_stage a _ t b ha (extend_selectedIndex_le I α t hα)

theorem selectedIndex_add_stage_bound_lt (I : Finset (Fin 3)) (α : I → ℕ)
    (a t : Fin 3 → ℕ) (b : ℕ) (ha : ∀ j, a j ≤ b * t j)
    (hα : ∀ i, α i < t i + 1) :
    ∀ j, (a + Function.extend (Subtype.val : I → Fin 3) α 0) j ≤ (b + 1) * t j :=
  selectedIndex_add_stage_bound I α a t b ha fun i ↦ Nat.lt_succ_iff.mp (hα i)



noncomputable section

variable {A B : Type*} [CommRing A] [Algebra ℚ A] [CommRing B] [Algebra ℚ B]

def derivationJet (D : Fin 3 → Derivation ℚ A A) (β : Fin 3 → ℕ) (a : A) : A :=
  ((D 0).toLinearMap ^ β 0) (((D 1).toLinearMap ^ β 1) (((D 2).toLinearMap ^ β 2) a))

def derivativeStageIdeal (D : Fin 3 → Derivation ℚ A A) (t : Fin 3 → ℕ)
    (b : ℕ) (F : A) : Ideal A :=
  Ideal.span ((fun β => derivationJet D β F) '' {β | ∀ j, β j ≤ b * t j})

@[simp] theorem derivationJet_zero (D : Fin 3 → Derivation ℚ A A) (a : A) :
    derivationJet D 0 a = a := by
  simp [derivationJet]

omit [Algebra ℚ B] in
theorem derivativeStageIdeal_le_ker_iff (D : Fin 3 → Derivation ℚ A A)
    (t : Fin 3 → ℕ) (b : ℕ) (F : A) (f : A →+* B) :
    derivativeStageIdeal D t b F ≤ RingHom.ker f ↔
      ∀ β, (∀ j, β j ≤ b * t j) → f (derivationJet D β F) = 0 := by
  rw [derivativeStageIdeal, Ideal.span_le, Set.image_subset_iff]
  rfl

theorem derivationJet_map (D : Fin 3 → Derivation ℚ A A)
    (E : Fin 3 → Derivation ℚ B B) (f : A →+* B)
    (h : ∀ i a, f (D i a) = E i (f a)) (β : Fin 3 → ℕ) (a : A) :
    f (derivationJet D β a) = derivationJet E β (f a) := by
  have hp (i : Fin 3) (n : ℕ) (x : A) :
      f (((D i).toLinearMap ^ n) x) = ((E i).toLinearMap ^ n) (f x) := by
    induction n with
    | zero => rfl
    | succ n ih =>
        simp only [pow_succ', Module.End.mul_apply, Derivation.coeFn_coe, h, ih]
  simp only [derivationJet, hp]

theorem derivativeStageIdeal_map (D : Fin 3 → Derivation ℚ A A)
    (E : Fin 3 → Derivation ℚ B B) (f : A →+* B)
    (h : ∀ i a, f (D i a) = E i (f a)) (t : Fin 3 → ℕ) (b : ℕ) (F : A) :
    Ideal.map f (derivativeStageIdeal D t b F) = derivativeStageIdeal E t b (f F) := by
  unfold derivativeStageIdeal
  rw [Ideal.map_span, Set.image_image]
  simp only [derivationJet_map D E f h]

theorem derivationJet_shift (D : Fin 3 → Derivation ℚ A A)
    (h01 : Function.Commute (D 0) (D 1))
    (h02 : Function.Commute (D 0) (D 2))
    (h12 : Function.Commute (D 1) (D 2))
    (j : Fin 3) (n : ℕ) (β : Fin 3 → ℕ) (a : A) :
    ((D j).toLinearMap ^ n) (derivationJet D β a) =
      derivationJet D (β + Pi.single j n) a :=
  derivation_pow_mixed_derivation_pow D h01 h02 h12 j n β a

theorem single_index_le {j : Fin 3} {n : ℕ} (t : Fin 3 → ℕ) (hn : n ≤ t j) :
    ∀ l, (Pi.single j n : Fin 3 → ℕ) l ≤ t l := by
  intro l
  by_cases h : l = j
  · simpa [h] using hn
  · simp [Pi.single_eq_of_ne h]

theorem pair_index_le {i j : Fin 3} (hij : i ≠ j) {m n : ℕ} (t : Fin 3 → ℕ)
    (hm : m ≤ t i) (hn : n ≤ t j) :
    ∀ l, ((Pi.single i m : Fin 3 → ℕ) + (Pi.single j n : Fin 3 → ℕ)) l ≤ t l := by
  intro l
  by_cases hi : l = i
  · subst l
    simpa [Pi.single_apply, hij] using hm
  · by_cases hj : l = j
    · subst l
      simpa [Pi.single_apply, Ne.symm hij] using hn
    · simp [hi, hj]

theorem triple_index_le {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {m n p : ℕ} (t : Fin 3 → ℕ) (hm : m ≤ t i) (hn : n ≤ t j) (hp : p ≤ t k) :
    ∀ l, (((Pi.single i m : Fin 3 → ℕ) + (Pi.single j n : Fin 3 → ℕ)) +
      (Pi.single k p : Fin 3 → ℕ)) l ≤ t l := by
  intro l
  by_cases hi : l = i
  · subst l
    simpa [Pi.single_apply, hij, hik] using hm
  · by_cases hj : l = j
    · subst l
      simpa [Pi.single_apply, Ne.symm hij, hjk] using hn
    · by_cases hk : l = k
      · subst l
        simpa [Pi.single_apply, Ne.symm hik, Ne.symm hjk] using hp
      · simp [hi, hj, hk]

theorem derivativeStageIdeal_le_ker_taylor_one
    (D : Fin 3 → Derivation ℚ A A)
    (h01 : Function.Commute (D 0) (D 1))
    (h02 : Function.Commute (D 0) (D 2))
    (h12 : Function.Commute (D 1) (D 2))
    (I : Finset (Fin 3)) (i : I) (t : Fin 3 → ℕ) (b : ℕ) (F : A) (f : A →+* B)
    (hvanish : ∀ β, (∀ j, β j ≤ (b + 1) * t j) → f (derivationJet D β F) = 0) :
    derivativeStageIdeal D t b F ≤ RingHom.ker
      (rectangularTaylorThree I (fun j => t j + 1) (D i) 0 0 i i i f) := by
  apply Ideal.span_le.mpr
  rintro _ ⟨β, hβ, rfl⟩
  change rectangularTaylorThree _ _ _ _ _ _ _ _ _ _ = 0
  rw [rectangularTaylorThree_one_apply]
  apply Finset.sum_eq_zero
  intro n hn
  have hbound := add_jet_indices_le_next_stage β (Pi.single (i : Fin 3) n) t b hβ
    (single_index_le t (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)))
  rw [derivationJet_shift D h01 h02 h12, hvanish _ hbound]
  simp

theorem derivativeStageIdeal_le_ker_taylor_two
    (D : Fin 3 → Derivation ℚ A A)
    (h01 : Function.Commute (D 0) (D 1))
    (h02 : Function.Commute (D 0) (D 2))
    (h12 : Function.Commute (D 1) (D 2))
    (I : Finset (Fin 3)) (i j : I) (hij : i ≠ j)
    (t : Fin 3 → ℕ) (b : ℕ) (F : A) (f : A →+* B)
    (hvanish : ∀ β, (∀ l, β l ≤ (b + 1) * t l) → f (derivationJet D β F) = 0) :
    derivativeStageIdeal D t b F ≤ RingHom.ker
      (rectangularTaylorThree I (fun l => t l + 1) (D i) (D j) 0 i j j f) := by
  apply Ideal.span_le.mpr
  rintro _ ⟨β, hβ, rfl⟩
  change rectangularTaylorThree _ _ _ _ _ _ _ _ _ _ = 0
  rw [rectangularTaylorThree_two_apply]
  apply Finset.sum_eq_zero
  intro n hn
  apply Finset.sum_eq_zero
  intro m hm
  have hji : (j : Fin 3) ≠ (i : Fin 3) := fun he => hij (Subtype.ext he.symm)
  have hbound := add_jet_indices_le_next_stage β
    ((Pi.single (j : Fin 3) n : Fin 3 → ℕ) + (Pi.single (i : Fin 3) m : Fin 3 → ℕ)) t b hβ
    (pair_index_le hji t (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)))
  rw [derivationJet_shift D h01 h02 h12, derivationJet_shift D h01 h02 h12]
  rw [add_assoc, hvanish _ hbound]
  simp

theorem derivativeStageIdeal_le_ker_taylor_three
    (D : Fin 3 → Derivation ℚ A A)
    (h01 : Function.Commute (D 0) (D 1))
    (h02 : Function.Commute (D 0) (D 2))
    (h12 : Function.Commute (D 1) (D 2))
    (I : Finset (Fin 3)) (i j k : I) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (t : Fin 3 → ℕ) (b : ℕ) (F : A) (f : A →+* B)
    (hvanish : ∀ β, (∀ l, β l ≤ (b + 1) * t l) → f (derivationJet D β F) = 0) :
    derivativeStageIdeal D t b F ≤ RingHom.ker
      (rectangularTaylorThree I (fun l => t l + 1) (D i) (D j) (D k) i j k f) := by
  apply Ideal.span_le.mpr
  rintro _ ⟨β, hβ, rfl⟩
  change rectangularTaylorThree _ _ _ _ _ _ _ _ _ _ = 0
  rw [rectangularTaylorThree_apply]
  apply Finset.sum_eq_zero
  intro p hp
  apply Finset.sum_eq_zero
  intro n hn
  apply Finset.sum_eq_zero
  intro m hm
  have hkj : (k : Fin 3) ≠ (j : Fin 3) := fun he => hjk (Subtype.ext he.symm)
  have hki : (k : Fin 3) ≠ (i : Fin 3) := fun he => hik (Subtype.ext he.symm)
  have hji : (j : Fin 3) ≠ (i : Fin 3) := fun he => hij (Subtype.ext he.symm)
  have hbound := add_jet_indices_le_next_stage β
    (((Pi.single (k : Fin 3) p : Fin 3 → ℕ) + (Pi.single (j : Fin 3) n : Fin 3 → ℕ)) +
      (Pi.single (i : Fin 3) m : Fin 3 → ℕ)) t b hβ
    (triple_index_le hkj hki hji t (Nat.lt_succ_iff.mp (Finset.mem_range.mp hp))
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)))
  rw [derivationJet_shift D h01 h02 h12, derivationJet_shift D h01 h02 h12,
    derivationJet_shift D h01 h02 h12]
  simp only [add_assoc] at hbound
  rw [add_assoc, add_assoc, hvanish _ hbound]
  simp

end

end WeightedTorusJets.Geometry

noncomputable section

namespace WeightedTorusJets.Geometry

theorem local_module_length_eq_finrank {K A M : Type*} [Field K] [CommRing A]
    [IsLocalRing A] [Algebra K A] [AddCommGroup M] [Module K M] [Module A M]
    [IsScalarTower K A M] [Module.Finite K M]
    (hκ : Function.Surjective (algebraMap K (IsLocalRing.ResidueField A))) :
    Module.length A M = Module.finrank K M := by
  have hres : Module.length (IsLocalRing.ResidueField K) (IsLocalRing.ResidueField A) = 1 := by
    rw [← Module.length_eq_of_surjective (M := IsLocalRing.ResidueField A)
      (IsLocalRing.residue_surjective (R := K))]
    rw [Module.length_eq_of_surjective (M := IsLocalRing.ResidueField A) hκ]
    exact Module.length_eq_one _ _
  have h := IsLocalRing.length_restrictScalars K A M
  rw [hres, mul_one, Module.length_eq_finrank K M] at h
  exact h.symm

theorem local_length_eq_finrank {K A : Type*} [Field K] [CommRing A] [IsLocalRing A]
    [Algebra K A] [Module.Finite K A]
    (hκ : Function.Surjective (algebraMap K (IsLocalRing.ResidueField A))) :
    Module.length A A = Module.finrank K A :=
  local_module_length_eq_finrank hκ

theorem isNilpotent_of_mem_nilpotent_ideal {A : Type*} [CommRing A]
    (I : Ideal A) (hI : IsNilpotent I) {a : A} (ha : a ∈ I) : IsNilpotent a := by
  obtain ⟨n, hn⟩ := hI
  refine ⟨n, ?_⟩
  have h := Ideal.pow_mem_pow ha n
  rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at h
  exact h

theorem isLocalRing_of_nilpotent_augmentation {K A : Type*} [Field K] [CommRing A]
    [Algebra K A] (ε : A →ₐ[K] K) (hε : IsNilpotent (RingHom.ker ε)) :
    IsLocalRing A := by
  have : Nontrivial A := ε.toRingHom.domain_nontrivial
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro a
  by_cases ha : ε a = 0
  · exact Or.inr (isNilpotent_of_mem_nilpotent_ideal _ hε ha).isUnit_one_sub
  · apply Or.inl
    have hn : IsNilpotent (a - algebraMap K A (ε a)) :=
      isNilpotent_of_mem_nilpotent_ideal _ hε (by simp)
    simpa using hn.isUnit_add_left_of_commute
      ((isUnit_iff_ne_zero.mpr ha).map (algebraMap K A)) (Commute.all _ _)

theorem residue_surjective_of_nilpotent_augmentation {K A : Type*} [Field K]
    [CommRing A] [Algebra K A] [IsLocalRing A] (ε : A →ₐ[K] K)
    (hε : IsNilpotent (RingHom.ker ε)) :
    Function.Surjective (algebraMap K (IsLocalRing.ResidueField A)) := by
  intro b
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective b
  refine ⟨ε a, ?_⟩
  have hn : IsNilpotent (a - algebraMap K A (ε a)) :=
    isNilpotent_of_mem_nilpotent_ideal _ hε (by simp)
  have hm : a - algebraMap K A (ε a) ∈ IsLocalRing.maximalIdeal A := hn.not_isUnit
  have he := (IsLocalRing.residue_eq_zero_iff _).mpr hm
  rw [map_sub, sub_eq_zero] at he
  exact he.symm

theorem length_eq_finrank_of_nilpotent_augmentation {K A : Type*} [Field K]
    [CommRing A] [Algebra K A] [Module.Finite K A] (ε : A →ₐ[K] K)
    (hε : IsNilpotent (RingHom.ker ε)) :
    Module.length A A = Module.finrank K A := by
  let := isLocalRing_of_nilpotent_augmentation ε hε
  exact local_length_eq_finrank (residue_surjective_of_nilpotent_augmentation ε hε)

open MvPolynomial

instance finite_rectangularQuotient {σ K : Type*} [Fintype σ] [CommRing K] (k : σ → ℕ) :
    Module.Finite K (MvPolynomial σ K ⧸ rectangularIdeal k) :=
  Module.Finite.of_basis (rectangularQuotientBasis k)

open MvPolynomial

theorem ker_constantCoeff_eq_idealOfVars {σ K : Type*} [CommRing K] :
    RingHom.ker (constantCoeff : MvPolynomial σ K →+* K) = idealOfVars σ K := by
  classical
  ext p
  rw [RingHom.mem_ker, idealOfVars, ← Set.image_univ,
    mem_ideal_span_X_image]
  constructor
  · intro hp d hd
    have hd0 : d ≠ 0 := by
      intro h
      subst d
      exact (mem_support_iff.mp hd) hp
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hd0
    exact ⟨i, Set.mem_univ i, hi⟩
  · intro hp
    by_contra h
    obtain ⟨i, _, hi⟩ := hp 0 (mem_support_iff.mpr h)
    exact hi rfl

theorem isNilpotent_map_idealOfVars_of_pow_mem
    {σ K : Type*} [Finite σ] [CommRing K]
    (J : Ideal (MvPolynomial σ K)) (k : σ → ℕ)
    (hk : ∀ i, (X i : MvPolynomial σ K) ^ k i ∈ J) :
    IsNilpotent ((idealOfVars σ K).map (Ideal.Quotient.mk J)) := by
  apply ((idealOfVars_fg σ K).map (Ideal.Quotient.mk J)).isNilpotent_iff_le_nilradical.mpr
  rw [Ideal.map_le_iff_le_comap, idealOfVars, Ideal.span_le, Set.range_subset_iff]
  intro i
  change IsNilpotent (Ideal.Quotient.mk J (X i))
  refine ⟨k i, ?_⟩
  rw [← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (hk i)

def quotientAugmentation {σ K : Type*} [CommRing K]
    (J : Ideal (MvPolynomial σ K))
    (hJ : J ≤ RingHom.ker (constantCoeff : MvPolynomial σ K →+* K)) :
    (MvPolynomial σ K ⧸ J) →ₐ[K] K :=
  Ideal.Quotient.liftₐ J (aeval (0 : σ → K)) fun p hp => by
    simpa using hJ hp

@[simp] theorem quotientAugmentation_mk {σ K : Type*} [CommRing K]
    (J : Ideal (MvPolynomial σ K))
    (hJ : J ≤ RingHom.ker (constantCoeff : MvPolynomial σ K →+* K))
    (p : MvPolynomial σ K) :
    quotientAugmentation J hJ (Ideal.Quotient.mk J p) = constantCoeff p := by
  simp [quotientAugmentation]

theorem ker_quotientAugmentation {σ K : Type*} [CommRing K]
    (J : Ideal (MvPolynomial σ K))
    (hJ : J ≤ RingHom.ker (constantCoeff : MvPolynomial σ K →+* K)) :
    RingHom.ker (quotientAugmentation J hJ).toRingHom =
      (idealOfVars σ K).map (Ideal.Quotient.mk J) := by
  rw [← ker_constantCoeff_eq_idealOfVars]
  ext x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [RingHom.mem_ker]
  change quotientAugmentation J hJ (Ideal.Quotient.mk J p) = 0 ↔ _
  rw [quotientAugmentation_mk, Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective]
  constructor
  · intro hp
    exact ⟨p, hp, rfl⟩
  · rintro ⟨q, hq, hpq⟩
    change constantCoeff q = 0 at hq
    have hmem := (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp hpq
    have hh := hJ hmem
    change constantCoeff (q - p) = 0 at hh
    simpa only [map_sub, hq, zero_sub, neg_eq_zero] using hh

theorem isNilpotent_ker_quotientAugmentation
    {σ K : Type*} [Finite σ] [CommRing K]
    (J : Ideal (MvPolynomial σ K))
    (hJ : J ≤ RingHom.ker (constantCoeff : MvPolynomial σ K →+* K))
    (k : σ → ℕ) (hk : ∀ i, (X i : MvPolynomial σ K) ^ k i ∈ J) :
    IsNilpotent (RingHom.ker (quotientAugmentation J hJ).toRingHom) := by
  rw [ker_quotientAugmentation]
  exact isNilpotent_map_idealOfVars_of_pow_mem J k hk

theorem rectangularIdeal_le_ker_constantCoeff
    {σ K : Type*} [CommRing K] (k : σ → ℕ) (hk : ∀ i, k i ≠ 0) :
    Ideal.span (Set.range fun i => (X i : MvPolynomial σ K) ^ k i) ≤
      RingHom.ker (constantCoeff : MvPolynomial σ K →+* K) := by
  rw [Ideal.span_le, Set.range_subset_iff]
  intro i
  change constantCoeff ((X i : MvPolynomial σ K) ^ k i) = 0
  rw [map_pow, constantCoeff_X, zero_pow (hk i)]

def rectangularAugmentation {σ K : Type*} [CommRing K]
    (k : σ → ℕ) (hk : ∀ i, k i ≠ 0) :
    (MvPolynomial σ K ⧸
      Ideal.span (Set.range fun i => (X i : MvPolynomial σ K) ^ k i)) →ₐ[K] K :=
  quotientAugmentation _ (rectangularIdeal_le_ker_constantCoeff k hk)

theorem isNilpotent_ker_rectangularAugmentation
    {σ K : Type*} [Finite σ] [CommRing K] (k : σ → ℕ) (hk : ∀ i, k i ≠ 0) :
    IsNilpotent (RingHom.ker (rectangularAugmentation (K := K) k hk).toRingHom) := by
  apply isNilpotent_ker_quotientAugmentation _ _ k
  intro i
  exact Ideal.subset_span ⟨i, rfl⟩

end WeightedTorusJets.Geometry


namespace WeightedTorusJets.Geometry

theorem surjective_of_nilpotent_ideal_lifts {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (I : Ideal B) (hI : IsNilpotent I)
    (h₀ : ∀ b : B, ∃ a : A, b - f a ∈ I)
    (h₁ : ∀ b ∈ I, ∃ a : A, f a ∈ I ∧ b - f a ∈ I ^ 2) :
    Function.Surjective f := by
  have liftPower : ∀ n : ℕ, ∀ b ∈ I ^ n,
      ∃ a : A, f a ∈ I ^ n ∧ b - f a ∈ I ^ (n + 1) := by
    intro n
    induction n with
    | zero =>
        intro b _
        obtain ⟨a, ha⟩ := h₀ b
        exact ⟨a, by simp, by simpa using ha⟩
    | succ n hn =>
        intro b hb
        rw [pow_succ] at hb
        refine Submodule.mul_induction_on hb ?_ ?_
        · intro x hx y hy
          obtain ⟨a, ha, hxa⟩ := hn x hx
          obtain ⟨c, hc, hyc⟩ := h₁ y hy
          refine ⟨a * c, ?_, ?_⟩
          · rw [map_mul, pow_succ]
            exact Ideal.mul_mem_mul ha hc
          · have hleft : (x - f a) * y ∈ I ^ (n + 1 + 1) := by
              rw [pow_succ]
              exact Ideal.mul_mem_mul hxa hy
            have hright : f a * (y - f c) ∈ I ^ (n + 1 + 1) := by
              rw [show n + 1 + 1 = n + 2 by omega, pow_add]
              exact Ideal.mul_mem_mul ha hyc
            convert (I ^ (n + 1 + 1)).add_mem hleft hright using 1
            simp only [map_mul]
            ring
        · intro x y hx hy
          obtain ⟨a, ha, hxa⟩ := hx
          obtain ⟨c, hc, hyc⟩ := hy
          refine ⟨a + c, ?_, ?_⟩
          · simpa only [map_add] using (I ^ (n + 1)).add_mem ha hc
          · convert (I ^ (n + 1 + 1)).add_mem hxa hyc using 1
            simp only [map_add]
            ring
  have liftAll : ∀ n : ℕ, ∀ b : B, ∃ a : A, b - f a ∈ I ^ n := by
    intro n
    induction n with
    | zero => exact fun b => ⟨0, by simp⟩
    | succ n hn =>
        intro b
        obtain ⟨a, ha⟩ := hn b
        obtain ⟨c, _, hc⟩ := liftPower n (b - f a) ha
        refine ⟨a + c, ?_⟩
        convert hc using 1
        simp only [map_add]
        ring
  obtain ⟨n, hn⟩ := hI
  intro b
  obtain ⟨a, ha⟩ := liftAll n b
  rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at ha
  exact ⟨a, (sub_eq_zero.mp ha).symm⟩

end WeightedTorusJets.Geometry

end

end SiegelZeros

end OAI
