import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Differentials.TorusDerivationOverRat
import OAI.NumberTheory.SiegelZeros.Intersection.TorusRectangleJetIdealParametersProjectiveDegreeBound
import OAI.NumberTheory.SiegelZeros.Structure.FinrankDegreePiecePosPrimeVariableNotMem

namespace OAI

namespace SiegelZeros

section
section
section
open scoped BigOperators
open Module
open MvPolynomial
noncomputable section














open scoped BigOperators

namespace WeightedTorusJets.Geometry

variable {R ι : Type*} [CommSemiring R] [Fintype ι]

theorem invariantJet_monomial (c : Fin 3 → ι → R) (a : Fin 3 → ℕ)
    (m : ι →₀ ℕ) (r : R) :
    invariantJet c a (MvPolynomial.monomial m r) =
      ((∑ i, c 0 i * (m i : R)) ^ a 0 *
        (∑ i, c 1 i * (m i : R)) ^ a 1 *
        (∑ i, c 2 i * (m i : R)) ^ a 2) • MvPolynomial.monomial m r := by
  classical
  ext n
  rw [coeff_invariantJet, MvPolynomial.coeff_smul]
  simp only [MvPolynomial.coeff_monomial, smul_eq_mul]
  split_ifs with h
  · subst n
    rfl
  · simp




section ConcreteTorusParameters

variable {K : Type*} [Field K] [Infinite K]
local notation "P₄" => MvPolynomial (Fin 4) K
local notation "T₄" => Localization.Away (∏ i : Fin 4, (MvPolynomial.X i : P₄))

end ConcreteTorusParameters

end WeightedTorusJets.Geometry



noncomputable section
open scoped BigOperators
open MvPolynomial








namespace WeightedTorusJets.Geometry

section RectangleUpper

universe uSource
variable {K : Type uSource} [Field K] [Infinite K]
local notation "P₄" => MvPolynomial (Fin 4) K
local notation "T₄" => Localization.Away (∏ i : Fin 4, (MvPolynomial.X i : P₄))

theorem rectangleJetIdeal_length_le
    (p : Ideal T₄) [p.IsPrime] (c : Fin 3 → Fin 4 → K) (t : Fin 3 → ℕ) (b : ℕ)
    {N : ℕ} (hN : 0 < N) {F : P₄} (hF : F ∈ polynomialBox K N)
    (hp : p ∈ (rectangleJetIdeal (fun a => algebraMap P₄ T₄ (invariantJet c a F)) t b).minimalPrimes) :
    Module.length (Localization.AtPrime p) (Localization.AtPrime p ⧸
      (rectangleJetIdeal (fun a => algebraMap P₄ T₄ (invariantJet c a F)) t b).map
        (algebraMap T₄ (Localization.AtPrime p))) ≤
    ((4 * N) ^ Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime p))
      (IsLocalRing.CotangentSpace (Localization.AtPrime p)) : ℕ∞) := by
  obtain ⟨g, _, _, _, hle, hweighted⟩ :=
    torus_rectangleJetIdeal_exists_parameters_with_projective_degree_bound p c t b hN hF hp
  have : (p.comap (algebraMap P₄ T₄)).IsPrime := Ideal.comap_isPrime _ p
  have hdegree : (1 : ℕ∞) ≤ (GradedQuotient.projectiveDegree
      (coneIdeal (p.comap (algebraMap P₄ T₄)))
      (coneIdeal_isHomogeneous (p.comap (algebraMap P₄ T₄))) : ℕ∞) := by
    exact_mod_cast (Nat.succ_le_iff.mpr
      (GradedQuotient.cone_projectiveDegree_pos (p.comap (algebraMap P₄ T₄))))
  apply hle.trans
  exact (le_mul_of_one_le_right' hdegree).trans (by exact_mod_cast hweighted)

end RectangleUpper

end WeightedTorusJets.Geometry

end
end
end
end


namespace WeightedTorusJets.Geometry

open scoped BigOperators

theorem sum_pi_one {σ M : Type*} [Fintype σ] [DecidableEq σ] [AddCommMonoid M]
    (β : σ → Type*) [∀ i, Fintype (β i)] (i : σ) (hcover : ∀ u, u = i)
    (g : (∀ u, β u) → M) (h : β i → M) (hg : ∀ α, g α = h (α i)) :
    ∑ α, g α = ∑ n, h n := by
  let : Unique σ := ⟨⟨i⟩, hcover⟩
  exact Fintype.sum_equiv (Equiv.piUnique β) g h hg

theorem sum_pi_two {σ M : Type*} [Fintype σ] [DecidableEq σ] [AddCommMonoid M]
    (β : σ → Type*) [∀ i, Fintype (β i)] (i j : σ) (hij : i ≠ j)
    (hcover : ∀ u, u = i ∨ u = j)
    (g : (∀ u, β u) → M) (h : β j → β i → M) (hg : ∀ α, g α = h (α j) (α i)) :
    ∑ α, g α = ∑ n, ∑ m, h n m := by
  classical
  rw [← Fintype.sum_prod_type' h]
  apply Fintype.sum_bijective (fun α : ∀ u, β u => (α j, α i)) ?_ g _ hg
  constructor
  · intro α γ he
    funext u
    rcases hcover u with rfl | rfl
    · exact congrArg Prod.snd he
    · exact congrArg Prod.fst he
  · rintro ⟨n, m⟩
    refine ⟨fun u => if hu : u = j then hu.symm ▸ n
      else ((hcover u).resolve_right hu).symm ▸ m, ?_⟩
    simp [hij]

theorem sum_pi_three {σ M : Type*} [Fintype σ] [DecidableEq σ] [AddCommMonoid M]
    (β : σ → Type*) [∀ i, Fintype (β i)] (i j l : σ)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hcover : ∀ u, u = i ∨ u = j ∨ u = l)
    (g : (∀ u, β u) → M) (h : β l → β j → β i → M)
    (hg : ∀ α, g α = h (α l) (α j) (α i)) :
    ∑ α, g α = ∑ p, ∑ n, ∑ m, h p n m := by
  classical
  have hsum : (∑ z : β l × β j × β i, h z.1 z.2.1 z.2.2) =
      ∑ p, ∑ n, ∑ m, h p n m := by simp only [Fintype.sum_prod_type]
  rw [← hsum]
  apply Fintype.sum_bijective (fun α : ∀ u, β u => (α l, α j, α i)) ?_ g _ hg
  constructor
  · intro α γ he
    funext u
    rcases hcover u with rfl | rfl | rfl
    · exact congrArg (fun x => x.2.2) he
    · exact congrArg (fun x => x.2.1) he
    · exact congrArg Prod.fst he
  · rintro ⟨p, n, m⟩
    refine ⟨fun u => if hul : u = l then hul.symm ▸ p
      else if huj : u = j then huj.symm ▸ n
      else ((hcover u).resolve_right (not_or.mpr ⟨huj, hul⟩)).symm ▸ m, ?_⟩
    simp [hij, hil, hjl]

variable {A B : Type*} [CommRing A] [Algebra ℚ A] [CommRing B] [Algebra ℚ B]

theorem rectangularTaylorThree_selected_sum
    (D : Fin 3 → Derivation ℚ A A)
    (h01 : Function.Commute (D 0) (D 1))
    (h02 : Function.Commute (D 0) (D 2))
    (h12 : Function.Commute (D 1) (D 2))
    (I : Finset (Fin 3)) (i j l : I) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hcover : ∀ u : I, u = i ∨ u = j ∨ u = l) (k : I → ℕ) (f : A →+* B) (a : A) :
    rectangularTaylorThree I k (D i) (D j) (D l) i j l f a =
      ∑ α : (u : I) → Fin (k u), (∏ u : I, ((α u).val.factorial : ℚ))⁻¹ •
        Ideal.Quotient.mk (rectangularIdeal k)
          (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm (fun u => (α u).val))
            (f (derivationJet D (Function.extend (Subtype.val : I → Fin 3)
              (fun u => (α u).val) 0) a))) := by
  classical
  rw [rectangularTaylorThree_apply]
  simp_rw [Finset.sum_range]
  symm
  refine sum_pi_three (fun u => Fin (k u)) i j l hij hil hjl hcover _ _ ?_
  intro α
  let β : I → ℕ := fun u => (α u).val
  have huniv : (Finset.univ : Finset I) = {i, j, l} := by
    ext u
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact hcover u
  have hprod : (∏ u : I, ((β u).factorial : ℚ)) =
      ((β i).factorial : ℚ) * ((β j).factorial : ℚ) * ((β l).factorial : ℚ) := by
    rw [huniv]
    simp [hij, hil, hjl, mul_assoc]
  have hexp : Finsupp.equivFunOnFinite.symm β =
      Finsupp.single i (β i) + (Finsupp.single j (β j) + Finsupp.single l (β l)) := by
    ext u
    rcases hcover u with rfl | rfl | rfl <;>
      simp [hij, hil, hjl, Ne.symm hij, Ne.symm hil, Ne.symm hjl]
  have hjet := derivationJet_selected_three D h01 h02 h12 I i j l hij hil hjl hcover β a
  change (∏ u : I, ((β u).factorial : ℚ))⁻¹ •
      Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.monomial
        (Finsupp.equivFunOnFinite.symm β)
          (f (derivationJet D (Function.extend (Subtype.val : I → Fin 3) β 0) a))) = _
  rw [hprod, hexp, ← hjet]
  simp only [mul_inv_rev, mul_assoc, β]

theorem rectangularTaylorThree_one_selected_sum
    (D : Fin 3 → Derivation ℚ A A)
    (h01 : Function.Commute (D 0) (D 1))
    (h02 : Function.Commute (D 0) (D 2))
    (h12 : Function.Commute (D 1) (D 2))
    (I : Finset (Fin 3)) (i : I) (hcover : ∀ u : I, u = i)
    (k : I → ℕ) (f : A →+* B) (a : A) :
    rectangularTaylorThree I k (D i) 0 0 i i i f a =
      ∑ α : (u : I) → Fin (k u), (∏ u : I, ((α u).val.factorial : ℚ))⁻¹ •
        Ideal.Quotient.mk (rectangularIdeal k)
          (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm (fun u => (α u).val))
            (f (derivationJet D (Function.extend (Subtype.val : I → Fin 3)
              (fun u => (α u).val) 0) a))) := by
  classical
  rw [rectangularTaylorThree_one_apply]
  simp_rw [Finset.sum_range]
  symm
  refine sum_pi_one (fun u => Fin (k u)) i hcover _ _ ?_
  intro α
  let β : I → ℕ := fun u => (α u).val
  have huniv : (Finset.univ : Finset I) = {i} := by
    ext u
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    exact hcover u
  have hprod : (∏ u : I, ((β u).factorial : ℚ)) = ((β i).factorial : ℚ) := by
    rw [huniv, Finset.prod_singleton]
  have hexp : Finsupp.equivFunOnFinite.symm β = Finsupp.single i (β i) := by
    ext u
    rcases hcover u with rfl
    simp
  have hjet := derivationJet_selected_one D h01 h02 h12 I i hcover β a
  change (∏ u : I, ((β u).factorial : ℚ))⁻¹ •
      Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.monomial
        (Finsupp.equivFunOnFinite.symm β)
          (f (derivationJet D (Function.extend (Subtype.val : I → Fin 3) β 0) a))) = _
  rw [hprod, hexp, ← hjet]

theorem rectangularTaylorThree_two_selected_sum
    (D : Fin 3 → Derivation ℚ A A)
    (h01 : Function.Commute (D 0) (D 1))
    (h02 : Function.Commute (D 0) (D 2))
    (h12 : Function.Commute (D 1) (D 2))
    (I : Finset (Fin 3)) (i j : I) (hij : i ≠ j)
    (hcover : ∀ u : I, u = i ∨ u = j) (k : I → ℕ) (f : A →+* B) (a : A) :
    rectangularTaylorThree I k (D i) (D j) 0 i j j f a =
      ∑ α : (u : I) → Fin (k u), (∏ u : I, ((α u).val.factorial : ℚ))⁻¹ •
        Ideal.Quotient.mk (rectangularIdeal k)
          (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm (fun u => (α u).val))
            (f (derivationJet D (Function.extend (Subtype.val : I → Fin 3)
              (fun u => (α u).val) 0) a))) := by
  classical
  rw [rectangularTaylorThree_two_apply]
  simp_rw [Finset.sum_range]
  symm
  refine sum_pi_two (fun u => Fin (k u)) i j hij hcover _ _ ?_
  intro α
  let β : I → ℕ := fun u => (α u).val
  have huniv : (Finset.univ : Finset I) = {i, j} := by
    ext u
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact hcover u
  have hprod : (∏ u : I, ((β u).factorial : ℚ)) =
      ((β i).factorial : ℚ) * ((β j).factorial : ℚ) := by
    rw [huniv]
    simp [hij]
  have hexp : Finsupp.equivFunOnFinite.symm β =
      Finsupp.single i (β i) + Finsupp.single j (β j) := by
    ext u
    rcases hcover u with rfl | rfl <;> simp [hij, Ne.symm hij]
  have hjet := derivationJet_selected_two D h01 h02 h12 I i j hij hcover β a
  change (∏ u : I, ((β u).factorial : ℚ))⁻¹ •
      Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.monomial
        (Finsupp.equivFunOnFinite.symm β)
          (f (derivationJet D (Function.extend (Subtype.val : I → Fin 3) β 0) a))) = _
  rw [hprod, hexp, ← hjet]
  simp only [mul_inv_rev, β]

theorem exists_selected_taylor_ringHom
    (D : Fin 3 → Derivation ℚ A A)
    (h01 : Function.Commute (D 0) (D 1))
    (h02 : Function.Commute (D 0) (D 2))
    (h12 : Function.Commute (D 1) (D 2))
    (I : Finset (Fin 3)) (hI : I.Nonempty) (k : I → ℕ) (f : A →+* B) :
    ∃ φ : A →+* (MvPolynomial I B ⧸ rectangularIdeal k), ∀ a,
      φ a = ∑ α : (u : I) → Fin (k u), (∏ u : I, ((α u).val.factorial : ℚ))⁻¹ •
        Ideal.Quotient.mk (rectangularIdeal k)
          (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm (fun u => (α u).val))
            (f (derivationJet D (Function.extend (Subtype.val : I → Fin 3)
              (fun u => (α u).val) 0) a))) := by
  classical
  have hpos := Finset.card_pos.mpr hI
  have hmax : I.card ≤ 3 := by simpa using Finset.card_le_univ I
  have hcard : I.card = 1 ∨ I.card = 2 ∨ I.card = 3 := by omega
  rcases hcard with hcard | hcard | hcard
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hcard
    let ii : ↥({i} : Finset (Fin 3)) := ⟨i, by simp⟩
    refine ⟨rectangularTaylorThree _ k (D i) 0 0 ii ii ii f, fun a => ?_⟩
    exact rectangularTaylorThree_one_selected_sum D h01 h02 h12 {i} ii
      (fun j => Subtype.ext (Finset.mem_singleton.mp j.property)) k f a
  · obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp hcard
    let ii : ↥({i, j} : Finset (Fin 3)) := ⟨i, by simp⟩
    let jj : ↥({i, j} : Finset (Fin 3)) := ⟨j, by simp⟩
    refine ⟨rectangularTaylorThree _ k (D i) (D j) 0 ii jj jj f, fun a => ?_⟩
    refine rectangularTaylorThree_two_selected_sum D h01 h02 h12 {i, j} ii jj
      (fun h => hij (congrArg Subtype.val h)) ?_ k f a
    intro u
    rcases Finset.mem_insert.mp u.property with hu | hu
    · exact Or.inl (Subtype.ext hu)
    · exact Or.inr (Subtype.ext (Finset.mem_singleton.mp hu))
  · obtain ⟨i, j, l, hij, hil, hjl, rfl⟩ := Finset.card_eq_three.mp hcard
    let ii : ↥({i, j, l} : Finset (Fin 3)) := ⟨i, by simp⟩
    let jj : ↥({i, j, l} : Finset (Fin 3)) := ⟨j, by simp⟩
    let ll : ↥({i, j, l} : Finset (Fin 3)) := ⟨l, by simp⟩
    refine ⟨rectangularTaylorThree _ k (D i) (D j) (D l) ii jj ll f, fun a => ?_⟩
    refine rectangularTaylorThree_selected_sum D h01 h02 h12 {i, j, l} ii jj ll
      (fun h => hij (congrArg Subtype.val h))
      (fun h => hil (congrArg Subtype.val h))
      (fun h => hjl (congrArg Subtype.val h)) ?_ k f a
    intro u
    have hu : u.val = i ∨ u.val = j ∨ u.val = l := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using u.property
    rcases hu with hu | hu | hu
    · exact Or.inl (Subtype.ext hu)
    · exact Or.inr (Or.inl (Subtype.ext hu))
    · exact Or.inr (Or.inr (Subtype.ext hu))

theorem factorial_smul_quotient_monomial {σ K : Type*} [Fintype σ] [Field K] [Algebra ℚ K]
    (J : Ideal (MvPolynomial σ K)) (α : σ → ℕ) (c : K) :
    (∏ u : σ, ((α u).factorial : ℚ))⁻¹ •
      Ideal.Quotient.mk J (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm α) c) =
      Ideal.Quotient.mk J (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm α)
        (c / ∏ u : σ, ((α u).factorial : K))) := by
  let : CharZero K := algebraRat.charZero K
  have hs := ratCast_smul_eq ℚ K (∏ u : σ, ((α u).factorial : ℚ))⁻¹
    (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm α) c)
  simp only [Rat.cast_id] at hs
  rw [← map_rat_smul, hs, MvPolynomial.smul_monomial, smul_eq_mul]
  simp [div_eq_mul_inv, mul_comm]

theorem exists_source_taylor_ringHom {K : Type*} [Field K] [Algebra ℚ K]
    (D : Fin 3 → Derivation ℚ A A)
    (h01 : Function.Commute (D 0) (D 1))
    (h02 : Function.Commute (D 0) (D 2))
    (h12 : Function.Commute (D 1) (D 2))
    (I : Finset (Fin 3)) (hI : I.Nonempty) (t : Fin 3 → ℕ) (f : A →+* K) :
    ∃ φ : A →+* (MvPolynomial I K ⧸ rectangularIdeal (fun u : I => t u + 1)), ∀ a,
      φ a = ∑ α : (u : I) → Fin (t u + 1),
        Ideal.Quotient.mk (rectangularIdeal (fun u : I => t u + 1))
          (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm (fun u => (α u).val))
            (f (derivationJet D (Function.extend (Subtype.val : I → Fin 3)
              (fun u => (α u).val) 0) a) / ∏ u : I, ((α u).val.factorial : K))) := by
  obtain ⟨φ, hφ⟩ := exists_selected_taylor_ringHom D h01 h02 h12 I hI
    (fun u : I => t u + 1) f
  refine ⟨φ, fun a => ?_⟩
  rw [hφ]
  apply Finset.sum_congr rfl
  intro α _
  exact factorial_smul_quotient_monomial _ _ _

theorem exists_source_taylor_quotient_ringHom {K : Type*} [Field K] [Algebra ℚ K]
    (D : Fin 3 → Derivation ℚ A A)
    (h01 : Function.Commute (D 0) (D 1))
    (h02 : Function.Commute (D 0) (D 2))
    (h12 : Function.Commute (D 1) (D 2))
    (I : Finset (Fin 3)) (hI : I.Nonempty) (t : Fin 3 → ℕ) (b : ℕ) (F : A)
    (f : A →+* K) (hnext : derivativeStageIdeal D t (b + 1) F ≤ RingHom.ker f) :
    ∃ φ : (A ⧸ derivativeStageIdeal D t b F) →+*
        (MvPolynomial I K ⧸ rectangularIdeal (fun u : I => t u + 1)), ∀ a,
      φ (Ideal.Quotient.mk (derivativeStageIdeal D t b F) a) =
        ∑ α : (u : I) → Fin (t u + 1),
          Ideal.Quotient.mk (rectangularIdeal (fun u : I => t u + 1))
            (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm (fun u => (α u).val))
              (f (derivationJet D (Function.extend (Subtype.val : I → Fin 3)
                (fun u => (α u).val) 0) a) / ∏ u : I, ((α u).val.factorial : K))) := by
  classical
  obtain ⟨φ, hφ⟩ := exists_source_taylor_ringHom D h01 h02 h12 I hI t f
  have hvanish := (derivativeStageIdeal_le_ker_iff D t (b + 1) F f).mp hnext
  have hker : derivativeStageIdeal D t b F ≤ RingHom.ker φ := by
    apply Ideal.span_le.mpr
    rintro _ ⟨β, hβ, rfl⟩
    change φ (derivationJet D β F) = 0
    rw [hφ]
    apply Finset.sum_eq_zero
    intro α _
    let γ : I → ℕ := fun u => (α u).val
    have hbound := selectedIndex_add_stage_bound_lt I γ β t b hβ (fun u => (α u).isLt)
    have hjet : derivationJet D (Function.extend (Subtype.val : I → Fin 3) γ 0)
        (derivationJet D β F) =
        derivationJet D (β + Function.extend (Subtype.val : I → Fin 3) γ 0) F := by
      simpa only [derivationJet, Pi.add_apply, Nat.add_comm] using
        (mixed_derivation_pow_add D h01 h02 h12
          (Function.extend (Subtype.val : I → Fin 3) γ 0) β F).symm
    change Ideal.Quotient.mk _ (MvPolynomial.monomial _
      (f (derivationJet D (Function.extend (Subtype.val : I → Fin 3) γ 0)
        (derivationJet D β F)) / _)) = 0
    rw [hjet, hvanish _ hbound]
    simp
  refine ⟨Ideal.Quotient.lift (derivativeStageIdeal D t b F) φ (fun _ ha => hker ha), ?_⟩
  exact hφ

end WeightedTorusJets.Geometry

end

end SiegelZeros

end OAI
