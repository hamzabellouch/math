import Mathlib
import OAI.RepresentationTheory.RestrictedTilting.AssociatedLattices

namespace OAI

/-! Weak regularity and local freeness of associated sections. -/

noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators

namespace FiberFunctorProof
section
open scoped Pointwise TensorProduct
open RingTheory.Sequence

section
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

lemma weaklyRegular_pair_iff (x y : R) :
    IsWeaklyRegular M [x,y] ↔
      Function.Injective (fun m : M => x • m) ∧
        ∀ v n : M, y • v = x • n → ∃ w : M, v = x • w := by
  rw [isWeaklyRegular_cons_iff, isWeaklyRegular_singleton_iff]
  change IsSMulRegular M x ∧ IsSMulRegular (M ⧸ (x • (⊤ : Submodule R M))) y ↔ _
  rw [isSMulRegular_on_quot_iff_lsmul_comap_le]
  constructor
  · rintro ⟨hx,hy⟩
    refine ⟨hx, fun v n hn => ?_⟩
    have hv : v ∈ x • (⊤ : Submodule R M) := hy (by
      change y • v ∈ x • (⊤ : Submodule R M)
      rw [hn]
      exact Submodule.smul_mem_pointwise_smul n x ⊤ (by trivial))
    obtain ⟨w,_,hw⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hv
    exact ⟨w,hw.symm⟩
  · rintro ⟨hx,hy⟩
    refine ⟨hx, ?_⟩
    intro v hv
    obtain ⟨n,_,hn⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hv
    obtain ⟨w,hw⟩ := hy v n hn.symm
    rw [hw]
    exact Submodule.smul_mem_pointwise_smul w x ⊤ (by trivial)

end

 

theorem flat_baseChange_free {R S M : Type*}
    [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    [IsLocalRing S] [IsNoetherianRing S]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (x y : R) (hm : IsLocalRing.maximalIdeal S =
      Ideal.span {algebraMap R S x, algebraMap R S y})
    (hx : Function.Injective (fun m : M => x • m))
    (hy : ∀ v n : M, y • v = x • n → ∃ w : M, v = x • w) :
    Module.Free S (S ⊗[R] M) := by
  have hr := (weaklyRegular_pair_iff x y).mpr ⟨hx,hy⟩
  have hS := hr.isWeaklyRegular_lTensor (M₂ := S)
  obtain ⟨hxS,hyS⟩ := (weaklyRegular_pair_iff (M := S ⊗[R] M) x y).mp hS
  let : Module.FinitePresentation S (S ⊗[R] M) := Module.finitePresentation_of_finite S _
  apply free_of_two_generators (algebraMap R S x) (algebraMap R S y) hm
  · simpa only [algebraMap_smul] using hxS
  · simpa only [algebraMap_smul] using hyS
end

open scoped TensorProduct

lemma gluedLattice_regular {R K ι : Type*} [CommRing R] [Field K]
    [Algebra R K] [FaithfulSMul R K] (x y : R) (hx : x ≠ 0) (hy : y ≠ 0)
    (P : (ι → K) ≃ₗ[K] (ι → K)) :
    Function.Injective (fun m : gluedLattice x y P => x • m) ∧
      ∀ v n : gluedLattice x y P, y • v = x • n →
        ∃ w : gluedLattice x y P, v = x • w := by
  have hinj := FaithfulSMul.algebraMap_injective R K
  have hxK : algebraMap R K x ≠ 0 := fun h => hx (hinj (h.trans (map_zero _).symm))
  have hyK : algebraMap R K y ≠ 0 := fun h => hy (hinj (h.trans (map_zero _).symm))
  have hB : ∀ z ∈ (powerLocalization y coordinateLattice).map (P.toLinearMap.restrictScalars R),
      (algebraMap R K y)⁻¹ • z ∈
        (powerLocalization y coordinateLattice).map (P.toLinearMap.restrictScalars R) := by
    rintro z ⟨v,hv,rfl⟩
    refine ⟨(algebraMap R K y)⁻¹ • v, powerLocalization_div y _ hyK hv, ?_⟩
    exact P.map_smul _ _
  exact intersection_regular _ _ x y hxK hyK
    (fun _ hv => powerLocalization_div x _ hxK hv) hB

lemma regular_pair_equiv {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (x y : R)
    (hx : Function.Injective (fun n : N => x • n))
    (hy : ∀ v n : N, y • v = x • n → ∃ w : N, v = x • w) :
    Function.Injective (fun m : M => x • m) ∧
      ∀ v n : M, y • v = x • n → ∃ w : M, v = x • w := by
  constructor
  · intro a b hab
    apply e.injective
    apply hx
    simpa using congrArg e hab
  · intro v n hn
    obtain ⟨w,hw⟩ := hy (e v) (e n) (by simpa using congrArg e hn)
    refine ⟨e.symm w, e.injective ?_⟩
    simpa using hw

universe u
variable (k : Type u) [Field k] [Infinite k]
variable (ι : Type u) [Fintype ι] [DecidableEq ι]
variable (ρ : Representation k (Multiplicative k) (ι → k))
variable (P : Matrix ι ι (Polynomial k))
variable (hP : ∀ t : k, polynomialMatrixEval P t = LinearMap.toMatrix' (ρ (Multiplicative.ofAdd t)))

include hP in
 
theorem associatedSections_regular :
    Function.Injective (fun m : associatedSectionsSubmodule k ι ρ =>
      (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) k) • m) ∧
    ∀ v n : associatedSectionsSubmodule k ι ρ,
      (MvPolynomial.X 1 : MvPolynomial (Fin 2) k) • v = (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) • n →
        ∃ w : associatedSectionsSubmodule k ι ρ, v = (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) • w := by
  obtain ⟨hx,hy⟩ := gluedLattice_regular
    (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) k) (MvPolynomial.X 1)
    (MvPolynomial.X_ne_zero 0) (MvPolynomial.X_ne_zero 1)
    (planeGlobalTransition k P (associatedPolynomial_zero k ι ρ P hP)
      (associatedPolynomial_add k ι ρ P hP))
  exact regular_pair_equiv (associatedLatticeEquiv k ι ρ P hP) _ _ hx hy

include hP in
 

theorem associatedStalk_free (d : ℕ) (hd : ∀ i j, (P i j).natDegree ≤ d) :
    Module.Free (planeOriginRing k)
      ((planeOriginRing k) ⊗[MvPolynomial (Fin 2) k] (associatedSectionsSubmodule k ι ρ)) := by
  let : Module.Finite (MvPolynomial (Fin 2) k) (associatedSectionsSubmodule k ι ρ) :=
    associatedSections_finite k ι ρ P hP d hd
  obtain ⟨hx,hy⟩ := associatedSections_regular k ι ρ P hP
  exact flat_baseChange_free (MvPolynomial.X 0) (MvPolynomial.X 1)
    (planeOrigin_maximalIdeal k) hx hy
end FiberFunctorProof
end

end OAI
