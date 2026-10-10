import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.FinrankSpanImage

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace SharpRamseyFive.LinearPolynomial
open scoped BigOperators
open MvPolynomial Module
variable {K I : Type*} [Field K]

theorem exists_linear_form (P : MvPolynomial I K) (hP : P.totalDegree ≤ 1) :
    ∃ φ : (K × (I → K)) →ₗ[K] K, ∀ x, φ (1, x) = eval x P := by
  classical
  have hterm (d : P.support) :
      ∃ φ : (K × (I → K)) →ₗ[K] K,
        ∀ x, φ (1, x) = eval x (monomial d.val (P.coeff d.val)) := by
    have hd : d.val.degree ≤ 1 := (le_totalDegree d.property).trans hP
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hd with hd | hd
    · have he := (Finsupp.degree_eq_zero_iff _).mp hd
      refine ⟨P.coeff d.val • LinearMap.fst K K (I → K), ?_⟩
      intro x
      simp [he]
    · obtain ⟨i, hi⟩ := (Finsupp.sum_eq_one_iff d.val).mp hd
      refine ⟨P.coeff d.val • ((LinearMap.proj i).comp (LinearMap.snd K K (I → K))), ?_⟩
      intro x
      simp [hi, eval_monomial]
  choose φ hφ using hterm
  refine ⟨∑ d : P.support, φ d, ?_⟩
  intro x
  simp only [LinearMap.sum_apply]
  simp_rw [hφ]
  rw [← map_sum, Finset.sum_coe_sort P.support (fun d => monomial d (P.coeff d)), ← P.as_sum]

theorem exists_hyperplane [Infinite K] [Fintype I]
    (P : MvPolynomial I K) (hP : P.totalDegree = 1) :
    ∃ W : Submodule K (K × (I → K)), finrank K W = Fintype.card I ∧
      ∀ x, eval x P = 0 → ((1 : K), x) ∈ W := by
  obtain ⟨φ, hφ⟩ := exists_linear_form P hP.le
  have hφ0 : φ ≠ 0 := by
    intro he
    have hP0 : P = 0 := MvPolynomial.funext (fun x => by simpa [he] using (hφ x).symm)
    subst P
    simp at hP
  refine ⟨LinearMap.ker φ, ?_, ?_⟩
  · have h := Module.Dual.finrank_ker_add_one_of_ne_zero hφ0
    simp only [Module.finrank_prod, Module.finrank_self, Module.finrank_pi] at h
    omega
  · intro x hx
    rw [LinearMap.mem_ker, hφ, hx]
end SharpRamseyFive.LinearPolynomial

namespace SharpRamseyFive.AffineRealization

section
open Module
open scoped LinearAlgebra.Projectivization
variable {K L I ι : Type*} [Field K] [Field L] [Algebra K L]

lemma projective_pair_rank {V : Type*} [AddCommGroup V] [Module K V]
    {p r : ℙ K V} (hpr : p ≠ r) :
    finrank K (Submodule.span K {p.rep, r.rep}) = 2 := by
  have hi := Projectivization.independent_iff.mp
    ((Projectivization.independent_pair_iff_ne p r).mpr hpr)
  have hr : Set.range (Projectivization.rep ∘ ![p, r]) = {p.rep, r.rep} := by
    ext v
    simp only [Set.mem_range, Function.comp_apply, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  have h := finrank_span_eq_card hi
  rw [hr] at h
  simpa using h

omit [Algebra K L] in

lemma injective_of_ranks [Fintype I] [DecidableEq ι]
    (p : ι → ℙ K (I → K)) (hp : Function.Injective p)
    (a : ι → Fin 3 → L)
    (hr : ∀ Y : Finset ι,
      finrank L (Submodule.span L ((fun i => ((1 : L), a i)) '' (Y : Set ι))) =
        min (finrank K (Submodule.span K ((fun i => (p i).rep) '' (Y : Set ι)))) 4) :
    Function.Injective a := by
  intro i j hij
  by_contra hn
  have h := hr {i,j}
  rw [Finset.coe_insert, Finset.coe_singleton, Set.image_pair, Set.image_pair, hij,
    Set.insert_eq_of_mem (Set.mem_singleton _), projective_pair_rank (by exact fun he => hn (hp he))] at h
  have hv : ((1 : L), a j) ≠ 0 := by
    intro he
    have he1 := congrArg Prod.fst he
    exact one_ne_zero he1
  rw [finrank_span_singleton hv] at h
  norm_num at h

theorem exists_projective_realization [Infinite L] [Fintype I] [Fintype ι] [Nonempty ι]
    (hI : Fintype.card I = 4 ∨ Fintype.card I = 5)
    (p : ι → ℙ K (I → K)) (hp : Function.Injective p) :
    ∃ a : ι → Fin 3 → L, Function.Injective a ∧ ∀ Y : Finset ι,
      finrank L (Submodule.span L ((fun i => ((1 : L), a i)) '' (Y : Set ι))) =
        min (finrank K (Submodule.span K ((fun i => (p i).rep) '' (Y : Set ι)))) 4 := by
  classical
  obtain ⟨a, ha⟩ := exists_realization (L := L) hI (fun i => (p i).rep)
    (fun i => (p i).rep_nonzero)
  exact ⟨a, injective_of_ranks p hp a ha, ha⟩
end

open Module MvPolynomial
open scoped LinearAlgebra.Projectivization Classical
variable {K L I ι : Type*} [Field K] [Field L] [Fintype I] [Fintype ι]

theorem plane_cap_of_ranks [Infinite L]
    (hI : 3 ≤ Fintype.card I) (p : ι → ℙ K (I → K))
    (a : ι → Fin 3 → L) (ha : Function.Injective a)
    (hr : ∀ Y : Finset ι,
      finrank L (Submodule.span L ((fun i => ((1 : L), a i)) '' (Y : Set ι))) =
        min (finrank K (Submodule.span K ((fun i => (p i).rep) '' (Y : Set ι)))) 4)
    (Kp : ℕ)
    (hcap : ∀ W : Submodule K (I → K), finrank K W = 3 →
      (Finset.univ.filter (fun i => (p i).rep ∈ W)).card ≤ Kp)
    (P : MvPolynomial (Fin 3) L) (hP : P.totalDegree = 1) :
    ((Finset.univ.image a).filter (fun y => eval y P = 0)).card ≤ Kp := by
  classical
  let Y : Finset ι := Finset.univ.filter (fun i => eval (a i) P = 0)
  obtain ⟨W, hW, hWmem⟩ := LinearPolynomial.exists_hyperplane P hP
  have hYW : Submodule.span L ((fun i => ((1 : L), a i)) '' (Y : Set ι)) ≤ W := by
    apply Submodule.span_le.mpr
    rintro z ⟨i, hi, rfl⟩
    exact hWmem _ (Finset.mem_filter.mp hi).2
  have hry : finrank K (Submodule.span K ((fun i => (p i).rep) '' (Y : Set ι))) ≤ 3 := by
    have hy := Submodule.finrank_mono hYW
    rw [hr Y, hW] at hy
    simp only [Fintype.card_fin] at hy
    omega
  obtain ⟨U, hU, hUrank⟩ := SubspaceExtension.exists_rank
    (Submodule.span K ((fun i => (p i).rep) '' (Y : Set ι))) 3 hry (by simpa using hI)
  have hYu : Y ⊆ Finset.univ.filter (fun i => (p i).rep ∈ U) := by
    intro i hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, hU ?_⟩
    exact Submodule.subset_span ⟨i, hi, rfl⟩
  have he : (Finset.univ.image a).filter (fun y => eval y P = 0) = Y.image a := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and, Y]
    constructor
    · rintro ⟨⟨i, rfl⟩, hi⟩
      exact ⟨i, hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, rfl⟩, hi⟩
  rw [he, Finset.card_image_of_injective _ ha]
  exact (Finset.card_le_card hYu).trans (hcap U hUrank)
end SharpRamseyFive.AffineRealization

end OAI
