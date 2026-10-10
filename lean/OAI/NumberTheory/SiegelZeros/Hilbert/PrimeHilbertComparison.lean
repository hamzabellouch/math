import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Analysis.Normed.Group.Rat
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.DirectSum.Finite
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.Ideal.Prime
import Mathlib.Tactic
import OAI.NumberTheory.SiegelZeros.EntireFunctions.FiniteNormalizationGrowth
import OAI.NumberTheory.SiegelZeros.EntireFunctions.PolynomialGrowthRanks
import OAI.NumberTheory.SiegelZeros.Hilbert.ProperHypersurfaceHilbert
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.PolynomialCumulative

namespace OAI

namespace SiegelZeros

noncomputable section
namespace WeightedTorusJets.W25

open MvPolynomial
open WeightedTorusJets.W64
open DirectSum

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k]

def quotientDegreeProjection (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) (n : ℕ) :
    (MvPolynomial σ k ⧸ I) →ₗ[k] (MvPolynomial σ k ⧸ I) :=
  (I.restrictScalars k).liftQ
    ((Ideal.Quotient.mkₐ k I).toLinearMap.comp
      (GradedAlgebra.proj (MvPolynomial.homogeneousSubmodule σ k) n)) (by
    intro p hp
    change Ideal.Quotient.mk I
      (GradedAlgebra.proj (MvPolynomial.homogeneousSubmodule σ k) n p) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact (Ideal.IsHomogeneous.mem_iff
      (MvPolynomial.homogeneousSubmodule σ k) hI).mp hp n)

@[simp] theorem quotientDegreeProjection_mk (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) (n : ℕ)
    (p : MvPolynomial σ k) :
    quotientDegreeProjection I hI n (Ideal.Quotient.mk I p) =
      Ideal.Quotient.mk I
        (GradedAlgebra.proj (MvPolynomial.homogeneousSubmodule σ k) n p) := rfl

theorem quotientDegreeProjection_of_mem (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (n m : ℕ) (x : MvPolynomial σ k ⧸ I) (hx : x ∈ quotientSection I m) :
    quotientDegreeProjection I hI n x = if n = m then x else 0 := by
  obtain ⟨p, hp, rfl⟩ := hx
  change quotientDegreeProjection I hI n (Ideal.Quotient.mk I p) = _
  rw [quotientDegreeProjection_mk, GradedAlgebra.proj_apply]
  by_cases hnm : n = m
  · subst n
    rw [DirectSum.decompose_of_mem_same (MvPolynomial.homogeneousSubmodule σ k) hp]
    simp
  · rw [DirectSum.decompose_of_mem_ne (MvPolynomial.homogeneousSubmodule σ k) hp
      (Ne.symm hnm)]
    simp [hnm]

theorem quotientSection_iSupIndep (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) :
    iSupIndep (quotientSection I) := by
  classical
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s v hv hsum i hi
  have hcalc : quotientDegreeProjection I hI i (∑ j ∈ s, v j) = v i := by
    rw [map_sum]
    calc
      ∑ j ∈ s, quotientDegreeProjection I hI i (v j) =
          ∑ j ∈ s, if i = j then v j else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        exact quotientDegreeProjection_of_mem I hI i j (v j) (hv j hj)
      _ = v i := by simp [hi]
  rw [hsum, map_zero] at hcalc
  exact hcalc.symm

theorem quotientSection_iSup_eq_top (I : Ideal (MvPolynomial σ k)) :
    (⨆ n, quotientSection I n) = ⊤ := by
  simp only [quotientSection, ← Submodule.map_iSup]
  rw [(DirectSum.Decomposition.isInternal
    (MvPolynomial.homogeneousSubmodule σ k)).submodule_iSup_eq_top]
  rw [Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (Ideal.Quotient.mkₐ_surjective k I)

theorem quotientSection_isInternal (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) :
    DirectSum.IsInternal (quotientSection I) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (quotientSection_iSupIndep I hI) (quotientSection_iSup_eq_top I)

def homogeneousQuotientDirectSumEquiv (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) :
    (⨁ n : ℕ, quotientSection I n) ≃ₗ[k] (MvPolynomial σ k ⧸ I) :=
  LinearEquiv.ofBijective (DirectSum.coeLinearMap (quotientSection I))
    (quotientSection_isInternal I hI)

theorem quotientSection_bounded_iSup_eq_top (I : Ideal (MvPolynomial σ k)) (B : ℕ)
    (hzero : ∀ n, B < n → quotientSection I n = ⊥) :
    (⨆ n : Fin (B+1), quotientSection I n.val) = ⊤ := by
  rw [← quotientSection_iSup_eq_top I]
  apply le_antisymm
  · exact iSup_le fun n => le_iSup (quotientSection I) n.val
  · apply iSup_le
    intro n
    by_cases hn : n < B+1
    · exact le_iSup (fun j : Fin (B+1) => quotientSection I j.val) ⟨n, hn⟩
    · rw [hzero n (Nat.lt_of_succ_le (Nat.le_of_not_lt hn))]
      exact bot_le

def boundedHomogeneousQuotientEquiv (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) (B : ℕ)
    (hzero : ∀ n, B < n → quotientSection I n = ⊥) :
    (⨁ n : Fin (B+1), quotientSection I n.val) ≃ₗ[k] (MvPolynomial σ k ⧸ I) :=
  LinearEquiv.ofBijective
    (DirectSum.coeLinearMap (fun n : Fin (B+1) => quotientSection I n.val))
    (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      ((quotientSection_iSupIndep I hI).comp Fin.val_injective)
      (quotientSection_bounded_iSup_eq_top I B hzero))

variable [Finite σ]

theorem homogeneousQuotient_finite (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) (B : ℕ)
    (hzero : ∀ n, B < n → quotientSection I n = ⊥) :
    Module.Finite k (MvPolynomial σ k ⧸ I) :=
  Module.Finite.equiv (boundedHomogeneousQuotientEquiv I hI B hzero)

theorem homogeneousQuotient_finrank_eq_sum (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) (B : ℕ)
    (hzero : ∀ n, B < n → quotientSection I n = ⊥) :
    Module.finrank k (MvPolynomial σ k ⧸ I) =
      ∑ n : Fin (B+1), Module.finrank k (quotientSection I n.val) := by
  rw [← (boundedHomogeneousQuotientEquiv I hI B hzero).finrank_eq,
    Module.finrank_directSum]

end WeightedTorusJets.W25

end

section

namespace WeightedTorusJets.W27

open scoped BigOperators
open Filter Polynomial
open WeightedTorusJets.W64

variable {k σ : Type*} [Field k] [Fintype σ]

theorem prime_quotientSection_finrank_pos
    (P : Ideal (MvPolynomial σ k)) [hP : P.IsPrime]
    (i : σ) (hi : MvPolynomial.X i ∉ P) (n : ℕ) :
    0 < Module.finrank k (quotientSection P n) := by
  apply Module.finrank_pos_iff_exists_ne_zero.mpr
  let x : quotientSection P n :=
    ⟨Ideal.Quotient.mk P (MvPolynomial.X i ^ n),
      Submodule.mem_map.mpr ⟨MvPolynomial.X i ^ n,
        MvPolynomial.isHomogeneous_X_pow i n, rfl⟩⟩
  refine ⟨x, ?_⟩
  intro hx
  have hx' : Ideal.Quotient.mk P (MvPolynomial.X i ^ n) = 0 :=
    congrArg Subtype.val hx
  exact hi (hP.mem_of_pow_mem n (Ideal.Quotient.eq_zero_iff_mem.mp hx'))

theorem polynomial_leadingCoeff_nonneg_of_eventually_nonneg
    (p : Polynomial ℚ) (N : ℕ)
    (hp : ∀ n : ℕ, N ≤ n → 0 ≤ p.eval (n : ℚ)) :
    0 ≤ p.leadingCoeff := by
  by_cases hd : p.natDegree = 0
  · have he : p = Polynomial.C p.leadingCoeff := by
      simpa [Polynomial.leadingCoeff, hd] using Polynomial.eq_C_of_natDegree_eq_zero hd
    have hconst := hp N le_rfl
    rw [he, Polynomial.eval_C] at hconst
    exact hconst
  · by_contra hneg
    have hneg' : p.leadingCoeff < 0 := lt_of_not_ge hneg
    have hdeg : 0 < p.degree := Polynomial.natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hd)
    have ht : Tendsto (fun n : ℕ => p.eval (n : ℚ)) atTop atBot :=
      (p.tendsto_atBot_of_leadingCoeff_nonpos hdeg hneg'.le).comp
        tendsto_natCast_atTop_atTop
    obtain ⟨n, hnN, hn⟩ := ((eventually_ge_atTop N).and
      (ht.eventually_lt_atBot 0)).exists
    exact (not_lt_of_ge (hp n hnN)) hn

theorem polynomial_leadingCoeff_pos_of_eventually_pos
    (p : Polynomial ℚ) (N : ℕ)
    (hp : ∀ n : ℕ, N ≤ n → 0 < p.eval (n : ℚ)) :
    0 < p.leadingCoeff := by
  have hn := polynomial_leadingCoeff_nonneg_of_eventually_nonneg p N
    (fun n hn => (hp n hn).le)
  have hp0 : p ≠ 0 := by
    intro h
    simpa [h] using hp N le_rfl
  exact lt_of_le_of_ne hn (Polynomial.leadingCoeff_ne_zero.mpr hp0).symm

theorem factorial_leadingCoeff_is_integer
    (p : Polynomial ℚ) (values : ℕ → ℕ) (N : ℕ)
    (hp : ∀ n : ℕ, N ≤ n → p.eval (n : ℚ) = (values n : ℚ)) :
    ∃ z : ℤ, (z : ℚ) = p.leadingCoeff * (p.natDegree.factorial : ℚ) := by
  let d := p.natDegree
  let z : ℤ := ∑ j ∈ Finset.range (d + 1),
    ((-1 : ℤ) ^ (d-j) * (d.choose j : ℤ)) * (values (N+j) : ℤ)
  refine ⟨z, ?_⟩
  have hd := congrFun p.fwdDiff_iter_degree_eq_factorial (N : ℚ)
  rw [fwdDiff_iter_eq_sum_shift] at hd
  have he (j : ℕ) : p.eval ((N : ℚ) + j • (1 : ℚ)) = (values (N+j) : ℚ) := by
    simpa using hp (N+j) (Nat.le_add_right N j)
  simp only [he] at hd
  simpa [z, d, Int.cast_sum, Int.cast_mul, Int.cast_pow, zsmul_eq_mul,
    Pi.smul_apply, smul_eq_mul] using hd

theorem eventual_hilbert_degree_ge_one
    (p : Polynomial ℚ) (values : ℕ → ℕ) (N : ℕ)
    (hp : ∀ n : ℕ, N ≤ n → p.eval (n : ℚ) = (values n : ℚ))
    (hv : ∀ n : ℕ, N ≤ n → 0 < values n) :
    1 ≤ p.leadingCoeff * (p.natDegree.factorial : ℚ) := by
  have hl := polynomial_leadingCoeff_pos_of_eventually_pos p N (by
    intro n hn
    rw [hp n hn]
    exact_mod_cast hv n hn)
  have hpos : 0 < p.leadingCoeff * (p.natDegree.factorial : ℚ) :=
    mul_pos hl (by exact_mod_cast Nat.factorial_pos p.natDegree)
  obtain ⟨z, hz⟩ := factorial_leadingCoeff_is_integer p values N hp
  have hzpos : 0 < z := by exact_mod_cast (hz.symm ▸ hpos)
  have hzge : (1 : ℤ) ≤ z := by omega
  rw [← hz]
  exact_mod_cast hzge

theorem prime_eventual_hilbert_degree_ge_one
    (P : Ideal (MvPolynomial σ k)) [P.IsPrime]
    (i : σ) (hi : MvPolynomial.X i ∉ P)
    (p : Polynomial ℚ) (N : ℕ)
    (hp : ∀ n : ℕ, N ≤ n → p.eval (n : ℚ) =
      (Module.finrank k (quotientSection P n) : ℚ)) :
    1 ≤ p.leadingCoeff * (p.natDegree.factorial : ℚ) :=
  eventual_hilbert_degree_ge_one p _ N hp
    (fun n _ => prime_quotientSection_finrank_pos P i hi n)

theorem prime_eventual_hilbert_coefficient_ge_one
    (P : Ideal (MvPolynomial σ k)) [P.IsPrime]
    (i : σ) (hi : MvPolynomial.X i ∉ P)
    (p : Polynomial ℚ) (N d : ℕ)
    (hp : ∀ n : ℕ, N ≤ n → p.eval (n : ℚ) =
      (Module.finrank k (quotientSection P n) : ℚ))
    (hd : p.natDegree = d) :
    1 ≤ p.coeff d * (d.factorial : ℚ) := by
  simpa [Polynomial.leadingCoeff, hd] using
    prime_eventual_hilbert_degree_ge_one P i hi p N hp

end WeightedTorusJets.W27

end

noncomputable section
namespace WeightedTorusJets.W25

open MvPolynomial DirectSum
open WeightedTorusJets.W24 WeightedTorusJets.W64

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k]

theorem restrictTotalDegree_eq_iSup_homogeneous (n : ℕ) :
    restrictTotalDegree σ k n =
      ⨆ j : Fin (n + 1), homogeneousSubmodule σ k j.val := by
  classical
  apply le_antisymm
  · intro p hp
    have hpdegree : p.totalDegree ≤ n := (mem_restrictTotalDegree σ _ _).mp hp
    have hsum : (∑ j ∈ Finset.range (p.totalDegree + 1), homogeneousComponent j p) ∈
        ⨆ j : Fin (n + 1), homogeneousSubmodule σ k j.val := by
      apply Submodule.sum_mem
      intro j hj
      have hjdegree : j ≤ n :=
        (Nat.le_of_lt_succ (Finset.mem_range.mp hj)).trans hpdegree
      exact (le_iSup (fun a : Fin (n + 1) => homogeneousSubmodule σ k a.val)
        ⟨j, Nat.lt_succ_of_le hjdegree⟩) (homogeneousComponent_mem j p)
    simpa only [sum_homogeneousComponent] using hsum
  · apply iSup_le
    intro j p hp
    apply (mem_restrictTotalDegree σ _ _).mpr
    exact (show p.IsHomogeneous j.val from hp).totalDegree_le.trans
      (Nat.le_of_lt_succ j.isLt)

theorem quotientDegreeFiltration_eq_iSup_sections
    (I : Ideal (MvPolynomial σ k)) (n : ℕ) :
    quotientDegreeFiltration I n =
      ⨆ j : Fin (n + 1), quotientSection I j.val := by
  unfold quotientDegreeFiltration quotientSection
  rw [restrictTotalDegree_eq_iSup_homogeneous, Submodule.map_iSup]

theorem cumulativeSectionMap_injective (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) (n : ℕ) :
    Function.Injective
      (DirectSum.coeLinearMap (fun j : Fin (n + 1) => quotientSection I j.val)) :=
  ((quotientSection_iSupIndep I hI).comp Fin.val_injective).dfinsupp_lsum_injective

theorem cumulativeSectionMap_range (I : Ideal (MvPolynomial σ k)) (n : ℕ) :
    LinearMap.range
        (DirectSum.coeLinearMap (fun j : Fin (n + 1) => quotientSection I j.val)) =
      quotientDegreeFiltration I n := by
  rw [DirectSum.range_coeLinearMap, quotientDegreeFiltration_eq_iSup_sections]

def cumulativeHomogeneousQuotientEquiv (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) (n : ℕ) :
    (⨁ j : Fin (n + 1), quotientSection I j.val) ≃ₗ[k]
      quotientDegreeFiltration I n :=
  (LinearEquiv.ofInjective
    (DirectSum.coeLinearMap (fun j : Fin (n + 1) => quotientSection I j.val))
    (cumulativeSectionMap_injective I hI n)).trans
      (LinearEquiv.ofEq _ _ (cumulativeSectionMap_range I n))

@[simp] theorem cumulativeHomogeneousQuotientEquiv_apply
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) (n : ℕ)
    (x : ⨁ j : Fin (n + 1), quotientSection I j.val) :
    (cumulativeHomogeneousQuotientEquiv I hI n x : MvPolynomial σ k ⧸ I) =
      DirectSum.coeLinearMap (fun j : Fin (n + 1) => quotientSection I j.val) x := rfl

variable [Finite σ]

theorem quotientDegreeFiltration_finrank_eq_sum_fin
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) (n : ℕ) :
    Module.finrank k (quotientDegreeFiltration I n) =
      ∑ j : Fin (n + 1), Module.finrank k (quotientSection I j.val) := by
  rw [← (cumulativeHomogeneousQuotientEquiv I hI n).finrank_eq,
    Module.finrank_directSum]

theorem quotientDegreeFiltration_finrank_eq_sum
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) (n : ℕ) :
    Module.finrank k (quotientDegreeFiltration I n) =
      ∑ j ∈ Finset.range (n + 1), Module.finrank k (quotientSection I j) := by
  rw [quotientDegreeFiltration_finrank_eq_sum_fin I hI n]
  exact Fin.sum_univ_eq_sum_range
    (fun j : ℕ => Module.finrank k (quotientSection I j)) (n + 1)

end WeightedTorusJets.W25

end

section

namespace WeightedTorusJets.W24

open Polynomial

theorem natDegree_le_of_eventual_polynomial_le (p q : Polynomial ℚ)
    (hp : 0 < p.leadingCoeff) (N : ℕ)
    (hle : ∀ n : ℕ, N ≤ n → p.eval (n : ℚ) ≤ q.eval (n : ℚ)) :
    p.natDegree ≤ q.natDegree := by
  by_contra hn
  have hdeg : q.degree < p.degree := degree_lt_degree (Nat.lt_of_not_ge hn)
  have hnonneg := W27.polynomial_leadingCoeff_nonneg_of_eventually_nonneg
    (q - p) N (fun n hn => by simpa only [eval_sub] using sub_nonneg.mpr (hle n hn))
  rw [leadingCoeff_sub_of_degree_lt' hdeg] at hnonneg
  exact (not_le_of_gt hp) (neg_nonneg.mp hnonneg)

theorem natDegree_affine_comp_le (p : Polynomial ℚ) (a b : ℚ) :
    (p.comp (C a * X + C b)).natDegree ≤ p.natDegree := by
  have ha : (C a * X + C b : Polynomial ℚ).natDegree ≤ 1 := by
    rw [natDegree_add_C]
    simpa only [natDegree_X] using natDegree_C_mul_le a (X : Polynomial ℚ)
  exact (natDegree_comp_le).trans ((Nat.mul_le_mul_left _ ha).trans_eq (Nat.mul_one _))

theorem natDegree_eq_of_polynomial_growth_bounds
    (q lower upper : Polynomial ℚ) (d : ℕ)
    (hql : 0 < q.leadingCoeff) (hll : 0 < lower.leadingCoeff)
    (hld : lower.natDegree = d) (hud : upper.natDegree ≤ d)
    (a b c e : ℚ) (N : ℕ)
    (hlo : ∀ n : ℕ, N ≤ n → lower.eval (n : ℚ) ≤ q.eval (a * n + b))
    (hup : ∀ n : ℕ, N ≤ n → q.eval (n : ℚ) ≤ upper.eval (c * n + e)) :
    q.natDegree = d := by
  have hlow : lower.natDegree ≤ (q.comp (C a * X + C b)).natDegree :=
    natDegree_le_of_eventual_polynomial_le lower _ hll N (by
      simpa only [eval_comp, eval_add, eval_mul, eval_C, eval_X] using hlo)
  have hupp : q.natDegree ≤ (upper.comp (C c * X + C e)).natDegree :=
    natDegree_le_of_eventual_polynomial_le q _ hql N (by
      simpa only [eval_comp, eval_add, eval_mul, eval_C, eval_X] using hup)
  exact le_antisymm
    (hupp.trans ((natDegree_affine_comp_le upper c e).trans hud))
    (hld ▸ hlow.trans (natDegree_affine_comp_le q a b))

end WeightedTorusJets.W24

end

section

namespace WeightedTorusJets.W24

open MvPolynomial Polynomial Finset
open WeightedTorusJets.W64

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k] [Fintype σ]

theorem normalization_binomial_lower_bound (s : ℕ)
    (I : Ideal (MvPolynomial σ k))
    (g : MvPolynomial (Fin s) k →ₐ[k] (MvPolynomial σ k ⧸ I))
    (hg : Function.Injective g) (F : Fin s → MvPolynomial σ k)
    (hF : ∀ i, Ideal.Quotient.mk I (F i) = g (MvPolynomial.X i))
    (D : ℕ) (hD : ∀ i, (F i).totalDegree ≤ D) (m : ℕ) :
    (m + s).choose s ≤ Module.finrank k (quotientDegreeFiltration I (D * m)) := by
  let L : restrictTotalDegree (Fin s) k m →ₗ[k]
      quotientDegreeFiltration I (D * m) :=
    { toFun := fun p => ⟨g p, by
        simpa only [Nat.mul_comm D m] using
          normalization_mem_quotientDegreeFiltration I g F hF D hD m p
            ((mem_restrictTotalDegree _ _ _).mp p.property)⟩
      map_add' := fun p q => Subtype.ext (g.map_add p q)
      map_smul' := fun c p => Subtype.ext (g.toLinearMap.map_smul c p) }
  rw [← W32.finrank_restrictTotalDegree k s m]
  exact LinearMap.finrank_le_finrank_of_injective (f := L)
    (fun p q h => Subtype.ext (hg (congrArg Subtype.val h)))

theorem normalization_binomial_lower_growth (s : ℕ)
    (I : Ideal (MvPolynomial σ k))
    (g : MvPolynomial (Fin s) k →ₐ[k] (MvPolynomial σ k ⧸ I))
    (hg : Function.Injective g) :
    ∃ D : ℕ, 0 < D ∧ ∀ m : ℕ,
      (m + s).choose s ≤ Module.finrank k (quotientDegreeFiltration I (D * m)) := by
  classical
  choose F hF using fun i : Fin s => Ideal.Quotient.mk_surjective (g (MvPolynomial.X i))
  let D := max (Finset.univ.sup fun i => (F i).totalDegree) 1
  have hD : ∀ i, (F i).totalDegree ≤ D := fun i =>
    (Finset.le_sup (f := fun j : Fin s => (F j).totalDegree)
      (Finset.mem_univ i)).trans (le_max_left _ _)
  exact ⟨D, lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _),
    normalization_binomial_lower_bound s I g hg F hF D hD⟩

theorem prime_quotientDegreeFiltration_finrank_pos
    (P : Ideal (MvPolynomial σ k)) [P.IsPrime]
    (hP : P.IsHomogeneous (homogeneousSubmodule σ k))
    (i : σ) (hi : MvPolynomial.X i ∉ P) (n : ℕ) :
    0 < Module.finrank k (quotientDegreeFiltration P n) := by
  rw [W25.quotientDegreeFiltration_finrank_eq_sum P hP n]
  exact (W27.prime_quotientSection_finrank_pos P i hi 0).trans_le
    (Finset.single_le_sum (s := Finset.range (n + 1)) (a := 0)
      (f := fun j => Module.finrank k (quotientSection P j))
      (fun j _ => Nat.zero_le _) (Finset.mem_range.mpr (Nat.zero_lt_succ n)))

theorem prime_hilbert_natDegree_add_one_eq_krullDim
    (P : Ideal (MvPolynomial σ k)) [P.IsPrime]
    (hP : P.IsHomogeneous (homogeneousSubmodule σ k))
    (i : σ) (hi : MvPolynomial.X i ∉ P)
    (p : Polynomial ℚ) (N : ℕ)
    (hp : ∀ n : ℕ, N ≤ n → p.eval (n : ℚ) =
      (Module.finrank k (quotientSection P n) : ℚ)) :
    (p.natDegree + 1 : WithBot ℕ∞) = ringKrullDim (MvPolynomial σ k ⧸ P) := by
  have hpl : 0 < p.leadingCoeff :=
    W27.polynomial_leadingCoeff_pos_of_eventually_pos p N (by
      intro n hn
      rw [hp n hn]
      exact_mod_cast W27.prime_quotientSection_finrank_pos P i hi n)
  have hp0 : p ≠ 0 := leadingCoeff_ne_zero.mp (ne_of_gt hpl)
  obtain ⟨q, hqd, hq⟩ := exists_eventual_cumulative_polynomial
    (fun n => Module.finrank k (quotientSection P n)) p hp0 N hp
  have hqv (n : ℕ) (hn : N ≤ n) :
      q.eval (n : ℚ) = (Module.finrank k (quotientDegreeFiltration P n) : ℚ) := by
    rw [hq n hn, W25.quotientDegreeFiltration_finrank_eq_sum P hP n]
  have hql : 0 < q.leadingCoeff :=
    W27.polynomial_leadingCoeff_pos_of_eventually_pos q N (by
      intro n hn
      rw [hqv n hn]
      exact_mod_cast prime_quotientDegreeFiltration_finrank_pos P hP i hi n)
  obtain ⟨s, g, hg, hfin, hdim⟩ :=
    exists_finite_normalization_with_dimension k (MvPolynomial σ k ⧸ P)
  obtain ⟨D, hD, hlo⟩ := normalization_binomial_lower_growth s P g hg
  obtain ⟨C, E, hC, hup⟩ := W29.finite_normalization_upper_growth P g hfin
  have hdeg : q.natDegree = s := natDegree_eq_of_polynomial_growth_bounds
      q (W32.polynomialGrowth s) (W32.scaledPolynomialGrowth C s) s
      hql (W32.polynomialGrowth_leadingCoeff_pos s)
      (W32.polynomialGrowth_natDegree s) (W32.scaledPolynomialGrowth_natDegree_le C s)
      (D : ℚ) 0 (C : ℚ) (E : ℚ) N (by
        intro n hn
        have hDn : N ≤ D * n := hn.trans (by nlinarith)
        rw [add_zero, ← Nat.cast_mul, hqv (D * n) hDn, W32.polynomialGrowth_eval]
        exact_mod_cast hlo n) (by
        intro n hn
        rw [hqv n hn, ← Nat.cast_mul, ← Nat.cast_add,
          W32.scaledPolynomialGrowth_eval_finrank k C s (C * n + E)]
        exact_mod_cast hup n)
  rw [hdim, ← hdeg, hqd]
  norm_cast

theorem exists_prime_hilbert_polynomial_with_dimension
    (P : Ideal (MvPolynomial σ k)) [P.IsPrime]
    (hP : P.IsHomogeneous (homogeneousSubmodule σ k))
    (i : σ) (hi : MvPolynomial.X i ∉ P) :
    ∃ p : Polynomial ℚ,
      (∃ N : ℕ, ∀ n : ℕ, N ≤ n → p.eval (n : ℚ) =
        (Module.finrank k (quotientSection P n) : ℚ)) ∧
      (p.natDegree + 1 : WithBot ℕ∞) = ringKrullDim (MvPolynomial σ k ⧸ P) := by
  obtain ⟨p, N, hp⟩ := exists_homogeneous_hilbert_polynomial σ P hP
  have hp' (n : ℕ) (hn : N + 1 ≤ n) := (hp n (by omega)).symm
  exact ⟨p, ⟨N + 1, hp'⟩,
    prime_hilbert_natDegree_add_one_eq_krullDim P hP i hi p (N + 1) hp'⟩

end WeightedTorusJets.W24

end

end SiegelZeros

end OAI
