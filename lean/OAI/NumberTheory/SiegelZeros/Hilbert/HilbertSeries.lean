import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Structure.DegreeMap

namespace OAI

namespace SiegelZeros

section
open MvPolynomial
noncomputable section
open scoped BigOperators
open scoped BigOperators
namespace PowerSeries

open _root_.PowerSeries

variable {F : Type*} [Field F]

theorem coeff_mul_invOneSubPow_one (S : PowerSeries F) (n : ℕ) :
    (S * invOneSubPow F 1).coeff n = ∑ j ∈ Finset.range (n + 1), S.coeff j := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [invOneSubPow]

theorem sum_coeff_mul_invOneSubPow (p : Polynomial F) (d n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), (p * invOneSubPow F d : PowerSeries F).coeff j) =
      (p * invOneSubPow F (d + 1) : PowerSeries F).coeff n := by
  rw [← coeff_mul_invOneSubPow_one, invOneSubPow_add, Units.val_mul, mul_assoc]

theorem sum_coeff_mul_invOneSubPow_eq_hilbertPoly_eval [CharZero F] (p : Polynomial F)
    (d : ℕ) {n : ℕ} (hn : p.natDegree < n) :
    (∑ j ∈ Finset.range (n + 1), (p * invOneSubPow F d : PowerSeries F).coeff j) =
      (Polynomial.hilbertPoly p (d + 1)).eval (n : F) := by
  rw [sum_coeff_mul_invOneSubPow]
  exact Polynomial.coeff_mul_invOneSubPow_eq_hilbertPoly_eval _ hn

theorem exists_reduced_mul_invOneSubPow (p : Polynomial F) (d : ℕ) :
    ∃ q : Polynomial F, ∃ e : ℕ,
      (p * invOneSubPow F d : PowerSeries F) = q * invOneSubPow F e ∧
        (e = 0 ∨ q.eval 1 ≠ 0) := by
  induction d generalizing p with
  | zero => exact ⟨p, 0, rfl, Or.inl rfl⟩
  | succ d ih =>
    by_cases hp : p.eval 1 = 0
    · obtain ⟨q, hq⟩ := Polynomial.dvd_iff_isRoot.mpr hp
      have hfactor : p = (1 - Polynomial.X) * (-q) := by
        rw [hq]
        simp only [Polynomial.C_1]
        ring
      have hcancel : (p * invOneSubPow F (d + 1) : PowerSeries F) =
          (-q : Polynomial F) * invOneSubPow F d := by
        rw [hfactor, Polynomial.coe_mul, Polynomial.coe_sub,
          Polynomial.coe_one, Polynomial.coe_X]
        calc
          _ = ((-q : Polynomial F) : PowerSeries F) *
              ((1 - PowerSeries.X) ^ 1 * (invOneSubPow F (d + 1)).val) := by ring
          _ = _ := by rw [one_sub_pow_mul_invOneSubPow_val_add_eq_invOneSubPow_val]
      obtain ⟨r, e, hre, he⟩ := ih (-q)
      exact ⟨r, e, hcancel.trans hre, he⟩
    · exact ⟨p, d + 1, rfl, Or.inr hp⟩

end PowerSeries

namespace WeightedTorusJets.Geometry.GradedQuotient

open MvPolynomial

variable {K σ : Type*} [Field K] [Finite σ]

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable def hilbertSeries (I : Ideal (MvPolynomial σ K)) : PowerSeries ℚ :=
  PowerSeries.mk fun n ↦ (Module.finrank K (degreePiece I n) : ℚ)

theorem hilbertSeries_eq_add_X_mul_colon {I : Ideal (MvPolynomial σ K)}
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) (i : σ) :
    hilbertSeries I = hilbertSeries (I ⊔ Ideal.span {X i}) +
      PowerSeries.X * hilbertSeries (I.colon {X i}) := by
  ext n
  rw [map_add, ← pow_one (PowerSeries.X : PowerSeries ℚ), PowerSeries.coeff_X_pow_mul']
  simp only [hilbertSeries, PowerSeries.coeff_mk]
  have h := finrank_degreePiece_sup_span_add_colon hI (isHomogeneous_X K i) n
  split_ifs with hn
  · rw [ite_eq_left hn] at h
    exact_mod_cast h.symm
  · rw [ite_eq_right hn, add_zero] at h
    simpa only [add_zero] using congrArg (Nat.cast : ℕ → ℚ) h.symm

theorem exists_hilbertSeries_numerator (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) :
    ∃ d : ℕ, ∃ p : Polynomial ℚ,
      (1 - PowerSeries.X) ^ d * hilbertSeries I = (p : PowerSeries ℚ) := by
  apply hilbertRational_of_noetherian_recurrence hilbertSeries
    (fun J ↦ J.IsHomogeneous (homogeneousSubmodule σ K)) ?_ I hI
  intro J hJ
  by_cases hvars : ∀ i : σ, X i ∈ J
  · left
    have hconstant : hilbertSeries J =
        (Polynomial.C (Module.finrank K (degreePiece J 0) : ℚ) : PowerSeries ℚ) := by
      ext n
      cases n with
      | zero => simp [hilbertSeries]
      | succ n =>
        simp [hilbertSeries, finrank_degreePiece_eq_zero_of_variables_mem J hvars (Nat.succ_pos n)]
    rw [hconstant]
    exact HilbertRational.polynomial _
  · right
    push Not at hvars
    obtain ⟨i, hi⟩ := hvars
    refine ⟨J ⊔ Ideal.span {X i}, J.colon {X i}, ?_, Ideal.le_colon,
      ?_, colon_isHomogeneous hJ (isHomogeneous_X K i),
      hilbertSeries_eq_add_X_mul_colon hJ i⟩
    · refine lt_of_le_of_ne le_sup_left ?_
      intro heq
      apply hi
      rw [heq]
      exact (le_sup_right : Ideal.span {X i} ≤ J ⊔ Ideal.span {X i})
        (Ideal.subset_span (Set.mem_singleton (X i)))
    · apply hJ.sup
      apply Ideal.homogeneous_span
      intro f hf
      rcases hf with rfl
      exact ⟨1, isHomogeneous_X K i⟩

theorem exists_hilbertSeries_eq_mul_invOneSubPow (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) :
    ∃ p : Polynomial ℚ, ∃ d : ℕ,
      hilbertSeries I = p * PowerSeries.invOneSubPow ℚ d :=
  HilbertRational.exists_mul_invOneSubPow (exists_hilbertSeries_numerator I hI)

theorem existsUnique_hilbertPolynomial (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) :
    ∃! P : Polynomial ℚ, ∃ N : ℕ, ∀ n > N,
      (Module.finrank K (degreePiece I n) : ℚ) = P.eval (n : ℚ) := by
  obtain ⟨p, d, hpd⟩ := exists_hilbertSeries_eq_mul_invOneSubPow I hI
  have h := Polynomial.existsUnique_hilbertPoly p d
  simpa only [← hpd, hilbertSeries, PowerSeries.coeff_mk] using h

noncomputable def hilbertPolynomial (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) : Polynomial ℚ :=
  (existsUnique_hilbertPolynomial I hI).choose

theorem hilbertPolynomial_spec (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) :
    ∃ N : ℕ, ∀ n > N,
      (Module.finrank K (degreePiece I n) : ℚ) = (hilbertPolynomial I hI).eval (n : ℚ) :=
  (existsUnique_hilbertPolynomial I hI).choose_spec.1

theorem hilbertPolynomial_eq_of_eventual_eval (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) {P : Polynomial ℚ}
    (hP : ∃ N : ℕ, ∀ n > N,
      (Module.finrank K (degreePiece I n) : ℚ) = P.eval (n : ℚ)) :
    hilbertPolynomial I hI = P :=
  ((existsUnique_hilbertPolynomial I hI).choose_spec.2 P hP).symm

theorem exists_component_cumulative_hilbertPoly (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) :
    ∃ p : Polynomial ℚ, ∃ d : ℕ, ∀ n > p.natDegree,
      (Module.finrank K (degreePiece I n) : ℚ) =
          (Polynomial.hilbertPoly p d).eval (n : ℚ) ∧
      (∑ j ∈ Finset.range (n + 1), (Module.finrank K (degreePiece I j) : ℚ)) =
          (Polynomial.hilbertPoly p (d + 1)).eval (n : ℚ) := by
  obtain ⟨p, d, hpd⟩ := exists_hilbertSeries_eq_mul_invOneSubPow I hI
  refine ⟨p, d, fun n hn ↦ ⟨?_, ?_⟩⟩
  · have h := Polynomial.coeff_mul_invOneSubPow_eq_hilbertPoly_eval (p := p) d hn
    simpa only [← hpd, hilbertSeries, PowerSeries.coeff_mk] using h
  · have h := PowerSeries.sum_coeff_mul_invOneSubPow_eq_hilbertPoly_eval p d hn
    simpa only [← hpd, hilbertSeries, PowerSeries.coeff_mk] using h

theorem exists_reduced_hilbertSeries (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) :
    ∃ p : Polynomial ℚ, ∃ d : ℕ,
      hilbertSeries I = p * PowerSeries.invOneSubPow ℚ d ∧
        (d = 0 ∨ p.eval 1 ≠ 0) := by
  obtain ⟨p, d, hpd⟩ := exists_hilbertSeries_eq_mul_invOneSubPow I hI
  obtain ⟨q, e, hqe, hred⟩ := PowerSeries.exists_reduced_mul_invOneSubPow p d
  exact ⟨q, e, hpd.trans hqe, hred⟩

theorem exists_cumulative_hilbertPolynomial (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K))
    (hne : hilbertPolynomial I hI ≠ 0) :
    ∃ Q : Polynomial ℚ,
      (∃ N : ℕ, ∀ n > N,
        (∑ j ∈ Finset.range (n + 1), (Module.finrank K (degreePiece I j) : ℚ)) =
          Q.eval (n : ℚ)) ∧
      Q.natDegree = (hilbertPolynomial I hI).natDegree + 1 ∧
      Q.leadingCoeff = (hilbertPolynomial I hI).leadingCoeff /
        ((hilbertPolynomial I hI).natDegree + 1 : ℚ) := by
  obtain ⟨p, d, hpd, hred⟩ := exists_reduced_hilbertSeries I hI
  have hP : hilbertPolynomial I hI = Polynomial.hilbertPoly p d := by
    apply hilbertPolynomial_eq_of_eventual_eval
    refine ⟨p.natDegree, fun n hn ↦ ?_⟩
    have h := Polynomial.coeff_mul_invOneSubPow_eq_hilbertPoly_eval (p := p) d hn
    simpa only [← hpd, hilbertSeries, PowerSeries.coeff_mk] using h
  have hd : d ≠ 0 := by
    intro hd
    apply hne
    rw [hP, hd, Polynomial.hilbertPoly_zero_right]
  obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd
  have hp : p.eval 1 ≠ 0 := hred.resolve_left hd
  refine ⟨Polynomial.hilbertPoly p (e + 2), ⟨p.natDegree, fun n hn ↦ ?_⟩, ?_, ?_⟩
  · have h := PowerSeries.sum_coeff_mul_invOneSubPow_eq_hilbertPoly_eval p (e + 1) hn
    simpa only [← hpd, hilbertSeries, PowerSeries.coeff_mk] using h
  · simp only [hP, show e + 2 = (e + 1) + 1 by omega,
      Polynomial.natDegree_hilbertPoly_succ_of_eval_one_ne_zero hp]
  · rw [hP, Polynomial.natDegree_hilbertPoly_succ_of_eval_one_ne_zero hp]
    rw [show e + 2 = (e + 1) + 1 by omega]
    rw [Polynomial.leadingCoeff_hilbertPoly_succ_of_eval_one_ne_zero hp,
      Polynomial.leadingCoeff_hilbertPoly_succ_of_eval_one_ne_zero hp]
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    rw [div_div]
    congr 1
    ring

end WeightedTorusJets.Geometry.GradedQuotient

open Filter

namespace WeightedTorusJets.Geometry

theorem leadingCoeff_pos_of_eventually_nat_eval_nonneg (P : Polynomial ℚ) (hP : P ≠ 0)
    (hpos : ∀ᶠ n : ℕ in atTop, 0 ≤ P.eval (n : ℚ)) : 0 < P.leadingCoeff := by
  by_contra h
  have hneg : P.leadingCoeff < 0 :=
    lt_of_le_of_ne (le_of_not_gt h) (Polynomial.leadingCoeff_ne_zero.mpr hP)
  by_cases hdeg : 0 < P.degree
  · have hlim : Tendsto (fun n : ℕ => P.eval (n : ℚ)) atTop atBot :=
      (P.tendsto_atBot_of_leadingCoeff_nonpos hdeg hneg.le).comp tendsto_natCast_atTop_atTop
    obtain ⟨n, hn, hn'⟩ := (hpos.and (hlim.eventually_lt_atBot 0)).exists
    exact hn'.not_ge hn
  · obtain ⟨n, hn⟩ := hpos.exists
    have hconst : P.eval (n : ℚ) = P.leadingCoeff := by
      rw [Polynomial.eq_C_of_degree_le_zero (le_of_not_gt hdeg)]
      simp
    exact hneg.not_ge (hconst ▸ hn)

end WeightedTorusJets.Geometry

open scoped BigOperators

namespace WeightedTorusJets.Geometry

theorem numerator_eval_one_is_integer (S : PowerSeries ℚ)
    (hS : ∀ n : ℕ, ∃ z : ℤ, (z : ℚ) = S.coeff n)
    (q : Polynomial ℚ) (d : ℕ)
    (hclear : (1 - PowerSeries.X) ^ d * S = (q : PowerSeries ℚ)) :
    ∃ z : ℤ, (z : ℚ) = q.eval 1 := by
  classical
  choose a ha using hS
  let T : PowerSeries ℤ := PowerSeries.mk a
  have hT : PowerSeries.map (Int.castRingHom ℚ) T = S := by
    ext n
    simpa only [T, PowerSeries.coeff_map, PowerSeries.coeff_mk, Int.coe_castRingHom] using ha n
  let U : PowerSeries ℤ := (1 - PowerSeries.X) ^ d * T
  have hU : PowerSeries.map (Int.castRingHom ℚ) U = (q : PowerSeries ℚ) := by
    simpa only [U, map_mul, map_pow, map_sub, map_one, PowerSeries.map_X, hT] using hclear
  refine ⟨∑ n ∈ q.support, U.coeff n, ?_⟩
  rw [Int.cast_sum, Polynomial.eval_eq_sum, Polynomial.sum_def]
  apply Finset.sum_congr rfl
  intro n _
  simpa only [one_pow, mul_one, PowerSeries.coeff_map, Int.coe_castRingHom,
    Polynomial.coeff_coe] using congrArg (fun P : PowerSeries ℚ => P.coeff n) hU

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry.GradedQuotient

open MvPolynomial Filter

attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_pos_integer_factorial_mul_leadingCoeff_hilbertPolynomial
    {K σ : Type*} [Field K] [Finite σ]
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K))
    (hne : hilbertPolynomial I hI ≠ 0) :
    ∃ z : ℤ, 0 < z ∧ (z : ℚ) =
      ((hilbertPolynomial I hI).natDegree.factorial : ℚ) *
        (hilbertPolynomial I hI).leadingCoeff := by
  obtain ⟨p, d, hpd, hred⟩ := exists_reduced_hilbertSeries I hI
  have hP : hilbertPolynomial I hI = Polynomial.hilbertPoly p d := by
    apply hilbertPolynomial_eq_of_eventual_eval
    refine ⟨p.natDegree, fun n hn ↦ ?_⟩
    have h := Polynomial.coeff_mul_invOneSubPow_eq_hilbertPoly_eval (p := p) d hn
    simpa only [← hpd, hilbertSeries, PowerSeries.coeff_mk] using h
  have hd : d ≠ 0 := by
    intro hd
    apply hne
    rw [hP, hd, Polynomial.hilbertPoly_zero_right]
  have hp : p.eval 1 ≠ 0 := hred.resolve_left hd
  have hclear : (1 - PowerSeries.X) ^ d * hilbertSeries I = (p : PowerSeries ℚ) := by
    rw [hpd, ← PowerSeries.invOneSubPow_inv_eq_one_sub_pow]
    simp only [mul_left_comm (PowerSeries.invOneSubPow ℚ d).inv,
      Units.inv_val, mul_one]
  obtain ⟨z, hz⟩ := numerator_eval_one_is_integer (hilbertSeries I)
    (fun n => ⟨(Module.finrank K (degreePiece I n) : ℤ), by simp [hilbertSeries]⟩) p d hclear
  have heq : ((hilbertPolynomial I hI).natDegree.factorial : ℚ) *
      (hilbertPolynomial I hI).leadingCoeff = p.eval 1 := by
    obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd
    rw [hP, Polynomial.natDegree_hilbertPoly_succ_of_eval_one_ne_zero hp,
      Polynomial.factorial_mul_leadingCoeff_hilbertPoly_succ hp]
  have hlead : 0 < (hilbertPolynomial I hI).leadingCoeff := by
    apply leadingCoeff_pos_of_eventually_nat_eval_nonneg _ hne
    obtain ⟨N, hN⟩ := hilbertPolynomial_spec I hI
    filter_upwards [eventually_gt_atTop N] with n hn
    rw [← hN n hn]
    positivity
  refine ⟨z, ?_, hz.trans heq.symm⟩
  have hpos : 0 < (z : ℚ) := by
    rw [hz, ← heq]
    exact mul_pos (by positivity) hlead
  exact_mod_cast hpos

end WeightedTorusJets.Geometry.GradedQuotient

namespace WeightedTorusJets.Geometry.GradedQuotient

open MvPolynomial

variable {K σ : Type*} [Field K] [Finite σ]

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable def projectiveDegree (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) : ℕ :=
  if h : hilbertPolynomial I hI = 0 then 0
  else (exists_pos_integer_factorial_mul_leadingCoeff_hilbertPolynomial I hI h).choose.toNat

theorem projectiveDegree_cast (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) :
    (projectiveDegree I hI : ℚ) =
      ((hilbertPolynomial I hI).natDegree.factorial : ℚ) *
        (hilbertPolynomial I hI).leadingCoeff := by
  unfold projectiveDegree
  split_ifs with h
  · simp [h]
  · have hz := (exists_pos_integer_factorial_mul_leadingCoeff_hilbertPolynomial I hI h).choose_spec
    have hcast := Int.toNat_of_nonneg hz.1.le
    exact (by exact_mod_cast hcast :
      ((exists_pos_integer_factorial_mul_leadingCoeff_hilbertPolynomial I hI h).choose.toNat : ℚ) =
        ((exists_pos_integer_factorial_mul_leadingCoeff_hilbertPolynomial I hI h).choose : ℚ)).trans hz.2

theorem projectiveDegree_pos_iff (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) :
    0 < projectiveDegree I hI ↔ hilbertPolynomial I hI ≠ 0 := by
  constructor
  · intro hpos hzero
    simp [projectiveDegree, hzero] at hpos
  · intro hne
    rw [projectiveDegree, dite_eq_right hne]
    have hz := (exists_pos_integer_factorial_mul_leadingCoeff_hilbertPolynomial I hI hne).choose_spec.1
    omega

theorem projectiveDegree_eq_zero_iff (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) :
    projectiveDegree I hI = 0 ↔ hilbertPolynomial I hI = 0 := by
  simpa only [not_lt, Nat.le_zero, not_not] using not_congr (projectiveDegree_pos_iff I hI)

end WeightedTorusJets.Geometry.GradedQuotient

end
end


namespace WeightedTorusJets

open DirectSum

variable {K A M : Type*} [Field K] [CommRing A] [Algebra K A]
  [AddCommGroup M] [Module K M] [Module A M]
  (𝒜 : ℕ → Submodule K A) [GradedAlgebra 𝒜]
  (ℳ : ℕ → Submodule K M) [DirectSum.Decomposition ℳ]
  [SetLike.GradedSMul 𝒜 ℳ]

theorem decompose_smul_of_homogeneous_right (r : A) {m : M} {j : ℕ}
    (hm : m ∈ ℳ j) (i : ℕ) :
    (decompose ℳ (r • m) (i + j) : M) = (decompose 𝒜 r i : A) • m := by
  refine DirectSum.Decomposition.inductionOn 𝒜 ?_ ?_ ?_ r
  · simp
  · intro k a
    have ham : (a : A) • m ∈ ℳ (k + j) := by
      simpa only [vadd_eq_add] using SetLike.GradedSMul.smul_mem a.2 hm
    by_cases hki : k = i
    · subst k
      rw [decompose_of_mem_same ℳ ham,
        decompose_of_mem_same 𝒜 a.2]
    · rw [decompose_of_mem_ne ℳ ham
        (by omega : k + j ≠ i + j), decompose_of_mem_ne 𝒜 a.2 hki, zero_smul]
  · intro r s hr hs
    simpa only [add_smul, decompose_add, DirectSum.add_apply, Submodule.coe_add] using
      congrArg₂ (· + ·) hr hs

theorem homogeneous_component_smul_mem (N : Submodule A M) (hN : N.IsHomogeneous ℳ)
    {r : A} (hr : ∀ m : M, r • m ∈ N) (i : ℕ) (m : M) :
    (decompose 𝒜 r i : A) • m ∈ N := by
  refine DirectSum.Decomposition.inductionOn ℳ ?_ ?_ ?_ m
  · simp
  · intro j m
    rw [← decompose_smul_of_homogeneous_right 𝒜 ℳ r m.2 i]
    exact hN (i + j) (hr m)
  · intro m n hm hn
    simpa only [smul_add] using N.add_mem hm hn

theorem exists_homogeneous_annihilator_of_annihilator
    (N : Submodule A M) (hN : N.IsHomogeneous ℳ)
    {r : A} (hr0 : r ≠ 0) (hr : ∀ m : M, r • m ∈ N) :
    ∃ s : A, s ≠ 0 ∧ (∃ i : ℕ, s ∈ 𝒜 i) ∧ ∀ m : M, s • m ∈ N := by
  classical
  have hex : ∃ i : ℕ, (decompose 𝒜 r i : A) ≠ 0 := by
    by_contra! h
    apply hr0
    rw [← sum_support_decompose 𝒜 r]
    exact Finset.sum_eq_zero (fun i _ => h i)
  obtain ⟨i, hi⟩ := hex
  exact ⟨decompose 𝒜 r i, hi, ⟨i, (decompose 𝒜 r i).2⟩,
    homogeneous_component_smul_mem 𝒜 ℳ N hN hr i⟩

theorem exists_homogeneous_annihilator_of_rank_zero [IsDomain A]
    (N : Submodule A M) (hN : N.IsHomogeneous ℳ) [Module.Finite A (M ⧸ N)]
    (hrank : Module.rank A (M ⧸ N) = 0) :
    ∃ s : A, s ≠ 0 ∧ (∃ i : ℕ, s ∈ 𝒜 i) ∧ ∀ m : M, s • m ∈ N := by
  have ht : Module.IsTorsion A (M ⧸ N) := by
    intro x
    obtain ⟨r, hr, hx⟩ := rank_eq_zero_iff.mp hrank x
    exact ⟨⟨r, mem_nonZeroDivisors_iff_ne_zero.mpr hr⟩, hx⟩
  obtain ⟨r, hr, hr0⟩ := Submodule.annihilator_top_inter_nonZeroDivisors ht
  apply exists_homogeneous_annihilator_of_annihilator 𝒜 ℳ N hN
    (mem_nonZeroDivisors_iff_ne_zero.mp hr0)
  apply (Module.isTorsionBy_quotient_iff N r).mp
  intro x
  exact Submodule.mem_annihilator.mp hr x Submodule.mem_top

include 𝒜 in

theorem decompose_smul_mem_of_homogeneous (N : Submodule A M)
    (r : A) {m : M} (hm : SetLike.IsHomogeneousElem ℳ m) (hNm : m ∈ N) (j : ℕ) :
    (decompose ℳ (r • m) j : M) ∈ N := by
  classical
  rw [← DirectSum.sum_support_decompose 𝒜 r, Finset.sum_smul,
    decompose_sum, DFinsupp.finsetSum_apply, AddSubmonoidClass.coe_finsetSum]
  apply N.sum_mem
  intro k _
  obtain ⟨i, hi⟩ := hm
  have hki : (decompose 𝒜 r k : A) • m ∈ ℳ (k + i) := by
    simpa only [vadd_eq_add] using
      SetLike.GradedSMul.smul_mem (decompose 𝒜 r k).2 hi
  by_cases h : k + i = j
  · subst j
    rw [decompose_of_mem_same ℳ hki]
    exact N.smul_mem _ hNm
  · rw [decompose_of_mem_ne ℳ hki h]
    exact N.zero_mem

include 𝒜 in

theorem homogeneous_submodule_span (s : Set M)
    (hs : ∀ m ∈ s, SetLike.IsHomogeneousElem ℳ m) :
    (Submodule.span A s).IsHomogeneous ℳ := by
  rintro i m hm
  rw [Finsupp.span_eq_range_linearCombination, LinearMap.mem_range] at hm
  obtain ⟨c, rfl⟩ := hm
  rw [Finsupp.linearCombination_apply, Finsupp.sum, decompose_sum,
    DFinsupp.finsetSum_apply, AddSubmonoidClass.coe_finsetSum]
  apply Submodule.sum_mem
  intro z _
  exact decompose_smul_mem_of_homogeneous 𝒜 ℳ _ (c z) (hs z z.2)
    (Submodule.subset_span z.2) i

variable [IsScalarTower K A M]

omit [GradedAlgebra 𝒜] [DirectSum.Decomposition ℳ] in

theorem homogeneous_coefficients_sum_mem {r D n : ℕ} (v : Fin r → M)
    (hv : ∀ i, v i ∈ ℳ D) (hn : D ≤ n) (c : Fin r → 𝒜 (n - D)) :
    (∑ i, (c i : A) • v i) ∈
      (ℳ n ⊓ (Submodule.span A (Set.range v)).restrictScalars K) := by
  constructor
  · apply Submodule.sum_mem
    intro i _
    simpa only [vadd_eq_add, Nat.sub_add_cancel hn] using
      SetLike.GradedSMul.smul_mem (c i).2 (hv i)
  · apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

omit [IsScalarTower K A M] in

theorem exists_homogeneous_coefficients {r D n : ℕ} (v : Fin r → M)
    (hv : ∀ i, v i ∈ ℳ D) (hn : D ≤ n) (y : M)
    (hy : y ∈ ℳ n) (hyspan : y ∈ Submodule.span A (Set.range v)) :
    ∃ c : Fin r → 𝒜 (n - D), (∑ i, (c i : A) • v i) = y := by
  classical
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp hyspan
  refine ⟨fun i => decompose 𝒜 (c i) (n - D), ?_⟩
  have hp := congrArg (fun z : M => (decompose ℳ z n : M)) hc
  rw [decompose_sum, DFinsupp.finsetSum_apply, AddSubmonoidClass.coe_finsetSum,
    decompose_of_mem_same ℳ hy] at hp
  convert hp using 1
  apply Finset.sum_congr rfl
  intro i _
  have h := (decompose_smul_of_homogeneous_right 𝒜 ℳ (c i) (hv i) (n - D)).symm
  rw [Nat.sub_add_cancel hn] at h
  exact h

end WeightedTorusJets

open scoped BigOperators


end SiegelZeros

end OAI
