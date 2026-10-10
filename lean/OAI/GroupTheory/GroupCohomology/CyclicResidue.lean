import Mathlib
import OAI.GroupTheory.GroupCohomology.DividedBinomial

namespace OAI

/-! Nonzero cyclic cohomology classes in a Laurent monomial line. -/

noncomputable section
open Finset
namespace LowerSphereCyclic
abbrev Cyclic (p : ℕ) := Multiplicative (ZMod p)

def sigma (p : ℕ) : Cyclic p := Multiplicative.ofAdd 1

def residueKappa (p : ℕ) (k : Type) [Field k] [CharP k p] (a : k)
    (g : Cyclic p) : k := a * ZMod.castHom (dvd_refl p) k g.toAdd

lemma residueKappa_mul (p : ℕ) (k : Type) [Field k] [CharP k p]
    (a : k) (g h : Cyclic p) :
    residueKappa p k a (g * h) = residueKappa p k a g + residueKappa p k a h := by
  change a * (ZMod.castHom (dvd_refl p) k) (g.toAdd + h.toAdd) = _
  rw [map_add, mul_add]
  rfl

def cyclicCochain (p : ℕ) (k : Type) [Field k] [CharP k p] (a : k) :
    Cyclic p × Cyclic p → k :=
  fun gh => dividedBinomial p
    (a * ZMod.castHom (dvd_refl p) k gh.1.toAdd)
    (a * ZMod.castHom (dvd_refl p) k gh.2.toAdd)

lemma cyclicCochain_is_cocycle (p : ℕ) (hp : p.Prime)
    (k : Type) [Field k] [CharP k p] (a : k) :
    cyclicCochain p k a ∈ groupCohomology.cocycles₂ (Rep.trivial k (Cyclic p) k) := by
  rw [groupCohomology.mem_cocycles₂_iff]
  intro g h j
  simp only [Representation.isTrivial_apply]
  change dividedBinomial p (residueKappa p k a (g * h)) (residueKappa p k a j) +
      dividedBinomial p (residueKappa p k a g) (residueKappa p k a h) =
    dividedBinomial p (residueKappa p k a h) (residueKappa p k a j) +
      dividedBinomial p (residueKappa p k a g) (residueKappa p k a (h * j))
  rw [residueKappa_mul, residueKappa_mul]
  exact dividedBinomial_cocycle hp _ _ _

lemma sigma_pow_p (p : ℕ) : (sigma p) ^ p = 1 := by
  apply Multiplicative.toAdd.injective
  simp [sigma]

lemma residueKappa_sigma (p : ℕ) (k : Type) [Field k] [CharP k p] (a : k) :
    residueKappa p k a (sigma p) = a := by
  simp [residueKappa, sigma]

lemma residueKappa_sigma_pow (p : ℕ) (k : Type) [Field k] [CharP k p]
    (a : k) (j : ℕ) :
    residueKappa p k a ((sigma p) ^ j) = a * (j : k) := by
  simp [residueKappa, sigma]

lemma cyclicCochain_at_sigma (p : ℕ) (k : Type) [Field k] [CharP k p]
    (a : k) (j : ℕ) :
    cyclicCochain p k a (sigma p, (sigma p) ^ j) =
      a ^ p * dividedBinomial p (1 : k) (j : k) := by
  change dividedBinomial p (residueKappa p k a (sigma p))
    (residueKappa p k a ((sigma p) ^ j)) = _
  rw [residueKappa_sigma, residueKappa_sigma_pow]
  simpa only [mul_one] using dividedBinomial_smul p a (1 : k) (j : k)

lemma cyclicCochain_sum (p : ℕ) (hp : p.Prime) (k : Type)
    [Field k] [CharP k p] (a : k) :
    (∑ j ∈ Finset.range p, cyclicCochain p k a (sigma p, (sigma p) ^ j)) =
      -(a ^ p) := by
  simp only [cyclicCochain_at_sigma]
  rw [← Finset.mul_sum, dividedBinomial_sum_charP hp]
  ring

lemma coboundary_sum (p : ℕ) (k : Type) [Field k] [CharP k p]
    (v : Cyclic p → k) :
    (∑ j ∈ Finset.range p,
      groupCohomology.d₁₂ (Rep.trivial k (Cyclic p) k) v (sigma p, (sigma p) ^ j)) = 0 := by
  simp only [groupCohomology.d₁₂_hom_apply, Representation.isTrivial_apply]
  simp only [← pow_succ']
  rw [Finset.sum_add_distrib,
    Finset.sum_range_sub' (fun j : ℕ => v ((sigma p) ^ j)) p]
  simp [sigma_pow_p, nsmul_eq_mul]

lemma cyclicCochain_not_coboundary (p : ℕ) (hp : p.Prime) (k : Type)
    [Field k] [CharP k p] (a : k) (ha : a ≠ 0) :
    cyclicCochain p k a ∉ groupCohomology.coboundaries₂ (Rep.trivial k (Cyclic p) k) := by
  intro hb
  obtain ⟨v, hv⟩ := hb
  have hsum := coboundary_sum p k v
  change (∑ j ∈ Finset.range p,
    ((groupCohomology.d₁₂ (Rep.trivial k (Cyclic p) k)).hom v)
      (sigma p, (sigma p) ^ j)) = 0 at hsum
  rw [hv, cyclicCochain_sum p hp k a] at hsum
  exact pow_ne_zero p ha (neg_eq_zero.mp hsum)

theorem cyclic_detection (p : ℕ) (hp : p.Prime) (_hodd : Odd p)
    (k : Type) [Field k] [CharP k p] (a : k) (ha : a ≠ 0) :
    cyclicCochain p k a ∈
        groupCohomology.cocycles₂ (Rep.trivial k (Multiplicative (ZMod p)) k) ∧
      cyclicCochain p k a ∉
        groupCohomology.coboundaries₂ (Rep.trivial k (Multiplicative (ZMod p)) k) :=
  ⟨cyclicCochain_is_cocycle p hp k a, cyclicCochain_not_coboundary p hp k a ha⟩

def binomialCocycle (p : ℕ) (hp : p.Prime) (k : Type)
    [Field k] [CharP k p] (a : k) :
    groupCohomology.cocycles₂ (Rep.trivial k (Cyclic p) k) :=
  ⟨cyclicCochain p k a, cyclicCochain_is_cocycle p hp k a⟩

def binomialClass (p : ℕ) (hp : p.Prime) (k : Type)
    [Field k] [CharP k p] (a : k) :
    groupCohomology.H2 (Rep.trivial k (Cyclic p) k) :=
  groupCohomology.H2π _ (binomialCocycle p hp k a)

theorem binomialClass_ne_zero (p : ℕ) (hp : p.Prime) (k : Type)
    [Field k] [CharP k p] (a : k) (ha : a ≠ 0) :
    binomialClass p hp k a ≠ 0 := by
  intro hz
  have hb := (groupCohomology.H2π_eq_zero_iff (binomialCocycle p hp k a)).mp hz
  exact cyclicCochain_not_coboundary p hp k a ha hb

def residueLine (k : Type) [Field k] (n : ℤ) : Submodule k (LaurentPolynomial k) :=
  LinearMap.range (AddMonoidAlgebra.lsingle (R := k) (S := k) (-n))

def residueLineMap (k : Type) [Field k] (n : ℤ) : k →ₗ[k] residueLine k n :=
  (AddMonoidAlgebra.lsingle (R := k) (S := k) (-n)).rangeRestrict

def firstResidue (p : ℕ) (k : Type) [Field k] (c : k) : LaurentPolynomial k :=
  LaurentPolynomial.C c * LaurentPolynomial.T (-((p - 1 : ℕ) : ℤ))

def gradedCochain (p : ℕ) (k : Type) [Field k] [CharP k p] (c : k) :
    Multiplicative (ZMod p) × Multiplicative (ZMod p) →
      residueLine k ((p : ℤ) * ((p - 1 : ℕ) : ℤ)) :=
  fun gh => residueLineMap k ((p : ℤ) * ((p - 1 : ℕ) : ℤ)) (cyclicCochain p k c gh)

lemma residueLineMap_val (k : Type) [Field k] (n : ℤ) (c : k) :
    (residueLineMap k n c : LaurentPolynomial k) =
      LaurentPolynomial.C c * LaurentPolynomial.T (-n) :=
  LaurentPolynomial.single_eq_C_mul_T c (-n)

def residueLineCoeff (k : Type) [Field k] (n : ℤ) : residueLine k n →ₗ[k] k :=
  (Finsupp.lapply (-n)).comp
    ((AddMonoidAlgebra.coeffLinearEquiv k).toLinearMap.comp (residueLine k n).subtype)

@[simp]
lemma residueLineCoeff_map (k : Type) [Field k] (n : ℤ) (c : k) :
    residueLineCoeff k n (residueLineMap k n c) = c := by
  change (AddMonoidAlgebra.single (-n) c).coeff (-n) = c
  change (Finsupp.single (-n) c) (-n) = c
  exact Finsupp.single_eq_same

lemma gradedCochain_val (p : ℕ) (k : Type) [Field k] [CharP k p]
    (c : k) (gh : Cyclic p × Cyclic p) :
    (gradedCochain p k c gh : LaurentPolynomial k) =
      dividedBinomial p
        (firstResidue p k c * LaurentPolynomial.C
          (ZMod.castHom (dvd_refl p) k gh.1.toAdd))
        (firstResidue p k c * LaurentPolynomial.C
          (ZMod.castHom (dvd_refl p) k gh.2.toAdd)) := by
  let q₁ := ZMod.castHom (dvd_refl p) k gh.1.toAdd
  let q₂ := ZMod.castHom (dvd_refl p) k gh.2.toAdd
  have harg (q : k) : firstResidue p k c * LaurentPolynomial.C q =
      LaurentPolynomial.T (-((p - 1 : ℕ) : ℤ)) * LaurentPolynomial.C (c * q) := by
    simp only [firstResidue, map_mul]
    ring
  change (residueLineMap k ((p : ℤ) * ((p - 1 : ℕ) : ℤ))
    (dividedBinomial p (c * q₁) (c * q₂)) : LaurentPolynomial k) = _
  rw [residueLineMap_val, harg, harg, dividedBinomial_smul (R := LaurentPolynomial k),
    ← map_dividedBinomial LaurentPolynomial.C, LaurentPolynomial.T_pow]
  rw [mul_neg]
  exact mul_comm _ _

@[simp]
lemma gradedCochain_coeff (p : ℕ) (k : Type) [Field k] [CharP k p]
    (c : k) (gh : Cyclic p × Cyclic p) :
    residueLineCoeff k ((p : ℤ) * ((p - 1 : ℕ) : ℤ)) (gradedCochain p k c gh) =
      cyclicCochain p k c gh := residueLineCoeff_map _ _ _

lemma gradedCochain_is_cocycle (p : ℕ) (hp : p.Prime) (k : Type)
    [Field k] [CharP k p] (c : k) :
    gradedCochain p k c ∈ groupCohomology.cocycles₂
      (Rep.trivial k (Cyclic p) (residueLine k ((p : ℤ) * ((p - 1 : ℕ) : ℤ)))) := by
  rw [groupCohomology.mem_cocycles₂_iff]
  intro g h j
  have hh := ((groupCohomology.mem_cocycles₂_iff _).mp
    (cyclicCochain_is_cocycle p hp k c)) g h j
  have hh' := congrArg (residueLineMap k ((p : ℤ) * ((p - 1 : ℕ) : ℤ))) hh
  simpa only [Representation.isTrivial_apply, map_add, gradedCochain] using hh'

lemma gradedCochain_not_coboundary (p : ℕ) (hp : p.Prime) (k : Type)
    [Field k] [CharP k p] (c : k) (hc : c ≠ 0) :
    gradedCochain p k c ∉ groupCohomology.coboundaries₂
      (Rep.trivial k (Cyclic p) (residueLine k ((p : ℤ) * ((p - 1 : ℕ) : ℤ)))) := by
  intro hb
  obtain ⟨v, hv⟩ := hb
  apply cyclicCochain_not_coboundary p hp k c hc
  refine ⟨fun g => residueLineCoeff k ((p : ℤ) * ((p - 1 : ℕ) : ℤ)) (v g), ?_⟩
  funext gh
  have hh := congrArg (fun f =>
    residueLineCoeff k ((p : ℤ) * ((p - 1 : ℕ) : ℤ)) (f gh)) hv
  simpa only [groupCohomology.d₁₂_hom_apply, Representation.isTrivial_apply,
    map_add, map_sub, gradedCochain_coeff] using hh

theorem cyclic_residue_detection (p : ℕ) (hp : p.Prime) (_hodd : Odd p)
    (k : Type) [Field k] [CharP k p] (c : k) (hc : c ≠ 0) :
    (∀ gh, (gradedCochain p k c gh : LaurentPolynomial k) =
      dividedBinomial p
        (firstResidue p k c * LaurentPolynomial.C
          (ZMod.castHom (dvd_refl p) k gh.1.toAdd))
        (firstResidue p k c * LaurentPolynomial.C
          (ZMod.castHom (dvd_refl p) k gh.2.toAdd))) ∧
    gradedCochain p k c ∈ groupCohomology.cocycles₂
      (Rep.trivial k (Multiplicative (ZMod p))
        (residueLine k ((p : ℤ) * ((p - 1 : ℕ) : ℤ)))) ∧
    gradedCochain p k c ∉ groupCohomology.coboundaries₂
      (Rep.trivial k (Multiplicative (ZMod p))
        (residueLine k ((p : ℤ) * ((p - 1 : ℕ) : ℤ)))) :=
  ⟨gradedCochain_val p k c, gradedCochain_is_cocycle p hp k c,
    gradedCochain_not_coboundary p hp k c hc⟩

def gradedBinomialCocycle (p : ℕ) (hp : p.Prime) (k : Type)
    [Field k] [CharP k p] (c : k) :
    groupCohomology.cocycles₂
      (Rep.trivial k (Cyclic p) (residueLine k ((p : ℤ) * ((p - 1 : ℕ) : ℤ)))) :=
  ⟨gradedCochain p k c, gradedCochain_is_cocycle p hp k c⟩

def gradedBinomialClass (p : ℕ) (hp : p.Prime) (k : Type)
    [Field k] [CharP k p] (c : k) :
    groupCohomology.H2
      (Rep.trivial k (Cyclic p) (residueLine k ((p : ℤ) * ((p - 1 : ℕ) : ℤ)))) :=
  groupCohomology.H2π _ (gradedBinomialCocycle p hp k c)

theorem gradedBinomialClass_ne_zero (p : ℕ) (hp : p.Prime) (k : Type)
    [Field k] [CharP k p] (c : k) (hc : c ≠ 0) :
    gradedBinomialClass p hp k c ≠ 0 := by
  intro hz
  have hb := (groupCohomology.H2π_eq_zero_iff (gradedBinomialCocycle p hp k c)).mp hz
  exact gradedCochain_not_coboundary p hp k c hc hb

end LowerSphereCyclic

end

end OAI
