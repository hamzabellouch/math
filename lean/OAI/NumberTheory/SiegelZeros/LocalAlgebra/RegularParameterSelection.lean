import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Regular.RegularSequence
import OAI.NumberTheory.SiegelZeros.Structure.GenericCombination

namespace OAI

namespace SiegelZeros

section

namespace W20

open scoped BigOperators

section Ring

variable {R : Type*} [CommRing R]

theorem regular_sequence_ideal_ne_top (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) : Ideal.ofList rs ≠ ⊤ := by
  intro htop
  apply hreg.top_ne_smul
  have hmul : (Ideal.ofList rs • (⊤ : Submodule R R)) = Ideal.ofList rs :=
    (Ideal.ofList rs).mul_top
  rw [hmul, htop]

theorem regular_sequence_term_not_isUnit (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) (i : Fin rs.length) :
    ¬ IsUnit rs[i] := by
  intro hunit
  apply regular_sequence_ideal_ne_top rs hreg
  exact (Ideal.ofList rs).eq_top_of_isUnit_mem
    (Ideal.subset_span (List.getElem_mem i.isLt)) hunit

theorem regular_sequence_term_ne_zero (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) (i : Fin rs.length) : rs[i] ≠ 0 := by
  let I : Ideal R := Ideal.ofList (rs.take i.val)
  have hle : I ≤ Ideal.ofList rs :=
    Ideal.span_mono (List.take_subset i.val rs)
  have hproper : I ≠ ⊤ := ne_top_of_le_ne_top
    (regular_sequence_ideal_ne_top rs hreg) hle
  let : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hproper
  have hsmul := hreg.toIsWeaklyRegular.regular_mod_prev i.val i.isLt
  have hmul : (Ideal.ofList (rs.take i.val) • (⊤ : Submodule R R)) = I := I.mul_top
  rw [hmul] at hsmul
  intro hz
  have hz' : rs[i.val] = 0 := by simpa only [Fin.getElem_fin] using hz
  have hsmulzero : IsSMulRegular (R ⧸ I) (0 : R) := hz' ▸ hsmul
  exact IsSMulRegular.not_zero hsmulzero

end Ring

section Polynomial

variable {k σ : Type*} [Field k]

theorem regular_homogeneous_degrees_pos
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ)
    (hhom : ∀ i : Fin rs.length, rs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial σ k) rs) :
    ∀ i, 0 < degrees i := by
  intro i
  by_contra hpos
  have hzero : degrees i = 0 := Nat.eq_zero_of_not_pos hpos
  have hhomzero : rs[i].IsHomogeneous 0 := by simpa only [hzero] using hhom i
  have hdegzero : (rs[i]).totalDegree = 0 :=
    (MvPolynomial.totalDegree_zero_iff_isHomogeneous (σ := σ)).mpr hhomzero
  have hconstant : rs[i] = MvPolynomial.C ((rs[i]).coeff 0) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdegzero
  have hcoeff : (rs[i]).coeff 0 ≠ 0 := by
    intro hz
    apply regular_sequence_term_ne_zero rs hreg i
    rw [hconstant, hz, map_zero]
  apply regular_sequence_term_not_isUnit rs hreg i
  rw [hconstant]
  exact (isUnit_iff_ne_zero.mpr hcoeff).map MvPolynomial.C

theorem regular_homogeneous_degree_product_ne_zero
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ)
    (hhom : ∀ i : Fin rs.length, rs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial σ k) rs) :
    (∏ i : Fin rs.length, degrees i) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact Nat.ne_of_gt (regular_homogeneous_degrees_pos rs degrees hhom hreg i)

end Polynomial

end W20

end

section

noncomputable section
open IsLocalRing RingTheory.Sequence
namespace W58

variable {R : Type*} [CommRing R] [IsNoetherianRing R]

theorem isSMulRegular_of_avoids_associatedPrimes
    (M : Type*) [AddCommGroup M] [Module R M] (x : R)
    (hx : ∀ P : Ideal R, IsAssociatedPrime P M → x ∉ P) :
    IsSMulRegular M x := by
  apply IsSMulRegular.of_right_eq_zero_of_smul
  intro y hy
  by_contra hne
  have hzero : x ∈ {r : R | ∃ z : M, z ≠ 0 ∧ r • z = 0} := ⟨y, hne, hy⟩
  rw [← biUnion_associatedPrimes_eq_zero_divisors R M] at hzero
  obtain ⟨P, hP, hxP⟩ := Set.mem_iUnion₂.mp hzero
  exact hx P hP hxP

variable [IsLocalRing R]

omit [IsNoetherianRing R] in
theorem regular_append_singleton_of_quotient_smulRegular
    (rs : List R) (hreg : IsRegular R rs) (x : R)
    (hx : x ∈ maximalIdeal R)
    (hregular : IsSMulRegular (R ⧸ Ideal.ofList rs) x) :
    IsRegular R (rs ++ [x]) := by
  apply (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal
    (M := R) (rs := rs ++ [x]) ?_).mpr
  · apply (isWeaklyRegular_append_iff R rs [x]).mpr
    refine ⟨hreg.toIsWeaklyRegular, ?_⟩
    have heq : (Ideal.ofList rs • (⊤ : Submodule R R)) = Ideal.ofList rs :=
      (Ideal.ofList rs).mul_top
    rw [heq, isWeaklyRegular_singleton_iff]
    exact hregular
  · intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · exact (le_maximalIdeal (SiegelZeros.W20.regular_sequence_ideal_ne_top rs hreg))
        (Ideal.subset_span hy)
    · have heq : y = x := List.mem_singleton.mp hy
      simpa only [heq] using hx

variable {k J : Type*} [Field k] [Infinite k] [Algebra k R]

theorem exists_constant_regular_extension
    (generators : J → R)
    (hrad : (Ideal.span (Set.range generators)).radical = maximalIdeal R)
    (rs : List R) (hreg : IsRegular R rs)
    (hnot : ¬ IsAssociatedPrime (maximalIdeal R) (R ⧸ Ideal.ofList rs)) :
    ∃ c : J →₀ k,
      Finsupp.linearCombination k generators c ∈ Ideal.span (Set.range generators) ∧
      IsRegular R (rs ++ [Finsupp.linearCombination k generators c]) := by
  classical
  let ass := associatedPrimes R (R ⧸ Ideal.ofList rs)
  let : Fintype ass := (associatedPrimes.finite R (R ⧸ Ideal.ofList rs)).fintype
  have hbelow (P : ass) : P.val < maximalIdeal R := by
    refine lt_iff_le_and_ne.mpr ⟨le_maximalIdeal P.property.isPrime.ne_top, ?_⟩
    intro heq
    exact hnot (heq ▸ P.property)
  obtain ⟨c, hc⟩ := SiegelZeros.W20.exists_linearCombination_avoiding_primes_below_radical
    (K := k) generators (maximalIdeal R) hrad (fun P : ass => P.val)
    (fun P => P.property.isPrime) hbelow
  have hlin : Finsupp.linearCombination k generators c ∈
      Submodule.span k (Set.range generators) := by
    rw [← Finsupp.range_linearCombination]
    exact ⟨c, rfl⟩
  have hspan : Submodule.span k (Set.range generators) ≤
      (Ideal.span (Set.range generators)).restrictScalars k := by
    apply Submodule.span_le.mpr
    exact fun _ h => Ideal.subset_span h
  have hin : Finsupp.linearCombination k generators c ∈
      Ideal.span (Set.range generators) := hspan hlin
  refine ⟨c, hin, regular_append_singleton_of_quotient_smulRegular rs hreg _ ?_ ?_⟩
  · rw [← hrad]
    exact Ideal.le_radical hin
  · apply isSMulRegular_of_avoids_associatedPrimes
    intro P hP
    exact hc ⟨P, hP⟩

end W58

end

end

section

noncomputable section
open IsLocalRing RingTheory.Sequence
namespace W58

variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

theorem regular_full_length_radical_eq_maximalIdeal (rs : List R)
    (hreg : IsRegular R rs) (hdim : ringKrullDim R = rs.length) :
    (Ideal.ofList rs).radical = maximalIdeal R := by
  let I := Ideal.ofList rs
  have hproper : I ≠ ⊤ := SiegelZeros.W20.regular_sequence_ideal_ne_top rs hreg
  let : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hproper
  let : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let : IsLocalHom (Ideal.Quotient.mk I) :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hzero : ringKrullDim (R ⧸ I) = 0 := by
    apply (ENat.WithBot.add_natCast_cancel (c := rs.length)).mp
    simpa only [zero_add, hdim] using
      ringKrullDim_add_length_eq_ringKrullDim_of_isRegular rs hreg
  let : Ring.KrullDimLE 0 (R ⧸ I) :=
    ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr hzero
  have hnil := Ring.KrullDimLE.radical_eq_maximalIdeal
    (⊥ : Ideal (R ⧸ I)) bot_ne_top
  have hc := congrArg (Ideal.comap (Ideal.Quotient.mk I)) hnil
  rw [Ideal.comap_radical, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
    IsLocalRing.maximalIdeal_comap] at hc
  exact hc

variable {k J : Type*} [Field k] [Infinite k] [Algebra k R]

omit [IsNoetherianRing R] [IsLocalRing R] [Infinite k] in
theorem constant_linearCombination_mem_ideal (generators : J → R) (c : J →₀ k) :
    Finsupp.linearCombination k generators c ∈ Ideal.span (Set.range generators) := by
  have hspan : Submodule.span k (Set.range generators) ≤
      (Ideal.span (Set.range generators)).restrictScalars k :=
    Submodule.span_le.mpr (fun _ h => Ideal.subset_span h)
  apply hspan
  rw [← Finsupp.range_linearCombination]
  exact ⟨c, rfl⟩

theorem exists_constant_regular_parameters_of_no_maximal_associated
    (generators : J → R)
    (hrad : (Ideal.span (Set.range generators)).radical = maximalIdeal R)
    (h : ℕ) (hdim : ringKrullDim R = h)
    (hnot : ∀ rs : List R, IsRegular R rs → rs.length < h →
      ¬ IsAssociatedPrime (maximalIdeal R) (R ⧸ Ideal.ofList rs)) :
    ∃ cs : List (J →₀ k), cs.length = h ∧
      IsRegular R (cs.map (Finsupp.linearCombination k generators)) ∧
      Ideal.ofList (cs.map (Finsupp.linearCombination k generators)) ≤
        Ideal.span (Set.range generators) ∧
      (Ideal.ofList (cs.map (Finsupp.linearCombination k generators))).radical =
        maximalIdeal R := by
  have build : ∀ t : ℕ, t ≤ h → ∃ cs : List (J →₀ k), cs.length = t ∧
      IsRegular R (cs.map (Finsupp.linearCombination k generators)) := by
    intro t
    induction t with
    | zero =>
      intro _
      exact ⟨[], rfl, IsRegular.nil R R⟩
    | succ t ih =>
      intro ht
      obtain ⟨cs, hlen, hreg⟩ := ih (Nat.le_trans (Nat.le_succ t) ht)
      have hshort : (cs.map (Finsupp.linearCombination k generators)).length < h := by
        simpa only [List.length_map, hlen] using (Nat.lt_of_succ_le ht)
      obtain ⟨c, _, hc⟩ := exists_constant_regular_extension (k := k) generators hrad _ hreg
        (hnot _ hreg hshort)
      refine ⟨cs ++ [c], by simp [hlen], ?_⟩
      simpa only [List.map_append, List.map_cons, List.map_nil] using hc
  obtain ⟨cs, hlen, hreg⟩ := build h le_rfl
  refine ⟨cs, hlen, hreg, ?_, regular_full_length_radical_eq_maximalIdeal _ hreg ?_⟩
  · apply Ideal.span_le.mpr
    intro x hx
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx
    exact constant_linearCombination_mem_ideal generators c
  · simpa only [List.length_map, hlen] using hdim

end W58

end

end

end SiegelZeros

end OAI
