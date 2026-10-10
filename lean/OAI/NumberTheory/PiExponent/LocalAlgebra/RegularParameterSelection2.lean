import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import OAI.NumberTheory.PiExponent.LocalAlgebra.RegularParameterAvoidance

namespace OAI

noncomputable section
open IsLocalRing RingTheory.Sequence
namespace PiExponentSiegel.W58

variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

theorem regular_full_length_radical_eq_maximalIdeal (rs : List R)
    (hreg : IsRegular R rs) (hdim : ringKrullDim R = rs.length) :
    (Ideal.ofList rs).radical = maximalIdeal R := by
  let I := Ideal.ofList rs
  have hproper : I ≠ ⊤ := PiExponentSiegel.W20.regular_sequence_ideal_ne_top rs hreg
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

end PiExponentSiegel.W58

end

end OAI
