import OAI.NumberTheory.TwoPoint.Bounds.QuotientLines
import Mathlib.Data.Finset.Max

namespace OAI

/-! Finite maximal selection of jointly independent direction/difference pairs. -/

namespace TwoPointCorrelations

open Finset Submodule

variable {K κ V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype κ] [DecidableEq κ]

def pairFamily (v : κ → Fin 2 → V) (S : Finset κ) : S × Fin 2 → V :=
  fun z => v z.1 z.2

private noncomputable def insertPairEquiv (S : Finset κ) (k : κ) (hk : k ∉ S) :
    (S × Fin 2) ⊕ Fin 2 ≃ ↥(insert k S) × Fin 2 :=
  Equiv.ofBijective
    (Sum.elim (fun z => (⟨z.1, mem_insert_of_mem z.1.property⟩, z.2))
      (fun b => (⟨k, mem_insert_self k S⟩, b))) (by
    constructor
    · intro z w heq
      cases z with
      | inl z =>
        cases w with
        | inl w =>
          apply congrArg Sum.inl
          apply Prod.ext
          · apply Subtype.ext
            exact congrArg (fun a : ↥(insert k S) × Fin 2 => (a.1 : κ)) heq
          · exact congrArg (fun a : ↥(insert k S) × Fin 2 => a.2) heq
        | inr b =>
          have hz : (z.1 : κ) = k :=
            congrArg (fun a : ↥(insert k S) × Fin 2 => (a.1 : κ)) heq
          exact (hk (hz ▸ z.1.property)).elim
      | inr b =>
        cases w with
        | inl w =>
          have hw : k = (w.1 : κ) :=
            congrArg (fun a : ↥(insert k S) × Fin 2 => (a.1 : κ)) heq
          exact (hk (hw ▸ w.1.property)).elim
        | inr c => exact congrArg Sum.inr (congrArg Prod.snd heq)
    · rintro ⟨⟨j, hj⟩, b⟩
      rcases mem_insert.mp hj with rfl | hj
      · exact ⟨.inr b, rfl⟩
      · exact ⟨.inl (⟨j, hj⟩, b), rfl⟩)

omit [Fintype κ] in
private theorem independent_insert_pair (v : κ → Fin 2 → V) (S : Finset κ)
    (k : κ) (hk : k ∉ S)
    (h : LinearIndependent K (Sum.elim (pairFamily v S) (v k))) :
    LinearIndependent K (pairFamily v (insert k S)) := by
  apply (linearIndependent_equiv (insertPairEquiv S k hk)).mp
  convert h using 1
  funext z
  cases z <;> rfl

/-- A maximal collection exists among the finitely many candidate pairs.
No further pair can be adjoined, and its span has twice the selected size. -/
theorem exists_maximal_independent_pairs (v : κ → Fin 2 → V) :
    ∃ S : Finset κ, LinearIndependent K (pairFamily v S) ∧
      Module.finrank K (span K (Set.range (pairFamily v S))) = 2 * S.card ∧
      ∀ k ∉ S, ¬LinearIndependent K (Sum.elim (pairFamily v S) (v k)) := by
  classical
  let good : Finset (Finset κ) := univ.filter (fun S => LinearIndependent K (pairFamily v S))
  have hempty : (∅ : Finset κ) ∈ good := by
    simp only [good, mem_filter, mem_univ, true_and]
    exact linearIndependent_empty_type
  obtain ⟨S, hS, hmax⟩ := good.exists_max_image Finset.card ⟨∅, hempty⟩
  have hind := (mem_filter.mp hS).2
  refine ⟨S, hind, ?_, ?_⟩
  · rw [finrank_span_eq_card hind, Fintype.card_prod, Fintype.card_coe, Fintype.card_fin]
    omega
  · intro k hk hnew
    have hgood : insert k S ∈ good := by
      exact mem_filter.mpr ⟨mem_univ _, independent_insert_pair v S k hk hnew⟩
    have hc := hmax (insert k S) hgood
    rw [card_insert_of_notMem hk] at hc
    omega

/-- Maximal pair selection forces each unselected direction/difference
pair onto one line in the quotient by the selected span. -/
theorem exists_maximal_pair_quotient (v : κ → Fin 2 → V) :
    ∃ S : Finset κ, LinearIndependent K (pairFamily v S) ∧
      Module.finrank K (span K (Set.range (pairFamily v S))) = 2 * S.card ∧
      ∀ k, (span K (Set.range (pairFamily v S))).mkQ (v k 1) ≠ 0 →
        ∃ c : K, (span K (Set.range (pairFamily v S))).mkQ (v k 0) =
          c • (span K (Set.range (pairFamily v S))).mkQ (v k 1) := by
  classical
  obtain ⟨S, hS, hdim, hmax⟩ := exists_maximal_independent_pairs (K := K) v
  refine ⟨S, hS, hdim, ?_⟩
  intro k hk
  have hkS : k ∉ S := by
    intro hmem
    apply hk
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact subset_span ⟨(⟨k, hmem⟩, 1), rfl⟩
  have hpair : v k = ![v k 0, v k 1] := by ext b; fin_cases b <;> rfl
  exact quotient_line_of_nonextendable_pair (pairFamily v S) hS (v k 1) (v k 0) hk
    (by simpa only [← hpair] using hmax k hkS)


omit [Fintype κ] [DecidableEq κ] in
/-- Restriction to fewer candidate pairs preserves joint independence. -/
theorem independent_pairFamily_mono (v : κ → Fin 2 → V) {S T : Finset κ}
    (hTS : T ⊆ S) (hS : LinearIndependent K (pairFamily v S)) :
    LinearIndependent K (pairFamily v T) := by
  let f : T × Fin 2 → S × Fin 2 := fun z => (⟨z.1, hTS z.1.property⟩, z.2)
  have hf : Function.Injective f := by
    intro x y hxy
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun z : S × Fin 2 => (z.1 : κ)) hxy
    · exact congrArg (fun z : S × Fin 2 => z.2) hxy
  exact hS.comp f hf

/-- Excluding `r` independent pairs bounds every maximal collection by `r-1`. -/
theorem exists_small_maximal_independent_pairs (v : κ → Fin 2 → V) (r : ℕ)
    (hno : ∀ S : Finset κ, S.card = r → ¬LinearIndependent K (pairFamily v S)) :
    ∃ S : Finset κ, S.card < r ∧ LinearIndependent K (pairFamily v S) ∧
      Module.finrank K (span K (Set.range (pairFamily v S))) = 2 * S.card ∧
      ∀ k ∉ S, ¬LinearIndependent K (Sum.elim (pairFamily v S) (v k)) := by
  obtain ⟨S, hS, hdim, hmax⟩ := exists_maximal_independent_pairs (K := K) v
  refine ⟨S, ?_, hS, hdim, hmax⟩
  by_contra h
  obtain ⟨T, hTS, hcard⟩ := Finset.exists_subset_card_eq (Nat.le_of_not_gt h)
  exact hno T hcard (independent_pairFamily_mono v hTS hS)

end TwoPointCorrelations

end OAI
