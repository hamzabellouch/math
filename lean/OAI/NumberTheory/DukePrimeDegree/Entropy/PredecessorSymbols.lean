import OAI.NumberTheory.DukePrimeDegree.Entropy.LayeredPredecessors

namespace OAI

/-! # A finite symbol recovers a countable label from its successor

A uniform finite predecessor bound replaces an unbounded observation by
a finite symbol once its next countable label is known.
-/

noncomputable section
open Set MeasureTheory
namespace DukePrimeDegree

theorem exists_finite_predecessor_observation {Y : Type*} [MeasurableSpace Y]
    (T : Y → Y) (hT : Measurable T) (Q : Y → ℕ) (hQ : Measurable Q)
    (hfinite : UniformFinitePredecessors T Q) :
    ∃ (M : ℕ) (B : Y → Fin (M+1)) (decode : ℕ → Fin (M+1) → ℕ),
      Measurable B ∧
      (∀ x y, Q x=Q y → Q (T x)=Q (T y) → B x=B y) ∧
      ∀ x, decode (Q (T x)) (B x)=Q x := by
  classical
  obtain ⟨M,hM⟩ := hfinite
  choose F hF hcard using hM
  let code : ℕ × ℕ → Fin (M+1) := fun p =>
    if hv : p.2 ∈ F p.1 then
      ⟨((F p.1).equivFin ⟨p.2,hv⟩).val,
        lt_of_lt_of_le ((F p.1).equivFin ⟨p.2,hv⟩).isLt
          (Nat.le_succ_of_le (hcard p.1))⟩
    else 0
  let decode : ℕ → Fin (M+1) → ℕ := fun q b =>
    if hb : b.val < (F q).card then
      ((F q).equivFin.symm ⟨b.val,hb⟩).val
    else 0
  let B : Y → Fin (M+1) := fun x => code (Q (T x),Q x)
  refine ⟨M,B,decode,?_,?_,?_⟩
  · exact (measurable_of_countable code).comp ((hQ.comp hT).prodMk hQ)
  · intro x y hxy hTxy
    dsimp only [B]
    rw [hxy,hTxy]
  · intro x
    have hx : Q x ∈ F (Q (T x)) := hF (Q (T x)) ⟨x,rfl,rfl⟩
    have hb : ((F (Q (T x))).equivFin ⟨Q x,hx⟩).val < (F (Q (T x))).card :=
      ((F (Q (T x))).equivFin ⟨Q x,hx⟩).isLt
    dsimp only [B,code]
    rw [dite_eq_left hx]
    dsimp only [decode]
    rw [dite_eq_left hb]
    exact congrArg Subtype.val ((F (Q (T x))).equivFin.symm_apply_apply ⟨Q x,hx⟩)

lemma predecessor_word_recovers {Y : Type*} {M : ℕ}
    (T : Y → Y) (Q : Y → ℕ) (B : Y → Fin M)
    (decode : ℕ → Fin M → ℕ) (hdecode : ∀ x, decode (Q (T x)) (B x)=Q x)
    {x y : Y} {N : ℕ}
    (hterminal : Q (T^[N] x)=Q (T^[N] y))
    (hword : ∀ k < N, B (T^[k] x)=B (T^[k] y)) :
    ∀ k ≤ N, Q (T^[k] x)=Q (T^[k] y) := by
  induction N with
  | zero =>
      intro k hk
      have hk0 : k=0 := by omega
      subst k
      exact hterminal
  | succ N ih =>
      have hlast : Q (T^[N] x)=Q (T^[N] y) := by
        rw [←hdecode (T^[N] x),←hdecode (T^[N] y)]
        have ht : T (T^[N] x)=T^[N+1] x := (Function.iterate_succ_apply' T N x).symm
        have hu : T (T^[N] y)=T^[N+1] y := (Function.iterate_succ_apply' T N y).symm
        rw [ht,hu,hterminal,hword N (Nat.lt_succ_self N)]
      intro k hk
      by_cases hkn : k ≤ N
      · exact ih hlast (fun i hi => hword i (Nat.lt_trans hi (Nat.lt_succ_self N))) k hkn
      · have he : k=N+1 := by omega
        subst k
        exact hterminal

end DukePrimeDegree

end

end OAI
