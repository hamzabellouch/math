import OAI.MathematicalPhysics.AlternatingFlow.DerivativeBounds
import OAI.MathematicalPhysics.AlternatingFlow.Effective
import OAI.MathematicalPhysics.AlternatingFlow.Quantitative

namespace OAI

section EffectiveProfilesDevelopment

open scoped BigOperators ContDiff

namespace AlternatingNS
namespace Effective

lemma factorial : Primrec Nat.factorial := by
  have hs : Primrec₂ (fun n a : ℕ => (n + 1) * a) :=
    Primrec.nat_mul.comp (Primrec.succ.comp Primrec.fst) Primrec.snd
  have h := Primrec.nat_rec₁ 1 hs
  refine h.of_eq ?_
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simpa only [Nat.rec_add_one, ih] using (Nat.factorial_succ n).symm

lemma sum_range {A : Type*} [Primcodable A] {f : A → ℕ → ℕ} (hf : Primrec₂ f) :
    Primrec₂ (fun a n => ∑ i ∈ Finset.range n, f a i) := by
  have hs : Primrec₂ (fun a : A => fun z : ℕ × ℕ => z.2 + f a z.1) :=
    Primrec.nat_add.comp (Primrec.snd.comp Primrec.snd)
      (hf.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
  have h := Primrec.nat_rec (Primrec.const (0 : ℕ) : Primrec (fun _ : A => (0 : ℕ))) hs
  refine h.of_eq ?_
  intro a n
  induction n with
  | zero => simp
  | succ n ih => simp only [Finset.sum_range_succ, ih]

lemma choose : Primrec₂ Nat.choose := by
  apply Primrec.ite (Primrec.nat_le.comp Primrec.snd Primrec.fst)
    (Primrec.nat_div.comp (factorial.comp Primrec.fst)
      (Primrec.nat_mul.comp (factorial.comp Primrec.snd)
        (factorial.comp (Primrec.nat_sub.comp Primrec.fst Primrec.snd)))) (Primrec.const 0) |>.of_eq
  rintro ⟨n,k⟩
  dsimp only
  split_ifs with h
  · exact (Nat.choose_eq_factorial_div_factorial h).symm
  · exact (Nat.choose_eq_zero_of_lt (by omega)).symm

lemma rhoBound : Primrec Quantitative.rhoBound := by
  exact Primrec.nat_mul.comp (factorial.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id))
    (nat_pow.comp (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)
      (Primrec.const 1)) Primrec.id)

lemma reciprocalBound {A : Type*} [Primcodable A] {q : A → ℕ} {B : A → ℕ → ℕ}
    (hq : Primrec q) (hB : Primrec₂ B) :
    Primrec₂ (fun a r => Quantitative.reciprocalBound (q a) (B a) r) := by
  let hr : Primrec (fun z : A × ℕ => z.2) := Primrec.snd
  let hfac := factorial.comp hr
  exact Primrec.nat_mul.comp
    (Primrec.nat_mul.comp hfac
      (Primrec.nat_mul.comp hfac (nat_pow.comp (hq.comp Primrec.fst) (Primrec.succ.comp hr))))
    (nat_pow.comp (Primrec.nat_add.comp (Primrec.const 1)
      ((sum_range hB).comp Primrec.fst (Primrec.succ.comp hr))) hr)

lemma transitionInvBound : Primrec Quantitative.transitionInvBound := by
  have hs : Primrec₂ (fun _ : ℕ => fun r : ℕ => 2 * Quantitative.rhoBound r) :=
    Primrec.nat_mul.comp (Primrec.const 2) (rhoBound.comp Primrec.snd)
  exact (reciprocalBound (Primrec.const 9 : Primrec (fun _ : ℕ => (9 : ℕ))) hs).comp
    Primrec.id Primrec.id

lemma transitionBound : Primrec Quantitative.transitionBound := by
  have hs : Primrec₂ (fun r i : ℕ => r.choose i * Quantitative.rhoBound i *
      Quantitative.transitionInvBound (r - i)) :=
    Primrec.nat_mul.comp (Primrec.nat_mul.comp choose (rhoBound.comp Primrec.snd))
      (transitionInvBound.comp (Primrec.nat_sub.comp Primrec.fst Primrec.snd))
  exact (sum_range hs).comp Primrec.id Primrec.succ

theorem profile_bound_programs :
    ∃ cρ cH : Program,
      (∀ r : ℕ, Returns cρ r (Quantitative.rhoBound r) ∧
        ∀ x : ℝ, ‖iteratedFDeriv ℝ r expNegInvGlue x‖ ≤ Quantitative.rhoBound r) ∧
      (∀ r : ℕ, Returns cH r (Quantitative.transitionBound r) ∧
        ∀ x : ℝ, ‖iteratedFDeriv ℝ r Real.smoothTransition x‖ ≤ Quantitative.transitionBound r) := by
  obtain ⟨cρ, hρ⟩ := program_of_computable Quantitative.rhoBound rhoBound.to_comp
  obtain ⟨cH, hH⟩ := program_of_computable Quantitative.transitionBound transitionBound.to_comp
  exact ⟨cρ, cH, fun r => ⟨hρ r, Quantitative.rho_jet_bound r⟩,
    fun r => ⟨hH r, Quantitative.transition_jet_bound r⟩⟩

end Effective
end AlternatingNS

end EffectiveProfilesDevelopment

end OAI
