import OAI.NumberTheory.TwoPoint.Walks.WeightedWordEnvelope
import OAI.NumberTheory.TwoPoint.Bounds.BoundedPaddingUnion

namespace OAI

/-! Sum full centered-word averages against the numerical witness catalog. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem centered_words_le_witness_catalog {ι τ : Type*}
    [Fintype ι] [Fintype τ] [DecidableEq ι] {D n : ℕ} (slots : ℕ → ℕ)
    (P Q : Finset ℕ) (F : Finset (List SignedStep))
    (p : ι → ℕ) (hinj : Function.Injective p) (B h s J : ℕ)
    (supply : ℕ → ℕ → Prop) (hp : ∀ i, 0 < p i) (hpB : ∀ i, p i ≤ B)
    (hP : ∀ q ∈ P, q.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (hcover : ∀ q ∈ P ∪ Q, ∃ i, p i = q)
    (label : List SignedStep → τ → ι) (target : List SignedStep → τ → Fin B)
    (base : ι → Fin B) (R G : List SignedStep → (ι → Fin B) → ℝ)
    (C : List SignedStep → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (htarget : ∀ main ∈ F, ∀ t, (target main t).val < p (label main t))
    (hR : ∀ main ∈ F, ∀ x, 0 ≤ R main x)
    (hRC : ∀ main ∈ F, ∀ x, R main x ≤ C main)
    (hC : ∀ main ∈ F, 0 ≤ C main)
    (hG : ∀ main ∈ F, ∀ x, |G main x| ≤ 1)
    (hcost : ∀ main ∈ F,
      C main * 2 ^ (Fintype.card τ + (singletonLabels (label main)).card) ≤ K)
    (hRdep : ∀ main ∈ F, ∀ x y,
      (∀ i, i ∉ univ.image (label main) → x i = y i) → R main x = R main y)
    (hS : ∀ main ∈ F, ∀ i ∈ univ.image (label main), p i ∈ wordDivisorPrimeSupport main)
    (hsupport : ∀ main ∈ F, ∀ x,
      centeredWordEnvelope (label main) (target main) base (R main) (G main) x ≠ 0 →
      ∃ r : Fin (D + 1), ∃ d : WitnessRecord n r.val,
        ∃ e : PrimeWordEncoding r.val (slots r.val) P Q,
          EncodedPaddingWitnessEvent (univ.image (label main)) d e main p B h s J supply x) :
    (∑ main ∈ F,
      |(FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).average
        (fun x => R main x * (∏ t,
          ((if x (label main t) = target main t then (1 : ℝ) else 0) -
            (p (label main t) : ℝ)⁻¹)) * G main x)|) ≤
      K * ∑ r : Fin (D + 1), ∑ d : WitnessRecord n r.val,
        ∑ e : PrimeWordEncoding r.val (slots r.val) P Q,
          if e.Witnesses n d.1.1.val (fun i => (d.1.2.1 i).val)
            (fun i => (d.1.2.2 i).val) h s J supply then e.weight else 0 := by
  let μ := FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))
  let envelope (main : List SignedStep) :=
    centeredWordEnvelope (label main) (target main) base (R main) (G main)
  calc
    _ ≤ ∑ main ∈ F, (∏ i ∈ univ.image (label main), (p i : ℝ)⁻¹) *
        μ.average (fun x => |envelope main x|) := by
      apply sum_le_sum
      intro main hm
      have hb := uniform_weighted_centered_word_envelope B p hp hpB (label main)
        (target main) base (htarget main hm) (R main) (G main) (hR main hm) (hRdep main hm)
      have he : (fun x => |envelope main x|) = envelope main := by
        funext x
        exact abs_of_nonneg (centeredWordEnvelope_nonneg _ _ _ _ _ (hR main hm) x)
      rw [he]
      exact hb
    _ ≤ _ := by
      apply weighted_supported_padding_averages_le_catalog slots F
        (fun main => univ.image (label main)) p hinj B h s J supply hp hpB hP hQ
        hcover hS envelope K hK _ hsupport
      intro main hm x
      rw [abs_of_nonneg (centeredWordEnvelope_nonneg _ _ _ _ _ (hR main hm) x)]
      exact (centeredWordEnvelope_le (label main) (target main) base (R main) (G main)
        (C main) (hC main hm) (hRC main hm) (hG main hm) x).trans (hcost main hm)

end TwoPointCorrelations

end OAI
