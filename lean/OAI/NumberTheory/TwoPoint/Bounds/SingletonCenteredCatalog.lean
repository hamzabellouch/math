import OAI.NumberTheory.TwoPoint.Bounds.CenteredWitnessCatalog
import OAI.NumberTheory.TwoPoint.Bounds.SingletonWordEnvelope

namespace OAI

/-! The complete singleton word contribution is bounded by the numerical witness catalog. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem singleton_centered_words_le_catalog {ι τ W : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype τ] [Fintype W] [DecidableEq W]
    (p : ι → ℕ) (hprime : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (B h s J n M D : ℕ) (P Q : Finset ℕ) (supply : ℕ → ℕ → Prop)
    (F : Finset (List SignedStep))
    (label : List SignedStep → τ → ι) (target : List SignedStep → τ → Fin B)
    (base : ι → Fin B) (R : List SignedStep → (ι → Fin B) → ℝ)
    (word : List SignedStep → W → List SignedStep)
    (attachment : List SignedStep → W → ℕ)
    (C : List SignedStep → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hpB : ∀ i, p i ≤ B) (hP : ∀ q ∈ P, q.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (hPQ : Disjoint P Q) (hcover : ∀ q ∈ P ∪ Q, ∃ i, p i = q)
    (htarget : ∀ main ∈ F, ∀ t, (target main t).val < p (label main t))
    (hR : ∀ main ∈ F, ∀ x, 0 ≤ R main x)
    (hRC : ∀ main ∈ F, ∀ x, R main x ≤ C main)
    (hC : ∀ main ∈ F, 0 ≤ C main)
    (hcost : ∀ main ∈ F,
      C main * 2 ^ (Fintype.card τ + (singletonLabels (label main)).card) ≤ K)
    (hRdep : ∀ main ∈ F, ∀ x y,
      (∀ i, i ∉ univ.image (label main) → x i = y i) → R main x = R main y)
    (hS : ∀ main ∈ F, ∀ i ∈ univ.image (label main), p i ∈ wordDivisorPrimeSupport main)
    (hatt : ∀ main ∈ F, ∀ w, attachment main w ≤ main.length)
    (hminimal : ∀ main ∈ F, ∀ w,
      MinimalWord (ForwardProhibited h s supply) (word main w))
    (hlen : ∀ main ∈ F, ∀ w, (word main w).length ≤ s)
    (hdivsq : ∀ main ∈ F, ∀ w t, t ∈ word main w → Squarefree (t.padding * t.tuple))
    (hcard : ∀ main ∈ F, ∀ w t, t ∈ word main w → t.tuple.primeFactors.card = J)
    (hsupport : ∀ main ∈ F, ∀ w q j, TuplePrimeAt (word main w) q j →
      ¬q ∣ h ∧ ∀ t ∈ word main w, ¬q ∣ t.padding)
    (hpad : ∀ main ∈ F, ∀ i ∈ singletonLabels (label main), ∀ w t,
      t ∈ word main w → ¬p i ∣ t.padding)
    (hwordcover : ∀ main ∈ F, ∀ w q,
      q ∈ wordDivisorPrimeSupport (word main w) → ∃ i, p i = q)
    (position : ∀ main, singletonLabels (label main) → ℕ)
    (hmain : ∀ main ∈ F, ∀ i : singletonLabels (label main), ∀ v,
      TuplePrimeAt main (p i) v → v = position main i)
    (hretain : ∀ main ∈ F, ∀ x,
      R main x ≠ 0 → RetainedMainTests p (univ.image (label main)) h B main x)
    (hmainvalid : ∀ main ∈ F, ∀ t ∈ main, WitnessStepAdmissible P Q J M t)
    (hwordvalid : ∀ main ∈ F, ∀ w t, t ∈ word main w → WitnessStepAdmissible P Q J M t)
    (hD : ∀ main ∈ F, main.length + n * s ≤ D)
    (hn : ∀ main ∈ F, n * (s * J) < (singletonLabels (label main)).card) :
    (∑ main ∈ F,
      |(FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hprime i).pos (hpB i))).average
        (fun x => R main x * (∏ t,
          ((if x (label main t) = target main t then (1 : ℝ) else 0) -
            (p (label main t) : ℝ)⁻¹)) *
          witnessAvoidance (fun w z => decide (AttachedResiduePositiveWord p h (word main w)
            (wordDisplacement h (main.take (attachment main w))) B z)) x)|) ≤
      K * ∑ r : Fin (D + 1), ∑ d : WitnessRecord n r.val,
        ∑ e : PrimeWordEncoding r.val (r.val * (J + M)) P Q,
          if e.Witnesses n d.1.1.val (fun i => (d.1.2.1 i).val)
            (fun i => (d.1.2.2 i).val) h s J supply then e.weight else 0 := by
  apply centered_words_le_witness_catalog (fun r => r * (J + M)) P Q F p hinj B h s J supply
    (fun i => (hprime i).pos) hpB hP hQ hcover label target base R _ C K hK
    htarget hR hRC hC (fun _ _ x => witnessAvoidance_abs_le_one _ x) hcost hRdep hS
  intro main hm x hx
  exact singleton_envelope_has_padding_witness (label main) p hprime hinj B h s J n M D
    P Q supply main (word main) (attachment main) (target main) base x (R main)
    (hatt main hm) (hminimal main hm) (hlen main hm) (hdivsq main hm) (hcard main hm)
    (hsupport main hm) (hpad main hm) (hwordcover main hm) (position main) (hmain main hm)
    (hretain main hm x) (hmainvalid main hm) (hwordvalid main hm) hP hPQ (hD main hm)
    (hn main hm) hx

end TwoPointCorrelations

end OAI
