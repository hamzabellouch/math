import OAI.RepresentationTheory.FoulkesHowe.MultilinearPolynomial
import OAI.RepresentationTheory.FoulkesHowe.SlotDerivative
import OAI.RepresentationTheory.FoulkesHowe.EncodingHomogeneous
import OAI.RepresentationTheory.FoulkesHowe.BlockInjectivity

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem346

/-- Cancel one directional derivative of a repeated-block multilinear polynomial.
It suffices that every single source-slot replacement vanishes; no normalization
or nonvanishing factorial is needed. -/
theorem multilinearPolynomial_eq_zero_of_replacements
    {V S I B : Type*} [AddCommGroup V] [Module ℂ V]
    [Fintype S] [Fintype I] [Fintype B] [hS : DecidableEq S] [hB : DecidableEq B]
    (L : MultilinearMap ℂ (fun _ : S => V) ℂ) (e : I → V)
    (blocks : S → B) (src dst : B) (hsd : src ≠ dst)
    (hdegree : (Finset.univ.filter (fun s => blocks s = dst)).card <
      (Finset.univ.filter (fun s => blocks s = src)).card)
    (hzero : ∀ s, blocks s = src →
      multilinearPolynomial L e (Function.update blocks s dst) = 0) :
    multilinearPolynomial L e blocks = 0 := by
  classical
  have hS_eq : hS = Classical.decEq S := Subsingleton.elim _ _
  cases hS_eq
  have hB_eq : hB = Classical.decEq B := Subsingleton.elim _ _
  cases hB_eq
  apply PolynomialShift.eq_zero_of_shift_eq_zero src dst hsd hdegree
  · unfold PolynomialWeights.IsBlockHomogeneous PolynomialWeights.blockWeight
    simpa only [multilinearPolynomial] using
      EncodingDegree.blockHomogeneous_expansion
        (fun k => L (fun s => e (k s))) blocks src
  · unfold PolynomialWeights.IsBlockHomogeneous PolynomialWeights.blockWeight
    simpa only [multilinearPolynomial] using
      EncodingDegree.blockHomogeneous_expansion
        (fun k => L (fun s => e (k s))) blocks dst
  · have hd := SlotPolynomial.derivation_polynomial
      (fun k => L (fun s => e (k s))) blocks src dst
      (PolynomialShift.derivation src dst) (by intro b i; simp)
    have hz : (∑ s ∈ Finset.univ.filter (fun s => blocks s = src),
        SlotPolynomial.polynomial (fun k => L (fun s => e (k s)))
          (Function.update blocks s dst)) = 0 := by
      apply Finset.sum_eq_zero
      intro s hs
      simpa only [SlotPolynomial.polynomial, multilinearPolynomial] using
        hzero s (Finset.mem_filter.mp hs).2
    rw [hz] at hd
    simpa only [PolynomialShift.shift_apply, SlotPolynomial.polynomial,
      multilinearPolynomial] using hd

end Problem346

end

end OAI
