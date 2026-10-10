import OAI.LinearAlgebra.MatrixMultiplication.Numerical.CurveLawsCertificates
import OAI.LinearAlgebra.MatrixMultiplication.Entropy.ConditionalContinuity
import OAI.LinearAlgebra.MatrixMultiplication.Entropy.ConditionalRateBridge

namespace OAI

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

noncomputable section

namespace MatrixMultiplication.CurveLaws

open MatrixMultiplication.Foundation ComplexWitness ConditionalLabels Filter
open scoped BigOperators Topology

theorem exists_rational_rate_bounds :
    ∃ q : RationalLaw CurveLeaf,
      (31519 : ℝ) / 10000 <
        lawPairingRate q.toFiniteLaw curveLabels 5 curveReaderPair .xy +
          lawPairingRate q.toFiniteLaw curveLabels 5 curveReaderPair .xz ∧
      lawPairingRate q.toFiniteLaw curveLabels 5 curveReaderPair .xy +
          lawPairingRate q.toFiniteLaw curveLabels 5 curveReaderPair .xz <
        (15761 : ℝ) / 5000 ∧
      (27961 : ℝ) / 25000 <
        lawPairingRate q.toFiniteLaw curveLabels 5 curveReaderPair .yz ∧
      lawPairingRate q.toFiniteLaw curveLabels 5 curveReaderPair .yz <
        (6991 : ℝ) / 6250 := by
  obtain ⟨q, hq⟩ := exists_rational_law_sequence (leafLaw (2 / 3 : ℝ))
  have hi := (tendsto_lawPairingRate hq curveLabels 5 curveReaderPair .xy).add
    (tendsto_lawPairingRate hq curveLabels 5 curveReaderPair .xz)
  have hh := tendsto_lawPairingRate hq curveLabels 5 curveReaderPair .yz
  rw [incident_rate_two_thirds] at hi
  rw [hidden_rate_two_thirds] at hh
  have hilo := hi.eventually_const_lt ComplexCertificates.curveH_bounds.1
  have hihi := hi.eventually_lt_const ComplexCertificates.curveH_bounds.2
  have hhlo := hh.eventually_const_lt ComplexCertificates.curveG_bounds.1
  have hhhi := hh.eventually_lt_const ComplexCertificates.curveG_bounds.2
  obtain ⟨n, hn⟩ := (hilo.and (hihi.and (hhlo.and hhhi))).exists
  exact ⟨q n, hn⟩

theorem exists_count_rate_bounds :
    ∃ counts : CurveLeaf → ℕ, ∃ hD : 0 < ∑ a, counts a,
      (31519 : ℝ) / 10000 <
        lawPairingRate (normalizedCountLaw counts hD) curveLabels 5 curveReaderPair .xy +
          lawPairingRate (normalizedCountLaw counts hD) curveLabels 5 curveReaderPair .xz ∧
      lawPairingRate (normalizedCountLaw counts hD) curveLabels 5 curveReaderPair .xy +
          lawPairingRate (normalizedCountLaw counts hD) curveLabels 5 curveReaderPair .xz <
        (15761 : ℝ) / 5000 ∧
      (27961 : ℝ) / 25000 <
        lawPairingRate (normalizedCountLaw counts hD) curveLabels 5 curveReaderPair .yz ∧
      lawPairingRate (normalizedCountLaw counts hD) curveLabels 5 curveReaderPair .yz <
        (6991 : ℝ) / 6250 := by
  obtain ⟨q, hq⟩ := exists_rational_rate_bounds
  obtain ⟨counts, hD, hmass⟩ := q.exists_type_representation
  have law_eq (p r : FiniteLaw CurveLeaf) (h : p.mass = r.mass) : p = r := by
    cases p
    cases r
    cases h
    rfl
  have heq : normalizedCountLaw counts hD = q.toFiniteLaw :=
    law_eq _ _ (funext hmass)
  refine ⟨counts, hD, ?_⟩
  simpa only [heq] using hq

end MatrixMultiplication.CurveLaws

end

end OAI
