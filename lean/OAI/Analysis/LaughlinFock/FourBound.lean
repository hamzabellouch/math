import Mathlib
import OAI.Analysis.LaughlinFock.FourRetained
import OAI.Analysis.LaughlinFock.TailOrbit

namespace OAI

/-! Four Bound. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder
open Filter Topology

 

theorem averagedRowsFour_eventual_bound {ι : Type*} [Fintype ι]
    (rows : ι → ComparisonRow) (ε : ℝ) (hε : 0 ≤ ε)
    (hCertificate : ∀ D, 1 ≤ D → D ≤ 23 →
      (planarFourGram D * planarFourComparison rows ε D * planarFourGram D).PosSemidef) :
    ∃ e : ℕ → ℝ, (∀ Q, 0 ≤ e Q) ∧ Tendsto e atTop (𝓝 0) ∧
      ∀ Q, (hQ : 24 ≤ Q) →
        (exteriorLift Q 4 (fourWedgeMatrix Q * (fourWedgeMatrix Q)ᴴ) +
          (1222*ε+e Q) • hamiltonian Q -
          averagedRowsFour (by omega : 8 ≤ Q) rows).PosSemidef := by
  obtain ⟨e, hepos, helim, he⟩ := averagedFourComparison_transfer rows ε hCertificate
  refine ⟨e, hepos, helim, ?_⟩
  intro Q hQ
  have h := he Q hQ
  rw [averagedFourComparison_eq rows ε hQ] at h
  have hr : (1222 : ℂ) • hamiltonian Q = (1222 : ℝ) • hamiltonian Q := by
    rw [RCLike.real_smul_eq_coe_smul (K:=ℂ)]
    norm_num [RCLike.ofReal_eq_complex_ofReal]
  have hallow := (fourCopyAllowance_bound hQ).smul hε
  rw [hr] at hallow
  have hdisc := discardedFourTarget_lift_posSemidef Q 23 (by omega)
  convert (h.add hallow).add hdisc using 1
  simp only [smul_sub, smul_smul, add_smul, mul_comm ε (1222:ℝ)]
  abel

 

theorem fockInequality_eventual_of_certificates {ι : Type*} [Fintype ι]
    (rows : ι → ComparisonRow) (ε : ℝ) (hε : 0 ≤ ε)
    (hThree : ∀ z : ComparedThreeBlock,
      planarRowsThreeTrace rows z.val.val <
        (3/2 : ℝ)*(3*(z.val.val : ℝ)-1)*(-1/2)^z.val.val)
    (hFour : ∀ D, 1 ≤ D → D ≤ 23 →
      (planarFourGram D * planarFourComparison rows ε D * planarFourGram D).PosSemidef) :
    ∃ e : ℕ → ℝ, (∀ Q, 0 ≤ e Q) ∧ Tendsto e atTop (𝓝 0) ∧
      ∀ᶠ Q in atTop, FockInequality Q (1-rowsEta rows-tailCoefficient Q-1222*ε-e Q) := by
  obtain ⟨e, hepos, helim, he⟩ := averagedRowsFour_eventual_bound rows ε hε hFour
  refine ⟨e, hepos, helim, ?_⟩
  filter_upwards [threeTraceForm_eventual_bound rows hThree, eventually_ge_atTop 24] with Q h3 hQ
  have htail : (tailThreeTarget Q + tailCoefficient Q • hamiltonian Q).PosSemidef := by
    rw [RCLike.real_smul_eq_coe_smul (K:=ℂ), RCLike.ofReal_eq_complex_ofReal]
    exact tailThreeTarget_relative_bound (Q:=Q) (by omega)
  have hf := fockInequality_of_finite_comparisons rows (by omega : 16 ≤ Q)
    (averagedRowsFour (by omega : 8 ≤ Q) rows) (tailCoefficient Q) (1222*ε+e Q)
    (averagedRows_positive rows (by omega)) h3 (he Q hQ) htail
  convert hf using 1
  ring

 

theorem integer_threshold_of_certificates {ι : Type*} [Fintype ι]
    (rows : ι → ComparisonRow)
    (hEta : rowsEta rows = 93527408868499 / 10^14)
    (hThree : ∀ z : ComparedThreeBlock,
      planarRowsThreeTrace rows z.val.val <
        (3/2 : ℝ)*(3*(z.val.val : ℝ)-1)*(-1/2)^z.val.val)
    (hFour : ∀ D, 1 ≤ D → D ≤ 23 →
      (planarFourGram D * planarFourComparison rows (3/10^6) D * planarFourGram D).PosSemidef)
    (γ : ℝ) (hγ : γ < gammaStar) :
    ∃ Qγ : ℤ, 1 ≤ Qγ ∧ ∀ Q : ℤ, Qγ ≤ Q → FockInequality Q.toNat γ := by
  obtain ⟨e, _, helim, hb⟩ :=
    fockInequality_eventual_of_certificates rows (3/10^6) (by norm_num) hThree hFour
  exact uniform_integer_threshold_of_eventual_bound _
    (final_coefficient_tendsto rows hEta e helim) hb γ hγ

end LaughlinFock
end

end OAI
