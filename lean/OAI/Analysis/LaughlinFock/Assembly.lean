import Mathlib
import OAI.Analysis.LaughlinFock.CertificateRows
import OAI.Analysis.LaughlinFock.FourBound

namespace OAI

/-! Assembly. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder
open Filter Topology

 

theorem integer_threshold_of_certificates_le {ι : Type*} [Fintype ι]
    (rows : ι → ComparisonRow)
    (hEta : rowsEta rows ≤ 93527408868499 / 10^14)
    (hThree : ∀ z : ComparedThreeBlock,
      planarRowsThreeTrace rows z.val.val <
        (3/2 : ℝ)*(3*(z.val.val : ℝ)-1)*(-1/2)^z.val.val)
    (hFour : ∀ D, 1 ≤ D → D ≤ 23 →
      (planarFourGram D * planarFourComparison rows (3/10^6) D * planarFourGram D).PosSemidef)
    (γ : ℝ) (hγ : γ < gammaStar) :
    ∃ Qγ : ℤ, 1 ≤ Qγ ∧ ∀ Q : ℤ, Qγ ≤ Q → FockInequality Q.toNat γ := by
  obtain ⟨e, _, helim, hb⟩ :=
    fockInequality_eventual_of_certificates rows (3/10^6) (by norm_num) hThree hFour
  have hl : Tendsto (fun Q => 1-(93527408868499 / 10^14 : ℝ)-
      tailCoefficient Q-1222*(3/10^6)-e Q) atTop (𝓝 gammaStar) := by
    have h := (((tendsto_const_nhds (x := 1-(93527408868499 / 10^14 : ℝ))).sub
      tailCoefficient_tendsto).sub_const (1222*(3/10^6))).sub helim
    simpa only [sub_zero, final_margin_arithmetic] using h
  apply uniform_integer_threshold_of_eventual_bound _ hl _ γ hγ
  filter_upwards [hb] with Q hQ
  exact hQ.mono (by linarith only [hEta])

theorem certificateEta_le : rowsEta certificateRows ≤ 93527408868499 / 10^14 := by
  rw [certificateEta]
  norm_num

end LaughlinFock
end

end OAI
