import OAI.Geometry.HeilbronnTriangle.MainDigitLaw
import OAI.Geometry.HeilbronnTriangle.AuxiliarySamplingLaw
import OAI.Geometry.HeilbronnTriangle.PrimeLiftParameters

namespace OAI


noncomputable section

attribute [local irreducible] Problem355.heilbronnT Problem355.heilbronnM

namespace Problem355.ActualPointLaw

open Parameters FiniteFieldLabels

section WithAuxiliary
variable {r : ℕ} [Fact r.Prime] [Fintype (Label r)]

def withAuxiliary (D : PrimeParameterData heilbronnK r)
    [Fact D.q.Prime] (A : AuxiliarySampling.Law D.q (D.h ^ 2)) :
    ParameterSampling.PointLaw := by
  letI : NeZero (r ^ 9) := ⟨pow_ne_zero _ D.r_pos.ne'⟩
  exact PrimeLiftParameters.pointLaw D A.size A.size_pos A.weight
    (DigitColumnLaw.uniformWeight (MainDigitLaw.Latent r))
    (MainDigitLaw.column D) A.sets A.weight_nonneg A.weight_sum
    (DigitColumnLaw.uniformWeight_nonneg _) (DigitColumnLaw.sum_uniformWeight _)
    A.sets_card

theorem withAuxiliary_pairProbability_le
    (D : PrimeParameterData heilbronnK r)
    [Fact D.q.Prime] (A : AuxiliarySampling.Law D.q (D.h ^ 2)) :
    (withAuxiliary D A).pairProbability ≤
      8 * (D.M : ℝ) ^ 6 / (D.N : ℝ) ^ 3 := by
  unfold withAuxiliary
  apply PrimeLiftParameters.pairProbability_le

end WithAuxiliary

variable {r : ℕ} [Fact r.Prime]

def pointLaw (D : PrimeParameterData heilbronnK r) : ParameterSampling.PointLaw := by
  letI : Fintype (Label r) := Fintype.ofFinite (Label r)
  letI : Fact D.q.Prime := ⟨D.auxiliary_prime⟩
  have hH : 1 ≤ D.h ^ 2 := Nat.one_le_pow _ _ D.h_pos
  exact withAuxiliary D (Classical.choice
    (AuxiliarySampling.nonempty_law hH D.auxiliary_large))

theorem pairProbability_le (D : PrimeParameterData heilbronnK r) :
    (pointLaw D).pairProbability ≤ 8 * (D.M : ℝ) ^ 6 / (D.N : ℝ) ^ 3 := by
  let : Fintype (Label r) := Fintype.ofFinite (Label r)
  let : Fact D.q.Prime := ⟨D.auxiliary_prime⟩
  unfold pointLaw
  apply withAuxiliary_pairProbability_le

end Problem355.ActualPointLaw

end

end OAI
