import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import OAI.Analysis.Laughlin.Operators.CollectionAnnihilatorBound
import OAI.Analysis.Laughlin.Pair.FockHaar

namespace OAI

namespace Laughlin.Fock
open Rotation MeasureTheory
open scoped BigOperators

theorem linearMap_rotation_coordinate_continuous (Q : ℕ) (L : Module.End ℂ (Space Q))
    (x : Space Q) (A : Finset (Fin (Q+1))) :
    Continuous (fun g : SourceSU2 => (occupationBasis Q).repr (L (exteriorRotation Q g⁻¹ x)) A) := by
  have he (g : SourceSU2) : (occupationBasis Q).repr (L (exteriorRotation Q g⁻¹ x)) A =
      ∑ B, (occupationBasis Q).repr (exteriorRotation Q g⁻¹ x) B *
        (occupationBasis Q).repr (L (occupationBasis Q B)) A := by
    conv_lhs => rw [← (occupationBasis Q).sum_repr (exteriorRotation Q g⁻¹ x)]
    simp only [map_sum,map_smul,Finsupp.finsetSum_apply,Finsupp.smul_apply,smul_eq_mul]
  simp_rw [he]
  apply continuous_finsetSum
  intro B hB
  exact ((exteriorRotation_coordinate_continuous Q x B).comp continuous_inv).mul continuous_const

theorem linearMap_rotation_norm_continuous (Q : ℕ) (L : Module.End ℂ (Space Q)) (x : Space Q) :
    Continuous (fun g : SourceSU2 => occupationNormSq Q (L (exteriorRotation Q g⁻¹ x))) := by
  unfold occupationNormSq
  apply continuous_finsetSum
  intro A hA
  exact (linearMap_rotation_coordinate_continuous Q L x A).norm.pow 2

theorem linearMap_rotation_norm_integrable (Q : ℕ) (L : Module.End ℂ (Space Q)) (x : Space Q) :
    Integrable (fun g : SourceSU2 => occupationNormSq Q (L (exteriorRotation Q g⁻¹ x))) sourceHaar :=
  (linearMap_rotation_norm_continuous Q L x).integrable_of_hasCompactSupport
    (isClosed_tsupport _).isCompact

theorem physical_pair_norm_haar_real (Q : ℕ) (hQ : 0 < Q) (p : Fin (2*Q-2+1)) (x : Space Q) :
    (∫ g, occupationNormSq Q (sourcePairEnd Q p.val (exteriorRotation Q g⁻¹ x)) ∂sourceHaar) =
      sourceFockEnergy Q x/(2*Q-2+1 : ℕ) := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal,physical_pair_norm_haar Q hQ]
  push_cast
  rfl

theorem sourcePairWindow_haar (Q : ℕ) (hQ : 25 ≤ Q) (x : Space Q) :
    (2*Q-2+1 : ℕ) * (∫ g, sourcePairWindow Q (exteriorRotation Q g⁻¹ x) ∂sourceHaar) =
      24 * sourceFockEnergy Q x := by
  unfold sourcePairWindow
  rw [integral_finsetSum _ (fun p hp => linearMap_rotation_norm_integrable Q _ x)]
  have hp (p : ℕ) (h : p ∈ Finset.range 24) :
      (∫ g, occupationNormSq Q (sourcePairEnd Q p (exteriorRotation Q g⁻¹ x)) ∂sourceHaar) =
      sourceFockEnergy Q x/(2*Q-2+1 : ℕ) :=
    physical_pair_norm_haar_real Q (by omega) ⟨p,by simp only [Finset.mem_range] at h; omega⟩ x
  rw [Finset.sum_congr rfl hp]
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  have hd : ((2*Q-2+1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  ring

end Laughlin.Fock

end OAI
