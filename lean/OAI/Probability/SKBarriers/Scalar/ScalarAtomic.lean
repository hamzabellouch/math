import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarMassOne

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def quantileAtomLaw (k : ℕ) (Q : Fin (k+1) → ℝ) : Measure ℝ :=
  ∑ j : Fin (k+1), ENNReal.ofReal (((k+1:ℕ):ℝ)⁻¹) • Measure.dirac (Q j)

theorem quantileAtomLaw_apply (k : ℕ) (Q : Fin (k+1) → ℝ) (s : Set ℝ) [DecidablePred (· ∈ s)] :
    quantileAtomLaw k Q s = ENNReal.ofReal (∑ j : Fin (k+1), if Q j ∈ s then ((k+1:ℕ):ℝ)⁻¹ else 0) := by
  classical
  rw [quantileAtomLaw,Measure.finsetSum_apply,ENNReal.ofReal_sum_of_nonneg (fun j _ => by split_ifs <;> positivity)]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Measure.smul_apply,smul_eq_mul,Measure.dirac_apply,Set.indicator_apply,Pi.one_apply]
  split_ifs <;> simp

instance quantileAtomLaw_probability (k : ℕ) (Q : Fin (k+1) → ℝ) : IsProbabilityMeasure (quantileAtomLaw k Q) := by
  constructor
  rw [quantileAtomLaw_apply]
  simp only [Set.mem_univ,ite_true,uniformAtom_sum,ENNReal.ofReal_one]

def quantileCDF (k : ℕ) (Q : Fin (k+1) → ℝ) (s : ℝ) : ℝ := (quantileAtomLaw k Q).real (Set.Iic s)

theorem quantileCDF_formula (k : ℕ) (Q : Fin (k+1) → ℝ) (s : ℝ) :
    quantileCDF k Q s = ∑ j : Fin (k+1), if Q j ≤ s then ((k+1:ℕ):ℝ)⁻¹ else 0 := by
  rw [quantileCDF,Measure.real,quantileAtomLaw_apply,ENNReal.toReal_ofReal]
  · rfl
  · exact Finset.sum_nonneg (fun j _ => by split_ifs <;> positivity)

theorem quantileAtomLaw_supported (k : ℕ) (Q : Fin (k+1) → ℝ) (hQ : ∀ j, Q j ∈ Set.Icc 0 1) :
    quantileAtomLaw k Q (Set.Icc 0 1) = 1 := by
  rw [quantileAtomLaw_apply]
  simp only [hQ,ite_true,uniformAtom_sum,ENNReal.ofReal_one]

theorem quantileCDF_integral (k : ℕ) (Q : Fin (k+1) → ℝ) (hQ : ∀ j, Q j ∈ Set.Icc 0 1) :
    (∫ s in Set.Icc (0:ℝ) 1, s*quantileCDF k Q s) =
      (1-∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(Q j)^2)/2 := by
  have he (s : ℝ) : s*quantileCDF k Q s =
      ∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(Set.Ici (Q j)).indicator (fun x => x) s := by
    rw [quantileCDF_formula,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Set.indicator_apply,Set.mem_Ici]
    split_ifs <;> ring
  have hi (j : Fin (k+1)) : IntegrableOn ((Set.Ici (Q j)).indicator (fun x : ℝ => x)) (Set.Icc (0:ℝ) 1) :=
    (continuous_id.integrableOn_Icc).indicator measurableSet_Ici
  simp_rw [he]
  rw [integral_finsetSum _ (fun j _ => (hi j).const_mul _)]
  have hI (j : Fin (k+1)) : (∫ s in Set.Icc (0:ℝ) 1,
      ((k+1:ℕ):ℝ)⁻¹*(Set.Ici (Q j)).indicator (fun x => x) s) =
      ((k+1:ℕ):ℝ)⁻¹*((1-(Q j)^2)/2) := by
    rw [integral_const_mul,setIntegral_indicator measurableSet_Ici]
    have hs : Set.Icc (0:ℝ) 1 ∩ Set.Ici (Q j) = Set.Icc (Q j) 1 := by
      ext x
      simp only [Set.mem_inter_iff,Set.mem_Icc,Set.mem_Ici]
      constructor
      · intro H; exact ⟨H.2,H.1.2⟩
      · intro H; exact ⟨⟨(hQ j).1.trans H.1,H.2⟩,H.1⟩
    rw [hs,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (hQ j).2,integral_id,one_pow]
  simp_rw [hI]
  have he' (j : Fin (k+1)) : ((k+1:ℕ):ℝ)⁻¹*((1-(Q j)^2)/2) =
      (((k+1:ℕ):ℝ)⁻¹-((k+1:ℕ):ℝ)⁻¹*(Q j)^2)/2 := by ring
  simp_rw [he']
  rw [← Finset.sum_div,Finset.sum_sub_distrib,uniformAtom_sum]

def atomicScalarValue (k : ℕ) (β : ℝ) (Q : Fin (k+1) → ℝ) : ℝ :=
  scalarHierarchy (k+1) (quantileMass k)
    (fun b => β*Real.sqrt (cumulativeGapMap k Q b))
    (scalarStep 1 (β*Real.sqrt (1-Q (Fin.last k))) scalarSpinTerminal) 0

def atomicParisi (k : ℕ) (β : ℝ) (Q : Fin (k+1) → ℝ) : ℝ :=
  atomicScalarValue k β Q-(β^2/2)*∫ s in Set.Icc (0:ℝ) 1, s*quantileCDF k Q s

theorem atomicParisi_eq_extended (k : ℕ) (β : ℝ) (Q : Fin (k+1) → ℝ)
    (hQ : ∀ j, Q j ∈ Set.Icc 0 1) :
    atomicParisi k β Q = extendedQuantileParisi k β Q := by
  rw [atomicParisi,atomicScalarValue,scalar_quantile_terminal_shift k β Q (hQ (Fin.last k)).2,
    quantileCDF_integral k Q hQ,extendedQuantileParisi]
  ring
end SK.Analytic

end
end

end

end OAI
