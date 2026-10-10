import OAI.NumberTheory.DukePrimeDegree.Geometry.RootProductShear

namespace OAI

/-! # Swapping adjacent noncommuting factors of actual root products -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma adjacent_root_mul_swap {n : ℕ} {a b c : Fin n}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (r s : ℝ) :
    Matrix.SpecialLinearGroup.transvection hab r * Matrix.SpecialLinearGroup.transvection hbc s =
      (Matrix.SpecialLinearGroup.transvection hbc s * Matrix.SpecialLinearGroup.transvection hab r) *
        Matrix.SpecialLinearGroup.transvection hac (r*s) := by
  calc
    _ = Matrix.SpecialLinearGroup.transvection hbc s *
        (Matrix.SpecialLinearGroup.transvection hbc (-s) *
          Matrix.SpecialLinearGroup.transvection hab r * Matrix.SpecialLinearGroup.transvection hbc s) := by
      rw [←Matrix.SpecialLinearGroup.transvection_inv hbc s]
      group
    _ = _ := by rw [adjacent_root_conjugation hab hbc hac]; exact (mul_assoc _ _ _).symm

def rootTripleForward {n : ℕ} {a b c : Fin n} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (z : (ℝ × ℝ) × ℝ) : G n :=
  (Matrix.SpecialLinearGroup.transvection hab z.1.1 *
    Matrix.SpecialLinearGroup.transvection hbc z.1.2) *
      Matrix.SpecialLinearGroup.transvection hac z.2

def rootTripleSwapped {n : ℕ} {a b c : Fin n} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (z : (ℝ × ℝ) × ℝ) : G n :=
  (Matrix.SpecialLinearGroup.transvection hbc z.1.2 *
    Matrix.SpecialLinearGroup.transvection hab z.1.1) *
      Matrix.SpecialLinearGroup.transvection hac z.2

lemma rootTripleForward_eq_swapped_shear {n : ℕ} {a b c : Fin n}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    rootTripleForward hab hbc hac = rootTripleSwapped hab hbc hac ∘ rootProductShear := by
  funext z
  dsimp [rootTripleForward,rootTripleSwapped,rootProductShear]
  rw [adjacent_root_mul_swap hab hbc hac,mul_assoc,←Matrix.SpecialLinearGroup.transvection_add]
  congr 2
  ring

lemma measurable_rootTripleSwapped {n : ℕ} {a b c : Fin n}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    Measurable (rootTripleSwapped hab hbc hac) := by
  apply Continuous.measurable
  exact (((continuous_rootTransvection hbc).comp continuous_fst.snd).mul
    ((continuous_rootTransvection hab).comp continuous_fst.fst)).mul
      ((continuous_rootTransvection hac).comp continuous_snd)

theorem ae_intrinsic_rootTriple_swap
    (d : ℕ) {a b c : Fin (d+1)} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ] :
    ∀ᵐ x ∂μ,
      (((intrinsicRootLeaf hab μ x).prod (intrinsicRootLeaf hbc μ x)).prod
        (intrinsicRootLeaf hac μ x)).map (rootTripleForward hab hbc hac) =
      (((intrinsicRootLeaf hab μ x).prod (intrinsicRootLeaf hbc μ x)).prod
        (intrinsicRootLeaf hac μ x)).map (rootTripleSwapped hab hbc hac) := by
  filter_upwards [ae_intrinsic_rootProductShear_preserves d hab hbc hac μ] with x hx
  rw [rootTripleForward_eq_swapped_shear hab hbc hac,
    ←Measure.map_map (measurable_rootTripleSwapped hab hbc hac) measurable_rootProductShear,hx]

end DukePrimeDegree

end

end OAI
