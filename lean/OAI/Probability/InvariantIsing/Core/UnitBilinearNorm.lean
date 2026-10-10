import OAI.Probability.InvariantIsing.Gaussian.BilinearGaussianMean
import OAI.Probability.InvariantIsing.Core.DenseFiniteMaximum

namespace OAI

/-! The Euclidean operator norm as the supremum of unit bilinear tests. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace
namespace InvariantIsing

abbrev UnitVector (E : Type*) [NormedAddCommGroup E] := {x : E // ‖x‖ = 1}

lemma unitVector_nonempty (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Nontrivial E] : Nonempty (UnitVector E) := by
  obtain ⟨x,hx⟩ := exists_norm_eq E (show (0 : ℝ) ≤ 1 by norm_num)
  exact ⟨⟨x,hx⟩⟩

lemma unitBilinear_le_norm {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] (T : E →L[ℝ] F)
    (p : UnitVector F × UnitVector E) : ⟪p.1.1,T p.2.1⟫ ≤ ‖T‖ := by
  calc
    _ ≤ ‖p.1.1‖*‖T p.2.1‖ := real_inner_le_norm _ _
    _ = ‖T p.2.1‖ := by rw [p.1.2,one_mul]
    _ ≤ ‖T‖*‖p.2.1‖ := T.le_opNorm _
    _ = ‖T‖ := by rw [p.2.2,mul_one]

theorem norm_eq_iSup_unitBilinear {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [Nonempty (UnitVector E)] [Nonempty (UnitVector F)] (T : E →L[ℝ] F) :
    ‖T‖ = ⨆ p : UnitVector F × UnitVector E, ⟪p.1.1,T p.2.1⟫ := by
  let f := fun p : UnitVector F × UnitVector E => ⟪p.1.1,T p.2.1⟫
  have hb : BddAbove (range f) := ⟨‖T‖,fun _ ⟨p,hp⟩ => hp ▸ unitBilinear_le_norm T p⟩
  have hnonneg : 0 ≤ ⨆ p, f p := by
    let u : UnitVector F := Classical.choice inferInstance
    let v : UnitVector E := Classical.choice inferInstance
    let un : UnitVector F := ⟨-u.1,by simp only [norm_neg,u.2]⟩
    have h₁ := le_ciSup hb (u,v)
    have h₂ := le_ciSup hb (un,v)
    change ⟪u.1,T v.1⟫ ≤ _ at h₁
    change ⟪-u.1,T v.1⟫ ≤ _ at h₂
    rw [inner_neg_left] at h₂
    linarith
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_of_unit_norm hnonneg
    intro v hv
    by_cases hz : T v = 0
    · simpa only [hz,norm_zero] using hnonneg
    have hn : ‖T v‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    let u : UnitVector F := ⟨‖T v‖⁻¹ • T v,by simp [norm_smul,hn]⟩
    have hh := le_ciSup hb (u,⟨v,hv⟩)
    change ⟪‖T v‖⁻¹ • T v,T v⟫ ≤ _ at hh
    simpa only [real_inner_smul_left,real_inner_self_eq_norm_mul_norm,
      ← mul_assoc,inv_mul_cancel₀ hn,one_mul] using hh
  · exact ciSup_le (unitBilinear_le_norm T)

lemma gaussianPattern_unitBilinear {N m : ℕ} (z : EuclideanSpace ℝ (Fin N × Fin m))
    (u : EuclideanSpace ℝ (Fin N)) (v : EuclideanSpace ℝ (Fin m)) :
    ⟪u,gaussianPatternEuclideanOperator z v⟫ = ∑ ij, (u ij.1*v ij.2)*z ij := by
  change (∑ i, (∑ j, z (i,j)*v j)*u i) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

end InvariantIsing

end

end OAI
