import OAI.Analysis.Pureness.States.FiniteFamilyBlockValues
import OAI.Analysis.Pureness.Quasitrace.ComplexQuasitracePositive
import OAI.Analysis.Pureness.Operators.WeightedMatrixColumn
import OAI.Analysis.Pureness.Operators.WeightedScalarOptimization
import OAI.Analysis.Pureness.Quasitrace.QuasitraceMetricFromSqrt

namespace OAI
noncomputable section
namespace CuntzPureness.CompatibleFiniteQuasitrace
open CuntzTrace
open scoped NNReal CStarAlgebra
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (F : CompatibleFiniteQuasitrace A)
variable (hmono : ∀ n, Monotone (fun a : Positive (FinMatrix A n) => (F.level n a.1).re))

def positiveLevel (n : ℕ) : PositiveQuasitrace (FinMatrix A n) :=
  (F.level n).toPositiveQuasitrace (hmono n)

lemma positiveLevel_block_add (n : ℕ) (M N : Positive (FinMatrix A n)) :
    F.positiveLevel hmono (n*2) (Positive.map (matrixInterleave n) (positiveProduct M N)) =
      F.positiveLevel hmono n M+F.positiveLevel hmono n N := F.block_add_re n M N

private lemma positive_square_root (a : Positive A) :
    ∃ b : A, star b = b ∧ b * b = a.1 :=
  ⟨CFC.sqrt a.1, (CFC.sqrt_nonneg a.1).star_eq, CFC.sqrt_mul_sqrt_self a.1 a.2⟩

theorem positiveLevel_add_weighted
    (n : ℕ) (M N : Positive (FinMatrix A n)) (r : ℝ) (hr : r ≠ 0) :
    F.positiveLevel hmono n (Positive.add M N) ≤
      (1+r*r)*F.positiveLevel hmono n M +
      (1+r⁻¹*r⁻¹)*F.positiveLevel hmono n N := by
  obtain ⟨a, ha, haa⟩ := positive_square_root M
  obtain ⟨b, hb, hbb⟩ := positive_square_root N
  let e := CStarMatrix.reindexₐ ℂ A (finProdFinEquiv : (Fin n × Fin 2) ≃ Fin (n*2))
  let y := e (finiteOrthogonalColumn n (a) (b))
  let z := e (finiteOrthogonalColumn n (r • a) (-(r⁻¹ • b)))
  let u : ℝ≥0 := ⟨1+r*r,by nlinarith [sq_nonneg r]⟩
  let v : ℝ≥0 := ⟨1+r⁻¹*r⁻¹,by nlinarith [sq_nonneg r⁻¹]⟩
  have hl : Positive.starMul y = Positive.map (matrixInterleave n)
      (positiveProduct (Positive.add M N) Positive.zero) := by
    apply Subtype.ext
    change star (e (finiteOrthogonalColumn n (a) (b))) *
      e (finiteOrthogonalColumn n (a) (b)) =
      e (matrixInterleaveRaw n (M.1+N.1,0))
    rw [← map_star,← map_mul,finiteOrthogonalColumn_starMul,
      ha, hb, haa, hbb]
  have he : y*star y+z*star z =
      (Positive.map (matrixInterleave n) (positiveProduct (Positive.smul u M) (Positive.smul v N))).1 := by
    change e (finiteOrthogonalColumn n (a) (b))*
      star (e (finiteOrthogonalColumn n (a) (b)))+
      e (finiteOrthogonalColumn n (r • a) (-(r⁻¹ • b)))*
      star (e (finiteOrthogonalColumn n (r • a) (-(r⁻¹ • b)))) =
      e (matrixInterleaveRaw n ((1+r*r) • M.1,(1+r⁻¹*r⁻¹) • N.1))
    rw [← map_star,← map_star,← map_mul,← map_mul,← map_add,
      finiteOrthogonalColumn_weighted n _ _ r hr,
      ha, hb, haa, hbb]
  have ho : Positive.mulStar y ≤ Positive.map (matrixInterleave n)
      (positiveProduct (Positive.smul u M) (Positive.smul v N)) := by
    change y*star y ≤ _
    rw [← he]
    exact le_add_of_nonneg_right (mul_star_self_nonneg z)
  have h := ((F.positiveLevel hmono (n*2)).polar y).le.trans
    ((F.positiveLevel hmono (n*2)).monotone ho)
  rw [hl,F.positiveLevel_block_add,PositiveQuasitrace.map_zero,add_zero,
    F.positiveLevel_block_add,PositiveQuasitrace.map_smul,PositiveQuasitrace.map_smul] at h
  exact h

theorem positiveLevel_sqrt_add (n : ℕ) (M N : Positive (FinMatrix A n)) :
    Real.sqrt (F.positiveLevel hmono n (Positive.add M N)) ≤
      Real.sqrt (F.positiveLevel hmono n M)+Real.sqrt (F.positiveLevel hmono n N) := by
  let T := F.positiveLevel hmono n
  have h := weighted_scalar_sqrt_bound (T M) (T N) (T (Positive.add M N))
    (T.nonneg M) (T.nonneg N) (fun r hr => F.positiveLevel_add_weighted hmono n M N r hr)
  exact Real.sqrt_le_iff.mpr ⟨by positivity,h⟩

theorem positiveLevel_metricSize_add (n : ℕ) (x y : FinMatrix A n) :
    (F.positiveLevel hmono n).metricSize (x+y) ≤
      (F.positiveLevel hmono n).metricSize x+(F.positiveLevel hmono n).metricSize y :=
  (F.positiveLevel hmono n).metricSize_add_of_sqrt_add (F.positiveLevel_sqrt_add hmono n) x y
end CuntzPureness.CompatibleFiniteQuasitrace

end

end OAI
