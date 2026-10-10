import OAI.Analysis.Pureness.Operators.WeightedMatrixColumn
import OAI.Analysis.Pureness.Quasitrace.PositiveQuasitrace

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace
open scoped NNReal ENNReal CStarAlgebra
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

private lemma positive_square_root (a : Positive A) :
    ∃ b : A, star b = b ∧ b * b = a.1 :=
  ⟨CFC.sqrt a.1, (CFC.sqrt_nonneg a.1).star_eq, CFC.sqrt_mul_sqrt_self a.1 a.2⟩

theorem finiteSpectralIntegral_add_weighted
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (n : ℕ) (M N : Positive (FinMatrix A n)) (r : ℝ) (hr : r ≠ 0) :
    finiteSpectralIntegral d n (Positive.add M N) ≤
      ENNReal.ofReal (1+r*r)*finiteSpectralIntegral d n M +
      ENNReal.ofReal (1+r⁻¹*r⁻¹)*finiteSpectralIntegral d n N := by
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
  have h := (finiteSpectralIntegral_polar d (n*2) y).le.trans
    (finiteSpectralIntegral_monotone d hd (n*2) ho)
  rw [hl,finiteSpectralIntegral_block_add d hd,finiteSpectralIntegral_zero,add_zero,
    finiteSpectralIntegral_block_add d hd,finiteSpectralIntegral_smul d hd,
    finiteSpectralIntegral_smul d hd] at h
  have hu : (u : ℝ≥0∞) = ENNReal.ofReal (1+r*r) := by change (u : ℝ≥0∞) = ENNReal.ofReal (u : ℝ); exact ENNReal.ofReal_coe_nnreal.symm
  have hv : (v : ℝ≥0∞) = ENNReal.ofReal (1+r⁻¹*r⁻¹) := by change (v : ℝ≥0∞) = ENNReal.ofReal (v : ℝ); exact ENNReal.ofReal_coe_nnreal.symm
  rwa [hu,hv] at h

theorem finiteSpectralPositiveQuasitrace_add_weighted
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (hlsc : ∀ n, LowerSemicontinuous (fun M : Positive (FinMatrix A n) => d (finitePositiveClass n M)))
    (hfinite : ∀ x, d x ≠ ⊤)
    (n : ℕ) (M N : Positive (FinMatrix A n)) (r : ℝ) (hr : r ≠ 0) :
    finiteSpectralPositiveQuasitrace d hd hlsc hfinite n (Positive.add M N) ≤
      (1+r*r)*finiteSpectralPositiveQuasitrace d hd hlsc hfinite n M +
      (1+r⁻¹*r⁻¹)*finiteSpectralPositiveQuasitrace d hd hlsc hfinite n N := by
  have h := finiteSpectralIntegral_add_weighted d hd n M N r hr
  have hm := finiteSpectralIntegral_ne_top d hd n M (hfinite _)
  have hn := finiteSpectralIntegral_ne_top d hd n N (hfinite _)
  have hu : 0 ≤ 1+r*r := by nlinarith [sq_nonneg r]
  have hv : 0 ≤ 1+r⁻¹*r⁻¹ := by nlinarith [sq_nonneg r⁻¹]
  have ht := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
    ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hm,ENNReal.mul_ne_top ENNReal.ofReal_ne_top hn⟩) h
  change (finiteSpectralIntegral d n (Positive.add M N)).toReal ≤
    (1+r*r)*(finiteSpectralIntegral d n M).toReal +
    (1+r⁻¹*r⁻¹)*(finiteSpectralIntegral d n N).toReal
  simpa only [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hm)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hn),ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hu,ENNReal.toReal_ofReal hv] using ht
end CuntzPureness

end

end OAI
