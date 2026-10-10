import OAI.GroupTheory.PolycyclicRecognition.Analysis.PairChartSampling
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialGroupLaws

namespace OAI

/-! # The coordinate maps of the actual two-factor chart samples -/

noncomputable section

namespace PolycyclicRecognition

open Module
open scoped NNReal

/-- A Lie-algebra identification transports the same binary Dynkin formula. -/
theorem model_binary_dynkin
    {L L' N : Type*} [LieRing L] [LieAlgebra ℝ L]
    [LieRing L'] [LieAlgebra ℝ L'] [Group N]
    (e : L ≃ₗ⁅ℝ⁆ L') (Exp : L' → N) {c : ℕ} (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (x y : L) :
    Exp (e (finiteDynkinPolynomial a ![x, y])) = Exp (e x) * Exp (e y) := by
  have he := congrArg Exp (finiteDynkinPolynomial_map e.toLieHom a ![x, y])
  have hv : (fun i => e.toLieHom (![x, y] i)) = ![e x, e y] := by
    funext i
    fin_cases i <;> rfl
  rw [hv] at he
  exact he.trans (hm (e x) (e y))

/-- The coordinate Dynkin product maps to the actual group product. -/
theorem exp_basis_dynkinProduct
    {L N : Type*} [LieRing L] [LieAlgebra ℝ L] [Group N]
    {n c : ℕ} (b : Basis (Fin n) ℝ L) (Exp : L → N)
    (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (x y : Fin n → ℝ) :
    Exp (b.equivFun.symm (dynkinProduct a (basisBracket b) x y)) =
      Exp (b.equivFun.symm x) * Exp (b.equivFun.symm y) := by
  have h := basis_dynkinProduct b a (b.equivFun.symm x) (b.equivFun.symm y)
  simp only [LinearEquiv.apply_symm_apply] at h
  rw [h, LinearEquiv.symm_apply_apply, hm]

variable {G N D LN LD : Type*} [Group G] [MetricSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G] [Group N] [Group D]
  [LieRing LN] [LieAlgebra ℝ LN] [LieRing LD] [LieAlgebra ℝ LD]
  {n d : ℕ} {Λ : ℝ≥0}

/-- The chart sample uses the actual factor exponentials and includes the
deterministic enlarged suffix. -/
def coordinateChartPoint (p : NormalizedPair G Λ) (x : G)
    (ι : N →* G) (κ : D →* G) (ExpN : LN → N) (ExpD : LD → D)
    (bN : Basis (Fin n) ℝ LN) (bD : Basis (Fin d) ℝ LD) (k : N)
    (z : (Fin n → ℝ) × (Fin d → ℝ)) : NormalizedPair G Λ :=
  chartOccupationPoint p x (ι (ExpN (bN.equivFun.symm z.1)))
    (ι k) (κ (ExpD (bD.equivFun.symm z.2)))

/-- The second-factor coordinate translation is exactly the normalized
action of the corresponding fixed group element. -/
theorem coordinateChartPoint_right
    (p : NormalizedPair G Λ) (x : G) (ι : N →* G) (κ : D →* G)
    (ExpN : LN → N) (ExpD : LD → D)
    (bN : Basis (Fin n) ℝ LN) (bD : Basis (Fin d) ℝ LD) (k : N)
    {c : ℕ} (a : DynkinCoefficients c 2)
    (hm : ∀ x y, ExpD (finiteDynkinPolynomial a ![x, y]) = ExpD x * ExpD y)
    (v : LD) (z : (Fin n → ℝ) × (Fin d → ℝ)) :
    (κ (ExpD v))⁻¹ • coordinateChartPoint p x ι κ ExpN ExpD bN bD k z =
      coordinateChartPoint p x ι κ ExpN ExpD bN bD k
        (z.1, dynkinProduct a (basisBracket bD) z.2 (bD.equivFun v)) := by
  unfold coordinateChartPoint
  rw [chartOccupationPoint_right_factor, exp_basis_dynkinProduct bD ExpD a hm,
    LinearEquiv.symm_apply_apply, map_mul]

/-- The first-factor move has precisely the suffix-conjugated coordinate
parameter appearing in interior slack. Its expression is derived from the
actual factor action, rather than assumed as a coordinate identity. -/
theorem coordinateChartPoint_normal
    (p : NormalizedPair G Λ) (x : G) (ι : N →* G) (κ : D →* G)
    (φ : D →* MulAut N)
    (hφ : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (ExpN : LN → N) (ExpD : LD → D) (logN : N → LN)
    (hlog : ∀ n, ExpN (logN n) = n)
    (bN : Basis (Fin n) ℝ LN) (bD : Basis (Fin d) ℝ LD) (k u : N)
    {c : ℕ} (a : DynkinCoefficients c 2)
    (hm : ∀ x y, ExpN (finiteDynkinPolynomial a ![x, y]) = ExpN x * ExpN y)
    (z : (Fin n → ℝ) × (Fin d → ℝ)) :
    (ι u)⁻¹ • coordinateChartPoint p x ι κ ExpN ExpD bN bD k z =
      coordinateChartPoint p x ι κ ExpN ExpD bN bD k
        (dynkinProduct a (basisBracket bN) z.1
          (bN.equivFun (logN (k * φ (ExpD (bD.equivFun.symm z.2)) u * k⁻¹))), z.2) := by
  unfold coordinateChartPoint
  rw [chartOccupationPoint_normal_factor, exp_basis_dynkinProduct bN ExpN a hm,
    LinearEquiv.symm_apply_apply, hlog]
  simp only [map_mul, map_inv, hφ, mul_assoc]

/-- When the factor action on exponentials has been identified, its exact
coordinate move is the double Dynkin product controlled by interior slack.
No logarithm of a group product is left as an extra assumption. -/
theorem coordinateChartPoint_normal_of_exponential_action
    (p : NormalizedPair G Λ) (x : G) (ι : N →* G) (κ : D →* G)
    (φ : D →* MulAut N)
    (hφ : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (ExpN : LN → N) (ExpD : LD → D)
    (hneg : ∀ v, ExpN (-v) = (ExpN v)⁻¹)
    (A : LD → LN → LN)
    (hact : ∀ d v, φ (ExpD d) (ExpN v) = ExpN (A d v))
    (bN : Basis (Fin n) ℝ LN) (bD : Basis (Fin d) ℝ LD) (k v : LN)
    {c : ℕ} (a : DynkinCoefficients c 2)
    (hm : ∀ x y, ExpN (finiteDynkinPolynomial a ![x, y]) = ExpN x * ExpN y)
    (z : (Fin n → ℝ) × (Fin d → ℝ)) :
    (ι (ExpN v))⁻¹ • coordinateChartPoint p x ι κ ExpN ExpD bN bD (ExpN k) z =
      coordinateChartPoint p x ι κ ExpN ExpD bN bD (ExpN k)
        (dynkinProduct a (basisBracket bN) z.1
          (dynkinProduct a (basisBracket bN)
            (dynkinProduct a (basisBracket bN) (bN.equivFun k)
              (bN.equivFun (A (bD.equivFun.symm z.2) v))) (-(bN.equivFun k))), z.2) := by
  unfold coordinateChartPoint
  rw [chartOccupationPoint_normal_factor]
  rw [exp_basis_dynkinProduct bN ExpN a hm, exp_basis_dynkinProduct bN ExpN a hm,
    exp_basis_dynkinProduct bN ExpN a hm]
  simp only [map_neg, LinearEquiv.symm_apply_apply, hneg]
  rw [← hact]
  simp only [map_mul, map_inv, hφ, mul_assoc]

/-- Continuity of the factor charts gives continuity of the joint sample. -/
theorem continuous_coordinateChartPoint [ProperSpace G]
    (p : NormalizedPair G Λ) (x : G) (ι : N →* G) (κ : D →* G)
    (ExpN : LN → N) (ExpD : LD → D)
    (bN : Basis (Fin n) ℝ LN) (bD : Basis (Fin d) ℝ LD) (k : N)
    (hN : Continuous (fun z => ι (ExpN (bN.equivFun.symm z))))
    (hD : Continuous (fun z => κ (ExpD (bD.equivFun.symm z)))) :
    Continuous (coordinateChartPoint p x ι κ ExpN ExpD bN bD k) := by
  exact (continuous_chartOccupationPoint p).comp
    ((continuous_const.prodMk (hN.comp continuous_fst)).prodMk
      (continuous_const.prodMk (hD.comp continuous_snd)))

end PolycyclicRecognition

end

end OAI
