import OAI.Analysis.KadisonSimilarity.FreeProduct.TracialSpectralCompression
import OAI.Analysis.KadisonSimilarity.FreeProduct.TracialDihedralColumns

namespace OAI

/-! The actual normalized dihedral columns have the rotation-power formula
needed by the spectral Fourier computation. -/

noncomputable section
namespace KadisonSimilarity
namespace TracialCornerGeometry

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]
  (hf : ScalarFree G.trace D A) (hτ : G.trace 1 = 1)
  (d : D) (s : A) (e : D)
  (hdstar : star d = d) (hdsq : d * d = 1) (hd0 : G.trace (d : P) = 0)
  (hsstar : star s = s) (hssq : s * s = 1) (hs0 : G.trace (s : P) = 0)
  (he : IsStarProjection e) {t : ℝ} (ht : 0 < t) (hte : G.trace (e : P) = (t : ℂ))

local notation "dU" => symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq)
local notation "sU" => symmetryUnit (s : P) (congrArg (fun x : A => (x : P)) hssq)

omit [IsClosed (A : Set P)] [IsClosed (D : Set P)] in
/-- The repeated product column is exactly the normalized negative rotation
power column; the identity is proved on its actual bounded algebra vectors. -/
theorem tracialDihedralColumns_rotation_formula (N : ℕ) (i : Fin N) (a : A) :
    G.tracialDihedralColumns D A hf hτ d s e hdstar hdsq hd0 hsstar hssq hs0
      he ht hte N i (G.baseVector A a) =
      dihedralNormalization t • G.vector
        ((e : P) * (↑((dU * sU) ^ (-(i.val : ℤ))) : P) * (a : P)) := by
  change G.tracialDihedralInclusion D A hf hτ d s e hdstar hdsq hd0 hsstar hssq hs0
    he ht hte i.val (G.baseVector A a) = _
  rw [G.tracialDihedralInclusion_apply]
  simp only [zpow_neg, zpow_natCast, ← inv_pow, mul_inv_rev,
    symmetryUnit_inv, Units.val_pow_eq_pow_val, Units.val_mul, symmetryUnit_coe]

omit [IsClosed (A : Set P)] [IsClosed (D : Set P)] in
/-- The Fourier compression theorem, on the actual normalized columns.
The bounded column formula and reflected base compression are derived here. -/
theorem spectral_arc_actual_columns
    (C S : StarSubalgebra ℂ P)
    (E : TracialExpectation G.trace A) (EC : TracialExpectation G.trace C)
    (hCS : C ≤ S) (hDS : D ≤ S) (hfaithful : Function.Injective G.vector)
    (hdC : (d : P) ∈ C) (hsC : (s : P) ∈ C)
    (hdense : ∀ x, x ∈ S → G.vector x ∈ (Submodule.span ℂ
      (G.vector '' (StarAlgebra.adjoin ℂ ((D : Set P) ∪ {(s : P)}) : Set P))).topologicalClosure)
    (hpower : ∀ j : ℤ, (↑((dU * sU) ^ j) : P) ∈ C)
    (hp : IsStarProjection (dihedralHalfProjection dU))
    (hpD : dihedralHalfProjection dU ∈ D)
    (htp : G.trace (dihedralHalfProjection dU) = (1 / 2 : ℂ))
    (hfree : ScalarFree (CStarCorner.normalizedTrace (dihedralHalfProjection dU) hp G.trace)
      (CStarCorner.subalgebra (dihedralHalfProjection dU) hp D hpD)
      (CStarCorner.subalgebra (dihedralHalfProjection dU) hp C
        (C.smul_mem (C.add_mem C.one_mem hdC) (1 / 2))))
    (hep : dihedralHalfProjection dU * (e : P) = (e : P))
    (hpe : (e : P) * dihedralHalfProjection dU = (e : P))
    {N : ℕ} (hN : 0 < N)
    (F : DihedralSpectralArc G.trace C (dU * sU) dU (arcWidth N)) :
    let V := G.tracialDihedralColumns D A hf hτ d s e hdstar hdsq hd0 hsstar hssq hs0
      he ht hte N
    (sumColumns V).adjoint.comp
      ((G.left ((e : P) * (F.element * dihedralHalfProjection dU) * (e : P))).comp
        (sumColumns V)) =
      ((2 * t : ℝ) : ℂ) • matrixOperator (fun i j =>
        (realArcFourierCoefficient (arcWidth N) ((i.val : ℤ) - (j.val : ℤ)) : ℂ) •
          ContinuousLinearMap.id ℂ (G.baseSpace A) +
        (arcHankelMatrix N i j : ℂ) • G.baseRepresentation A s) := by
  have hshift : (dU * sU)⁻¹ * dU = sU :=
    dihedral_inverse_mul_reflection dU sU (symmetryUnit_inv _ _)
  let eC : CStarCorner (dihedralHalfProjection dU) hp := ⟨e, hep, hpe⟩
  have heP : IsStarProjection (e : P) :=
    ⟨congrArg (fun x : D => (x : P)) he.isIdempotentElem.eq,
      congrArg (fun x : D => (x : P)) he.isSelfAdjoint.star_eq⟩
  have h := G.spectral_arc_compression A C D S E EC hCS hDS hfaithful hτ hf
    (dU * sU) dU
    (free_symmetry_product_star dU sU
      (symmetryUnit_star _ _ (congrArg (fun x : D => (x : P)) hdstar))
      (symmetryUnit_star _ _ (congrArg (fun x : A => (x : P)) hsstar))
      (symmetryUnit_inv _ _) (symmetryUnit_inv _ _))
    (dihedral_reflection_relation dU sU (symmetryUnit_inv _ _) (symmetryUnit_inv _ _))
    hdC (by simpa only [hshift, symmetryUnit_coe] using s.property)
    (by simpa only [hshift, symmetryUnit_coe] using hsC)
    (by simpa only [hshift, symmetryUnit_coe] using hs0)
    (by simpa only [hshift, symmetryUnit_coe, MulMemClass.coe_mul, OneMemClass.coe_one] using
      congrArg (fun x : A => (x : P)) hssq)
    (by simpa only [hshift, symmetryUnit_coe, StarMemClass.coe_star] using
      congrArg (fun x : A => (x : P)) hsstar)
    (by simpa only [hshift, symmetryUnit_coe] using hdense)
    hpower hp hpD htp hfree eC heP e.property hN F t ht hte
    (dihedralNormalization t) (dihedralNormalization_sq ht)
    (G.tracialDihedralColumns D A hf hτ d s e hdstar hdsq hd0 hsstar hssq hs0 he ht hte N)
    (G.tracialDihedralColumns_rotation_formula A D hf hτ d s e hdstar hdsq hd0 hsstar hssq hs0
      he ht hte N)
  simpa only [hshift, symmetryUnit_coe, G.baseCompression_subalgebra] using h

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
