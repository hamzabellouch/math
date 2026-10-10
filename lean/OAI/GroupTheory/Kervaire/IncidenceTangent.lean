import OAI.GroupTheory.Kervaire.IncidenceSpaces

namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open scoped ComplexOrder
open MeasureTheory Measure Set Filter
open scoped Topology
open MeasureTheory ContinuousAlternatingMap Set VectorField
open scoped Topology ContDiff
open ContinuousAlternatingMap
open scoped ContDiff
open MeasureTheory NormedSpace
open scoped ContDiff
open Module Set ContinuousAlternatingMap
open Matrix Module
open scoped ContDiff Matrix.Norms.L2Operator
open scoped ComplexOrder

namespace KervaireIncidenceCurrent

section
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]
lemma contDiff_incidence {f : ℝ × Mat K → Mat (K ⊕ R)} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (incidence f) := by
  unfold incidence
  simp only [diag_eq_corner]
  have hX : ContDiff ℝ ∞ (fun p : ℝ × Alg K R ↦ f (p.1,p.2.1)) :=
    hf.comp (contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd))
  have hQ : ContDiff ℝ ∞ (fun p : ℝ × Alg K R ↦ p.2.2.1) := by fun_prop
  have hT : ContDiff ℝ ∞ (fun p : ℝ × Alg K R ↦ p.2.2.2) := by fun_prop
  have hTs : ContDiff ℝ ∞ (fun p : ℝ × Alg K R ↦ star p.2.2.2) := (starL ℝ).contDiff.comp hT
  have hQs : ContDiff ℝ ∞ (fun p : ℝ × Alg K R ↦ star p.2.2.1) := (starL ℝ).contDiff.comp hQ
  have hS : ContDiff ℝ ∞ (fun p : ℝ × Alg K R ↦ in11 (K := K) (R := R) 1 + in22 (K := K) (R := R) (star p.2.2.2)) :=
    contDiff_const.add ((in22 (K := K) (R := R)).contDiff.comp hTs)
  have h1 : ContDiff ℝ ∞ (fun p : ℝ × Alg K R ↦ f (p.1,p.2.1) * p.2.2.1) := hX.mul hQ
  have h2 : ContDiff ℝ ∞ (fun p : ℝ × Alg K R ↦ f (p.1,p.2.1) * p.2.2.1 * (in11 (K := K) (R := R) 1 + in22 (K := K) (R := R) (star p.2.2.2))) := h1.mul hS
  exact h2.mul hQs

/-- Its actual ambient Fréchet differential. -/
lemma fderiv_incidence {f : ℝ × Mat K → Mat (K ⊕ R)} (hf : ContDiff ℝ ∞ f)
    (p v : ℝ × Alg K R) :
    fderiv ℝ (incidence f) p v =
      fderiv ℝ f (p.1,p.2.1) (v.1,v.2.1) * p.2.2.1 * diag 1 (star p.2.2.2) * star p.2.2.1 +
      f (p.1,p.2.1) * v.2.2.1 * diag 1 (star p.2.2.2) * star p.2.2.1 +
      f (p.1,p.2.1) * p.2.2.1 * in22 (star v.2.2.2) * star p.2.2.1 +
      f (p.1,p.2.1) * p.2.2.1 * diag 1 (star p.2.2.2) * star v.2.2.1 := by
  let cX : (ℝ × Alg K R) →L[ℝ] (ℝ × Mat K) :=
    (ContinuousLinearMap.fst ℝ ℝ (Alg K R)).prod
      ((ContinuousLinearMap.fst ℝ (Mat K) (Mat (K ⊕ R) × Mat R)).comp
        (ContinuousLinearMap.snd ℝ ℝ (Alg K R)))
  let cQ : (ℝ × Alg K R) →L[ℝ] Mat (K ⊕ R) :=
    (ContinuousLinearMap.fst ℝ (Mat (K ⊕ R)) (Mat R)).comp
      ((ContinuousLinearMap.snd ℝ (Mat K) (Mat (K ⊕ R) × Mat R)).comp
        (ContinuousLinearMap.snd ℝ ℝ (Alg K R)))
  let cT : (ℝ × Alg K R) →L[ℝ] Mat R :=
    (ContinuousLinearMap.snd ℝ (Mat (K ⊕ R)) (Mat R)).comp
      ((ContinuousLinearMap.snd ℝ (Mat K) (Mat (K ⊕ R) × Mat R)).comp
        (ContinuousLinearMap.snd ℝ ℝ (Alg K R)))
  have hX := (hf.differentiable (by simp) (cX p)).hasFDerivAt.comp p (cX.hasFDerivAt)
  have hS := (hasFDerivAt_const (𝕜 := ℝ) (in11 (K := K) (R := R) 1) p).add
    ((in22 (K := K) (R := R)).hasFDerivAt.comp p ((starL ℝ).hasFDerivAt.comp p cT.hasFDerivAt))
  have h1 : HasFDerivAt (fun z ↦ f (cX z) * cQ z) _ p := hX.mul' cQ.hasFDerivAt
  have h2 : HasFDerivAt (fun z ↦ f (cX z) * cQ z * (in11 (K := K) (R := R) 1 + in22 (star (cT z)))) _ p := h1.mul' hS
  have hd : HasFDerivAt (fun z ↦ f (cX z) * cQ z * (in11 (K := K) (R := R) 1 + in22 (star (cT z))) * star (cQ z)) _ p :=
    h2.mul' ((starL ℝ).hasFDerivAt.comp p cQ.hasFDerivAt)
  have heq : (fun x ↦ (f (cX x) * cQ x) * (in11 (K := K) (R := R) 1 + in22 (star (cT x))) * star (cQ x)) =
      incidence f := by
    funext x
    simp only [incidence, diag_eq_corner]
    rfl
  rw [heq] at hd
  rw [hd.fderiv]
  simp only [_root_.add_apply, _root_.smul_apply, ContinuousLinearMap.comp_apply,
    zero_add, ← diag_eq_corner, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op,
    smul_eq_mul, Function.comp_apply]
  change f (p.1,p.2.1) * p.2.2.1 * diag 1 (star p.2.2.2) * star v.2.2.1 +
    (f (p.1,p.2.1) * p.2.2.1 * in22 (star v.2.2.2) +
      (f (p.1,p.2.1) * v.2.2.1 + fderiv ℝ f (p.1,p.2.1) (v.1,v.2.1) * p.2.2.1) *
        diag 1 (star p.2.2.2)) * star p.2.2.1 = _
  noncomm_ring

def horizontalInput (p : Alg K R) : Horizontal K R →ₗ[ℝ] (ℝ × Alg K R) where
  toFun h := (0,p*(direction h : Alg K R))
  map_add' h g := by
    change (0,p*(direction (h+g) : Alg K R)) = _
    rw [map_add]
    change ((0 : ℝ),p*((direction h : Alg K R)+(direction g : Alg K R))) =
      (0,p*(direction h : Alg K R))+(0,p*(direction g : Alg K R))
    rw [mul_add]
    exact Prod.ext (zero_add 0).symm rfl
  map_smul' c h := by
    change (0,p*(direction (c • h) : Alg K R)) = _
    rw [map_smul]
    change ((0 : ℝ),p*(c • (direction h : Alg K R))) = c • (0,p*(direction h : Alg K R))
    rw [mul_smul_comm]
    simp only [Prod.smul_mk,smul_zero]

def horizontalDifferential (f : ℝ × Mat K → Mat (K ⊕ R)) (t : ℝ) (p : Alg K R) :
    Horizontal K R →ₗ[ℝ] Mat (K ⊕ R) :=
  (fderiv ℝ (incidence f) (t,p)).toLinearMap.comp (horizontalInput p)

/-- Diagonal frame directions and compensated fiber directions have identical images. -/
lemma fderiv_frame_diagonal {f : ℝ × Mat K → Mat (K ⊕ R)} (hf : ContDiff ℝ ∞ f)
    (t : ℝ) (X : Mat K) (Q : Mat (K ⊕ R)) (T : unitary (Mat R))
    (U : skewAdjoint.submodule ℝ (Mat K)) (V : skewAdjoint.submodule ℝ (Mat R)) :
    fderiv ℝ (incidence f) (t,X,Q,(T : Mat R)) (0,0,Q*diag U V,0) =
    fderiv ℝ (incidence f) (t,X,Q,(T : Mat R)) (0,0,0,(T : Mat R)*compensated T V) := by
  have hU : star (U : Mat K) = -(U : Mat K) := U.property
  have hV : star (V : Mat R) = -(V : Mat R) := V.property
  rw [fderiv_incidence hf, fderiv_incidence hf]
  simp only [show ((0 : ℝ),(0 : Mat K)) = 0 from rfl, _root_.map_zero, zero_mul,
    mul_zero, star_zero, zero_add, add_zero]
  rw [compensated_star_mul, star_mul, diag_star, hU, hV]
  have h := frame_diagonal_commutator T (U : Mat K) (V : Mat R)
  have hn : diag (-(U : Mat K)) (-(V : Mat R)) = -diag U V := by
    ext i j
    cases i <;> cases j <;> simp [diag, fromBlocks]
  rw [hn]
  rw [← h]
  noncomm_ring

lemma direction_bracket (h g : Horizontal K R) :
    ((direction h : Alg K R)*(direction g : Alg K R)-
      (direction g : Alg K R)*(direction h : Alg K R)) =
    (direction (KervaireSkewTrace.bracket h.1 g.1,
      KervaireSkewTrace.bracket h.2.1 g.2.1,0) : Alg K R) +
    (0,diag (rectBracket h.2.2ᴴ g.2.2ᴴ : Mat K) (rectBracket h.2.2 g.2.2 : Mat R),0) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp [direction, KervaireSkewTrace.bracket]
  · change off h.2.2 * off g.2.2-off g.2.2*off h.2.2 = _
    rw [off_bracket]
    simp [direction, off, rectBracket]
  · simp [direction, KervaireSkewTrace.bracket]

/-- The differential of a bracket is in the span of horizontal directions,
with the explicitly computed coefficients. -/
lemma fderiv_direction_bracket {f : ℝ × Mat K → Mat (K ⊕ R)} (hf : ContDiff ℝ ∞ f)
    (t : ℝ) (p : unitary (Alg K R)) (h g : Horizontal K R) :
    fderiv ℝ (incidence f) (t,(p : Alg K R))
      (0,(p : Alg K R)*((direction h : Alg K R)*(direction g : Alg K R)-
        (direction g : Alg K R)*(direction h : Alg K R))) =
    fderiv ℝ (incidence f) (t,(p : Alg K R))
      (0,(p : Alg K R)*(direction (effectiveBracket ⟨p.val.2.2,(unitary_alg_parts p).2.2⟩ h g) : Alg K R)) := by
  let T : unitary (Mat R) := ⟨p.val.2.2,(unitary_alg_parts p).2.2⟩
  let b : Horizontal K R := (KervaireSkewTrace.bracket h.1 g.1,
    KervaireSkewTrace.bracket h.2.1 g.2.1,0)
  let c : Horizontal K R := (0,compensated T (rectBracket h.2.2 g.2.2),0)
  have he : effectiveBracket T h g = b+c := by simp [effectiveBracket,b,c]
  have hb : ((0 : ℝ),(p : Alg K R)*((direction h : Alg K R)*(direction g : Alg K R)-
        (direction g : Alg K R)*(direction h : Alg K R))) =
      (0,(p : Alg K R)*(direction b : Alg K R))+
      (0,0,p.val.2.1*diag (rectBracket h.2.2ᴴ g.2.2ᴴ : Mat K) (rectBracket h.2.2 g.2.2 : Mat R),0) := by
    rw [direction_bracket, mul_add]
    simp only [Prod.mul_def, mul_zero, Prod.add_def, add_zero]
    rfl
  rw [hb,map_add, fderiv_frame_diagonal hf t p.val.1 p.val.2.1 T
    (rectBracket h.2.2ᴴ g.2.2ᴴ) (rectBracket h.2.2 g.2.2)]
  have hc : ((0 : ℝ),0,0,p.val.2.2*(compensated T (rectBracket h.2.2 g.2.2) : Mat R)) =
      (0,(p : Alg K R)*(direction c : Alg K R)) := by
    simp [c,direction,off,Prod.mul_def]
  change _ = fderiv ℝ (incidence f) (t,(p : Alg K R))
    (0,(p : Alg K R)*(direction (effectiveBracket T h g) : Alg K R))
  rw [hc]
  change horizontalDifferential f t p b + horizontalDifferential f t p c =
    horizontalDifferential f t p (effectiveBracket T h g)
  rw [he,map_add]

end
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]
  {IK IR IZ : Type*} [Fintype IK] [Fintype IR] [Fintype IZ]
  (bK : Basis IK ℝ (skewAdjoint.submodule ℝ (Mat K)))
  (bR : Basis IR ℝ (skewAdjoint.submodule ℝ (Mat R)))
  (bZ : Basis IZ ℝ (Matrix R K ℂ))

omit [Fintype IZ] in
lemma basis_bracket_condition {n : ℕ} (e : (IK ⊕ IR ⊕ IZ) ≃ Fin (n+1))
    (hbK : (KervaireSkewTrace.pairing (I := K)).IsOrthoᵢ bK)
    (hbR : (KervaireSkewTrace.pairing (I := R)).IsOrthoᵢ bR)
    {f : ℝ × Mat K → Mat (K ⊕ R)} (hf : ContDiff ℝ ∞ f)
    (t : ℝ) (p : unitary (Alg K R)) (i j : Fin (n+1)) :
    let b := (horizontalBasis bK bR bZ).reindex e
    ∃ c : Fin (n+1) → ℝ, c i = 0 ∧ c j = 0 ∧
      fderiv ℝ (incidence f) (t,(p : Alg K R))
        (0,(p : Alg K R)*((direction (b i) : Alg K R)*(direction (b j) : Alg K R)-
          (direction (b j) : Alg K R)*(direction (b i) : Alg K R))) =
        ∑ l, c l • fderiv ℝ (incidence f) (t,(p : Alg K R))
          (0,(p : Alg K R)*(direction (b l) : Alg K R)) := by
  intro b
  let T : unitary (Mat R) := ⟨p.val.2.2,(unitary_alg_parts p).2.2⟩
  let v := effectiveBracket T (b i) (b j)
  refine ⟨fun l ↦ b.repr v l,?_,?_,?_⟩
  · simpa only [b,v,Basis.repr_reindex_apply,Basis.reindex_apply] using
      effectiveBracket_repr_left bK bR bZ hbK hbR T (e.symm i) (e.symm j)
  · simpa only [b,v,Basis.repr_reindex_apply,Basis.reindex_apply] using
      effectiveBracket_repr_right bK bR bZ hbK hbR T (e.symm i) (e.symm j)
  · rw [fderiv_direction_bracket hf]
    change horizontalDifferential f t p v = ∑ l, b.repr v l • horizontalDifferential f t p (b l)
    simpa only [_root_.map_sum,_root_.map_smul] using
      congrArg (horizontalDifferential f t p) (b.sum_repr v).symm

end KervaireIncidenceCurrent

namespace KervaireFixedSpace
open Matrix
variable {K R : Type*}
abbrev Skew (K : Type*) := skewAdjoint (Matrix K K ℂ)

/-- Entrywise skew-Hermitian symmetry. -/
theorem skew_entry (T : Skew K) (i j : K) : star (T.val j i) = -T.val i j := by
  exact congrFun (congrFun T.property i) j

/-- The first diagonal block of a skew-Hermitian matrix. -/
def skewBlock11 (T : Skew (K ⊕ R)) : Skew K :=
  ⟨T.val.toBlocks₁₁, by
    ext i j
    exact skew_entry T (Sum.inl i) (Sum.inl j)⟩

/-- The second diagonal block of a skew-Hermitian matrix. -/
def skewBlock22 (T : Skew (K ⊕ R)) : Skew R :=
  ⟨T.val.toBlocks₂₂, by
    ext i j
    exact skew_entry T (Sum.inr i) (Sum.inr j)⟩

/-- The block formula for the incidence derivative. -/
def derivativeMatrix (ε : ℝ) (A : Skew K) (B : Skew R) (Z : Matrix R K ℂ) :
    Matrix (K ⊕ R) (K ⊕ R) ℂ :=
  fromBlocks (ε • A.val) ((2 : ℝ) • Zᴴ) ((-2 : ℝ) • Z) (-B.val)

theorem derivativeMatrix_skew (ε : ℝ) (A : Skew K) (B : Skew R) (Z : Matrix R K ℂ) :
    derivativeMatrix ε A B Z ∈ skewAdjoint (Matrix (K ⊕ R) (K ⊕ R) ℂ) := by
  change star (derivativeMatrix ε A B Z) = -derivativeMatrix ε A B Z
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp [derivativeMatrix, Matrix.star_apply, Matrix.fromBlocks, skew_entry]
  · simp [derivativeMatrix, Matrix.star_apply, Matrix.fromBlocks]
  · simp [derivativeMatrix, Matrix.star_apply, Matrix.fromBlocks]
  · simp [derivativeMatrix, Matrix.star_apply, Matrix.fromBlocks, skew_entry]

def degreeDerivative (ε : ℝ) : (Skew K × Skew R × Matrix R K ℂ) →ₗ[ℝ] Skew (K ⊕ R) where
  toFun v := ⟨derivativeMatrix ε v.1 v.2.1 v.2.2,
    derivativeMatrix_skew ε v.1 v.2.1 v.2.2⟩
  map_add' v w := by
    apply Subtype.ext
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [derivativeMatrix, Matrix.fromBlocks, smul_add]; abel
  map_smul' c v := by
    apply Subtype.ext
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [derivativeMatrix, Matrix.fromBlocks, smul_comm ε c, smul_comm (2 : ℝ) c,
        smul_comm (-2 : ℝ) c]

/-- Explicit inverse coordinates of the differential; no finite-dimensional
or genericity assumption is needed for this algebraic step. -/
def inverseDerivative (ε : ℝ) (T : Skew (K ⊕ R)) : Skew K × Skew R × Matrix R K ℂ :=
  (ε⁻¹ • skewBlock11 T, -skewBlock22 T, (-((2 : ℝ)⁻¹)) • T.val.toBlocks₂₁)

theorem degreeDerivative_inverse (ε : ℝ) (hε : ε ≠ 0) (T : Skew (K ⊕ R)) :
    degreeDerivative ε (inverseDerivative ε T) = T := by
  apply Subtype.ext
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp [degreeDerivative, inverseDerivative, derivativeMatrix, skewBlock11,
      Matrix.fromBlocks, Matrix.toBlocks₁₁, smul_smul, hε]
  · simp [degreeDerivative, inverseDerivative, derivativeMatrix, Matrix.fromBlocks,
      Matrix.toBlocks₂₁, smul_smul, skew_entry]
  · simp [degreeDerivative, inverseDerivative, derivativeMatrix, Matrix.fromBlocks,
      Matrix.toBlocks₂₁, smul_smul]
  · simp [degreeDerivative, inverseDerivative, derivativeMatrix, skewBlock22,
      Matrix.fromBlocks, Matrix.toBlocks₂₂]

theorem inverse_degreeDerivative (ε : ℝ) (hε : ε ≠ 0) (v : Skew K × Skew R × Matrix R K ℂ) :
    inverseDerivative ε (degreeDerivative ε v) = v := by
  apply Prod.ext
  · apply Subtype.ext
    ext i j
    simp [inverseDerivative, degreeDerivative, derivativeMatrix, skewBlock11,
      Matrix.toBlocks₁₁, Matrix.fromBlocks, hε]
  · apply Prod.ext
    · apply Subtype.ext
      ext i j
      simp [inverseDerivative, degreeDerivative, derivativeMatrix, skewBlock22,
        Matrix.toBlocks₂₂, Matrix.fromBlocks]
    · ext i j
      simp [inverseDerivative, degreeDerivative, derivativeMatrix, Matrix.toBlocks₂₁,
        Matrix.fromBlocks]

/-- The differential at the regular fiber is a real-linear isomorphism. -/
def degreeDerivativeEquiv (ε : ℝ) (hε : ε ≠ 0) :
    (Skew K × Skew R × Matrix R K ℂ) ≃ₗ[ℝ] Skew (K ⊕ R) :=
  { degreeDerivative ε with
    invFun := inverseDerivative ε
    left_inv := inverse_degreeDerivative ε hε
    right_inv := degreeDerivative_inverse ε hε }

end KervaireFixedSpace
namespace KervaireIncidenceCurrent
open MeasureTheory
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]
  {IK IR IZ : Type*} [Fintype IK] [Fintype IR] [Fintype IZ]
  (bK : Basis IK ℝ (skewAdjoint.submodule ℝ (Mat K)))
  (bR : Basis IR ℝ (skewAdjoint.submodule ℝ (Mat R)))
  (bZ : Basis IZ ℝ (Matrix R K ℂ))
  [MeasurableSpace (unitary (Alg K R))] [BorelSpace (unitary (Alg K R))]
  {μ : Measure (unitary (Alg K R))} [IsFiniteMeasure μ] [IsMulRightInvariant μ]

omit [Fintype IZ] in
lemma incidence_integral_constant {n : ℕ} (e : (IK ⊕ IR ⊕ IZ) ≃ Fin (n+1))
    (hbK : (KervaireSkewTrace.pairing (I := K)).IsOrthoᵢ bK)
    (hbR : (KervaireSkewTrace.pairing (I := R)).IsOrthoᵢ bR)
    {f : ℝ × Mat K → Mat (K ⊕ R)} (hf : ContDiff ℝ ∞ f)
    (hu : ∀ t (X : unitary (Mat K)), f (t,(X : Mat K)) ∈ unitary (Mat (K ⊕ R)))
    (form : Mat (K ⊕ R) → Mat (K ⊕ R) [⋀^Fin (n+1)]→L[ℝ] ℝ)
    (hform : ContDiff ℝ ∞ form) (t₀ t₁ : ℝ) :
    let b := (horizontalBasis bK bR bZ).reindex e
    (∫ p : unitary (Alg K R), form (incidence f (t₀,(p : Alg K R)))
      (fun i ↦ fderiv ℝ (incidence f) (t₀,(p : Alg K R))
        (0,(p : Alg K R)*(direction (b i) : Alg K R))) ∂μ) =
    (∫ p : unitary (Alg K R), form (incidence f (t₁,(p : Alg K R)))
      (fun i ↦ fderiv ℝ (incidence f) (t₁,(p : Alg K R))
        (0,(p : Alg K R)*(direction (b i) : Alg K R))) ∂μ) := by
  intro b
  let : CompactSpace (unitary (Alg K R)) := KervaireCompactUnitary.compactSpace
  apply KervaireHorizontalCurrent.integral_pullback_constant (fun i ↦ direction (b i))
    (contDiff_incidence hf) (incidence_unitary hu) _ _ form hform t₀ t₁
  · let L : Horizontal K R ≃ₗ[ℝ] skewAdjoint.submodule ℝ (Mat (K ⊕ R)) :=
      KervaireFixedSpace.degreeDerivativeEquiv (K := K) (R := R) 1 one_ne_zero
    let c : Basis (Fin (n+1)) ℝ (skewAdjoint.submodule ℝ (Mat (K ⊕ R))) := b.map L
    have h : Module.finrank ℝ (skewAdjoint.submodule ℝ (Mat (K ⊕ R))) = n+1 := by
      simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis c
    exact h.le
  · intro t p i j _
    exact basis_bracket_condition bK bR bZ e hbK hbR hf t p i j

end KervaireIncidenceCurrent

end

end OAI
