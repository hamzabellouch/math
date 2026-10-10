import OAI.Analysis.KadisonSimilarity.Tracial.FullColumns
import OAI.Analysis.KadisonSimilarity.Derivation.CyclicApproximation

namespace OAI

/-!
# The full-column implementation argument

The corner commutator is constructed here, corrected by the proved cyclic
implementation theorem, and extended through finite matrix coordinates with
exactly the same norm. Extension by zero and the tracial commutation theorem
then identify the resulting intertwiner as a right multiplier.

The finite-factor realization of the corner and its matrix coordinates remains
explicit geometric data; the full-column conclusion is not an input.
-/

noncomputable section
namespace KadisonSimilarity

open scoped CStarAlgebra

section CornerCommutator

variable {C F K : Type*} [CStarAlgebra C]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The actual rectangular commutator of a corner operator. -/
def cornerCommutator (ρ : C →⋆ₐ[ℂ] (F →L[ℂ] F))
    (σ : C →⋆ₐ[ℂ] (K →L[ℂ] K)) (G : K →L[ℂ] F) : C →L[ℂ] (K →L[ℂ] F) where
  toFun a := G.comp (σ a) - (ρ a).comp G
  map_add' := by
    intro a b
    ext x
    simp
    abel
  map_smul' := by
    intro c a
    ext x
    simp [smul_sub]
  cont := ((map_continuous σ).const_clm_comp G).sub
    ((map_continuous ρ).clm_comp_const G)

@[simp] theorem cornerCommutator_apply (ρ : C →⋆ₐ[ℂ] (F →L[ℂ] F))
    (σ : C →⋆ₐ[ℂ] (K →L[ℂ] K)) (G : K →L[ℂ] F) (a : C) :
    cornerCommutator ρ σ G a = G.comp (σ a) - (ρ a).comp G := rfl

/-- The rectangular Leibniz rule follows from composition, with no derivation
hypothesis on the corner operator. -/
theorem cornerCommutator_leibniz (ρ : C →⋆ₐ[ℂ] (F →L[ℂ] F))
    (σ : C →⋆ₐ[ℂ] (K →L[ℂ] K)) (G : K →L[ℂ] F) (a b : C) :
    cornerCommutator ρ σ G (a * b) =
      (ρ a).comp (cornerCommutator ρ σ G b) +
        (cornerCommutator ρ σ G a).comp (σ b) := by
  ext x
  simp [mul_apply_eq_comp]

variable [PartialOrder C] [StarOrderedRing C]

/-- Correct the corner operator to an exact module intertwiner. -/
theorem exists_corner_intertwiner_of_published_inputs
    (ρ : C →⋆ₐ[ℂ] (F →L[ℂ] F)) (σ : C →⋆ₐ[ℂ] (K →L[ℂ] K))
    (G : K →L[ℂ] F) {ε : ℝ} (hG : ‖cornerCommutator ρ σ G‖ ≤ ε)
    (dickson : DicksonTwoBound (A := C) (RectangularSum F K))
    (haagerup : HaagerupCyclicVectorRealization σ)
    (kaplansky : KaplanskyColumnApproximation σ)
    (paulsen : PaulsenSimilarityInput (normalizedRectangularRepresentation ρ σ
      (cornerCommutator ρ σ G) (cornerCommutator_leibniz ρ σ G))) :
    ∃ T : K →L[ℂ] F,
      (∀ a, T.comp (σ a) = (ρ a).comp T) ∧
      ‖G - T‖ ≤ (1 + 4 * (4 * Real.sqrt 2)) ^ 2 * ε := by
  obtain ⟨V, hV, hnV⟩ := cyclic_derivation_implementation_of_published_inputs
    ρ σ (cornerCommutator ρ σ G) (cornerCommutator_leibniz ρ σ G)
    dickson haagerup kaplansky paulsen
  refine ⟨G - V, ?_, ?_⟩
  · intro a
    have h := hV a
    ext x
    have hx := congrArg (fun T : K →L[ℂ] F => T x) h
    simp only [cornerCommutator_apply, sub_apply,
      ContinuousLinearMap.comp_apply] at hx ⊢
    simp only [map_sub]
    apply sub_eq_sub_iff_add_eq_add.mpr
    simpa only [add_comm] using sub_eq_sub_iff_add_eq_add.mp hx
  · simpa only [sub_sub_cancel] using hnV.trans
      (mul_le_mul_of_nonneg_left hG (sq_nonneg _))

end CornerCommutator

section ScalarMatrixUnits

variable {F K : Type*}
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- Insertion into one coordinate of a finite Hilbert sum. -/
def copyInsert {n : ℕ} (i : Fin n) : K →L[ℂ] HilbertCopies K n :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => K)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.single ℂ (fun _ : Fin n => K) i)

@[simp] theorem copyInsert_apply {n : ℕ} (i : Fin n) (x : K) :
    copyInsert i x = PiLp.single 2 i x := rfl

/-- The scalar matrix unit which sends coordinate `j` to coordinate `i`. -/
def copyMatrixUnit {n : ℕ} (i j : Fin n) :
    HilbertCopies K n →L[ℂ] HilbertCopies K n :=
  (copyInsert i).comp (PiLp.proj 2 (fun _ : Fin n => K) j)

@[simp] theorem copyMatrixUnit_apply {n : ℕ} (i j : Fin n) (x : HilbertCopies K n) :
    copyMatrixUnit i j x = PiLp.single 2 i (x j) := rfl

/-- A diagonal corner of a bounded operator on two finite Hilbert sums. -/
def copyCorner {n : ℕ} (i : Fin n) (W : HilbertCopies K n →L[ℂ] HilbertCopies F n) :
    K →L[ℂ] F :=
  (PiLp.proj 2 (fun _ : Fin n => F) i).comp (W.comp (copyInsert i))

@[simp] theorem copyCorner_apply {n : ℕ} (i : Fin n)
    (W : HilbertCopies K n →L[ℂ] HilbertCopies F n) (x : K) :
    copyCorner i W x = W (PiLp.single 2 i x) i := rfl

/-- Commutation with the scalar matrix units forces one repeated diagonal
corner. Only the row of matrix units with target coordinate `i` is needed. -/
theorem eq_mapCopies_of_matrixUnit_intertwining {n : ℕ} (i : Fin n)
    (W : HilbertCopies K n →L[ℂ] HilbertCopies F n)
    (hW : ∀ j : Fin n, W.comp (copyMatrixUnit i j) = (copyMatrixUnit i j).comp W) :
    W = mapCopies (copyCorner i W) n := by
  ext x j
  have h := congrArg (fun T : HilbertCopies K n →L[ℂ] HilbertCopies F n => T x i) (hW j)
  simpa only [ContinuousLinearMap.comp_apply, copyMatrixUnit_apply,
    PiLp.single_eq_same, mapCopies_apply, copyCorner_apply] using h.symm

end ScalarMatrixUnits

section MatrixCoordinates

variable {P C H D F K : Type*} [CStarAlgebra P] [CStarAlgebra C]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup D] [InnerProductSpace ℂ D] [CompleteSpace D]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The finite matrix-unit coordinates of a full column and its corner.
The two action identities say that full left multiplication has the usual
corner matrix entries. They assert no existence of an intertwiner. -/
structure FullColumnCoordinates
    (L : P →⋆ₐ[ℂ] (H →L[ℂ] H)) (Lr : P →⋆ₐ[ℂ] (D →L[ℂ] D))
    (ρ : C →⋆ₐ[ℂ] (F →L[ℂ] F)) (σ : C →⋆ₐ[ℂ] (K →L[ℂ] K)) (n : ℕ) where
  domain : D ≃ₗᵢ[ℂ] HilbertCopies K n
  codomain : H ≃ₗᵢ[ℂ] HilbertCopies F n
  entry : P → Matrix (Fin n) (Fin n) C
  domain_action : ∀ a x, domain (Lr a x) =
    matrixOperator (fun i j => σ (entry a i j)) (domain x)
  codomain_action : ∀ a x, codomain (L a x) =
    matrixOperator (fun i j => ρ (entry a i j)) (codomain x)

namespace FullColumnCoordinates

variable {L : P →⋆ₐ[ℂ] (H →L[ℂ] H)} {Lr : P →⋆ₐ[ℂ] (D →L[ℂ] D)}
  {ρ : C →⋆ₐ[ℂ] (F →L[ℂ] F)} {σ : C →⋆ₐ[ℂ] (K →L[ℂ] K)} {n : ℕ}

/-- Diagonal extension of a corner operator through matrix-unit coordinates. -/
def extend (c : FullColumnCoordinates L Lr ρ σ n) (T : K →L[ℂ] F) : D →L[ℂ] H :=
  c.codomain.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((mapCopies T n).comp c.domain.toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem extend_apply (c : FullColumnCoordinates L Lr ρ σ n)
    (T : K →L[ℂ] F) (x : D) :
    c.codomain (c.extend T x) = mapCopies T n (c.domain x) := by
  simp [extend]

@[simp] theorem extend_sub (c : FullColumnCoordinates L Lr ρ σ n)
    (S T : K →L[ℂ] F) : c.extend (S - T) = c.extend S - c.extend T := by
  ext x
  apply c.codomain.injective
  simp only [map_sub, extend_apply, mapCopies_sub, sub_apply]

/-- No factor depending on the number of matrix units enters the norm. -/
theorem norm_extend (c : FullColumnCoordinates L Lr ρ σ n) (hn : 0 < n)
    (T : K →L[ℂ] F) : ‖c.extend T‖ = ‖T‖ := by
  rw [extend, norm_isometricCoordinates_comp, norm_comp_isometricCoordinates,
    norm_mapCopies _ hn]

theorem norm_extend_sub (c : FullColumnCoordinates L Lr ρ σ n) (hn : 0 < n)
    (S T : K →L[ℂ] F) : ‖c.extend S - c.extend T‖ = ‖S - T‖ := by
  rw [← extend_sub, norm_extend c hn]

/-- An intertwiner for the corner extends to one for the whole left action. -/
theorem extend_intertwines (c : FullColumnCoordinates L Lr ρ σ n)
    (T : K →L[ℂ] F) (hT : ∀ a, T.comp (σ a) = (ρ a).comp T) (a : P) :
    (c.extend T).comp (Lr a) = (L a).comp (c.extend T) := by
  ext x
  apply c.codomain.injective
  simp only [ContinuousLinearMap.comp_apply, extend_apply, c.domain_action,
    c.codomain_action]
  exact congrArg (fun T => T (c.domain x))
    (mapCopies_intertwines_matrix T _ _ (fun i j => hT (c.entry a i j)))

/-- Write a full-column operator in the finite matrix-unit coordinates. -/
def inCoordinates (c : FullColumnCoordinates L Lr ρ σ n) (G : D →L[ℂ] H) :
    HilbertCopies K n →L[ℂ] HilbertCopies F n :=
  c.codomain.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (G.comp c.domain.symm.toContinuousLinearEquiv.toContinuousLinearMap)

/-- The distinguished corner of a full-column operator. -/
def corner (c : FullColumnCoordinates L Lr ρ σ n) (i : Fin n) (G : D →L[ℂ] H) :
    K →L[ℂ] F := copyCorner i (c.inCoordinates G)

/-- A full operator commuting with the represented scalar matrix units is
exactly the extension of its corner, rather than merely close to a diagonal
operator. -/
theorem eq_extend_of_matrixUnit_intertwining
    (c : FullColumnCoordinates L Lr ρ σ n) (i : Fin n) (G : D →L[ℂ] H)
    (hG : ∀ j : Fin n, (c.inCoordinates G).comp (copyMatrixUnit i j) =
      (copyMatrixUnit i j).comp (c.inCoordinates G)) :
    G = c.extend (c.corner i G) := by
  have hd := eq_mapCopies_of_matrixUnit_intertwining i _ hG
  ext x
  apply c.codomain.injective
  rw [extend_apply]
  have hx := congrArg (fun T => T (c.domain x)) hd
  simpa only [inCoordinates, corner, ContinuousLinearMap.comp_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe,
    c.domain.symm_apply_apply] using hx

end FullColumnCoordinates
end MatrixCoordinates

section RightMultipliers

variable {P H D : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup D] [InnerProductSpace ℂ D] [CompleteSpace D]

/-- The right multiplication convention, including faithfulness. Composition
has the opposite order: `R_b ∘ R_a = R_(a*b)`. -/
structure TracialRightAction where
  right : P → (H →L[ℂ] H)
  injective : Function.Injective right
  mul : ∀ a b, right (a * b) = (right b).comp (right a)

/-- The finite-trace specialization of the tracial commutation theorem:
Hiai, Theorem 2.2 and Example 2.4 (`JMJ = M′`); equivalently every bounded
left-module endomorphism of `L²(P,τ)` is right multiplication by an element
of `P`. This remains an explicit published input. -/
def TracialCommutationInput (L : P →⋆ₐ[ℂ] (H →L[ℂ] H))
    (R : TracialRightAction (P := P) (H := H)) : Prop :=
  ∀ Z : H →L[ℂ] H, (∀ a, Z.comp (L a) = (L a).comp Z) →
    ∃ b : P, R.right b = Z

/-- A full-column intertwiner extends by zero to a left-module endomorphism;
tracial commutation therefore makes it a right multiplier supported on `r`. -/
theorem exists_supported_right_multiplier
    (L : P →⋆ₐ[ℂ] (H →L[ℂ] H)) (Lr : P →⋆ₐ[ℂ] (D →L[ℂ] D))
    (R : TracialRightAction (P := P) (H := H)) (r : P)
    (inc : D →L[ℂ] H) (pr : H →L[ℂ] D)
    (hpr : pr.comp inc = ContinuousLinearMap.id ℂ D)
    (hr : inc.comp pr = R.right r)
    (hmodule : ∀ a, pr.comp (L a) = (Lr a).comp pr)
    (commutation : TracialCommutationInput L R)
    (T : D →L[ℂ] H) (hT : ∀ a, T.comp (Lr a) = (L a).comp T) :
    ∃ b : P, r * b = b ∧ (R.right b).comp inc = T := by
  let Z := T.comp pr
  have hZ (a : P) : Z.comp (L a) = (L a).comp Z := by
    dsimp [Z]
    rw [ContinuousLinearMap.comp_assoc, hmodule, ← ContinuousLinearMap.comp_assoc,
      hT, ContinuousLinearMap.comp_assoc]
  obtain ⟨b, hb⟩ := commutation Z hZ
  refine ⟨b, R.injective ?_, ?_⟩
  · rw [R.mul, hb, ← hr]
    dsimp [Z]
    rw [ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc pr,
      hpr, ContinuousLinearMap.id_comp]
  · rw [hb]
    dsimp [Z]
    rw [ContinuousLinearMap.comp_assoc, hpr, ContinuousLinearMap.comp_id]

end RightMultipliers

section CyclicCornerData

variable {P C K Q : Type*} [CStarAlgebra P] [CStarAlgebra C]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]

/-- A representation has a vector whose algebra orbit is dense. Because the
representation is linear in the algebra variable, no additional span is needed. -/
def CyclicStarRepresentation (σ : C →⋆ₐ[ℂ] (K →L[ℂ] K)) : Prop :=
  ∃ ζ : K, DenseRange (fun a : C => σ a ζ)

/-- Cyclicity transfers through the unitary module coordinates furnished by
right multiplication by a partial isometry in the tracial corner argument. -/
theorem cyclicStarRepresentation_of_module_coordinates
    (σ : C →⋆ₐ[ℂ] (K →L[ℂ] K)) (σ' : C →⋆ₐ[ℂ] (Q →L[ℂ] Q))
    (U : K ≃ₗᵢ[ℂ] Q) (ζ : Q) (hζ : DenseRange (fun a : C => σ' a ζ))
    (hU : ∀ a x, U (σ a x) = σ' a (U x)) : CyclicStarRepresentation σ := by
  refine ⟨U.symm ζ, ?_⟩
  have hd := U.symm.surjective.denseRange.comp hζ U.symm.continuous
  have heq : (fun a : C => U.symm (σ' a ζ)) = (fun a : C => σ a (U.symm ζ)) := by
    funext a
    apply U.injective
    simp only [U.apply_symm_apply, hU]
  simpa only [Function.comp_def, heq] using hd

/-- The precise finite-factor comparison consequence needed for the chosen
corner. This is the trace form of projection comparison: Blackadar,
III.1.1.11, together with the faithful finite trace. -/
def FiniteFactorProjectionComparison (τ : P → ℝ) : Prop :=
  ∀ e r : P, IsStarProjection e → IsStarProjection r → τ r ≤ τ e →
    ∃ v : P, star v * v = r ∧ e * (v * star v) = v * star v

/-- The local tracial module realization needed after comparison: a partial
isometry from `r` into `e` realizes the corner representation on `eL²(P)r`
as a cyclic module. In a concrete tracial model this is proved using the
unitary `ξ ↦ ξ v*`, the dense orbit of `vv*`, and the preceding transfer
lemma. It is explicit geometric data, not an invariant or similarity claim. -/
def TracialCornerCyclicityInput (e r : P) (σ : C →⋆ₐ[ℂ] (K →L[ℂ] K)) : Prop :=
  ∀ v : P, star v * v = r → e * (v * star v) = v * star v →
    CyclicStarRepresentation σ

/-- The applicability of the published standard-form theorem to a cyclic
representation (Haagerup 1975, Lemma 2.10(1)). -/
def HaagerupForCyclicInput (σ : C →⋆ₐ[ℂ] (K →L[ℂ] K)) : Prop :=
  CyclicStarRepresentation σ → HaagerupCyclicVectorRealization σ

/-- Projection comparison and the explicit tracial cyclic realization provide
the precise standard-form hypothesis consumed by the analytic argument. -/
theorem haagerup_of_projection_comparison
    (τ : P → ℝ) (comparison : FiniteFactorProjectionComparison τ)
    (e r : P) (he : IsStarProjection e) (hr : IsStarProjection r) (hτ : τ r ≤ τ e)
    (σ : C →⋆ₐ[ℂ] (K →L[ℂ] K)) (cyclic : TracialCornerCyclicityInput e r σ)
    (haagerup : HaagerupForCyclicInput σ) : HaagerupCyclicVectorRealization σ := by
  obtain ⟨v, hv, hev⟩ := comparison e r he hr hτ
  exact haagerup (cyclic v hv hev)

end CyclicCornerData

section FullColumn

variable {P C H D F K : Type*} [CStarAlgebra P] [CStarAlgebra C]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup D] [InnerProductSpace ℂ D] [CompleteSpace D]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [PartialOrder C] [StarOrderedRing C]

/-- The full-column conclusion from the four specialized published cyclic
inputs and tracial commutation. The remaining hypotheses describe the actual
corner, its finite matrix coordinates, and its projection into the tracial
Hilbert space. In particular, no right-multiplier approximation is assumed. -/
theorem full_column_of_published_inputs
    (L : P →⋆ₐ[ℂ] (H →L[ℂ] H)) (Lr : P →⋆ₐ[ℂ] (D →L[ℂ] D))
    (ρ : C →⋆ₐ[ℂ] (F →L[ℂ] F)) (σ : C →⋆ₐ[ℂ] (K →L[ℂ] K))
    {n : ℕ} (hn : 0 < n) (c : FullColumnCoordinates L Lr ρ σ n)
    (R : TracialRightAction (P := P) (H := H)) (r : P)
    (inc : D →L[ℂ] H) (pr : H →L[ℂ] D)
    (hpr : pr.comp inc = ContinuousLinearMap.id ℂ D)
    (hr : inc.comp pr = R.right r)
    (hmodule : ∀ a, pr.comp (L a) = (Lr a).comp pr)
    (commutation : TracialCommutationInput L R)
    (G : K →L[ℂ] F) (Gfull : D →L[ℂ] H) (hfull : Gfull = c.extend G)
    {ε : ℝ} (hG : ‖cornerCommutator ρ σ G‖ ≤ ε)
    (dickson : DicksonTwoBound (A := C) (RectangularSum F K))
    (haagerup : HaagerupCyclicVectorRealization σ)
    (kaplansky : KaplanskyColumnApproximation σ)
    (paulsen : PaulsenSimilarityInput (normalizedRectangularRepresentation ρ σ
      (cornerCommutator ρ σ G) (cornerCommutator_leibniz ρ σ G))) :
    ∃ b : P, r * b = b ∧
      ‖Gfull - (R.right b).comp inc‖ ≤ (1 + 4 * (4 * Real.sqrt 2)) ^ 2 * ε := by
  obtain ⟨T, hT, hGT⟩ := exists_corner_intertwiner_of_published_inputs
    ρ σ G hG dickson haagerup kaplansky paulsen
  obtain ⟨b, hb, hTb⟩ := exists_supported_right_multiplier L Lr R r inc pr hpr hr
    hmodule commutation (c.extend T) (c.extend_intertwines T hT)
  refine ⟨b, hb, ?_⟩
  rw [hTb, hfull, c.norm_extend_sub hn]
  exact hGT

/-- Version of the full-column theorem in which the actual matrix-unit
commutation of the given operator supplies its diagonal form. -/
theorem full_column_of_matrixUnit_commutation
    (L : P →⋆ₐ[ℂ] (H →L[ℂ] H)) (Lr : P →⋆ₐ[ℂ] (D →L[ℂ] D))
    (ρ : C →⋆ₐ[ℂ] (F →L[ℂ] F)) (σ : C →⋆ₐ[ℂ] (K →L[ℂ] K))
    {n : ℕ} (i : Fin n) (c : FullColumnCoordinates L Lr ρ σ n)
    (R : TracialRightAction (P := P) (H := H)) (r : P)
    (inc : D →L[ℂ] H) (pr : H →L[ℂ] D)
    (hpr : pr.comp inc = ContinuousLinearMap.id ℂ D)
    (hr : inc.comp pr = R.right r)
    (hmodule : ∀ a, pr.comp (L a) = (Lr a).comp pr)
    (commutation : TracialCommutationInput L R)
    (G : D →L[ℂ] H)
    (hGmatrix : ∀ j : Fin n, (c.inCoordinates G).comp (copyMatrixUnit i j) =
      (copyMatrixUnit i j).comp (c.inCoordinates G))
    {ε : ℝ} (hG : ‖cornerCommutator ρ σ (c.corner i G)‖ ≤ ε)
    (dickson : DicksonTwoBound (A := C) (RectangularSum F K))
    (haagerup : HaagerupCyclicVectorRealization σ)
    (kaplansky : KaplanskyColumnApproximation σ)
    (paulsen : PaulsenSimilarityInput (normalizedRectangularRepresentation ρ σ
      (cornerCommutator ρ σ (c.corner i G))
      (cornerCommutator_leibniz ρ σ (c.corner i G)))) :
    ∃ b : P, r * b = b ∧
      ‖G - (R.right b).comp inc‖ ≤ (1 + 4 * (4 * Real.sqrt 2)) ^ 2 * ε := by
  exact full_column_of_published_inputs L Lr ρ σ
    (Nat.zero_lt_of_lt i.isLt) c R r inc pr hpr hr hmodule commutation
    (c.corner i G) G (c.eq_extend_of_matrixUnit_intertwining i G hGmatrix)
    hG dickson haagerup kaplansky paulsen

end FullColumn
end KadisonSimilarity

end

end OAI
