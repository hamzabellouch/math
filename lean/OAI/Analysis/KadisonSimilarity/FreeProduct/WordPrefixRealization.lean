import OAI.Analysis.KadisonSimilarity.FreeProduct.TracialRepeatedWords
import OAI.Analysis.KadisonSimilarity.Representation.ReducedCreationBlocks

namespace OAI

/-! The fixed alternating prefixes in propagation are isometries on the
appropriate reduced-word subspace. This follows by iterating the two
one-letter Fock creation formulas. Their global operator bounds follow from
the algebraic symmetry and normalized corner-unitary relations. -/

noncomputable section
namespace KadisonSimilarity

section Creation

variable {EA ED H : Type*}
  [NormedAddCommGroup EA] [InnerProductSpace ℂ EA]
  [NormedAddCommGroup ED] [InnerProductSpace ℂ ED]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The two elementary creation formulas for reduced words starting in the
opposite free factor. The tensor maps are the usual isometric inclusions of
reduced-word summands, and the specified letters have Hilbert norm one. -/
structure AlternatingCreationCoordinates (EA ED : Type*)
    [NormedAddCommGroup EA] [InnerProductSpace ℂ EA]
    [NormedAddCommGroup ED] [InnerProductSpace ℂ ED]
    (S : H →L[ℂ] H) (X : ℕ → H →L[ℂ] H) (DLead : Submodule ℂ H) where
  ALead : Submodule ℂ H
  s : EA
  x : ℕ → ED
  norm_s : ‖s‖ = 1
  norm_x : ∀ n, ‖x n‖ = 1
  createA : HilbertTensor EA DLead →ₗᵢ[ℂ] H
  createD : HilbertTensor ED ALead →ₗᵢ[ℂ] H
  createA_mem : ∀ w, createA w ∈ ALead
  createD_mem : ∀ w, createD w ∈ DLead
  actionA : ∀ y : DLead, S y = createA (hilbertTensorInsert s y)
  actionD : ∀ n (y : ALead), X n y = createD (hilbertTensorInsert (x n) y)

namespace AlternatingCreationCoordinates

variable {S : H →L[ℂ] H} {X : ℕ → H →L[ℂ] H} {DLead : Submodule ℂ H}
  (C : AlternatingCreationCoordinates EA ED S X DLead)

/-- The first elementary creation step has norm one and the expected range. -/
theorem actionA_isometry (y : H) (hy : y ∈ DLead) :
    S y ∈ C.ALead ∧ ‖S y‖ = ‖y‖ := by
  have h := C.actionA (⟨y, hy⟩ : DLead)
  refine ⟨?_, ?_⟩
  · rw [h]
    exact C.createA_mem _
  · rw [h, LinearIsometry.norm_map, norm_hilbertTensorInsert, C.norm_s, one_mul]
    rfl

/-- The second elementary creation step has norm one and returns to the
subspace of words starting in the other free factor. -/
theorem actionD_isometry (n : ℕ) (y : H) (hy : y ∈ C.ALead) :
    X n y ∈ DLead ∧ ‖X n y‖ = ‖y‖ := by
  have h := C.actionD n (⟨y, hy⟩ : C.ALead)
  refine ⟨?_, ?_⟩
  · rw [h]
    exact C.createD_mem _
  · rw [h, LinearIsometry.norm_map, norm_hilbertTensorInsert, C.norm_x, one_mul]
    rfl

/-- Iterating the elementary formulas proves the fixed alternating-prefix
isometry; no bound on a complete prefix is assumed. -/
theorem prefix_isometry (m n : ℕ) (y : H) (hy : y ∈ DLead) :
    ((S * X n) ^ m * S) y ∈ C.ALead ∧
      ‖((S * X n) ^ m * S) y‖ = ‖y‖ := by
  induction m with
  | zero => simpa only [pow_zero, one_mul] using C.actionA_isometry y hy
  | succ m ih =>
    have hx := C.actionD_isometry n _ ih.1
    have hs := C.actionA_isometry _ hx.1
    rw [pow_succ']
    change S (X n (((S * X n) ^ m * S) y)) ∈ C.ALead ∧
      ‖S (X n (((S * X n) ^ m * S) y))‖ = ‖y‖
    exact ⟨hs.1, hs.2.trans (hx.2.trans ih.2)⟩

end AlternatingCreationCoordinates
end Creation

section AlgebraBounds

variable {P : Type*} [CStarAlgebra P]

/-- A unitary has norm at most one, including in the zero C-star algebra. -/
theorem norm_unitary_le_one (u : unitary P) : ‖(u : P)‖ ≤ 1 := by
  have h : ‖(u : P)‖ = ‖(1 : P)‖ := by
    simpa only [mul_one] using CStarRing.norm_coe_unitary_mul u (1 : P)
  rw [h]
  exact IsStarProjection.norm_le 1 (.one P)

/-- The algebra norm of every corner Haar letter is bounded uniformly in its
frequency, using only its normalization and corner unitarity. -/
theorem norm_haarCornerLetter_le {q : P} {hq : IsStarProjection q}
    (z : unitary (CStarCorner q hq)) (a : ℝ) (n : ℕ) :
    ‖haarCornerLetter z a n‖ ≤ (Real.sqrt a)⁻¹ := by
  have hpow : ‖haarCornerPower z ((n : ℤ) + 1)‖ ≤ 1 :=
    norm_unitary_le_one (z ^ ((n : ℤ) + 1))
  have hc : ‖haarCornerCoefficient a‖ = (Real.sqrt a)⁻¹ := by
    simp only [haarCornerCoefficient, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg a))]
  rw [haarCornerLetter, norm_smul, hc]
  exact (mul_le_mul_of_nonneg_left hpow
    (inv_nonneg.mpr (Real.sqrt_nonneg a))).trans_eq (mul_one _)

/-- A selfadjoint involution is contractive without a nontriviality
assumption on its C-star algebra. -/
theorem norm_symmetry_le_one (s : P) (hstar : star s = s) (hsq : s * s = 1) :
    ‖s‖ ≤ 1 :=
  norm_unitary_le_one ⟨s, ⟨by rw [hstar, hsq], by rw [hstar, hsq]⟩⟩

end AlgebraBounds

section TracialPrefix

variable {D P E H F EA ED B V : Type*} [CStarAlgebra D] [CStarAlgebra P]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup EA] [InnerProductSpace ℂ EA]
  [NormedAddCommGroup ED] [InnerProductSpace ℂ ED]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {GD : TracialCornerGeometry D E} {G : TracialCornerGeometry P H}
  {ι : D →⋆ₐ[ℂ] P} (W : TracialHeadCoordinates GD G ι F)
  [W.vacuum.HasOrthogonalProjection]
  {q : D} {hq : IsStarProjection q} (z : unitary (CStarCorner q hq))
  (a : ℝ) (s : P)

/-- The degree-`m + 1` alternating algebra prefix. -/
def tracialWordPrefix (m n : ℕ) : P :=
  (s * ι (haarCornerLetter z a n)) ^ m * s

omit [CompleteSpace F] [W.vacuum.HasOrthogonalProjection] in
/-- The left multiplier of the actual algebra prefix is isometric on the
nonvacuum head subspace, by the elementary Fock creation identities. -/
theorem tracialWordPrefix_isometry
    (C : AlternatingCreationCoordinates EA ED (G.left s)
      (fun n => G.left (ι (haarCornerLetter z a n))) W.vacuumᗮ)
    (m n : ℕ) (y : H) (hy : y ∈ W.vacuumᗮ) :
    ‖G.left (tracialWordPrefix (ι := ι) z a s m n) y‖ = ‖y‖ := by
  simpa only [tracialWordPrefix, map_mul, map_pow] using
    (C.prefix_isometry m n y hy).2

/-- The complete prefix has a uniform bound for each fixed degree. Only the
algebraic unitary relations enter this global estimate. -/
theorem norm_tracialWordPrefix_le (hstar : star s = s) (hsq : s * s = 1)
    (m n : ℕ) :
    ‖G.left (tracialWordPrefix (ι := ι) z a s m n)‖ ≤ ((Real.sqrt a)⁻¹) ^ m := by
  have hs : ‖G.left s‖ ≤ 1 :=
    (NonUnitalStarAlgHom.norm_apply_le G.left.toNonUnitalStarAlgHom s).trans
      (norm_symmetry_le_one s hstar hsq)
  have hx : ‖G.left (ι (haarCornerLetter z a n))‖ ≤ (Real.sqrt a)⁻¹ :=
    (NonUnitalStarAlgHom.norm_apply_le G.left.toNonUnitalStarAlgHom _).trans
      ((NonUnitalStarAlgHom.norm_apply_le ι.toNonUnitalStarAlgHom _).trans
        (norm_haarCornerLetter_le z a n))
  have hc : 0 ≤ (Real.sqrt a)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg a)
  induction m with
  | zero => simpa only [tracialWordPrefix, pow_zero, one_mul] using hs
  | succ m ih =>
    have hid : G.left (tracialWordPrefix (ι := ι) z a s (m + 1) n) =
        (G.left s * G.left (ι (haarCornerLetter z a n))) *
          G.left (tracialWordPrefix (ι := ι) z a s m n) := by
      simp only [tracialWordPrefix, pow_succ', map_mul, map_pow, mul_assoc]
    rw [hid, pow_succ']
    calc
      _ ≤ (‖G.left s‖ * ‖G.left (ι (haarCornerLetter z a n))‖) *
          ‖G.left (tracialWordPrefix (ι := ι) z a s m n)‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
          (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (1 * (Real.sqrt a)⁻¹) * ((Real.sqrt a)⁻¹) ^ m := by
        exact mul_le_mul (mul_le_mul hs hx (norm_nonneg _) zero_le_one) ih
          (norm_nonneg _) (by positivity)
      _ = _ := by rw [one_mul]

/-- Construct the propagation realization from elementary reduced-word
creation and multiplication. Both complete-prefix fields are conclusions. -/
def tracialRepeatedWordRealizationOfCreation
    (hstar : star s = s) (hsq : s * s = 1)
    (C : AlternatingCreationCoordinates EA ED (G.left s)
      (fun n => G.left (ι (haarCornerLetter z a n))) W.vacuumᗮ)
    (m : ℕ) (Y : H →L[ℂ] H) (B₀ : B →L[ℂ] B) (Bₖ : V →L[ℂ] V)
    (repeatVector : B →ₗᵢ[ℂ] V) (word : ℕ → V →ₗᵢ[ℂ] H)
    (small : B →L[ℂ] H)
    (hsmall : ∀ v, ‖small v‖ = Real.sqrt a * ‖v‖)
    (hzero : ∀ v, Y (small v) = small (B₀ v))
    (hlevel : ∀ n v, Y (word n (repeatVector v)) = word n (Bₖ (repeatVector v)))
    (hsupport : ∀ v, G.left (ι q) (small v) = small v)
    (hword : ∀ n v, word n (repeatVector v) =
      G.left (tracialWordPrefix (ι := ι) z a s m n)
        (G.left (ι (haarCornerLetter z a n)) (small v))) :
    TracialRepeatedWordRealization W z a Y B₀ Bₖ where
  repeatVector := repeatVector
  word := word
  small := small
  small_norm := hsmall
  level_zero := hzero
  level_repeated := hlevel
  support_small := hsupport
  prefixElement := tracialWordPrefix (ι := ι) z a s m
  word_factor := hword
  prefix_isometry := tracialWordPrefix_isometry W z a s C m
  prefix_bound := ((Real.sqrt a)⁻¹) ^ m
  prefix_bound_le := norm_tracialWordPrefix_le z a s hstar hsq m

end TracialPrefix
end KadisonSimilarity

end

end OAI
