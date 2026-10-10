import OAI.Analysis.KadisonKastler.RegularCoreIntersection

namespace OAI

/-! # Normalization by the two actual regular actions

The translation and character formulas imply the required tensor-algebra
normalization. The two actions commute as conjugations, although their
implementing unitary groups commute only up to scalar characters.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem commute_conjugated_of_conjugate_commute
    (u : unitary (H →L[ℂ] H)) (a b : H →L[ℂ] H)
    (h : Commute (unitaryConj (star u) a) b) :
    Commute a (unitaryConj u b) := by
  have he := congrArg (Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) u) h.eq
  rw [map_mul, map_mul] at he
  change unitaryConj u (unitaryConj (star u) a) * unitaryConj u b =
    unitaryConj u b * unitaryConj u (unitaryConj (star u) a) at he
  have hi : unitaryConj u (unitaryConj (star u) a) = a := by
    simpa only [star_star] using unitaryConj_star_unitaryConj (star u) a
  change a * unitaryConj u b = unitaryConj u b * a
  simpa only [hi] using he

private theorem unitaryConj_star_eq_of_commute
    (u : unitary (H →L[ℂ] H)) (a : H →L[ℂ] H)
    (h : Commute (u : H →L[ℂ] H) a) :
    unitaryConj (star u) a = a := by
  simpa only [unitaryConj, Unitary.coe_star, star_star] using
    (commute_unitary_iff_star_left_conjugate u.property).mp h

/-- Constant operators commute with the actual scalar character multipliers. -/
theorem regularCharacter_commute_constant (a : ℝ) (T : H →L[ℂ] H) :
    Commute (regularCharacterUnitary (H := H) a :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (regularConstantHom volume T) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [regularCharacterUnitary_apply_ae a (regularConstantHom volume T f),
    regularConstantHom_apply_ae volume T f,
    regularConstantHom_apply_ae volume T
      ((regularCharacterUnitary (H := H) a :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f),
    regularCharacterUnitary_apply_ae a f] with t hQC hC hCQ hQ
  change (regularCharacterUnitary (H := H) a :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (regularConstantHom volume T f) t =
    regularConstantHom volume T
      ((regularCharacterUnitary (H := H) a :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) t
  rw [hQC, hC, hCQ, hQ, map_smul]

private theorem tensor_mem_conjugate_of_constant_commute
    (P : VonNeumannAlgebra H)
    (u : unitary (RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H))
    (hu : ∀ z, Commute (u : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      (regularConstantHom volume z))
    {T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hT : T ∈ regularTensorAlgebra P) : unitaryConj u T ∈ regularTensorAlgebra P := by
  apply (mem_regularTensorAlgebra_iff P _).mpr
  intro z hz
  apply commute_conjugated_of_conjugate_commute
  rw [unitaryConj_star_eq_of_commute u _ (hu z)]
  exact (mem_regularTensorAlgebra_iff P T).mp hT z hz

/-- Translation preserves the tensor algebra, without any action on `P`. -/
theorem regularTranslation_normalizes_tensor (P : VonNeumannAlgebra H)
    (s : Multiplicative ℝ) {T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hT : T ∈ regularTensorAlgebra P) :
    unitaryConj (regularRightTranslation (H := H) s) T ∈ regularTensorAlgebra P :=
  tensor_mem_conjugate_of_constant_commute P _
    (fun z => (regularConstant_commute_translation z s).symm) hT

/-- Scalar characters preserve the tensor algebra. -/
theorem regularCharacter_normalizes_tensor (P : VonNeumannAlgebra H)
    (a : Multiplicative ℝ) {T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hT : T ∈ regularTensorAlgebra P) :
    unitaryConj (regularCharacterRepresentation (H := H) a) T ∈ regularTensorAlgebra P :=
  tensor_mem_conjugate_of_constant_commute P _
    (regularCharacter_commute_constant a.toAdd) hT

private theorem regularConstant_conjugation (u : unitary (H →L[ℂ] H))
    (z : H →L[ℂ] H) :
    unitaryConj (regularConstantUnitary u) (regularConstantHom volume z) =
      regularConstantHom volume (unitaryConj u z) := by
  change regularConstantHom volume (u : H →L[ℂ] H) * regularConstantHom volume z *
      star (regularConstantHom volume (u : H →L[ℂ] H)) =
    regularConstantHom volume ((u : H →L[ℂ] H) * z * star (u : H →L[ℂ] H))
  rw [map_mul, map_mul, StarHomClass.map_star]

private theorem conjugate_commutant_of_normalizes (P : VonNeumannAlgebra H)
    (u : unitary (H →L[ℂ] H))
    (hu : ∀ x ∈ P, unitaryConj u x ∈ P) {z : H →L[ℂ] H} (hz : z ∈ P.commutant) :
    unitaryConj (star u) z ∈ P.commutant := by
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro x hx
  apply commute_conjugated_of_conjugate_commute (star u)
  have h := VonNeumannAlgebra.mem_commutant_iff.mp hz _ (hu x hx)
  change unitaryConj (star (star u)) x * z = z * unitaryConj (star (star u)) x
  simpa only [star_star] using h

private theorem regularConstant_normalizes_tensor (P : VonNeumannAlgebra H)
    (u : unitary (H →L[ℂ] H)) (hu : ∀ x ∈ P, unitaryConj u x ∈ P)
    {T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hT : T ∈ regularTensorAlgebra P) :
    unitaryConj (regularConstantUnitary u) T ∈ regularTensorAlgebra P := by
  apply (mem_regularTensorAlgebra_iff P _).mpr
  intro z hz
  apply commute_conjugated_of_conjugate_commute
  have hstar : star (regularConstantUnitary u) = regularConstantUnitary (star u) :=
    (map_inv regularConstantUnitary u).symm
  rw [hstar, regularConstant_conjugation]
  exact (mem_regularTensorAlgebra_iff P T).mp hT _
    (conjugate_commutant_of_normalizes P u hu hz)

/-- The common regular action preserves the tensor algebra whenever the
original group normalizes `P`. -/
theorem regularCoreAction_normalizes_tensor
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H)) (P : VonNeumannAlgebra H)
    (hP : ∀ s x, x ∈ P → unitaryConj (U s) x ∈ P)
    (s : Multiplicative ℝ) {T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hT : T ∈ regularTensorAlgebra P) :
    unitaryConj (regularCoreAction U s) T ∈ regularTensorAlgebra P := by
  have he : regularCoreAction U s =
      regularConstantUnitary (U s) * regularRightTranslation (H := H) s := rfl
  rw [he, unitaryConj_mul]
  exact regularConstant_normalizes_tensor P (U s) (hP s)
    (regularTranslation_normalizes_tensor P s hT)

private theorem conjugations_commute_of_scalar_product
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (u v : unitary (K →L[ℂ] K)) (c : ℂ) (hc : c * star c = 1)
    (huv : (u : K →L[ℂ] K) * v = c • ((v : K →L[ℂ] K) * u))
    (T : K →L[ℂ] K) :
    unitaryConj u (unitaryConj v T) = unitaryConj v (unitaryConj u T) := by
  rw [← unitaryConj_mul, ← unitaryConj_mul]
  change ((u : K →L[ℂ] K) * v) * T * star ((u : K →L[ℂ] K) * v) =
    ((v : K →L[ℂ] K) * u) * T * star ((v : K →L[ℂ] K) * u)
  rw [huv]
  have hc' : star c * c = 1 := by rwa [mul_comm]
  simp only [star_smul, smul_mul_assoc, mul_smul_comm, smul_smul, hc', one_smul]

/-- The regular and character actions commute as inner automorphisms. -/
theorem regularCore_character_actions_commute
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H)) (s a : Multiplicative ℝ)
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) :
    unitaryConj (regularCoreAction U s)
        (unitaryConj (regularCharacterRepresentation (H := H) a) T) =
      unitaryConj (regularCharacterRepresentation (H := H) a)
        (unitaryConj (regularCoreAction U s) T) := by
  let c : ℂ := regularCharacterScalar a.toAdd s.toAdd
  have hc : c * star c = 1 := by
    rw [mul_comm]
    change star (regularCharacterScalar a.toAdd s.toAdd) *
      regularCharacterScalar a.toAdd s.toAdd = 1
    rw [Complex.star_def, Complex.conj_mul']
    simp only [regularCharacterScalar, Circle.norm_coe, one_pow, Complex.ofReal_one]
  apply conjugations_commute_of_scalar_product _ _ c hc
  let C : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H :=
    regularConstantHom volume (U s : H →L[ℂ] H)
  let R : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H :=
    (regularRightTranslation (H := H) s :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
  let Q : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H :=
    (regularCharacterUnitary (H := H) a.toAdd :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
  change (C * R) * Q = c • (Q * (C * R))
  have hRQ : R * Q = c • (Q * R) := regularTranslation_character_covariance a.toAdd s
  have hCQ : C * Q = Q * C :=
    (regularCharacter_commute_constant (H := H) a.toAdd (U s : H →L[ℂ] H)).eq.symm
  calc
    (C * R) * Q = C * (R * Q) := mul_assoc _ _ _
    _ = C * (c • (Q * R)) := congrArg (fun X => C * X) hRQ
    _ = c • (C * (Q * R)) := mul_smul_comm _ _ _
    _ = c • ((C * Q) * R) := by rw [mul_assoc]
    _ = c • ((Q * C) * R) := by rw [hCQ]
    _ = c • (Q * (C * R)) := by rw [mul_assoc]

/-- The dual character action preserves the actual core fixed algebra. -/
theorem regularCharacter_normalizes_coreFixed
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H)) (P : VonNeumannAlgebra H)
    (a : Multiplicative ℝ) {T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hT : T ∈ fixedPointAlgebra (regularCoreAction U) (regularTensorAlgebra P)) :
    unitaryConj (regularCharacterRepresentation (H := H) a) T ∈
      fixedPointAlgebra (regularCoreAction U) (regularTensorAlgebra P) := by
  exact normalizes_fixedPointAlgebra_of_commuting_actions
    (regularCoreAction U) regularCharacterRepresentation (regularTensorAlgebra P)
    (fun b S hS => regularCharacter_normalizes_tensor P b hS)
    (regularCore_character_actions_commute U) a T hT

/-- Set form of the joint fixed-point identity, matching the range premise
of the character-average descent theorem. -/
theorem regular_jointFixed_coe
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
    (hU : ∀ ξ, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) ξ))
    [TopologicalSpace.SeparableSpace H]
    (hSpectral : PublishedRealSpectralCommutant.{u})
    (hDiagonal : PublishedRealDiagonalDecomposition.{u})
    (P : VonNeumannAlgebra H)
    (hP : ∀ s x, x ∈ P → unitaryConj (U s) x ∈ P) :
    (fixedPointAlgebra (regularCharacterRepresentation (H := H))
      (fixedPointAlgebra (regularCoreAction U) (regularTensorAlgebra P)) :
        Set (RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)) =
      regularCoreEmbedding U hU '' (P : Set (H →L[ℂ] H)) := by
  ext T
  change T ∈ fixedPointAlgebra (regularCharacterRepresentation (H := H))
    (fixedPointAlgebra (regularCoreAction U) (regularTensorAlgebra P)) ↔
    T ∈ regularCoreEmbedding U hU '' (P : Set (H →L[ℂ] H))
  rw [mem_regular_jointFixed_iff U hU hSpectral hDiagonal P hP]
  constructor
  · rintro ⟨A, hA, hT⟩
    exact ⟨A, hA, hT.symm⟩
  · rintro ⟨A, hA, hT⟩
    exact ⟨A, hA, hT.symm⟩

end

end KadisonKastler

end OAI
