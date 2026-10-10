import OAI.Analysis.KadisonKastler.WeakCPLimits
import OAI.Analysis.KadisonKastler.BoundaryBoundedTransport
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Algebra.Star.UnitaryStarAlgAut

namespace OAI

/-! # Operator averaging from an actual scalar invariant mean

The scalar mean is data on bounded scalar functions. Riesz representation
constructs the operator average from its coefficients. No operator-valued
mean, fixed-point projection, or amenability conclusion is assumed.
-/

namespace KadisonKastler

open scoped BoundedContinuousFunction BigOperators Topology CStarAlgebra

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

def scalarMeanTranslate (g : G) (f : G →ᵇ ℂ) : G →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (fun t => f (g⁻¹ * t)) ‖f‖
    (fun _ => f.norm_coe_le_norm _)

/-- The usual scalar invariant-mean data, with no assertion of existence. -/
structure ScalarInvariantMean (G : Type*) [Group G] [TopologicalSpace G] [DiscreteTopology G] where
  toCLM : (G →ᵇ ℂ) →L[ℂ] ℂ
  map_const_one : toCLM (BoundedContinuousFunction.const G 1) = 1
  norm_le : ∀ f, ‖toCLM f‖ ≤ ‖f‖
  positive : ∀ f, (∀ g, (f g).im = 0 ∧ 0 ≤ (f g).re) →
    (toCLM f).im = 0 ∧ 0 ≤ (toCLM f).re
  invariant : ∀ g f, toCLM (scalarMeanTranslate g f) = toCLM f

namespace ScalarInvariantMean

variable (m : ScalarInvariantMean G)

theorem fixed (c : ℂ) : m.toCLM (BoundedContinuousFunction.const G c) = c := by
  have he : BoundedContinuousFunction.const G c =
      c • BoundedContinuousFunction.const G (1 : ℂ) := by
    ext g
    simp
  rw [he, map_smul, m.map_const_one, smul_eq_mul, mul_one]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance invariantMeanFamilyCStar : CStarAlgebra (G →ᵇ (H →L[ℂ] H)) where

/-- The bounded scalar coefficient to which the scalar mean is applied. -/
def coefficient (F : G →ᵇ (H →L[ℂ] H)) (x y : H) : G →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun g => inner ℂ y (F g x)) (‖F‖ * ‖x‖ * ‖y‖) (fun g => by
      calc
        ‖inner ℂ y (F g x)‖ ≤ ‖y‖ * ‖F g x‖ := norm_inner_le_norm _ _
        _ ≤ ‖y‖ * (‖F‖ * ‖x‖) := mul_le_mul_of_nonneg_left
          (((F g).le_opNorm x).trans (mul_le_mul_of_nonneg_right
            (F.norm_coe_le_norm g) (norm_nonneg x))) (norm_nonneg y)
        _ = _ := by ring)

omit [Group G] [CompleteSpace H] in
@[simp] theorem coefficient_apply (F : G →ᵇ (H →L[ℂ] H)) (x y : H) (g : G) :
    coefficient F x y g = inner ℂ y (F g x) := rfl

omit [Group G] [CompleteSpace H] in
theorem norm_coefficient_le (F : G →ᵇ (H →L[ℂ] H)) (x y : H) :
    ‖coefficient F x y‖ ≤ ‖F‖ * ‖x‖ * ‖y‖ :=
  (BoundedContinuousFunction.norm_le (by positivity)).mpr (fun g => by
    calc
      ‖coefficient F x y g‖ ≤ ‖y‖ * ‖F g x‖ := norm_inner_le_norm _ _
      _ ≤ ‖y‖ * (‖F‖ * ‖x‖) := mul_le_mul_of_nonneg_left
        (((F g).le_opNorm x).trans (mul_le_mul_of_nonneg_right
          (F.norm_coe_le_norm g) (norm_nonneg x))) (norm_nonneg y)
      _ = _ := by ring)

omit [Group G] [CompleteSpace H] in
theorem coefficient_add_input (F : G →ᵇ (H →L[ℂ] H)) (x z y : H) :
    coefficient F (x + z) y = coefficient F x y + coefficient F z y := by
  ext g
  simp only [coefficient_apply, BoundedContinuousFunction.add_apply, map_add, inner_add_right]

omit [Group G] [CompleteSpace H] in
theorem coefficient_smul_input (F : G →ᵇ (H →L[ℂ] H)) (c : ℂ) (x y : H) :
    coefficient F (c • x) y = c • coefficient F x y := by
  ext g
  simp only [coefficient_apply, BoundedContinuousFunction.smul_apply, map_smul,
    inner_smul_right, smul_eq_mul]

omit [Group G] [CompleteSpace H] in
theorem coefficient_add_test (F : G →ᵇ (H →L[ℂ] H)) (x y z : H) :
    coefficient F x (y + z) = coefficient F x y + coefficient F x z := by
  ext g
  simp only [coefficient_apply, BoundedContinuousFunction.add_apply, inner_add_left]

omit [Group G] [CompleteSpace H] in
theorem coefficient_smul_test (F : G →ᵇ (H →L[ℂ] H)) (c : ℂ) (x y : H) :
    coefficient F x (c • y) = star c • coefficient F x y := by
  ext g
  simp only [coefficient_apply, BoundedContinuousFunction.smul_apply, inner_smul_left,
    smul_eq_mul]
  rfl

/-- A genuine continuous linear scalar functional in the test-vector slot. -/
def testFunctional (F : G →ᵇ (H →L[ℂ] H)) (x : H) : H →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun y => star (m.toCLM (coefficient F x y))
      map_add' := fun y z => by rw [coefficient_add_test, map_add, star_add]
      map_smul' := fun c y => by
        rw [coefficient_smul_test, map_smul, star_smul, star_star]
        rfl }
    (‖F‖ * ‖x‖) (fun y => by
      change ‖star (m.toCLM (coefficient F x y))‖ ≤ _
      rw [norm_star]
      exact (m.norm_le _).trans (norm_coefficient_le F x y))

def operatorValue (F : G →ᵇ (H →L[ℂ] H)) (x : H) : H :=
  (InnerProductSpace.toDual ℂ H).symm (m.testFunctional F x)

theorem inner_operatorValue (F : G →ᵇ (H →L[ℂ] H)) (x y : H) :
    inner ℂ y (m.operatorValue F x) = m.toCLM (coefficient F x y) := by
  calc
    inner ℂ y (m.operatorValue F x) = star (inner ℂ (m.operatorValue F x) y) :=
      (inner_conj_symm y (m.operatorValue F x)).symm
    _ = star (m.testFunctional F x y) := by
      rw [operatorValue, InnerProductSpace.toDual_symm_apply]
    _ = _ := star_star _

theorem norm_operatorValue_le (F : G →ᵇ (H →L[ℂ] H)) (x : H) :
    ‖m.operatorValue F x‖ ≤ ‖F‖ * ‖x‖ := by
  rw [operatorValue, (InnerProductSpace.toDual ℂ H).symm.norm_map]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro y
  change ‖star (m.toCLM (coefficient F x y))‖ ≤ _
  rw [norm_star]
  exact (m.norm_le _).trans (norm_coefficient_le F x y)

def operator (F : G →ᵇ (H →L[ℂ] H)) : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := m.operatorValue F
      map_add' := fun x z => by
        apply ext_inner_left ℂ
        intro y
        rw [inner_add_right, m.inner_operatorValue, m.inner_operatorValue,
          m.inner_operatorValue, coefficient_add_input, map_add]
      map_smul' := fun c x => by
        apply ext_inner_left ℂ
        intro y
        rw [inner_smul_right, m.inner_operatorValue, m.inner_operatorValue,
          coefficient_smul_input, map_smul]
        rfl }
    ‖F‖ (m.norm_operatorValue_le F)

@[simp] theorem inner_operator (F : G →ᵇ (H →L[ℂ] H)) (x y : H) :
    inner ℂ y (m.operator F x) = m.toCLM (coefficient F x y) :=
  m.inner_operatorValue F x y

theorem norm_operator_le (F : G →ᵇ (H →L[ℂ] H)) : ‖m.operator F‖ ≤ ‖F‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg F) (m.norm_operatorValue_le F)

theorem operator_add (F J : G →ᵇ (H →L[ℂ] H)) :
    m.operator (F + J) = m.operator F + m.operator J := by
  ext x
  apply ext_inner_left ℂ
  intro y
  simp only [add_apply, inner_add_right, m.inner_operator]
  rw [← map_add]
  congr 1
  ext g
  simp only [coefficient_apply, BoundedContinuousFunction.add_apply, add_apply, inner_add_right]

theorem operator_smul (c : ℂ) (F : G →ᵇ (H →L[ℂ] H)) :
    m.operator (c • F) = c • m.operator F := by
  ext x
  apply ext_inner_left ℂ
  intro y
  simp only [smul_apply, inner_smul_right, m.inner_operator]
  rw [← smul_eq_mul, ← map_smul]
  congr 1
  ext g
  simp only [coefficient_apply, BoundedContinuousFunction.smul_apply,
    smul_apply, inner_smul_right, smul_eq_mul]

/-- The actual contractive complex-linear operator average. -/
def operatorMean : (G →ᵇ (H →L[ℂ] H)) →L[ℂ] (H →L[ℂ] H) :=
  LinearMap.mkContinuous
    { toFun := m.operator
      map_add' := m.operator_add
      map_smul' := m.operator_smul }
    1 (fun F => by
      change ‖m.operator F‖ ≤ 1 * ‖F‖
      simpa only [one_mul] using m.norm_operator_le F)

theorem inner_operatorMean (F : G →ᵇ (H →L[ℂ] H)) (x y : H) :
    inner ℂ y (m.operatorMean F x) = m.toCLM (coefficient F x y) := m.inner_operator F x y

theorem operatorMean_const (T : H →L[ℂ] H) :
    m.operatorMean (BoundedContinuousFunction.const G T) = T := by
  ext x
  apply ext_inner_left ℂ
  intro y
  rw [m.inner_operatorMean]
  have hc : coefficient (BoundedContinuousFunction.const G T) x y =
      BoundedContinuousFunction.const G (inner ℂ y (T x)) := by ext g; rfl
  rw [hc, m.fixed]

theorem operatorMean_left (T : H →L[ℂ] H) (F : G →ᵇ (H →L[ℂ] H)) :
    m.operatorMean (BoundedContinuousFunction.const G T * F) = T * m.operatorMean F := by
  ext x
  apply ext_inner_left ℂ
  intro y
  rw [m.inner_operatorMean]
  have hc : coefficient (BoundedContinuousFunction.const G T * F) x y =
      coefficient F x (star T y) := by
    ext g
    simp only [coefficient_apply, BoundedContinuousFunction.mul_apply,
      BoundedContinuousFunction.const_apply, mul_apply_eq_comp,
      ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  rw [hc, ← m.inner_operatorMean, mul_apply_eq_comp,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]

theorem operatorMean_right (T : H →L[ℂ] H) (F : G →ᵇ (H →L[ℂ] H)) :
    m.operatorMean (F * BoundedContinuousFunction.const G T) = m.operatorMean F * T := by
  ext x
  apply ext_inner_left ℂ
  intro y
  rw [m.inner_operatorMean, mul_apply_eq_comp, m.inner_operatorMean]
  congr 1

/-- Averaging an actual family in a von Neumann algebra stays in that algebra. -/
theorem operatorMean_mem (M : VonNeumannAlgebra H) (F : G →ᵇ (H →L[ℂ] H))
    (hF : ∀ g, F g ∈ M) : m.operatorMean F ∈ M := by
  change m.operatorMean F ∈ (M : Set (H →L[ℂ] H))
  rw [← M.centralizer_centralizer]
  intro T hT
  rw [← m.operatorMean_left, ← m.operatorMean_right]
  congr 1
  apply BoundedContinuousFunction.ext
  intro g
  exact (hT (F g) (hF g)).symm

theorem operatorMean_isPositive (F : G →ᵇ (H →L[ℂ] H))
    (hF : ∀ g, (F g).IsPositive) : (m.operatorMean F).IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff_complex]
  intro x
  have hc := m.positive (coefficient F x x) (fun g => by
    have hp := (ContinuousLinearMap.isPositive_iff_complex (F g)).mp (hF g) x
    have he : inner ℂ x (F g x) = inner ℂ (F g x) x :=
      ((hF g).isSymmetric x x).symm
    rw [coefficient_apply, he]
    exact ⟨by rw [← hp.1]; simp, hp.2⟩)
  have hv := m.inner_operatorMean F x x
  have he : inner ℂ (m.operatorMean F x) x = m.toCLM (coefficient F x x) := by
    rw [← inner_conj_symm, hv]
    apply Complex.ext <;> simp [hc.1]
  rw [he]
  exact ⟨by apply Complex.ext <;> simp [hc.1], hc.2⟩

/-- Translation invariance survives the coefficient construction. -/
def translateFamily (g : G) (F : G →ᵇ (H →L[ℂ] H)) : G →ᵇ (H →L[ℂ] H) :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun t => F (g⁻¹ * t)) ‖F‖ (fun _ => F.norm_coe_le_norm _)

theorem operatorMean_translate (g : G) (F : G →ᵇ (H →L[ℂ] H)) :
    m.operatorMean (translateFamily g F) = m.operatorMean F := by
  ext x
  apply ext_inner_left ℂ
  intro y
  rw [m.inner_operatorMean, m.inner_operatorMean]
  have he : coefficient (translateFamily g F) x y =
      scalarMeanTranslate g (coefficient F x y) := by ext t; rfl
  rw [he, m.invariant]

local instance invariantMeanFamilyOrder : PartialOrder (G →ᵇ (H →L[ℂ] H)) :=
  CStarAlgebra.spectralOrder _
local instance invariantMeanFamilyStarOrder : StarOrderedRing (G →ᵇ (H →L[ℂ] H)) :=
  CStarAlgebra.spectralOrderedRing _

def evaluationHom (g : G) : (G →ᵇ (H →L[ℂ] H)) →⋆ₐ[ℂ] (H →L[ℂ] H) where
  toFun := fun F => F g
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

/-- Complete positivity follows by applying scalar positivity to the finite
sum of all the matrix coefficients of a positive amplified family. -/
def operatorMeanCP : (G →ᵇ (H →L[ℂ] H)) →CP (H →L[ℂ] H) where
  toLinearMap := m.operatorMean.toLinearMap
  map_cstarMatrix_nonneg' k X hX := by
    let T := hilbertMatrix (X.map m.operatorMean.toLinearMap)
    have hp : T.IsPositive := by
      rw [ContinuousLinearMap.isPositive_iff_complex]
      intro x
      let f : G →ᵇ ℂ := ∑ i, ∑ j, coefficient (X i j) (x j) (x i)
      have heval (g : G) : f g = inner ℂ x
          (hilbertMatrix (X.map (evaluationHom (H := H) g)) x) := by
        simp only [f, BoundedContinuousFunction.sum_apply, coefficient_apply,
          PiLp.inner_apply, hilbertMatrix_apply, CStarMatrix.map_apply,
          inner_sum]
        rfl
      have hpos : (m.toCLM f).im = 0 ∧ 0 ≤ (m.toCLM f).re :=
        m.positive f (fun g => by
          have hmat := map_nonneg
            (CStarMatrix.mapₙₐ (n := Fin k)
              (evaluationHom (H := H) g).toNonUnitalStarAlgHom) hX
          have hT := map_nonneg (hilbertMatrixHom (H := H) (n := Fin k)) hmat
          change (hilbertMatrix (X.map (evaluationHom (H := H) g)) - 0).IsPositive at hT
          rw [sub_zero] at hT
          have hs := (ContinuousLinearMap.isPositive_iff_complex _).mp hT x
          rw [heval]
          have hi : inner ℂ x (hilbertMatrix (X.map (evaluationHom (H := H) g)) x) =
              star (inner ℂ (hilbertMatrix (X.map (evaluationHom (H := H) g)) x) x) :=
            (inner_conj_symm _ _).symm
          rw [hi, ← hs.1]
          simpa using (show (0 : ℝ) = 0 ∧ 0 ≤
            (inner ℂ (hilbertMatrix (X.map (evaluationHom (H := H) g)) x) x).re
            from ⟨rfl, hs.2⟩))
      have hmean : inner ℂ x (T x) = m.toCLM f := by
        simp only [T, PiLp.inner_apply, hilbertMatrix_apply,
          CStarMatrix.map_apply, inner_sum]
        change (∑ i, ∑ j, inner ℂ (x i) (m.operatorMean (X i j) (x j))) = _
        simp_rw [m.inner_operatorMean]
        simp only [f, map_sum]
      have hi : inner ℂ (T x) x = m.toCLM f := by
        rw [← inner_conj_symm, hmean]
        apply Complex.ext <;> simp [hpos.1]
      rw [hi]
      exact ⟨by apply Complex.ext <;> simp [hpos.1], hpos.2⟩
    apply (NonUnitalStarAlgHom.map_le_map_iff
      (hilbertMatrixHom (H := H) (n := Fin k)) hilbertMatrixHom_injective).mp
    rw [map_zero]
    change (T - 0).IsPositive
    simpa only [sub_zero] using hp

theorem operatorMeanCP_one : m.operatorMeanCP (1 : G →ᵇ (H →L[ℂ] H)) = 1 :=
  m.operatorMean_const 1

/-- The orbit family of an operator under an actual unitary representation. -/
def conjugationFamily (U : G →* unitary (H →L[ℂ] H)) (T : H →L[ℂ] H) :
    G →ᵇ (H →L[ℂ] H) :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun g => unitaryConj (U g) T) ‖T‖ (fun _ => (norm_unitaryConj _ _).le)

@[simp] theorem conjugationFamily_apply (U : G →* unitary (H →L[ℂ] H))
    (T : H →L[ℂ] H) (g : G) : conjugationFamily U T g = unitaryConj (U g) T := rfl

def conjugationFamilyHom (U : G →* unitary (H →L[ℂ] H)) :
    (H →L[ℂ] H) →⋆ₐ[ℂ] (G →ᵇ (H →L[ℂ] H)) where
  toFun := conjugationFamily U
  map_one' := by
    apply BoundedContinuousFunction.ext
    intro g
    exact (Unitary.conjStarAlgAut ℂ _ (U g)).toStarAlgHom.map_one
  map_mul' S T := by
    apply BoundedContinuousFunction.ext
    intro g
    exact (Unitary.conjStarAlgAut ℂ _ (U g)).toStarAlgHom.map_mul S T
  map_zero' := by
    apply BoundedContinuousFunction.ext
    intro g
    exact (Unitary.conjStarAlgAut ℂ _ (U g)).toStarAlgHom.map_zero
  map_add' S T := by
    apply BoundedContinuousFunction.ext
    intro g
    exact (Unitary.conjStarAlgAut ℂ _ (U g)).toStarAlgHom.map_add S T
  commutes' c := by
    apply BoundedContinuousFunction.ext
    intro g
    exact (Unitary.conjStarAlgAut ℂ _ (U g)).toStarAlgHom.commutes c
  map_star' S := by
    apply BoundedContinuousFunction.ext
    intro g
    exact StarHomClass.map_star (Unitary.conjStarAlgAut ℂ _ (U g)).toStarAlgHom S

/-- The unital completely positive invariant average of conjugates. -/
def averageConjugation (U : G →* unitary (H →L[ℂ] H)) :
    (H →L[ℂ] H) →CP (H →L[ℂ] H) where
  toLinearMap := m.operatorMean.toLinearMap.comp (conjugationFamilyHom U).toAlgHom.toLinearMap
  map_cstarMatrix_nonneg' k X hX := by
    have h := m.operatorMeanCP.map_cstarMatrix_nonneg
      (X.map (conjugationFamilyHom U))
      (CompletelyPositiveMapClass.map_cstarMatrix_nonneg' (conjugationFamilyHom U) k X hX)
    exact h

theorem averageConjugation_apply (U : G →* unitary (H →L[ℂ] H)) (T : H →L[ℂ] H) :
    m.averageConjugation U T = m.operatorMean (conjugationFamily U T) := rfl

theorem averageConjugation_one (U : G →* unitary (H →L[ℂ] H)) :
    m.averageConjugation U 1 = 1 := by
  change m.operatorMean (conjugationFamilyHom U 1) = 1
  rw [show conjugationFamilyHom U 1 = 1 from (conjugationFamilyHom U).map_one]
  exact m.operatorMeanCP_one

theorem averageConjugation_fixed (U : G →* unitary (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (hT : ∀ g, unitaryConj (U g) T = T) : m.averageConjugation U T = T := by
  rw [averageConjugation_apply]
  have h : conjugationFamily U T = BoundedContinuousFunction.const G T := by
    apply BoundedContinuousFunction.ext
    intro g
    exact hT g
  rw [h, m.operatorMean_const]

theorem averageConjugation_invariant (U : G →* unitary (H →L[ℂ] H))
    (T : H →L[ℂ] H) (g : G) :
    unitaryConj (U g) (m.averageConjugation U T) = m.averageConjugation U T := by
  have he : translateFamily (g⁻¹) (conjugationFamily U T) =
      BoundedContinuousFunction.const G (U g : H →L[ℂ] H) * conjugationFamily U T *
        BoundedContinuousFunction.const G (star (U g : H →L[ℂ] H)) := by
    apply BoundedContinuousFunction.ext
    intro t
    change unitaryConj (U ((g⁻¹)⁻¹ * t)) T = _
    rw [inv_inv, map_mul, unitaryConj_mul]
    rfl
  have h := m.operatorMean_translate (g⁻¹) (conjugationFamily U T)
  rw [he, m.operatorMean_right, m.operatorMean_left] at h
  exact h

/-- Invariant algebras are preserved by the actual operator average. -/
theorem averageConjugation_mem (U : G →* unitary (H →L[ℂ] H))
    (M : VonNeumannAlgebra H) (T : H →L[ℂ] H)
    (hT : ∀ g, unitaryConj (U g) T ∈ M) : m.averageConjugation U T ∈ M :=
  m.operatorMean_mem M _ hT

theorem averageConjugation_eq_of_commutes (U : G →* unitary (H →L[ℂ] H))
    (T : H →L[ℂ] H) (hT : ∀ g, Commute T (U g : H →L[ℂ] H)) :
    m.averageConjugation U T = T := by
  apply m.averageConjugation_fixed U T
  intro g
  change (U g : H →L[ℂ] H) * T * star (U g : H →L[ℂ] H) = T
  rw [← (hT g).eq, mul_assoc, Unitary.mul_star_self_of_mem (U g).property, mul_one]

/-- A uniform orbit displacement bound is retained by averaging. -/
theorem norm_averageConjugation_sub_le (U : G →* unitary (H →L[ℂ] H))
    (T : H →L[ℂ] H) {c : ℝ} (hc : 0 ≤ c)
    (hT : ∀ g, ‖unitaryConj (U g) T - T‖ ≤ c) :
    ‖m.averageConjugation U T - T‖ ≤ c := by
  have he : m.averageConjugation U T - T = m.operatorMean
      (conjugationFamily U T - BoundedContinuousFunction.const G T) := by
    rw [map_sub, m.operatorMean_const, averageConjugation_apply]
  rw [he]
  exact (m.norm_operator_le _).trans ((BoundedContinuousFunction.norm_le hc).mpr hT)

/-- The scalar construction supplies the precise bimodule mean used by
the already proved boundary correction. -/
def bimoduleMean : BimoduleMean (boundaryConstant (G := G) (B := H →L[ℂ] H)) where
  toCLM := m.operatorMean
  map_one := m.operatorMeanCP_one
  map_star F := completelyPositive_map_star m.operatorMeanCP F
  norm_le := m.norm_operator_le
  map_left := m.operatorMean_left
  map_right F T := m.operatorMean_right T F

/-- With trivial action on the value algebra, the constructed bimodule
mean is equivariant for the actual boundary translation. -/
theorem bimoduleMean_trivial_equivariant (g : G) (F : G →ᵇ (H →L[ℂ] H)) :
    m.bimoduleMean.toCLM
        (boundaryTranslate (1 : G →* ((H →L[ℂ] H) ≃⋆ₐ[ℂ] (H →L[ℂ] H))) g F) =
      m.bimoduleMean.toCLM F := by
  have he : boundaryTranslate
      (1 : G →* ((H →L[ℂ] H) ≃⋆ₐ[ℂ] (H →L[ℂ] H))) g F = translateFamily g F := by
    apply BoundedContinuousFunction.ext
    intro t
    rfl
  change m.operatorMean _ = m.operatorMean F
  rw [he, m.operatorMean_translate]

end ScalarInvariantMean

end

end KadisonKastler

end OAI
