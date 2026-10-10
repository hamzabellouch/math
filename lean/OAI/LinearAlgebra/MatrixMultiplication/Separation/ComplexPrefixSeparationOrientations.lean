import OAI.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexPrefixSeparationPolynomialStage

namespace OAI

/-! Finite type counts, hierarchy separation and tensor execution bounds. -/

noncomputable section

namespace MatrixMultiplication.Foundation.PrefixSeparationOrientations

open Tensor LabelHierarchySeparation PolynomialLocalConstruction
open PrefixSeparationPolynomialStage

variable {Prefix X Y Z : Type*}

def auxiliaryXZ (k : ℕ) :
    Tensor ℂ (PoolAuxiliaryGroup k) (PoolAuxiliaryGroup k) (PoolAuxiliaryGroup k) :=
  fun a b c => poolAuxiliaryTensor k a c b

def auxiliaryYZ (k : ℕ) :
    Tensor ℂ (PoolAuxiliaryGroup k) (PoolAuxiliaryGroup k) (PoolAuxiliaryGroup k) :=
  fun a b c => poolAuxiliaryTensor k b c a

theorem auxiliaryXZ_rankAtMost (k : ℕ) :
    RankAtMost (auxiliaryXZ k) (poolAuxiliaryCost k) := by
  obtain ⟨a, b, c, h⟩ := poolAuxiliaryTensor_rankAtMost k
  refine ⟨a, c, b, ?_⟩
  funext x y z
  change poolAuxiliaryTensor k x z y = _
  rw [h]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [rankOne]
  ring

theorem auxiliaryYZ_rankAtMost (k : ℕ) :
    RankAtMost (auxiliaryYZ k) (poolAuxiliaryCost k) := by
  obtain ⟨a, b, c, h⟩ := poolAuxiliaryTensor_rankAtMost k
  refine ⟨c, a, b, ?_⟩
  funext x y z
  change poolAuxiliaryTensor k y z x = _
  rw [h]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [rankOne]
  ring

def stageLeadingXZ (k : ℕ)
    (codeX : Prefix → X → Fin k) (codeZ : Prefix → Z → Fin k)
    (keepX : Prefix → X → Prop) (keepY : Prefix → Y → Prop)
    (keepZ : Prefix → Z → Prop) (prior : Prefix) :
    Tensor ℂ (X × InformedOutput k) (Y × MissingOutput k) (Z × InformedOutput k) :=
  fun x y z => stageLeading k codeX codeZ keepX keepZ keepY prior x z y

def stageLeadingYZ (k : ℕ)
    (codeY : Prefix → Y → Fin k) (codeZ : Prefix → Z → Fin k)
    (keepX : Prefix → X → Prop) (keepY : Prefix → Y → Prop)
    (keepZ : Prefix → Z → Prop) (prior : Prefix) :
    Tensor ℂ (X × MissingOutput k) (Y × InformedOutput k) (Z × InformedOutput k) :=
  fun x y z => stageLeading k codeY codeZ keepY keepZ keepX prior y z x

theorem stageLeadingXZ_synchronized (k : ℕ)
    (codeX : Prefix → X → Fin k) (codeZ : Prefix → Z → Fin k)
    (keepX : Prefix → X → Prop) (keepY : Prefix → Y → Prop)
    (keepZ : Prefix → Z → Prop) (prior : Prefix)
    (x : X × InformedOutput k) (y : Y × MissingOutput k) (z : Z × InformedOutput k)
    (codes : codeX prior x.1 = codeZ prior z.1)
    (nonzero : stageLeadingXZ k codeX codeZ keepX keepY keepZ prior x y z ≠ 0) :
    x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧ x.2.2 = z.2.2 := by
  obtain ⟨hxz, hxy, hij⟩ := stageLeading_synchronized k codeX codeZ
    keepX keepZ keepY prior x z y codes nonzero
  exact ⟨hxy, hxz, hij⟩

theorem stageLeadingYZ_synchronized (k : ℕ)
    (codeY : Prefix → Y → Fin k) (codeZ : Prefix → Z → Fin k)
    (keepX : Prefix → X → Prop) (keepY : Prefix → Y → Prop)
    (keepZ : Prefix → Z → Prop) (prior : Prefix)
    (x : X × MissingOutput k) (y : Y × InformedOutput k) (z : Z × InformedOutput k)
    (codes : codeY prior y.1 = codeZ prior z.1)
    (nonzero : stageLeadingYZ k codeY codeZ keepX keepY keepZ prior x y z ≠ 0) :
    x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧ y.2.2 = z.2.2 := by
  obtain ⟨hyz, hyx, hij⟩ := stageLeading_synchronized k codeY codeZ
    keepY keepZ keepX prior y z x codes nonzero
  exact ⟨hyx.symm, hyx.symm.trans hyz, hij⟩

theorem stageLeadingXZ_retains_pairing (k : ℕ)
    (codeX : Prefix → X → Fin k) (codeZ : Prefix → Z → Fin k)
    (keepX : Prefix → X → Prop) (keepY : Prefix → Y → Prop)
    (keepZ : Prefix → Z → Prop) (prior : Prefix) (x : X) (y : Y) (z : Z)
    (hx : keepX prior x) (hy : keepY prior y) (hz : keepZ prior z)
    (codes : codeX prior x = codeZ prior z) (i : Fin k) :
    stageLeadingXZ k codeX codeZ keepX keepY keepZ prior
      (x, (codeX prior x, i)) (y, (codeX prior x, PUnit.unit))
      (z, (codeX prior x, i)) = 1 :=
  stageLeading_retains_pairing k codeX codeZ keepX keepZ keepY prior x z y hx hz hy codes i

theorem stageLeadingYZ_retains_pairing (k : ℕ)
    (codeY : Prefix → Y → Fin k) (codeZ : Prefix → Z → Fin k)
    (keepX : Prefix → X → Prop) (keepY : Prefix → Y → Prop)
    (keepZ : Prefix → Z → Prop) (prior : Prefix) (x : X) (y : Y) (z : Z)
    (hx : keepX prior x) (hy : keepY prior y) (hz : keepZ prior z)
    (codes : codeY prior y = codeZ prior z) (i : Fin k) :
    stageLeadingYZ k codeY codeZ keepX keepY keepZ prior
      (x, (codeY prior y, PUnit.unit)) (y, (codeY prior y, i))
      (z, (codeY prior y, i)) = 1 :=
  stageLeading_retains_pairing k codeY codeZ keepY keepZ keepX prior y z x hy hz hx codes i

theorem exists_prefix_stage_XZ (k : ℕ)
    (codeX : Prefix → X → Fin k) (codeZ : Prefix → Z → Fin k)
    (keepX : Prefix → X → Prop) (keepY : Prefix → Y → Prop)
    (keepZ : Prefix → Z → Prop)
    (eligible : Prefix → X → Y → Z → Prop)
    (agree : ∀ p x y z, eligible p x y z → codeX p x = codeZ p z) :
    ∃ (MX : Prefix → X → InformedOutput k → PoolAuxiliaryGroup k → Polynomial ℂ)
      (MY : Prefix → Y → MissingOutput k → PoolAuxiliaryGroup k → Polynomial ℂ)
      (MZ : Prefix → Z → InformedOutput k → PoolAuxiliaryGroup k → Polynomial ℂ),
      (∀ p x u i, (MX p x u i).degree ≤ (0 : ℕ)) ∧
      (∀ p y v j, (MY p y v j).degree ≤ (0 : ℕ)) ∧
      (∀ p z w l, (MZ p z w l).degree ≤ (0 : ℕ)) ∧
      ∀ p x y z, eligible p x.1 y.1 z.1 →
        kernel (auxiliaryXZ k) (MX p) (MY p) (MZ p) x y z =
          Polynomial.C (stageLeadingXZ k codeX codeZ keepX keepY keepZ p x y z) := by
  classical
  obtain ⟨left, right, tag, coefficients⟩ := exists_auxiliary_coordinates k
  let fx : Prefix → X × InformedOutput k → PoolAuxiliaryGroup k :=
    fun p x => left (codeX p x.1) x.2.2
  let fy : Prefix → Y × MissingOutput k → PoolAuxiliaryGroup k := fun _ y => tag y.2.1
  let fz : Prefix → Z × InformedOutput k → PoolAuxiliaryGroup k :=
    fun p z => right (codeZ p z.1) z.2.2
  let MX := fun p => weightedCoordinatePolynomialMatrix (fx p)
    (informedWeight (keepX p) (codeX p))
  let MY := fun p => weightedCoordinatePolynomialMatrix (fy p) (missingWeight (keepY p))
  let MZ := fun p => weightedCoordinatePolynomialMatrix (fz p)
    (informedWeight (keepZ p) (codeZ p))
  refine ⟨MX, MY, MZ, ?_, ?_, ?_, ?_⟩
  · intro p x u i
    exact weightedCoordinatePolynomialMatrix_degree _ _ x u i
  · intro p y v j
    exact weightedCoordinatePolynomialMatrix_degree _ _ y v j
  · intro p z w l
    exact weightedCoordinatePolynomialMatrix_degree _ _ z w l
  · intro p x y z h
    have codes := agree p x.1 y.1 z.1 h
    change kernel (auxiliaryXZ k)
      (weightedCoordinatePolynomialMatrix (fx p) (informedWeight (keepX p) (codeX p)))
      (weightedCoordinatePolynomialMatrix (fy p) (missingWeight (keepY p)))
      (weightedCoordinatePolynomialMatrix (fz p) (informedWeight (keepZ p) (codeZ p))) x y z = _
    rw [kernel_weightedCoordinatePolynomialMatrix]
    dsimp only [fx, fy, fz, auxiliaryXZ]
    rw [← codes, coefficients]
    congr 1
    unfold informedWeight missingWeight stageLeadingXZ stageLeading
    split_ifs <;> simp_all

theorem exists_prefix_stage_YZ (k : ℕ)
    (codeY : Prefix → Y → Fin k) (codeZ : Prefix → Z → Fin k)
    (keepX : Prefix → X → Prop) (keepY : Prefix → Y → Prop)
    (keepZ : Prefix → Z → Prop)
    (eligible : Prefix → X → Y → Z → Prop)
    (agree : ∀ p x y z, eligible p x y z → codeY p y = codeZ p z) :
    ∃ (MX : Prefix → X → MissingOutput k → PoolAuxiliaryGroup k → Polynomial ℂ)
      (MY : Prefix → Y → InformedOutput k → PoolAuxiliaryGroup k → Polynomial ℂ)
      (MZ : Prefix → Z → InformedOutput k → PoolAuxiliaryGroup k → Polynomial ℂ),
      (∀ p x u i, (MX p x u i).degree ≤ (0 : ℕ)) ∧
      (∀ p y v j, (MY p y v j).degree ≤ (0 : ℕ)) ∧
      (∀ p z w l, (MZ p z w l).degree ≤ (0 : ℕ)) ∧
      ∀ p x y z, eligible p x.1 y.1 z.1 →
        kernel (auxiliaryYZ k) (MX p) (MY p) (MZ p) x y z =
          Polynomial.C (stageLeadingYZ k codeY codeZ keepX keepY keepZ p x y z) := by
  classical
  obtain ⟨left, right, tag, coefficients⟩ := exists_auxiliary_coordinates k
  let fx : Prefix → X × MissingOutput k → PoolAuxiliaryGroup k := fun _ x => tag x.2.1
  let fy : Prefix → Y × InformedOutput k → PoolAuxiliaryGroup k :=
    fun p y => left (codeY p y.1) y.2.2
  let fz : Prefix → Z × InformedOutput k → PoolAuxiliaryGroup k :=
    fun p z => right (codeZ p z.1) z.2.2
  let MX := fun p => weightedCoordinatePolynomialMatrix (fx p) (missingWeight (keepX p))
  let MY := fun p => weightedCoordinatePolynomialMatrix (fy p)
    (informedWeight (keepY p) (codeY p))
  let MZ := fun p => weightedCoordinatePolynomialMatrix (fz p)
    (informedWeight (keepZ p) (codeZ p))
  refine ⟨MX, MY, MZ, ?_, ?_, ?_, ?_⟩
  · intro p x u i
    exact weightedCoordinatePolynomialMatrix_degree _ _ x u i
  · intro p y v j
    exact weightedCoordinatePolynomialMatrix_degree _ _ y v j
  · intro p z w l
    exact weightedCoordinatePolynomialMatrix_degree _ _ z w l
  · intro p x y z h
    have codes := agree p x.1 y.1 z.1 h
    change kernel (auxiliaryYZ k)
      (weightedCoordinatePolynomialMatrix (fx p) (missingWeight (keepX p)))
      (weightedCoordinatePolynomialMatrix (fy p) (informedWeight (keepY p) (codeY p)))
      (weightedCoordinatePolynomialMatrix (fz p) (informedWeight (keepZ p) (codeZ p))) x y z = _
    rw [kernel_weightedCoordinatePolynomialMatrix]
    dsimp only [fx, fy, fz, auxiliaryYZ]
    rw [← codes, coefficients]
    congr 1
    unfold informedWeight missingWeight stageLeadingYZ stageLeading
    split_ifs <;> simp_all

section RawPools

variable {RawLabel : Type*} [DecidableEq RawLabel]

def rawPoolLeadingXZ (pool : Prefix → Finset RawLabel) (k : ℕ) (positive : 0 < k)
    (counts : ∀ p, (pool p).card = k)
    (readX : Prefix → X → RawLabel) (readZ : Prefix → Z → RawLabel) (prior : Prefix) :
    Tensor ℂ (X × InformedOutput k) (Y × MissingOutput k) (Z × InformedOutput k) :=
  fun x y z => rawPoolLeading pool k positive counts readX readZ prior x z y

def rawPoolLeadingYZ (pool : Prefix → Finset RawLabel) (k : ℕ) (positive : 0 < k)
    (counts : ∀ p, (pool p).card = k)
    (readY : Prefix → Y → RawLabel) (readZ : Prefix → Z → RawLabel) (prior : Prefix) :
    Tensor ℂ (X × MissingOutput k) (Y × InformedOutput k) (Z × InformedOutput k) :=
  fun x y z => rawPoolLeading pool k positive counts readY readZ prior y z x

theorem exists_raw_pool_stage_XZ (pool : Prefix → Finset RawLabel) (k : ℕ)
    (positive : 0 < k) (counts : ∀ p, (pool p).card = k)
    (readX : Prefix → X → RawLabel) (readZ : Prefix → Z → RawLabel)
    (eligible : Prefix → X → Y → Z → Prop)
    (agree : ∀ p x y z, eligible p x y z → readX p x = readZ p z) :
    ∃ (MX : Prefix → X → InformedOutput k → PoolAuxiliaryGroup k → Polynomial ℂ)
      (MY : Prefix → Y → MissingOutput k → PoolAuxiliaryGroup k → Polynomial ℂ)
      (MZ : Prefix → Z → InformedOutput k → PoolAuxiliaryGroup k → Polynomial ℂ),
      (∀ p x u i, (MX p x u i).degree ≤ (0 : ℕ)) ∧
      (∀ p y v j, (MY p y v j).degree ≤ (0 : ℕ)) ∧
      (∀ p z w l, (MZ p z w l).degree ≤ (0 : ℕ)) ∧
      ∀ p x y z, eligible p x.1 y.1 z.1 →
        kernel (auxiliaryXZ k) (MX p) (MY p) (MZ p) x y z =
          Polynomial.C (rawPoolLeadingXZ pool k positive counts readX readZ p x y z) := by
  apply exists_prefix_stage_XZ k
    (fun p x => maskedPoolCode pool k positive counts p (readX p x))
    (fun p z => maskedPoolCode pool k positive counts p (readZ p z))
    (fun p x => readX p x ∈ pool p) (fun _ _ => True)
    (fun p z => readZ p z ∈ pool p) eligible
  intro p x y z h
  exact congrArg (maskedPoolCode pool k positive counts p) (agree p x y z h)

theorem exists_raw_pool_stage_YZ (pool : Prefix → Finset RawLabel) (k : ℕ)
    (positive : 0 < k) (counts : ∀ p, (pool p).card = k)
    (readY : Prefix → Y → RawLabel) (readZ : Prefix → Z → RawLabel)
    (eligible : Prefix → X → Y → Z → Prop)
    (agree : ∀ p x y z, eligible p x y z → readY p y = readZ p z) :
    ∃ (MX : Prefix → X → MissingOutput k → PoolAuxiliaryGroup k → Polynomial ℂ)
      (MY : Prefix → Y → InformedOutput k → PoolAuxiliaryGroup k → Polynomial ℂ)
      (MZ : Prefix → Z → InformedOutput k → PoolAuxiliaryGroup k → Polynomial ℂ),
      (∀ p x u i, (MX p x u i).degree ≤ (0 : ℕ)) ∧
      (∀ p y v j, (MY p y v j).degree ≤ (0 : ℕ)) ∧
      (∀ p z w l, (MZ p z w l).degree ≤ (0 : ℕ)) ∧
      ∀ p x y z, eligible p x.1 y.1 z.1 →
        kernel (auxiliaryYZ k) (MX p) (MY p) (MZ p) x y z =
          Polynomial.C (rawPoolLeadingYZ pool k positive counts readY readZ p x y z) := by
  apply exists_prefix_stage_YZ k
    (fun p y => maskedPoolCode pool k positive counts p (readY p y))
    (fun p z => maskedPoolCode pool k positive counts p (readZ p z))
    (fun _ _ => True) (fun p y => readY p y ∈ pool p)
    (fun p z => readZ p z ∈ pool p) eligible
  intro p x y z h
  exact congrArg (maskedPoolCode pool k positive counts p) (agree p x y z h)

end RawPools
end MatrixMultiplication.Foundation.PrefixSeparationOrientations

end

end OAI
