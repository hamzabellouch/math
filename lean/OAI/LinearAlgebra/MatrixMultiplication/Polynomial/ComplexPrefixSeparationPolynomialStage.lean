import OAI.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexSeparationPolynomialKernel

namespace OAI

/-! Polynomial tensor restrictions and exact coefficient extraction. -/

noncomputable section

namespace MatrixMultiplication.Foundation.PrefixSeparationPolynomialStage

open Tensor LabelHierarchySeparation PolynomialLocalConstruction

variable {Prefix X Y Z : Type*}

abbrev InformedOutput (k : ℕ) := Fin k × Fin k
abbrev MissingOutput (k : ℕ) := Fin k × PUnit

theorem exists_auxiliary_coordinates (k : ℕ) :
    ∃ (left right : Fin k → Fin k → PoolAuxiliaryGroup k)
      (tag : Fin k → PoolAuxiliaryGroup k),
      ∀ s s' i j,
        poolAuxiliaryTensor k (left s i) (right s j) (tag s') =
          if s = s' ∧ i = j then 1 else 0 := by
  classical
  by_cases hk : k = 1
  · subst k
    refine ⟨fun _ _ => 0, fun _ _ => 0, fun _ => 0, ?_⟩
    intro s s' i j
    simp [poolAuxiliaryTensor, Tensor.rankOne, Subsingleton.elim s s',
      Subsingleton.elim i j]
  · obtain ⟨tag, point, collision⟩ := Separation.exists_modular_separation
      (Separation.grid_population_bound k) (Separation.grid_population_bound k)
    refine ⟨point, fun s j => tag s - point s j, tag, ?_⟩
    intro s s' i j
    simp only [poolAuxiliaryTensor, ite_eq_right hk, groupTensor, collision]

def informedWeight {k : ℕ} (keep : X → Prop) (code : X → Fin k) :
    X × InformedOutput k → ℂ := by
  classical
  exact fun x => if keep x.1 ∧ x.2.1 = code x.1 then 1 else 0

def missingWeight {k : ℕ} (keep : Z → Prop) : Z × MissingOutput k → ℂ := by
  classical
  exact fun z => if keep z.1 then 1 else 0

def stageLeading (k : ℕ)
    (codeX : Prefix → X → Fin k) (codeY : Prefix → Y → Fin k)
    (keepX : Prefix → X → Prop) (keepY : Prefix → Y → Prop)
    (keepZ : Prefix → Z → Prop) (prior : Prefix) :
    Tensor ℂ (X × InformedOutput k) (Y × InformedOutput k) (Z × MissingOutput k) := by
  classical
  exact fun x y z => if
      (keepX prior x.1 ∧ x.2.1 = codeX prior x.1) ∧
      (keepY prior y.1 ∧ y.2.1 = codeY prior y.1) ∧
      keepZ prior z.1 ∧
      (codeX prior x.1 = z.2.1 ∧ x.2.2 = y.2.2)
    then 1 else 0

theorem stageLeading_synchronized (k : ℕ)
    (codeX : Prefix → X → Fin k) (codeY : Prefix → Y → Fin k)
    (keepX : Prefix → X → Prop) (keepY : Prefix → Y → Prop)
    (keepZ : Prefix → Z → Prop) (prior : Prefix)
    (x : X × InformedOutput k) (y : Y × InformedOutput k) (z : Z × MissingOutput k)
    (codes : codeX prior x.1 = codeY prior y.1)
    (nonzero : stageLeading k codeX codeY keepX keepY keepZ prior x y z ≠ 0) :
    x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧ x.2.2 = y.2.2 := by
  classical
  have guard :
      (keepX prior x.1 ∧ x.2.1 = codeX prior x.1) ∧
      (keepY prior y.1 ∧ y.2.1 = codeY prior y.1) ∧
      keepZ prior z.1 ∧
      (codeX prior x.1 = z.2.1 ∧ x.2.2 = y.2.2) := by
    by_contra hn
    exact nonzero (by simp [stageLeading, hn])
  exact ⟨guard.1.2.trans (codes.trans guard.2.1.2.symm),
    guard.1.2.trans guard.2.2.2.1, guard.2.2.2.2⟩

theorem stageLeading_retains_pairing (k : ℕ)
    (codeX : Prefix → X → Fin k) (codeY : Prefix → Y → Fin k)
    (keepX : Prefix → X → Prop) (keepY : Prefix → Y → Prop)
    (keepZ : Prefix → Z → Prop) (prior : Prefix) (x : X) (y : Y) (z : Z)
    (hx : keepX prior x) (hy : keepY prior y) (hz : keepZ prior z)
    (codes : codeX prior x = codeY prior y) (i : Fin k) :
    stageLeading k codeX codeY keepX keepY keepZ prior
      (x, (codeX prior x, i)) (y, (codeX prior x, i))
      (z, (codeX prior x, PUnit.unit)) = 1 := by
  simp [stageLeading, hx, hy, hz, codes]

theorem exists_prefix_stage (k : ℕ)
    (codeX : Prefix → X → Fin k) (codeY : Prefix → Y → Fin k)
    (keepX : Prefix → X → Prop) (keepY : Prefix → Y → Prop)
    (keepZ : Prefix → Z → Prop)
    (eligible : Prefix → X → Y → Z → Prop)
    (agree : ∀ p x y z, eligible p x y z → codeX p x = codeY p y) :
    ∃ (MX : Prefix → X → InformedOutput k → PoolAuxiliaryGroup k → Polynomial ℂ)
      (MY : Prefix → Y → InformedOutput k → PoolAuxiliaryGroup k → Polynomial ℂ)
      (MZ : Prefix → Z → MissingOutput k → PoolAuxiliaryGroup k → Polynomial ℂ),
      (∀ p x u i, (MX p x u i).degree ≤ (0 : ℕ)) ∧
      (∀ p y v j, (MY p y v j).degree ≤ (0 : ℕ)) ∧
      (∀ p z w l, (MZ p z w l).degree ≤ (0 : ℕ)) ∧
      ∀ p x y z, eligible p x.1 y.1 z.1 →
        kernel (poolAuxiliaryTensor k) (MX p) (MY p) (MZ p) x y z =
          Polynomial.C (stageLeading k codeX codeY keepX keepY keepZ p x y z) := by
  classical
  obtain ⟨left, right, tag, coefficients⟩ := exists_auxiliary_coordinates k
  let fx : Prefix → X × InformedOutput k → PoolAuxiliaryGroup k :=
    fun p x => left (codeX p x.1) x.2.2
  let fy : Prefix → Y × InformedOutput k → PoolAuxiliaryGroup k :=
    fun p y => right (codeY p y.1) y.2.2
  let fz : Prefix → Z × MissingOutput k → PoolAuxiliaryGroup k :=
    fun _ z => tag z.2.1
  let MX := fun p => weightedCoordinatePolynomialMatrix (fx p)
    (informedWeight (keepX p) (codeX p))
  let MY := fun p => weightedCoordinatePolynomialMatrix (fy p)
    (informedWeight (keepY p) (codeY p))
  let MZ := fun p => weightedCoordinatePolynomialMatrix (fz p) (missingWeight (keepZ p))
  refine ⟨MX, MY, MZ, ?_, ?_, ?_, ?_⟩
  · intro p x u i
    exact weightedCoordinatePolynomialMatrix_degree _ _ x u i
  · intro p y v j
    exact weightedCoordinatePolynomialMatrix_degree _ _ y v j
  · intro p z w l
    exact weightedCoordinatePolynomialMatrix_degree _ _ z w l
  · intro p x y z h
    have codes := agree p x.1 y.1 z.1 h
    change kernel (poolAuxiliaryTensor k)
      (weightedCoordinatePolynomialMatrix (fx p) (informedWeight (keepX p) (codeX p)))
      (weightedCoordinatePolynomialMatrix (fy p) (informedWeight (keepY p) (codeY p)))
      (weightedCoordinatePolynomialMatrix (fz p) (missingWeight (keepZ p))) x y z = _
    rw [kernel_weightedCoordinatePolynomialMatrix]
    dsimp only [fx, fy, fz]
    rw [← codes, coefficients]
    congr 1
    unfold informedWeight missingWeight stageLeading
    split_ifs <;> simp_all

section RawPools

variable {RawLabel : Type*} [DecidableEq RawLabel]

def maskedPoolCode (pool : Prefix → Finset RawLabel) (k : ℕ) (positive : 0 < k)
    (counts : ∀ p, (pool p).card = k) (p : Prefix) (label : RawLabel) : Fin k := by
  classical
  exact if h : label ∈ pool p then (poolEnumeration pool k counts p) ⟨label, h⟩
    else ⟨0, positive⟩

theorem maskedPoolCode_decode (pool : Prefix → Finset RawLabel) (k : ℕ)
    (positive : 0 < k) (counts : ∀ p, (pool p).card = k)
    (p : Prefix) (label : RawLabel) (allowed : label ∈ pool p) :
    ((poolEnumeration pool k counts p).symm
      (maskedPoolCode pool k positive counts p label)).val = label := by
  simp [maskedPoolCode, allowed]

def rawPoolLeading (pool : Prefix → Finset RawLabel) (k : ℕ) (positive : 0 < k)
    (counts : ∀ p, (pool p).card = k)
    (readX : Prefix → X → RawLabel) (readY : Prefix → Y → RawLabel) :
    Prefix → Tensor ℂ (X × InformedOutput k) (Y × InformedOutput k)
      (Z × MissingOutput k) :=
  stageLeading k
    (fun p x => maskedPoolCode pool k positive counts p (readX p x))
    (fun p y => maskedPoolCode pool k positive counts p (readY p y))
    (fun p x => readX p x ∈ pool p) (fun p y => readY p y ∈ pool p)
    (fun _ _ => True)

theorem exists_raw_pool_stage (pool : Prefix → Finset RawLabel) (k : ℕ)
    (positive : 0 < k) (counts : ∀ p, (pool p).card = k)
    (readX : Prefix → X → RawLabel) (readY : Prefix → Y → RawLabel)
    (eligible : Prefix → X → Y → Z → Prop)
    (agree : ∀ p x y z, eligible p x y z → readX p x = readY p y) :
    ∃ (MX : Prefix → X → InformedOutput k → PoolAuxiliaryGroup k → Polynomial ℂ)
      (MY : Prefix → Y → InformedOutput k → PoolAuxiliaryGroup k → Polynomial ℂ)
      (MZ : Prefix → Z → MissingOutput k → PoolAuxiliaryGroup k → Polynomial ℂ),
      (∀ p x u i, (MX p x u i).degree ≤ (0 : ℕ)) ∧
      (∀ p y v j, (MY p y v j).degree ≤ (0 : ℕ)) ∧
      (∀ p z w l, (MZ p z w l).degree ≤ (0 : ℕ)) ∧
      ∀ p x y z, eligible p x.1 y.1 z.1 →
        kernel (poolAuxiliaryTensor k) (MX p) (MY p) (MZ p) x y z =
          Polynomial.C (rawPoolLeading pool k positive counts readX readY p x y z) := by
  apply exists_prefix_stage k
    (fun p x => maskedPoolCode pool k positive counts p (readX p x))
    (fun p y => maskedPoolCode pool k positive counts p (readY p y))
    (fun p x => readX p x ∈ pool p) (fun p y => readY p y ∈ pool p)
    (fun _ _ => True) eligible
  intro p x y z h
  exact congrArg (maskedPoolCode pool k positive counts p) (agree p x y z h)

end RawPools

end MatrixMultiplication.Foundation.PrefixSeparationPolynomialStage

end

end OAI
