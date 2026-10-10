import OAI.Analysis.Mahler.CoordinateEuclidean
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.MeasureTheory.Function.Jacobian

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace MahlerStokes

lemma radiusSq_smul {n : ℕ} (r : ℝ) (x : Fin n → ℝ) :
    radiusSq (r • x) = r^2 * radiusSq x := by
  simp only [radiusSq, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

lemma chord_pos {n : ℕ} {y : Fin n → ℝ} (hy : y ∈ coordBall n 1) :
    0 < chord 1 y := Real.sqrt_pos.2 (sub_pos.mpr hy)

lemma chord_sq {n : ℕ} {y : Fin n → ℝ} (hy : y ∈ coordBall n 1) :
    (chord 1 y)^2 = 1 - radiusSq y := by
  simp only [chord, one_pow]
  apply Real.sq_sqrt
  have h : radiusSq y < 1 := by simpa [coordBall] using hy
  linarith

/-- Upper hemisphere graph, in the precise coordinate order used by Stokes. -/
def hemisphereGraph {n : ℕ} (i : Fin (n+1)) (y : Fin n → ℝ) : Fin (n+1) → ℝ :=
  i.insertNth (chord 1 y) y

lemma radiusSq_hemisphereGraph {n : ℕ} (i : Fin (n+1)) {y : Fin n → ℝ}
    (hy : y ∈ coordBall n 1) : radiusSq (hemisphereGraph i y) = 1 := by
  rw [hemisphereGraph, radiusSq_insertNth, chord_sq hy]
  ring

/-- Radial coordinates on the open upper half-ball. The i-th domain
coordinate is radius; all remaining coordinates parametrize the hemisphere. -/
def hemisphereCone {n : ℕ} (i : Fin (n+1)) (x : Fin (n+1) → ℝ) : Fin (n+1) → ℝ :=
  x i • hemisphereGraph i (i.removeNth x)

def hemisphereConeDomain {n : ℕ} (i : Fin (n+1)) : Set (Fin (n+1) → ℝ) :=
  {x | x i ∈ Ioo (0 : ℝ) 1 ∧ i.removeNth x ∈ coordBall n 1}

lemma radiusSq_hemisphereCone {n : ℕ} (i : Fin (n+1)) {x : Fin (n+1) → ℝ}
    (hx : x ∈ hemisphereConeDomain i) : radiusSq (hemisphereCone i x) = (x i)^2 := by
  rw [hemisphereCone, radiusSq_smul, radiusSq_hemisphereGraph i hx.2, mul_one]

lemma hemisphereCone_injOn {n : ℕ} (i : Fin (n+1)) :
    InjOn (hemisphereCone i) (hemisphereConeDomain i) := by
  intro x hx y hy h
  have hr : x i = y i := (sq_eq_sq₀ hx.1.1.le hy.1.1.le).mp
    ((radiusSq_hemisphereCone i hx).symm.trans ((congrArg radiusSq h).trans
      (radiusSq_hemisphereCone i hy)))
  have hv : i.removeNth x = i.removeNth y := by
    funext j
    have hj := congrFun h (i.succAbove j)
    simp only [hemisphereCone, hemisphereGraph, Pi.smul_apply, smul_eq_mul,
      Fin.insertNth_apply_succAbove] at hj
    rw [hr] at hj
    exact mul_left_cancel₀ hy.1.1.ne' hj
  apply funext
  rw [i.forall_iff_succAbove]
  exact ⟨hr, fun k => congrFun hv k⟩

lemma hemisphereCone_image {n : ℕ} (i : Fin (n+1)) :
    hemisphereCone i '' hemisphereConeDomain i =
      coordBall (n+1) 1 ∩ {x | 0 < x i} := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    constructor
    · change radiusSq (hemisphereCone i x) < 1^2
      rw [radiusSq_hemisphereCone i hx]
      exact (sq_lt_sq₀ hx.1.1.le (by positivity)).2 hx.1.2
    · simpa [hemisphereCone, hemisphereGraph] using mul_pos hx.1.1 (chord_pos hx.2)
  · rintro ⟨hz, hi⟩
    change 0 < z i at hi
    have hzsum : radiusSq z = (z i)^2 + radiusSq (i.removeNth z) := by
      have he : i.insertNth (z i) (i.removeNth z) = z := by simp
      rw [← he, radiusSq_insertNth]
      simp
    have hrest : 0 ≤ radiusSq (i.removeNth z) := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hrad : 0 < radiusSq z := by rw [hzsum]; positivity
    let t := Real.sqrt (radiusSq z)
    have ht : 0 < t := Real.sqrt_pos.2 hrad
    have htsq : t^2 = radiusSq z := Real.sq_sqrt hrad.le
    have ht1 : t < 1 := by
      apply (sq_lt_sq₀ ht.le (by positivity)).1
      simpa [htsq, coordBall] using hz
    let y := t⁻¹ • i.removeNth z
    have hysq : radiusSq y = t⁻¹^2 * radiusSq (i.removeNth z) := radiusSq_smul _ _
    have hy : y ∈ coordBall n 1 := by
      change radiusSq y < 1^2
      rw [hysq, inv_pow, inv_mul_eq_div, one_pow]
      apply (div_lt_one (sq_pos_of_pos ht)).2
      rw [htsq, hzsum]
      nlinarith
    have hc : chord 1 y = t⁻¹ * z i := by
      apply (sq_eq_sq₀ (chord_pos hy).le (le_of_lt (mul_pos (inv_pos.2 ht) hi))).1
      rw [chord_sq hy, hysq, mul_pow]
      field_simp
      nlinarith [htsq, hzsum]
    refine ⟨i.insertNth t y, ?_, ?_⟩
    · simpa [hemisphereConeDomain] using And.intro (And.intro ht ht1) hy
    · apply funext
      rw [i.forall_iff_succAbove]
      constructor
      · simp [hemisphereCone, hemisphereGraph, hc, ht.ne']
      · intro k
        simp [hemisphereCone, hemisphereGraph, y, ht.ne']
        rfl

/-- Real dot product as a continuous linear functional on coordinate space. -/
def coordinateDot {n : ℕ} (y : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ j, y j • ContinuousLinearMap.proj j

lemma coordinateDot_apply {n : ℕ} (y v : Fin n → ℝ) :
    coordinateDot y v = ∑ j, y j * v j := by
  simp [coordinateDot]

lemma hasFDerivAt_radiusSq {n : ℕ} (y : Fin n → ℝ) :
    HasFDerivAt radiusSq (2 • coordinateDot y) y := by
  have h := HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
    ((ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).hasFDerivAt (x := y)).pow 2)
  convert! h using 1
  ext v
  simp [coordinateDot, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

def chordDerivative {n : ℕ} (y : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  -(chord 1 y)⁻¹ • coordinateDot y

lemma hasFDerivAt_chord {n : ℕ} {y : Fin n → ℝ} (hy : y ∈ coordBall n 1) :
    HasFDerivAt (chord 1) (chordDerivative y) y := by
  have h := ((hasFDerivAt_radiusSq y).const_sub (1^2)).sqrt (sub_pos.mpr hy).ne'
  convert! h using 1
  ext v
  simp [chordDerivative, chord]
  ring

/-- Derivative of the hemisphere graph. -/
def hemisphereGraphDerivative {n : ℕ} (i : Fin (n+1)) (y : Fin n → ℝ) :
    (Fin n → ℝ) →L[ℝ] (Fin (n+1) → ℝ) :=
  ContinuousLinearMap.pi (i.insertNth (chordDerivative y) (fun j => ContinuousLinearMap.proj j))

lemma hasFDerivAt_hemisphereGraph {n : ℕ} (i : Fin (n+1)) {y : Fin n → ℝ}
    (hy : y ∈ coordBall n 1) :
    HasFDerivAt (hemisphereGraph i) (hemisphereGraphDerivative i y) y := by
  apply hasFDerivAt_pi.2
  rw [i.forall_iff_succAbove]
  constructor
  · simpa [hemisphereGraph, hemisphereGraphDerivative] using hasFDerivAt_chord hy
  · intro j
    simp only [hemisphereGraph, Fin.insertNth_apply_succAbove]
    exact hasFDerivAt_apply j y

def removeCoordinate {n : ℕ} (i : Fin (n+1)) :
    (Fin (n+1) → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi (fun j => ContinuousLinearMap.proj (i.succAbove j))

def hemisphereConeDerivative {n : ℕ} (i : Fin (n+1)) (x : Fin (n+1) → ℝ) :
    (Fin (n+1) → ℝ) →L[ℝ] (Fin (n+1) → ℝ) :=
  x i • (hemisphereGraphDerivative i (i.removeNth x)).comp (removeCoordinate i) +
    (ContinuousLinearMap.proj i).smulRight (hemisphereGraph i (i.removeNth x))

lemma hasFDerivAt_hemisphereCone {n : ℕ} (i : Fin (n+1)) {x : Fin (n+1) → ℝ}
    (hx : x ∈ hemisphereConeDomain i) :
    HasFDerivAt (hemisphereCone i) (hemisphereConeDerivative i x) x := by
  exact (ContinuousLinearMap.proj i : (Fin (n+1) → ℝ) →L[ℝ] ℝ).hasFDerivAt.smul
    ((hasFDerivAt_hemisphereGraph i hx.2).comp x (removeCoordinate i).hasFDerivAt)

end MahlerStokes

end

end OAI
