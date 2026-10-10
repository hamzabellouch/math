import OAI.Geometry.HeilbronnTriangle.MatrixAffineShell
import OAI.Geometry.HeilbronnTriangle.RowLatticeEqualShell
import OAI.Geometry.HeilbronnTriangle.MatrixSpecialRankTwo
import OAI.Geometry.HeilbronnTriangle.ZeroThreeCasePartition

namespace OAI


noncomputable section

namespace Problem355.ZeroDeterminantCount

open Matrix PrimitiveNormal
open scoped Matrix BigOperators
attribute [local instance] Classical.propDecidable

abbrev IntMatrix := Matrix (Fin 3) (Fin 3) ℤ
abbrev IntVector := Fin 3 → ℤ

structure RowData where
  B : ℕ
  b : ℕ
  e : ℕ
  k : ℕ
  prime : B.Prime
  e_le_k : e ≤ k
  L : Submodule ℤ IntVector
  C : IntMatrix
  P : (Matrix (Fin 3) (Fin 3) (ZMod (B ^ k)))ˣ
  Q : (Matrix (Fin 3) (Fin 3) (ZMod (B ^ k)))ˣ
  diagonal : C.map (Int.castRingHom (ZMod (B ^ k))) =
    (P : Matrix _ _ _) * Matrix.diagonal
      ![1, (B : ZMod (B ^ k)) ^ b, (B : ZMod (B ^ k)) ^ e] *
      (Q : Matrix _ _ _)
  contains : ∀ v : IntVector, (B ^ e) • v ∈ L
  rows : ∀ i, C i ∈ L
  index_eq : L.toAddSubgroup.index = B ^ (b + e)

def RowData.h (D : RowData) : ℝ := (D.B : ℝ) ^ D.k
def RowData.I (D : RowData) : ℕ := D.B ^ (D.b + D.e)
def RowData.E (D : RowData) : ℕ := D.B ^ D.e

lemma RowData.h_one (D : RowData) : 1 ≤ D.h := one_le_pow₀ (by exact_mod_cast D.prime.one_le)
lemma RowData.I_pos (D : RowData) : 0 < D.I := pow_pos D.prime.pos _
lemma RowData.E_pos (D : RowData) : 0 < D.E := pow_pos D.prime.pos _
lemma RowData.cube (D : RowData) : (D.E : ℝ) ^ 3 ≤ (D.I : ℝ) * D.h ^ 2 := by
  simpa only [RowData.E, RowData.I, RowData.h, Nat.cast_pow] using
    MatrixSpecialRankTwo.prime_power_cube_bound D.B D.b D.e D.k D.prime.one_le D.e_le_k

def planeConstant : ℝ := (144 * Real.pi) ^ 3
lemma planeConstant_nonneg : 0 ≤ planeConstant := by unfold planeConstant; positivity

theorem affine_shell_le (D : RowData) (q R : ℕ)
    (T : Finset IntVector) (hR : 0 < R)
    (hprimitive : ∀ x ∈ T, IsPrimitive x)
    (hnorm : ∀ x ∈ T, (R : ℝ) ≤ ‖toEuclidean x‖ ∧
      ‖toEuclidean x‖ < 2 * (R : ℝ))
    (F : IntVector → Finset IntMatrix)
    (hF : ∀ x, ∀ A ∈ F x, A *ᵥ x = 0 ∧ ∀ i, A i ∈ D.L)
    (W : IntMatrix → ℝ) (N Ca : ℝ) (hN : 0 ≤ N) (hCa : 0 ≤ Ca)
    (hcoord : ∀ x ∈ T, ∀ A ∈ F x, ∀ i j, |(A i j : ℝ)| ≤ 2 * N)
    (hproj : ∀ x ∈ T, ∀ A ∈ F x, ∃ s t : Fin 3,
      A 2 s ≠ 0 ∧ A 2 t ≠ 0 ∧
      PlaneRowTransport.projectedColumn A s ≠ PlaneRowTransport.projectedColumn A t)
    (hweight : ∀ x ∈ T, ∀ A ∈ F x,
      AffineIndependent (ZMod q) (A.map (Int.castRingHom (ZMod q))).col → W A ≤ Ca)
    (hexclude : ∀ x ∈ T, ∀ A ∈ F x,
      AffineIndependent (ZMod q) (A.map (Int.castRingHom (ZMod q))).col →
      0 < W A → D.h ^ 2 < ‖toEuclidean x‖) :
    (∑ x ∈ T, ∑ A ∈ (F x).filter (fun A =>
      AffineIndependent (ZMod q) (A.map (Int.castRingHom (ZMod q))).col), W A) ≤
      1024 * planeConstant * Ca * N ^ 6 / (D.I : ℝ) ^ 2 := by
  classical
  let F' := fun x => (F x).filter (fun A =>
    AffineIndependent (ZMod q) (A.map (Int.castRingHom (ZMod q))).col)
  have hb := MatrixAffineShell.weighted_matrix_shell_le_of_short_exclusion
    T D.L D.C D.B R D.b D.e D.k D.prime hR D.e_le_k D.P D.Q D.diagonal
    hnorm hprimitive D.contains D.rows F'
    (fun x A hA => hF x A (Finset.mem_filter.mp hA).1)
    (fun _ A => W A) N Ca hN hCa
    (fun x hx A hA => hweight x hx A (Finset.mem_filter.mp hA).1 (Finset.mem_filter.mp hA).2)
    (fun x hx A hA => hcoord x hx A (Finset.mem_filter.mp hA).1)
    (fun x hx A hA => hproj x hx A (Finset.mem_filter.mp hA).1)
    (fun x hx A hA hw => hexclude x hx A (Finset.mem_filter.mp hA).1
      (Finset.mem_filter.mp hA).2 hw) D.index_eq
  convert hb using 1 ; simp only [RowData.I, Nat.cast_pow, planeConstant] ; ring

theorem additional_shell_le (D : RowData) (q : ℕ) [Fact q.Prime]
    (hEq : IsUnit (D.E : ZMod q)) (hparam : D.h ^ 26 ≤ (q : ℝ))
    (i j : Fin 3) (hij : i ≠ j) (T : Finset IntVector)
    (hprimitive : ∀ x ∈ T, IsPrimitive x)
    (hspan : ∀ x ∈ T, ¬ ∃ a : ZMod q, (fun s => (x s : ZMod q)) =
      a • PlaneFunctional.coordinateDifference i j)
    (F : IntVector → Finset IntMatrix)
    (hF : ∀ x ∈ T, ∀ A ∈ F x, A *ᵥ x = 0 ∧ ∀ i, A i ∈ D.L)
    (W : IntMatrix → ℝ) (R N Cg : ℝ) (hR : 1 ≤ R)
    (hN : 0 ≤ N) (hCg : 0 ≤ Cg)
    (hnorm : ∀ x ∈ T, R ≤ ‖toEuclidean x‖ ∧ ‖toEuclidean x‖ ≤ 2 * R)
    (hequal : ∀ x ∈ T, ∀ A ∈ F x, ∀ s, (A s i : ZMod q) = (A s j : ZMod q))
    (hcoord : ∀ x ∈ T, ∀ A ∈ F x, ∀ i j, |(A i j : ℝ)| ≤ 2 * N)
    (hproj : ∀ x ∈ T, ∀ A ∈ F x, ∃ s t : Fin 3,
      A 2 s ≠ 0 ∧ A 2 t ≠ 0 ∧
      PlaneRowTransport.projectedColumn A s ≠ PlaneRowTransport.projectedColumn A t)
    (hweight : ∀ x ∈ T, ∀ A ∈ F x, W A ≤ Cg * (q : ℝ) ^ 2 * D.h ^ 24) :
    (∑ x ∈ T, ∑ A ∈ F x, W A) ≤
      125 * planeConstant * Cg * N ^ 6 / (D.I : ℝ) ^ 2 := by
  have hq : (0 : ℝ) < q := by exact_mod_cast (Fact.out : q.Prime).pos
  have hI : (0 : ℝ) < D.I := by exact_mod_cast D.I_pos
  have hb := RowLatticeEqualShell.weighted_matrix_shell_bound q D.L D.E D.E_pos
    hEq D.contains i j hij T hprimitive hspan F hF W R N D.I D.h
    (Cg * (q : ℝ) ^ 2 * D.h ^ 24) hR hN hI (by positivity)
    (by rw [D.index_eq]; rfl) D.cube hnorm hequal hcoord hproj hweight
  have hratio : D.h ^ 26 / (q : ℝ) ≤ 1 := (div_le_one hq).mpr hparam
  calc
    _ ≤ 125 * (144 * Real.pi) ^ 3 * (Cg * (q : ℝ) ^ 2 * D.h ^ 24) *
        N ^ 6 * D.h ^ 2 / ((q : ℝ) ^ 3 * (D.I : ℝ) ^ 2) := hb
    _ = (125 * planeConstant * Cg * N ^ 6 / (D.I : ℝ) ^ 2) *
        (D.h ^ 26 / (q : ℝ)) := by
      unfold planeConstant
      field_simp
    _ ≤ (125 * planeConstant * Cg * N ^ 6 / (D.I : ℝ) ^ 2) * 1 :=
      mul_le_mul_of_nonneg_left hratio (by unfold planeConstant; positivity)
    _ = _ := mul_one _

theorem special_shell_le (D : RowData) (q R : ℕ) (hq : 0 < q) (hR : 0 < R)
    (T : Finset IntVector) (hprimitive : ∀ x ∈ T, IsPrimitive x)
    (hnorm : ∀ x ∈ T, (R : ℝ) ≤ ‖toEuclidean x‖ ∧
      ‖toEuclidean x‖ < 2 * (R : ℝ))
    (i j k : Fin 3) (hki : k ≠ i) (hkj : k ≠ j)
    (hnonzero : ∀ x ∈ T, x k ≠ 0)
    (hline : ∀ x ∈ T, (fun t => (x t : ZMod q)) ∈
      Submodule.span (ZMod q) {Pi.single i (1 : ZMod q) - Pi.single j 1})
    (F : IntVector → Finset IntMatrix)
    (hF : ∀ x, ∀ A ∈ F x, A *ᵥ x = 0 ∧ ∀ i, A i ∈ D.L)
    (W : IntMatrix → ℝ) (N Cd : ℝ) (hN : 0 ≤ N) (hCd : 0 ≤ Cd)
    (hparam : D.h ^ 14 ≤ (q : ℝ))
    (hcoord : ∀ x ∈ T, ∀ A ∈ F x, ∀ i j, |(A i j : ℝ)| ≤ 2 * N)
    (hproj : ∀ x ∈ T, ∀ A ∈ F x, ∃ s t : Fin 3,
      A 2 s ≠ 0 ∧ A 2 t ≠ 0 ∧
      PlaneRowTransport.projectedColumn A s ≠ PlaneRowTransport.projectedColumn A t)
    (hweight : ∀ x ∈ T, ∀ A ∈ F x, W A ≤ Cd * (q : ℝ) * D.h ^ 12) :
    (∑ x ∈ T, ∑ A ∈ F x, W A) ≤
      512 * planeConstant * Cd * N ^ 6 / (D.I : ℝ) ^ 2 := by
  exact MatrixSpecialRankTwo.weighted_matrix_shell_le T D.L D.E D.I R q
    D.E_pos D.I_pos hR hq hprimitive D.contains D.index_eq hnorm
    i j k hki hkj hnonzero hline F hF (fun _ A => W A) N D.h Cd hN hCd
    hparam D.cube hweight hcoord hproj

end Problem355.ZeroDeterminantCount

end

end OAI
