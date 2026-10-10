import Mathlib
import OAI.Computability.MaxCut.Graphs.TestCut

namespace OAI

noncomputable section
namespace OptimalMaxCut.LongCode
open scoped BigOperators
open Finset MaxCutGames.Foundations.Hastad
open OptimalMaxCut.GaussianBellman OptimalMaxCut.MISProof

def bitPairWeightQ (t : ℚ) (a b : Bool) : ℚ :=
  (1 + t * (if a then -1 else 1) * (if b then -1 else 1)) / 4

def corrAverageQ (t : ℚ) : (n : ℕ) → (Cube (Fin n) → Cube (Fin n) → ℚ) → ℚ
  | 0, F => F default default
  | n + 1, F => corrAverageQ t n (fun x y =>
      ∑ a : Bool, ∑ b : Bool, bitPairWeightQ t a b * F (Fin.cons a x) (Fin.cons b y))

 theorem bitPairWeightQ_cast (t : ℚ) (a b : Bool) : (bitPairWeightQ t a b : ℝ) = bitPairWeight t a b := by
  cases a <;> cases b <;> simp [bitPairWeightQ, bitPairWeight, sign]

 theorem corrAverageQ_cast (t : ℚ) (n : ℕ) (F : Cube (Fin n) → Cube (Fin n) → ℚ) :
    (corrAverageQ t n F : ℝ) = corrAverage t n (fun x y => (F x y : ℝ)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [corrAverageQ, ih, Rat.cast_sum, Rat.cast_mul, bitPairWeightQ_cast, corrAverage]

 theorem corrAverageQ_const (t : ℚ) (n : ℕ) (a : ℚ) : corrAverageQ t n (fun _ _ => a) = a := by
  apply Rat.cast_injective (α := ℝ)
  rw [corrAverageQ_cast, corrAverage_fst, Fintype.expect_const]

 theorem corrAverageQ_nonneg {t : ℚ} (ht : t ∈ Set.Icc (-1 : ℚ) 1) (n : ℕ)
    (F : Cube (Fin n) → Cube (Fin n) → ℚ) (hF : ∀ x y, 0 ≤ F x y) :
    0 ≤ corrAverageQ t n F := by
  have ht' : (t : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := ⟨by exact_mod_cast ht.1, by exact_mod_cast ht.2⟩
  have hh : corrAverage (t : ℝ) n (fun _ _ => (0 : ℝ)) ≤
      corrAverage t n (fun x y => (F x y : ℝ)) :=
    corrAverage_mono ht' n (fun x y => by exact_mod_cast hF x y)
  rw [corrAverage_fst, Fintype.expect_const, ← corrAverageQ_cast] at hh
  exact_mod_cast hh

 theorem corrAverageQ_sum {I : Type*} [Fintype I] (t : ℚ) (n : ℕ)
    (F : I → Cube (Fin n) → Cube (Fin n) → ℚ) :
    corrAverageQ t n (fun x y => ∑ i, F i x y) = ∑ i, corrAverageQ t n (F i) := by
  apply Rat.cast_injective (α := ℝ)
  simp only [Rat.cast_sum, corrAverageQ_cast, corrAverage_sum]

/-- The joint law of all paired cube inputs, with actual rational point masses. -/
def jointLaw (t : ℚ) (ht : t ∈ Set.Icc (-1 : ℚ) 1) (n : ℕ) : Law (Cube (Fin n) × Cube (Fin n)) where
  weight p := corrAverageQ t n (fun x y => if (x, y) = p then 1 else 0)
  nonneg p := corrAverageQ_nonneg ht n _ (fun _ _ => by split_ifs <;> norm_num)
  total := by
    rw [← corrAverageQ_sum]
    simpa using corrAverageQ_const t n 1

 theorem jointLaw_average (t : ℚ) (ht : t ∈ Set.Icc (-1 : ℚ) 1) (n : ℕ)
    (F : Cube (Fin n) → Cube (Fin n) → ℝ) :
    (jointLaw t ht n).avg (fun p => F p.1 p.2) = corrAverage t n F := by
  unfold Law.avg jointLaw
  simp only [corrAverageQ_cast, apply_ite Rat.cast, Rat.cast_one, Rat.cast_zero]
  calc
    _ = ∑ p : Cube (Fin n) × Cube (Fin n), corrAverage t n (fun x y =>
        (if (x, y) = p then (1 : ℝ) else 0) * F p.1 p.2) := by
      simp only [corrAverage_mul_const]
    _ = corrAverage t n (fun x y => ∑ p : Cube (Fin n) × Cube (Fin n),
        (if (x, y) = p then (1 : ℝ) else 0) * F p.1 p.2) := (corrAverage_sum _ _ _ _).symm
    _ = _ := by simp

namespace Law
variable {I J : Type*} [Fintype I] [Fintype J]

/-- Finite conditional sampling; both the law and all output masses are rational. -/
def bind (p : Law I) (q : I → Law J) : Law (I × J) where
  weight x := p.weight x.1 * (q x.1).weight x.2
  nonneg x := mul_nonneg (p.nonneg _) ((q _).nonneg _)
  total := by
    rw [Fintype.sum_prod_type]
    simp only [← mul_sum, Law.total, mul_one]

 theorem bind_average (p : Law I) (q : I → Law J) (F : I × J → ℝ) :
    (p.bind q).avg F = p.avg (fun i => (q i).avg (fun j => F (i,j))) := by
  simp only [avg, bind, Rat.cast_mul, Fintype.sum_prod_type, mul_sum, mul_assoc]

 theorem corrAverage_avg (p : Law I) (t : ℝ) (n : ℕ)
    (F : I → Cube (Fin n) → Cube (Fin n) → ℝ) :
    corrAverage t n (fun x y => p.avg (fun i => F i x y)) = p.avg (fun i => corrAverage t n (F i)) := by
  simp only [avg, corrAverage_sum, corrAverage_const_mul]

end Law

namespace Game
variable {X Y E : Type*} [Fintype X] [Fintype Y] [Fintype E] {q : ℕ}

/-- Every atom records exactly the finite random choices made by the long-code
Max-Cut test. In particular no real random numbers occur in the construction. -/
def sampleLaw (G : Game X Y E q) (t : ℚ) (ht : t ∈ Set.Icc (-1 : ℚ) 1) :
    Law (Y × (E × (E × (Cube (Fin q) × Cube (Fin q))))) :=
  G.rightLaw.bind (fun y => (G.edgeLaw y).bind (fun _ =>
    (G.edgeLaw y).bind (fun _ => jointLaw t ht q)))

/-- The two actual graph vertices queried at each test atom. -/
def queries (G : Game X Y E q)
    (a : Y × (E × (E × (Cube (Fin q) × Cube (Fin q))))) :
    (X × Cube (Fin q)) × (X × Cube (Fin q)) :=
  ((G.source a.2.1, cubePerm (G.permutation a.2.1) a.2.2.2.1),
   (G.source a.2.2.1, cubePerm (G.permutation a.2.2.1) (antipode a.2.2.2.2)))

 theorem testCut_expanded (G : Game X Y E q) (t : ℝ) (f : X → Cube (Fin q) → ℝ) :
    G.testCut t f = G.rightLaw.avg (fun y => (G.edgeLaw y).avg (fun e =>
      (G.edgeLaw y).avg (fun e' => corrAverage t q (fun z z' =>
        (1 - f (G.source e) (cubePerm (G.permutation e) z) *
          f (G.source e') (cubePerm (G.permutation e') (antipode z'))) / 2)))) := by
  have hp : ∀ y z z', G.averageCode f y z * G.averageCode f y (antipode z') =
      (G.edgeLaw y).avg (fun e => (G.edgeLaw y).avg (fun e' =>
      f (G.source e) (cubePerm (G.permutation e) z) *
        f (G.source e') (cubePerm (G.permutation e') (antipode z')))) := by
    intro y z z'
    simp only [averageCode, reindex, Law.avg_mul, Law.avg_smul]
  unfold testCut
  simp_rw [hp, Law.corrAverage_avg]
  simp_rw [div_eq_mul_inv, corrAverage_mul_const, corrAverage_sub,
    corrAverage_fst, Fintype.expect_const, Law.avg_mul, Law.avg_sub, Law.avg_const]

/-- The analytic test value is exactly the expectation over explicit rational
atoms. This identity will be used to aggregate a genuine finite graph. -/
 theorem testCut_sampleLaw (G : Game X Y E q) (t : ℚ) (ht : t ∈ Set.Icc (-1 : ℚ) 1)
    (f : X → Cube (Fin q) → ℝ) :
    G.testCut t f = (G.sampleLaw t ht).avg (fun a =>
      (1 - f (G.queries a).1.1 (G.queries a).1.2 *
        f (G.queries a).2.1 (G.queries a).2.2) / 2) := by
  rw [testCut_expanded]
  simp only [sampleLaw, Law.bind_average, queries]
  congr 1; funext y
  congr 1; funext e
  congr 1; funext e'
  exact (jointLaw_average t ht q _).symm

end Game
end OptimalMaxCut.LongCode

end

end OAI
