import OAI.Probability.RadialTransition.CoreUpper

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

lemma dist_le_twice_coordinate {x y : Position} {a : ℝ} (ha : 0 ≤ a)
    (hxy : ∀ k, |x k-y k| ≤ a) : dist x y ≤ 2*a := by
  have hh : dist x y ^ 2 ≤ 3*a^2 := by
    rw [EuclideanSpace.dist_sq_eq]
    calc
      _ ≤ ∑ _k : Fin 3, a^2 := Finset.sum_le_sum (fun k _ => by
        simpa only [Real.dist_eq] using (sq_le_sq₀ (abs_nonneg _) ha).mpr (hxy k))
      _ = _ := by simp
  nlinarith [dist_nonneg (x := x) (y := y)]

def tetraEdge (t : ℝ) : ℝ := microLength t + microLength t/2000

def tetraVertex (t : ℝ) (i : Fin 4) : Position :=
  WithLp.toLp 2 (fun k : Fin 3 => if i.val=0 ∨ i.val=k.val+1 then 0 else tetraEdge t*Real.sqrt 2/2)

def tetraEpsilon (t : ℝ) : ℝ := microLength t/100000

lemma tetraEdge_pos (t : ℝ) : 0 < tetraEdge t := by
  unfold tetraEdge
  have := microLength_pos t
  positivity

lemma tetraEpsilon_pos (t : ℝ) : 0 < tetraEpsilon t := div_pos (microLength_pos t) (by norm_num)

lemma tetraVertex_zero (t : ℝ) : tetraVertex t 0 = 0 := by ext k; simp [tetraVertex]

lemma tetraVertex_coordinate (t : ℝ) (i : Fin 4) (k : Fin 3) :
    0 ≤ tetraVertex t i k ∧ tetraVertex t i k ≤ 2*microLength t := by
  have hl := (microLength_pos t).le
  have hs0 := Real.sqrt_nonneg (2:ℝ)
  have hs2 : Real.sqrt (2:ℝ) ≤ 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  change 0 ≤ (if i.val=0 ∨ i.val=k.val+1 then 0 else tetraEdge t*Real.sqrt 2/2) ∧
    (if i.val=0 ∨ i.val=k.val+1 then 0 else tetraEdge t*Real.sqrt 2/2) ≤ 2*microLength t
  split_ifs
  · exact ⟨le_rfl, by positivity⟩
  · constructor
    · exact div_nonneg (mul_nonneg (tetraEdge_pos t).le hs0) (by norm_num)
    · unfold tetraEdge
      nlinarith [mul_le_mul_of_nonneg_left hs2 (tetraEdge_pos t).le]

lemma tetraVertex_dist (t : ℝ) {i j : Fin 4} (hij : i ≠ j) :
    dist (tetraVertex t i) (tetraVertex t j) = tetraEdge t := by
  have hs : Real.sqrt (2:ℝ)^2 = 2 := Real.sq_sqrt (by norm_num)
  have ha : (tetraEdge t*Real.sqrt 2/2)^2 = (tetraEdge t)^2/2 := by
    calc
      _ = (tetraEdge t)^2*(Real.sqrt 2)^2/4 := by ring
      _ = _ := by rw [hs]; ring
  have hd : dist (tetraVertex t i) (tetraVertex t j)^2 = (tetraEdge t)^2 := by
    rw [EuclideanSpace.dist_sq_eq]
    fin_cases i <;> fin_cases j <;> first
    | exact (hij rfl).elim
    | norm_num [tetraVertex, Fin.sum_univ_succ, Real.dist_eq, sq_abs]; nlinarith [ha]
  nlinarith [dist_nonneg (x := tetraVertex t i) (y := tetraVertex t j), tetraEdge_pos t]

def tetraRegion (t a : ℝ) : Set (Fin 4 → Position) :=
  {x | x 0 ∈ cube a ∧ ∀ j : Fin 3, x j.succ - x 0 - tetraVertex t j.succ ∈ cube (tetraEpsilon t)}

lemma tetraRegion_error {t a : ℝ} {x : Fin 4 → Position} (hx : x ∈ tetraRegion t a) (i : Fin 4) :
    dist (x i) (x 0+tetraVertex t i) ≤ 2*tetraEpsilon t := by
  cases i using Fin.cases with
  | zero => simp only [tetraVertex_zero, add_zero, dist_self]; positivity [tetraEpsilon_pos t]
  | succ i =>
    apply dist_le_twice_coordinate (tetraEpsilon_pos t).le
    intro k
    have hk := hx.2 i k
    change 0 ≤ x i.succ k-x 0 k-tetraVertex t i.succ k ∧ x i.succ k-x 0 k-tetraVertex t i.succ k ≤ tetraEpsilon t at hk
    change |x i.succ k-(x 0 k+tetraVertex t i.succ k)| ≤ tetraEpsilon t
    rw [abs_of_nonneg (by linarith : 0 ≤ x i.succ k-(x 0 k+tetraVertex t i.succ k))]
    linarith

lemma tetraRegion_core_zero {t a : ℝ} {x : Fin 4 → Position} (hx : x ∈ tetraRegion t a) :
    energy (corePotential t) x = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j hj
  have hij := ne_of_lt (Finset.mem_filter.mp hj).2
  have hdist : dist (x 0+tetraVertex t i) (x 0+tetraVertex t j) = tetraEdge t := by
    rw [dist_add_left, tetraVertex_dist t hij]
  have hi := tetraRegion_error hx i
  have hj := tetraRegion_error hx j
  have hupper := dist_triangle4 (x i) (x 0+tetraVertex t i) (x 0+tetraVertex t j) (x j)
  have hlower := dist_triangle4 (x 0+tetraVertex t i) (x i) (x j) (x 0+tetraVertex t j)
  rw [hdist, dist_comm (x 0+tetraVertex t j) (x j)] at hupper
  rw [hdist, dist_comm (x 0+tetraVertex t i) (x i)] at hlower
  apply coreReal_zero_plateau
  · change microLength t + shellStep t ≤ dist (x i) (x j)
    dsimp [tetraEdge, tetraEpsilon, shellStep] at *
    linarith [microLength_pos t]
  · change dist (x i) (x j) ≤ microLength t + 2*shellStep t
    dsimp [tetraEdge, tetraEpsilon, shellStep] at *
    linarith [microLength_pos t]

lemma tetraRegion_cube {t a : ℝ} {x : Fin 4 → Position} (hx : x ∈ tetraRegion t a) :
    x ∈ configurationCube (a+3*microLength t) 4 := by
  intro i k
  have hl := (microLength_pos t).le
  cases i using Fin.cases with
  | zero => have hh := hx.1 k; constructor <;> linarith
  | succ i =>
    have hi := hx.2 i k
    change 0 ≤ x i.succ k-x 0 k-tetraVertex t i.succ k ∧ x i.succ k-x 0 k-tetraVertex t i.succ k ≤ tetraEpsilon t at hi
    have hv := tetraVertex_coordinate t i.succ k
    have h0 := hx.1 k
    dsimp [tetraEpsilon] at hi
    constructor <;> linarith

end RadialTransition
end

end OAI
