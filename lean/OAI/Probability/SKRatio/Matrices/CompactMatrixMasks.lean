import Mathlib
import OAI.Probability.SKRatio.Matrices.RandomMatrixNet

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Set Metric
namespace SKRatio.MatrixNet
attribute [local instance] Classical.propDecidable

lemma masked_matrix_norm_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (s t : Fin n → Prop) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (fun i j => if s i ∧ t j then A i j else 0)‖ ≤
        ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A‖ := by
  let D (s : Fin n → Prop) : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.diagonal (fun i => if s i then 1 else 0)
  have hde (s : Fin n → Prop) :
      ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (D s)‖ ≤ 1 := by
    apply matrix_diagonal_opNorm_le _ 1 zero_le_one
    intro i
    split_ifs <;> norm_num
  have he : (fun i j => if s i ∧ t j then A i j else 0) = D s*A*D t := by
    ext i j
    simp only [D,Matrix.diagonal_mul,Matrix.mul_diagonal]
    split_ifs <;> simp_all
  rw [he,map_mul,map_mul]
  calc
    _ ≤ (‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (D s)‖*
        ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A‖)*
        ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (D t)‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (1*‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A‖)*1 :=
      mul_le_mul (mul_le_mul_of_nonneg_right (hde s) (norm_nonneg _)) (hde t)
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

lemma bin_kernel_decomposition {n : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → κ) (G : κ → κ → ℝ) :
    Matrix.of (fun i j => A i j*G (b i) (b j)) =
      ∑ a : κ, ∑ c : κ, G a c • Matrix.of (fun i j => if b i=a ∧ b j=c then A i j else 0) := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.sum_apply,Matrix.of_apply,Matrix.smul_apply,smul_eq_mul]
  simp only [mul_ite,mul_zero, ite_and,
    Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq,
    Finset.mem_univ,ite_true]
  ring

lemma euclideanCLM_smul {n : ℕ} (a : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (a • A) =
      a • Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A := by
  exact map_smul (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)) a A

lemma masked_smul_norm_le {n : ℕ} (a : ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (s t : Fin n → Prop) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (a • Matrix.of (fun i j => if s i ∧ t j then A i j else 0))‖ ≤
      |a| * ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A‖ := by
  rw [euclideanCLM_smul,norm_smul,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (masked_matrix_norm_le A s t) (abs_nonneg a)

lemma bin_kernel_norm_le {n : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → κ) (G : κ → κ → ℝ) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (Matrix.of (fun i j => A i j*G (b i) (b j)))‖ ≤
      (∑ a : κ, ∑ c : κ, |G a c|) * ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A‖ := by
  let T := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
  let P (a c : κ) : Matrix (Fin n) (Fin n) ℝ :=
    G a c • Matrix.of (fun i j => if b i=a ∧ b j=c then A i j else 0)
  have hmap : T (∑ a, ∑ c, P a c) = ∑ a, ∑ c, T (P a c) := by
    rw [map_sum]
    exact Finset.sum_congr rfl (fun a _ => map_sum T _ _)
  have hnormsum : ‖∑ a, ∑ c, T (P a c)‖ ≤ ∑ a, ∑ c, ‖T (P a c)‖ :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum (fun a _ => norm_sum_le _ _))
  have hbnd : ∑ a, ∑ c, ‖T (P a c)‖ ≤ ∑ a, ∑ c, |G a c| *‖T A‖ := by
    dsimp only [T,P]
    apply Finset.sum_le_sum
    intro a _
    apply Finset.sum_le_sum
    intro c _
    convert masked_smul_norm_le (G a c) A (fun i => b i=a) (fun j => b j=c) using 1
    try rfl
    apply congrArg (fun M : Matrix (Fin n) (Fin n) ℝ =>
      ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M‖)
    apply Matrix.ext
    intro i j
    simp only [Matrix.smul_apply,Matrix.of_apply,smul_eq_mul]
    split_ifs <;> rfl
  rw [bin_kernel_decomposition A b G]
  change ‖T (∑ a, ∑ c, P a c)‖ ≤ _
  rw [hmap]
  apply (hnormsum.trans hbnd).trans_eq
  simp only [T, Finset.sum_mul]

lemma kernel_error_norm_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (G G' : Fin n → Fin n → ℝ) {a C : ℝ} (ha : 0≤a) (hC : 0≤C)
    (hr : ∀ i, ∑ j, |A i j| ≤ C) (hc : ∀ j, ∑ i, |A i j| ≤ C)
    (he : ∀ i j, |G i j-G' i j| ≤ a) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (fun i j => A i j*(G i j-G' i j))‖ ≤ a*C := by
  apply matrix_opNorm_le_schur _ (a*C) (mul_nonneg ha hC)
  · intro i
    calc
      _ ≤ ∑ j, a*|A i j| := Finset.sum_le_sum (fun j _ => by
        rw [abs_mul,mul_comm]
        exact mul_le_mul_of_nonneg_right (he i j) (abs_nonneg _))
      _ = a*(∑ j, |A i j|) := (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (hr i) ha
  · intro j
    calc
      _ ≤ ∑ i, a*|A i j| := Finset.sum_le_sum (fun i _ => by
        rw [abs_mul,mul_comm]
        exact mul_le_mul_of_nonneg_right (he i j) (abs_nonneg _))
      _ = a*(∑ i, |A i j|) := (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (hc j) ha

lemma compact_kernel_approximation {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    (G : X × X → ℝ) (hG : Continuous G) {a : ℝ} (ha : 0<a) :
    ∃ (s : Finset X) (b : X → s), ∀ x y, |G (x,y)-G (b x,b y)| ≤ a := by
  classical
  obtain ⟨δ,hδ,hcont⟩ := Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous hG) a ha
  obtain ⟨s,_,hs,hcov⟩ := finite_cover_balls_of_compact (X := X) isCompact_univ hδ
  have hnear (x : X) : ∃ y : {z // z ∈ hs.toFinset}, dist x y < δ := by
    obtain ⟨y,hy,hxy⟩ := Set.mem_iUnion₂.mp (hcov (Set.mem_univ x))
    exact ⟨⟨y,hs.mem_toFinset.mpr hy⟩,hxy⟩
  choose b hb using hnear
  refine ⟨hs.toFinset,b,?_⟩
  intro x y
  have hh := hcont (show dist (x,y) ((b x: X),(b y: X)) < δ by
    simpa only [Prod.dist_eq,max_lt_iff] using And.intro (hb x) (hb y))
  exact (Real.dist_eq _ _ ▸ hh).le

theorem continuous_kernel_insertion {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    (G : X × X → ℝ) (hG : Continuous G) {C u : ℝ} (hC : 0≤C) (hu : 0<u) :
    ∃ δ : ℝ, 0<δ ∧ ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ),
      (∀ i, ∑ j, |A i j| ≤ C) → (∀ j, ∑ i, |A i j| ≤ C) →
      ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A‖ ≤ δ →
      ∀ x : Fin n → X,
      ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (fun i j => A i j*G (x i,x j))‖ ≤ u := by
  classical
  let a := u/(2*(C+1))
  have ha : 0<a := by dsimp [a]; positivity
  obtain ⟨s,b,hb⟩ := compact_kernel_approximation G hG ha
  let B : ℝ := ∑ k : s, ∑ l : s, |G (k,l)|
  have hB : 0≤B := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  let δ := u/(2*(B+1))
  have hd : 0<δ := by dsimp [δ]; positivity
  refine ⟨δ,hd,?_⟩
  intro n A hr hc hsmall x
  have hbin := bin_kernel_norm_le A (fun i => b (x i)) (fun k l => G (k,l))
  have herr := kernel_error_norm_le A (fun i j => G (x i,x j))
    (fun i j => G (b (x i),b (x j))) ha.le hC hr hc (fun i j => hb (x i) (x j))
  have hdecomp : Matrix.of (fun i j => A i j*G (x i,x j)) =
      Matrix.of (fun i j => A i j*G (b (x i),b (x j))) +
      Matrix.of (fun i j => A i j*(G (x i,x j)-G (b (x i),b (x j)))) := by
    apply Matrix.ext
    intro i j
    change A i j*G (x i,x j) = A i j*G (b (x i),b (x j)) + A i j*(G (x i,x j)-G (b (x i),b (x j)))
    ring
  have hBδ : B*δ ≤ u/2 := by
    dsimp [δ]
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by positivity : (0:ℝ)<2*(B+1))).mpr
    nlinarith
  have haC : a*C ≤ u/2 := by
    dsimp [a]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : (0:ℝ)<2*(C+1))).mpr
    nlinarith
  calc
    _ ≤ B*‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A‖+a*C := by
      change ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (Matrix.of (fun i j => A i j*G (x i,x j)))‖ ≤ _
      rw [hdecomp,map_add]
      exact (norm_add_le _ _).trans (add_le_add hbin herr)
    _ ≤ B*δ+a*C := add_le_add_left (mul_le_mul_of_nonneg_left hsmall hB) _
    _ ≤ u := by linarith only [hBδ,haC]

end SKRatio.MatrixNet

end

end OAI
