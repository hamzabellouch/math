import Mathlib
import OAI.Combinatorics.ThinTrees.Metric.Numerator

namespace OAI

/-! Metric matrix bound. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical MatrixOrder

variable {n m d : ℕ}

def difference (u v : Fin n) : Fin n → ℝ := point u-point v

def Test (Z : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  Z.PosSemidef ∧ ∀u v w, qform Z (difference u w) ≤
    qform Z (difference u v)+qform Z (difference v w)

def CenteredTest (Z : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  Test Z ∧ Z *ᵥ (fun _ => 1)=0

lemma test_zero : Test (0 : Matrix (Fin n) (Fin n) ℝ) := by
  refine ⟨Matrix.PosSemidef.zero,?_⟩
  intro u v w
  simp [qform]

lemma test_add {X Y : Matrix (Fin n) (Fin n) ℝ} (hX : Test X) (hY : Test Y) :
    Test (X+Y) := by
  refine ⟨hX.1.add hY.1,?_⟩
  intro u v w
  simp only [qform_add]
  linarith only [hX.2 u v w,hY.2 u v w]

lemma test_smul {X : Matrix (Fin n) (Fin n) ℝ} (hX : Test X) {a : ℝ} (ha : 0 ≤ a) :
    Test (a • X) := by
  refine ⟨hX.1.smul ha,?_⟩
  intro u v w
  simpa only [qform_smul,mul_add] using mul_le_mul_of_nonneg_left (hX.2 u v w) ha

lemma test_sum {I : Type*} (S : Finset I) (X : I → Matrix (Fin n) (Fin n) ℝ)
    (hX : ∀i ∈ S, Test (X i)) : Test (∑i ∈ S, X i) := by
  induction S using Finset.induction_on with
  | empty => simpa using test_zero (n := n)
  | @insert i S hi ih =>
    rw [sum_insert hi]
    exact test_add (hX i (mem_insert_self _ _)) (ih (fun j hj => hX j (mem_insert_of_mem hj)))

lemma test_convex : Convex ℝ {Z : Matrix (Fin n) (Fin n) ℝ | Test Z} := by
  intro X hX Y hY a b ha hb _
  exact test_add (test_smul hX ha) (test_smul hY hb)

lemma test_closed : IsClosed {Z : Matrix (Fin n) (Fin n) ℝ | Test Z} := by
  simp only [Test,Set.ofPred_and,Set.ofPred_forall]
  exact isClosed_psd.inter (isClosed_iInter fun u => isClosed_iInter fun v =>
    isClosed_iInter fun w => isClosed_le (qform_continuous _) ((qform_continuous _).add (qform_continuous _)))

def columnPoints (X : Matrix (Fin d) (Fin n) ℝ) : Fin n → EuclideanSpace ℝ (Fin d) :=
  fun v => WithLp.toLp 2 (fun i => X i v)

lemma eval_difference (x : Fin n → ℝ) (u v : Fin n) :
    x ⬝ᵥ difference u v=x u-x v := by
  simp [difference,point,dotProduct_sub]

lemma gram_distance (X : Matrix (Fin d) (Fin n) ℝ) (u v : Fin n) :
    ‖columnPoints X u-columnPoints X v‖^2=qform (Xᵀ*X) (difference u v) := by
  have hnorm (x : Fin d → ℝ) : ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖^2=x ⬝ᵥ x := by
    simp [EuclideanSpace.norm_sq_eq,dotProduct,←pow_two]
  have hv : X *ᵥ difference u v=(fun i => X i u-X i v) := by
    ext i
    exact eval_difference (fun j => X i j) u v
  have hq : qform (Xᵀ*X) (difference u v)=(X *ᵥ difference u v) ⬝ᵥ (X *ᵥ difference u v) := by
    rw [qform,←mulVec_mulVec,dotProduct_mulVec,vecMul_transpose]
  rw [hq,hv,←hnorm]
  rfl

lemma sqrt_gram {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : Z.PosSemidef) :
    (CFC.sqrt Z)ᵀ*CFC.sqrt Z=Z := by
  rw [isHermitian_iff_isSymm.mp (CFC.sqrt_nonneg Z).posSemidef.isHermitian]
  exact CFC.sqrt_mul_sqrt_self Z hZ.nonneg

lemma sqrt_columns_metric {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : Test Z) :
    MetricProfiles.SquaredTriangle (columnPoints (CFC.sqrt Z)) := by
  intro u v w
  simpa only [gram_distance,sqrt_gram hZ.1] using hZ.2 u v w

lemma contraction (X : Matrix (Fin d) (Fin n) ℝ) (U : Matrix (Fin m) (Fin d) ℝ)
    (hU : Uᵀ*U ≤ 1) :
    let Y : Fin n → EuclideanSpace ℝ (Fin m) := fun v => WithLp.toLp 2 (U *ᵥ (fun i => X i v))
    ∀u v, ‖Y u-Y v‖^2 ≤ ‖columnPoints X u-columnPoints X v‖^2 := by
  intro Y u v
  have hh := StrongThinTree.Polar.norm_sq_mulVec_le hU (fun i => X i u-X i v)
  have heq : Y u-Y v=WithLp.toLp 2 (U *ᵥ (fun i => X i u-X i v)) := by
    dsimp [Y]
    rw [show (fun i => X i u-X i v)=(fun i => X i u)-(fun i => X i v) from rfl,mulVec_sub]
    rfl
  rw [heq]
  simpa [EuclideanSpace.norm_sq_eq,dotProduct,columnPoints,←pow_two] using hh

lemma laplacian_pairing (G : MultiGraph n m) (Z : Matrix (Fin n) (Fin n) ℝ) :
    (G.laplacian univ*Z).trace=∑e, qform Z (G.incidence e) := by
  simp only [laplacian,sum_mul,trace_sum,ShortcutDual.trace_outer_mul,qform]

lemma column_edge_energy (G : MultiGraph n m) (X : Matrix (Fin d) (Fin n) ℝ) :
    (∑e, ‖columnPoints X (G.left e)-columnPoints X (G.right e)‖^2)=
      (G.laplacian univ*(Xᵀ*X)).trace := by
  rw [laplacian_pairing]
  apply sum_congr rfl
  intro e _
  exact gram_distance X (G.left e) (G.right e)

theorem polynomial_nuclear_bound :
    ∃ qH : ℕ, 2 ≤ qH ∧ ∀ q : ℕ, qH ≤ q →
      ∀ (n m : ℕ) (G : MultiGraph n m) (H : Hierarchy n),
      H.LocallyConnectedReal G q →
      ∀ M : Finset (Finset (Fin n)), M ⊆ H.nodes →
      (∀t ∈ M, t ≠ univ) →
      (∀t ∈ M, ((G.cut univ t).card : ℝ)/q ≤ (H.parentBoundary G t).card) →
      ∀ (Z : Matrix (Fin n) (Fin n) ℝ), Test Z →
      ∀ (lam : M → ℝ), (∀t, 0 ≤ lam t) → (∑t, lam t)=1 →
      (CFC.sqrt (CFC.sqrt Z*ShortcutDual.objectiveMatrix G.incidence
        (fun t : M => H.parentBoundary G t) lam*CFC.sqrt Z)).trace^2 ≤
        ((q:ℝ)^(-31/40:ℝ)/2)*(G.laplacian univ*Z).trace := by
  obtain ⟨qH,hqH,hbound⟩ := MetricProfiles.polynomial_metric_numerator
  refine ⟨qH,hqH,?_⟩
  intro q hq n m G H hconn M hM hroot hratio Z hZ lam hlam hsum
  let X := CFC.sqrt Z
  have hn := ShortcutDual.nuclear_bound_of_embedding_bound G.incidence
    (fun t : M => H.parentBoundary G t) X (K := ((q:ℝ)^(-31/40:ℝ)/2)*(G.laplacian univ*Z).trace) ?_ hlam hsum
  · simpa only [X,sqrt_gram hZ.1] using hn
  intro U hU hpos
  let Y : Fin n → EuclideanSpace ℝ (Fin m) := fun v => WithLp.toLp 2 (U *ᵥ (fun i => X i v))
  have he := hbound q hq n m G H hconn M hM hroot hratio n (columnPoints X)
    (sqrt_columns_metric hZ) Y (contraction X U hU)
    (fun e => by simpa only [Y,G.contraction_edge_diag] using hpos e)
  rw [sum_coe_sort M (fun t => (∑e ∈ H.parentBoundary G t,
    (U*(X*Matrix.of (fun v e => G.incidence e v))) e e)^2 /
      ((H.parentBoundary G t).card : ℝ))]
  dsimp only [Y] at he
  simp only [G.contraction_edge_diag] at he
  change (∑t ∈ M, _) ≤ _ at he
  rw [column_edge_energy,show Xᵀ*X=Z from sqrt_gram hZ.1] at he
  exact he

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
