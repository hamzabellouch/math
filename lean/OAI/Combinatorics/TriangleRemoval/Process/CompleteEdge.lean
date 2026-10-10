import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.TerminalLaw
import OAI.Combinatorics.TriangleRemoval.Spectral.MatrixInfinityAlgHom
import OAI.Combinatorics.TriangleRemoval.Asymptotics.ActiveL2Map

namespace OAI

section
noncomputable section
open scoped BigOperators
open Classical Matrix

namespace SharpTerminalLeave

abbrev CompleteEdge (n : ℕ) := ↥(completeGraph n)

def graphActive {n : ℕ} (G : Graph n) : Finset (CompleteEdge n) :=
  Finset.univ.filter (fun e => e.val ∈ G)

@[simp] lemma mem_graphActive {n : ℕ} (G : Graph n) (e : CompleteEdge n) :
    e ∈ graphActive G ↔ e.val ∈ G := by simp [graphActive]

def graphEdgeEmbed {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n) : G ↪ CompleteEdge n :=
  ⟨fun e => ⟨e.val,hG e.property⟩,fun _ _ h => Subtype.ext (congrArg (fun e : CompleteEdge n => e.val) h)⟩

lemma graphActive_sum {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n) (f : CompleteEdge n → ℝ) :
    (∑ e ∈ graphActive G, f e) = ∑ e : G, f (graphEdgeEmbed G hG e) := by
  apply Finset.sum_bij (fun e he => (⟨e.val,(mem_graphActive G e).mp he⟩ : G))
  · intro _ _; exact Finset.mem_univ _
  · intro a ha b hb he
    exact Subtype.ext (congrArg (fun e : G => e.val) he)
  · intro e _
    exact ⟨graphEdgeEmbed G hG e,by exact (mem_graphActive G _).mpr e.property,rfl⟩
  · intro _ _; rfl

lemma graphActive_card_le {n : ℕ} : Fintype.card (CompleteEdge n) ≤ n^2 := by
  rw [Fintype.card_coe,card_completeGraph]
  exact (Nat.choose_le_pow n 2)

lemma graphActive_nested {n : ℕ} {G H : Graph n} (h : H ⊆ G) : graphActive H ⊆ graphActive G := by
  intro e he
  exact (mem_graphActive G e).mpr (h ((mem_graphActive H e).mp he))

def graphRestrict {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n) :
    (CompleteEdge n → ℝ) →ₗ[ℝ] (G → ℝ) where
  toFun x e := x (graphEdgeEmbed G hG e)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def graphExtend {n : ℕ} (G : Graph n) : (G → ℝ) →ₗ[ℝ] (CompleteEdge n → ℝ) where
  toFun z e := if he : e.val ∈ G then z ⟨e.val,he⟩ else 0
  map_add' _ _ := by funext e; by_cases he : e.val ∈ G <;> simp [he]
  map_smul' _ _ := by funext e; by_cases he : e.val ∈ G <;> simp [he]

@[simp] lemma graphRestrict_extend {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n) (z : G → ℝ) :
    graphRestrict G hG (graphExtend G z) = z := by
  funext e
  change (if he : e.val ∈ G then z ⟨e.val,he⟩ else 0) = z e
  simp only [dite_eq_left e.property]

lemma activeLinf_restrict {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n) (x : CompleteEdge n → ℝ) :
    activeLinf (graphActive G) x = ‖graphRestrict G hG x‖ := by
  apply le_antisymm
  · apply activeLinf_bound _ _ (norm_nonneg _)
    intro e he
    have hh := norm_le_pi_norm (graphRestrict G hG x) (⟨e.val,(mem_graphActive G e).mp he⟩ : G)
    exact hh
  · apply (pi_norm_le_iff_of_nonneg (apply_nonneg _ _)).mpr
    intro e
    exact activeLinf_coordinate _ _ (e := graphEdgeEmbed G hG e) ((mem_graphActive _ _).mpr e.property)

lemma activeL2_restrict {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n) (x : CompleteEdge n → ℝ) :
    activeL2 (graphActive G) x = ‖WithLp.toLp 2 (graphRestrict G hG x)‖ := by
  have hsq : (activeL2 (graphActive G) x)^2 = ‖WithLp.toLp 2 (graphRestrict G hG x)‖^2 := by
    rw [activeL2_sq,EuclideanSpace.real_norm_sq_eq,graphActive_sum G hG]
    rfl
  nlinarith [apply_nonneg (activeL2 (graphActive G)) x,norm_nonneg (WithLp.toLp 2 (graphRestrict G hG x))]

noncomputable def graphMatrixLift {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n)
    (M : Matrix G G ℝ) : Module.End ℝ (CompleteEdge n → ℝ) :=
  (graphExtend G).comp ((Matrix.toLin' M).comp (graphRestrict G hG))

@[simp] lemma graphMatrixLift_restrict {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n)
    (M : Matrix G G ℝ) (x : CompleteEdge n → ℝ) :
    graphRestrict G hG (graphMatrixLift G hG M x) = M *ᵥ (graphRestrict G hG x) := by
  simp [graphMatrixLift]

open scoped Matrix.Norms.Operator in

lemma graphMatrixLift_linf {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n)
    (M : Matrix G G ℝ) (x : CompleteEdge n → ℝ) :
    activeLinf (graphActive G) (graphMatrixLift G hG M x) ≤ ‖M‖*activeLinf (graphActive G) x := by
  rw [activeLinf_restrict G hG,graphMatrixLift_restrict,activeLinf_restrict G hG]
  exact (matrixInfinityAlgHom M).le_opNorm _ |>.trans_eq (by rw [matrixInfinityAlgHom_norm])

open scoped Matrix.Norms.L2Operator in

lemma graphMatrixLift_l2 {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n)
    (M : Matrix G G ℝ) (x : CompleteEdge n → ℝ) :
    activeL2 (graphActive G) (graphMatrixLift G hG M x) ≤ ‖M‖*activeL2 (graphActive G) x := by
  rw [activeL2_restrict G hG,graphMatrixLift_restrict,activeL2_restrict G hG]
  have hh := (Matrix.toEuclideanCLM (n := G) (𝕜 := ℝ) M).le_opNorm (WithLp.toLp 2 (graphRestrict G hG x))
  simpa only [Matrix.toEuclideanCLM_toLp,← Matrix.l2_opNorm_toEuclideanCLM] using hh

end SharpTerminalLeave
end
end

end OAI
