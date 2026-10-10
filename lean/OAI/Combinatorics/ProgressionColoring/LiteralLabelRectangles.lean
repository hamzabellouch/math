import OAI.Combinatorics.ProgressionColoring.UniformMesh
import OAI.Combinatorics.ProgressionColoring.AdaptiveMesh

namespace OAI

noncomputable section

namespace QuantitativeVanDerWaerden

/-- The actual two-system full label of a cyclic point. -/
def literalFullLabel (mesh : AdaptiveMesh) (q D lam Ucount : ℕ)
    (hU : 0 < Ucount) (n : CyclicGroup q D) :
    (Fin D → Fin Ucount) × (Fin D → mesh.Label) :=
  (fun i => UniformMesh.label Ucount hU (xRep q D n i),
    fun i => mesh.meshLabel (yRep q D lam n i))

theorem uniformLabel_xRep_eq_iff (q D Ucount : ℕ) (hU : 0 < Ucount)
    (n : CyclicGroup q D) (i : Fin D) (u : Fin Ucount) :
    UniformMesh.label Ucount hU (xRep q D n i) = u ↔
      UniformMesh.Contains Ucount u (xRep q D n i) := by
  have hf := Int.fract_eq_self.mpr (xRep_mem q D n i)
  simpa only [hf] using UniformMesh.label_mem_iff Ucount hU (xRep q D n i) u

theorem meshLabel_yRep_eq_iff (mesh : AdaptiveMesh) (q D lam : ℕ)
    (n : CyclicGroup q D) (i : Fin D) (v : mesh.Label) :
    mesh.meshLabel (yRep q D lam n i) = v ↔
      mesh.Contains v (yRep q D lam n i) := by
  have hy := yRep_mem q D lam n i
  have hc := centered_eq_of_mem hy.1 hy.2
  simpa only [hc] using mesh.meshLabel_eq_iff (yRep q D lam n i) v

theorem literalFullLabel_first_mem (mesh : AdaptiveMesh) (q D lam Ucount : ℕ)
    (hU : 0 < Ucount) (n : CyclicGroup q D) (i : Fin D) :
    UniformMesh.Contains Ucount ((literalFullLabel mesh q D lam Ucount hU n).1 i)
      (xRep q D n i) :=
  (uniformLabel_xRep_eq_iff q D Ucount hU n i _).mp rfl

theorem literalFullLabel_second_mem (mesh : AdaptiveMesh) (q D lam Ucount : ℕ)
    (hU : 0 < Ucount) (n : CyclicGroup q D) (i : Fin D) :
    mesh.Contains ((literalFullLabel mesh q D lam Ucount hU n).2 i)
      (yRep q D lam n i) :=
  (meshLabel_yRep_eq_iff mesh q D lam n i _).mp rfl

/-- Both directions use the actual half-open mesh labels. -/
theorem literalFullLabel_eq_iff (mesh : AdaptiveMesh) (q D lam Ucount : ℕ)
    (hU : 0 < Ucount) (n : CyclicGroup q D)
    (beta : (Fin D → Fin Ucount) × (Fin D → mesh.Label)) :
    literalFullLabel mesh q D lam Ucount hU n = beta ↔
      (∀ i, UniformMesh.Contains Ucount (beta.1 i) (xRep q D n i)) ∧
      (∀ i, mesh.Contains (beta.2 i) (yRep q D lam n i)) := by
  constructor
  · intro h
    constructor
    · intro i
      apply (uniformLabel_xRep_eq_iff q D Ucount hU n i (beta.1 i)).mp
      exact congrFun (congrArg Prod.fst h) i
    · intro i
      apply (meshLabel_yRep_eq_iff mesh q D lam n i (beta.2 i)).mp
      exact congrFun (congrArg Prod.snd h) i
  · rintro ⟨hx, hy⟩
    apply Prod.ext
    · funext i
      exact (uniformLabel_xRep_eq_iff q D Ucount hU n i (beta.1 i)).mpr (hx i)
    · funext i
      exact (meshLabel_yRep_eq_iff mesh q D lam n i (beta.2 i)).mpr (hy i)

/-- An unfolded rectangle API, retaining every excluded upper endpoint. -/
theorem literalFullLabel_eq_iff_mem_rectangle (mesh : AdaptiveMesh)
    (q D lam Ucount : ℕ) (hU : 0 < Ucount) (n : CyclicGroup q D)
    (beta : (Fin D → Fin Ucount) × (Fin D → mesh.Label)) :
    literalFullLabel mesh q D lam Ucount hU n = beta ↔
      (∀ i, UniformMesh.left Ucount (beta.1 i) ≤ xRep q D n i ∧
        xRep q D n i < UniformMesh.right Ucount (beta.1 i)) ∧
      (∀ i, mesh.left (beta.2 i) ≤ yRep q D lam n i ∧
        yRep q D lam n i < mesh.right (beta.2 i)) :=
  literalFullLabel_eq_iff mesh q D lam Ucount hU n beta

theorem literalFullLabel_first_endpoints (mesh : AdaptiveMesh)
    (D Ucount : ℕ) (hU : 0 < Ucount)
    (beta : (Fin D → Fin Ucount) × (Fin D → mesh.Label)) (i : Fin D) :
    0 ≤ UniformMesh.left Ucount (beta.1 i) ∧
      UniformMesh.left Ucount (beta.1 i) < UniformMesh.right Ucount (beta.1 i) ∧
      UniformMesh.right Ucount (beta.1 i) ≤ 1 :=
  ⟨UniformMesh.left_nonneg Ucount (beta.1 i),
    UniformMesh.left_lt_right Ucount hU (beta.1 i),
    UniformMesh.right_le_one Ucount hU (beta.1 i)⟩

theorem literalFullLabel_second_endpoints (mesh : AdaptiveMesh)
    (D Ucount : ℕ)
    (beta : (Fin D → Fin Ucount) × (Fin D → mesh.Label)) (i : Fin D) :
    -(1 / 2 : ℝ) ≤ mesh.left (beta.2 i) ∧
      mesh.left (beta.2 i) < mesh.right (beta.2 i) ∧
      mesh.right (beta.2 i) ≤ 1 / 2 :=
  ⟨mesh.left_ge_neg_half (beta.2 i), sub_pos.mp (mesh.width_pos (beta.2 i)),
    mesh.right_le_half (beta.2 i)⟩

theorem literalFullLabel_same_first_distance (mesh : AdaptiveMesh)
    (q D lam Ucount : ℕ) (hU : 0 < Ucount) {a b : CyclicGroup q D}
    (h : literalFullLabel mesh q D lam Ucount hU a =
      literalFullLabel mesh q D lam Ucount hU b) (i : Fin D) :
    |xRep q D a i - xRep q D b i| ≤ 1 / (Ucount : ℝ) := by
  have ha := literalFullLabel_first_mem mesh q D lam Ucount hU a i
  have hb := literalFullLabel_first_mem mesh q D lam Ucount hU b i
  have hi := congrFun (congrArg Prod.fst h) i
  rw [← hi] at hb
  have hw := UniformMesh.width_eq Ucount ((literalFullLabel mesh q D lam Ucount hU a).1 i)
  unfold UniformMesh.Contains at ha hb
  apply abs_le.mpr
  constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

theorem literalFullLabel_same_second_distance (mesh : AdaptiveMesh)
    (q D lam Ucount : ℕ) (hU : 0 < Ucount) {a b : CyclicGroup q D}
    (h : literalFullLabel mesh q D lam Ucount hU a =
      literalFullLabel mesh q D lam Ucount hU b) (i : Fin D) :
    |yRep q D lam a i - yRep q D lam b i| ≤ 2 * mesh.H := by
  have ha := literalFullLabel_second_mem mesh q D lam Ucount hU a i
  have hb := literalFullLabel_second_mem mesh q D lam Ucount hU b i
  have hi := congrFun (congrArg Prod.snd h) i
  rw [← hi] at hb
  have hw := mesh.width_le_two_H ((literalFullLabel mesh q D lam Ucount hU a).2 i)
  unfold AdaptiveMesh.Contains at ha hb
  unfold AdaptiveMesh.width at hw
  apply abs_le.mpr
  constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

end QuantitativeVanDerWaerden

end

end OAI
