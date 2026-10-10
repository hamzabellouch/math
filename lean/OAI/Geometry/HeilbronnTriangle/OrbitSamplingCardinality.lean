import OAI.Geometry.HeilbronnTriangle.OrbitSampling
import OAI.Geometry.HeilbronnTriangle.PrimePowerData

namespace OAI


noncomputable section

namespace Problem355.OrbitSampling

variable {h : ℕ} [NeZero h]

theorem mem_orbitFinset_iff_transpose
    (C A : Fin 3 → Fin 3 → ZMod h) :
    A ∈ orbitFinset (MainGroup h) C ↔
      (Matrix.transpose A) ∈ Section04Orbit.slOrbit (Matrix.transpose C) := by
  constructor
  · intro hA
    obtain ⟨G, hG⟩ := (mem_orbitFinset C A).mp hA
    refine ⟨G, ?_⟩
    change G.val * Matrix.transpose C = Matrix.transpose A
    change G • C = A at hG
    rw [← sl_action_transpose, hG]
  · rintro ⟨G, hG⟩
    apply (mem_orbitFinset C A).mpr
    refine ⟨G, ?_⟩
    apply Matrix.transpose_injective
    simpa only [sl_action_transpose] using hG

def orbitTransposeEquiv (C : Fin 3 → Fin 3 → ZMod h) :
    {A // A ∈ orbitFinset (MainGroup h) C} ≃
      Section04Orbit.slOrbit (Matrix.transpose C) where
  toFun A := ⟨(Matrix.transpose A.val), (mem_orbitFinset_iff_transpose C A.val).mp A.property⟩
  invFun A := ⟨(Matrix.transpose A.val), (mem_orbitFinset_iff_transpose C (Matrix.transpose A.val)).mpr
    (by simpa only [Matrix.transpose_transpose] using A.property)⟩
  left_inv A := by apply Subtype.ext; rfl
  right_inv A := by simp

theorem card_orbitFinset_eq_slOrbit (C : Fin 3 → Fin 3 → ZMod h) :
    (orbitFinset (MainGroup h) C).card =
      Nat.card (Section04Orbit.slOrbit (Matrix.transpose C)) := by
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using
    (Nat.card_congr (orbitTransposeEquiv C))

theorem orbitFinset_lower_bound {p k : ℕ} [NeZero (p ^ k)] (hp : p.Prime) (hk : 0 < k)
    (C : Fin 3 → Fin 3 → ZMod (p ^ k))
    (d : PrimePowerData p k (Matrix.transpose C)) :
    (21 / 64 : ℝ) * ((p ^ k : ℕ) : ℝ) ^ 8 /
      (((p ^ d.b : ℕ) : ℝ) ^ 3 * ((p ^ d.e : ℕ) : ℝ) ^ 2) ≤
        ((orbitFinset (MainGroup (p ^ k)) C).card : ℝ) := by
  rw [card_orbitFinset_eq_slOrbit]
  exact d.orbit_lower_bound hp hk

end Problem355.OrbitSampling

end

end OAI
