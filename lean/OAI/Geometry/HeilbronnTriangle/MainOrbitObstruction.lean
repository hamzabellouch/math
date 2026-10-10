import OAI.Geometry.HeilbronnTriangle.MainResidueSystem
import OAI.Geometry.HeilbronnTriangle.OrbitSampling
import OAI.Geometry.HeilbronnTriangle.LiftedBadEvent

namespace OAI


noncomputable section

namespace Problem355.MainOrbitObstruction

open OrbitSampling

def columnResidue (h : ℕ) (A : Matrix (Fin 3) (Fin 3) ℤ) :
    Fin 3 → Fin 3 → ZMod h := fun j i => (A i j : ZMod h)

lemma reduction_of_mem_orbit (h : ℕ) [NeZero h]
    (C : Fin 3 → Fin 3 → ZMod h) (A : Matrix (Fin 3) (Fin 3) ℤ)
    (hA : columnResidue h A ∈ orbitFinset (MainGroup h) C) :
    ∃ G : MainGroup h, A.map (Int.castRingHom (ZMod h)) =
      G.val * Matrix.transpose C := by
  obtain ⟨G, hG⟩ := (mem_orbitFinset C _).mp hA
  refine ⟨G, ?_⟩
  change Matrix.transpose (columnResidue h A) = G.val * Matrix.transpose C
  rw [← hG, sl_action_transpose]

def encodedColumns (h B : ℕ) (d : Fin 3 → Fin 3 → ℕ → ℤ) :
    Fin 3 → Fin 3 → ZMod h :=
  fun j i => ((∑ v ∈ Finset.range heilbronnK, d i j v * (B : ℤ) ^ v : ℤ) : ZMod h)

variable (p : ℕ) [Fact p.Prime]

theorem small_det_forces_repeated_labels_of_mem_orbit (hp : 2 < p)
    (B : ℕ) (L : ℤ) (hB : 2 ≤ B) (hL : 0 ≤ L)
    (hbase : 100 * (heilbronnK : ℤ) ^ 2 * L ^ 3 < B)
    (labels : Fin 3 → FiniteFieldLabels.Label p)
    (d : Fin 3 → Fin 3 → ℕ → ℤ)
    (hd : ∀ i j v, v < heilbronnK → |d i j v| ≤ L)
    (hresidue : ∀ i j v, v < heilbronnK →
      (Int.castRingHom (ZMod p)) (d i j v) =
        MainResidueSystem.prescribedResidue p i v (labels j))
    (h : ℕ) [NeZero h] (hh : h = B ^ heilbronnK)
    (A : Matrix (Fin 3) (Fin 3) ℤ)
    (hA : columnResidue h A ∈ orbitFinset (MainGroup h) (encodedColumns h B d))
    (hsmall : |A.det| ≤ (B : ℤ) ^ (heilbronnK - 1) / 2) :
    ∃ i j : Fin 3, i ≠ j ∧ labels i = labels j := by
  obtain ⟨G, hG⟩ := reduction_of_mem_orbit h (encodedColumns h B d) A hA
  exact MainResidueSystem.small_det_forces_repeated_labels p hp B L hB hL hbase
    labels d hd hresidue A h hh G hG hsmall

theorem det_abs_gt_of_injective_labels (hp : 2 < p)
    (B : ℕ) (L : ℤ) (hB : 2 ≤ B) (hL : 0 ≤ L)
    (hbase : 100 * (heilbronnK : ℤ) ^ 2 * L ^ 3 < B)
    (labels : Fin 3 → FiniteFieldLabels.Label p) (hinj : Function.Injective labels)
    (d : Fin 3 → Fin 3 → ℕ → ℤ)
    (hd : ∀ i j v, v < heilbronnK → |d i j v| ≤ L)
    (hresidue : ∀ i j v, v < heilbronnK →
      (Int.castRingHom (ZMod p)) (d i j v) =
        MainResidueSystem.prescribedResidue p i v (labels j))
    (h : ℕ) [NeZero h] (hh : h = B ^ heilbronnK)
    (A : Matrix (Fin 3) (Fin 3) ℤ)
    (hA : columnResidue h A ∈ orbitFinset (MainGroup h) (encodedColumns h B d)) :
    (B : ℤ) ^ (heilbronnK - 1) / 2 < |A.det| := by
  by_contra hn
  obtain ⟨i, j, hij, heq⟩ := small_det_forces_repeated_labels_of_mem_orbit p hp
    B L hB hL hbase labels d hd hresidue h hh A hA (le_of_not_gt hn)
  exact hij (hinj heq)

theorem lifted_small_event_eq_zero_of_injective_labels
    {X Ω Y : Type*} [DecidableEq X] [Fintype Ω]
    (hp : 2 < p) (B : ℕ) (L : ℤ) (hB : 2 ≤ B) (hL : 0 ≤ L)
    (hbase : 100 * (heilbronnK : ℤ) ^ 2 * L ^ 3 < B)
    (labels : Fin 3 → FiniteFieldLabels.Label p) (hinj : Function.Injective labels)
    (d : Fin 3 → Fin 3 → ℕ → ℤ)
    (hd : ∀ i j v, v < heilbronnK → |d i j v| ≤ L)
    (hresidue : ∀ i j v, v < heilbronnK →
      (Int.castRingHom (ZMod p)) (d i j v) =
        MainResidueSystem.prescribedResidue p i v (labels j))
    (h : ℕ) [NeZero h] (hh : h = B ^ heilbronnK)
    (A : X → Matrix (Fin 3) (Fin 3) ℤ) (g : X → Fin 3 → Y)
    (w : Ω → ℝ) (V : Ω → Finset Y) (s M : ℕ) (S : Finset X)
    (τ : ℤ) (hτ : τ ≤ (B : ℤ) ^ (heilbronnK - 1) / 2) :
    (∑ x ∈ S.filter (fun x => |(A x).det| ≤ τ),
      LiftingProbability.liftedMass (fun x => columnResidue h (A x)) g
        (orbitFinset (MainGroup h) (encodedColumns h B d)) w V s M x) = 0 := by
  apply LiftingProbability.lifted_small_event_eq_zero
  intro x _ hx
  exact hτ.trans_lt (det_abs_gt_of_injective_labels p hp B L hB hL hbase
    labels hinj d hd hresidue h hh (A x) hx)

end Problem355.MainOrbitObstruction

end

end OAI
