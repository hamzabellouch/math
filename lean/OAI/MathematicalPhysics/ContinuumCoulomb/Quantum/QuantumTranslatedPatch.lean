import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingPatch
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPatchSeparation

namespace OAI

/-! Translating the fixed crossing patch to every isolated route crossing. -/

namespace ContinuumCoulomb

def qmaPatchTranslate (p z : ℕ × ℕ) : ℕ × ℕ := (32*p.1+10+z.1,32*p.2+10+z.2)

theorem qmaPatchTranslate_injective (p : ℕ × ℕ) : Function.Injective (qmaPatchTranslate p) := by
  intro x y h
  apply Prod.ext
  · exact Nat.add_left_cancel (congrArg Prod.fst h)
  · exact Nat.add_left_cancel (congrArg Prod.snd h)

theorem qmaPatchTranslate_distance (p x y : ℕ × ℕ) :
    Nat.dist (qmaPatchTranslate p x).1 (qmaPatchTranslate p y).1+
      Nat.dist (qmaPatchTranslate p x).2 (qmaPatchTranslate p y).2 =
        Nat.dist x.1 y.1+Nat.dist x.2 y.2 := by
  simp only [qmaPatchTranslate,Nat.dist_add_add_left]

theorem qmaPatchTranslate_mem {p z : ℕ × ℕ} (hx : z.1 ≤ 12) (hy : z.2 ≤ 12) :
    qmaPatchTranslate p z ∈ qmaPatchBox p := by
  unfold qmaPatchBox qmaPatchTranslate qmaExpandedPoint Nat.dist
  simp only [Set.mem_ofPred_eq]
  omega

theorem qmaPatchTranslate_ne {p q x y : ℕ × ℕ} (hpq : p ≠ q)
    (hx : x.1 ≤ 12 ∧ x.2 ≤ 12) (hy : y.1 ≤ 12 ∧ y.2 ≤ 12) :
    qmaPatchTranslate p x ≠ qmaPatchTranslate q y := by
  intro he
  have h1 := qmaPatchTranslate_mem (p := p) hx.1 hx.2
  have h2 := qmaPatchTranslate_mem (p := q) hy.1 hy.2
  rw [← he] at h2
  exact Set.disjoint_left.mp (qmaPatchBox_disjoint hpq) h1 h2

def qmaCrossingPathAt (p : ℕ × ℕ) (e : Fin 9) : List (ℕ × ℕ) :=
  (qmaCrossingPatchPath e).map (qmaPatchTranslate p)

theorem qmaCrossingPathAt_chain (p : ℕ × ℕ) (e : Fin 9) :
    (qmaCrossingPathAt p e).IsChain
      (fun x y => Nat.dist x.1 y.1+Nat.dist x.2 y.2 = 1) := by
  apply List.isChain_map_of_isChain (qmaPatchTranslate p) _ (qmaCrossingPatch_chain e)
  intro x y h
  simpa only [qmaPatchTranslate_distance] using h

theorem qmaCrossingPathAt_simple (p : ℕ × ℕ) (e : Fin 9) : (qmaCrossingPathAt p e).Nodup :=
  (qmaCrossingPatch_simple e).map (qmaPatchTranslate_injective p)

theorem qmaCrossingPathAt_mem (p : ℕ × ℕ) (e : Fin 9) {z : ℕ × ℕ}
    (hz : z ∈ qmaCrossingPathAt p e) : z ∈ qmaPatchBox p := by
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hz
  exact qmaPatchTranslate_mem (qmaCrossingPatch_bounded e w hw).1 (qmaCrossingPatch_bounded e w hw).2

theorem qmaCrossingPathAt_disjoint {p q : ℕ × ℕ} (hpq : p ≠ q) (e f : Fin 9) :
    Disjoint (qmaCrossingPathAt p e).toFinset (qmaCrossingPathAt q f).toFinset := by
  apply Finset.disjoint_left.mpr
  intro z hz hq
  exact Set.disjoint_left.mp (qmaPatchBox_disjoint hpq)
    (qmaCrossingPathAt_mem p e (List.mem_toFinset.mp hz))
    (qmaCrossingPathAt_mem q f (List.mem_toFinset.mp hq))

def qmaCrossingPortAt (p : ℕ × ℕ) : Fin 4 → ℕ × ℕ :=
  ![(32*p.1+9,32*p.2+16),(32*p.1+16,32*p.2+23),
    (32*p.1+23,32*p.2+16),(32*p.1+16,32*p.2+9)]

theorem qmaCrossingPortAt_step (p : ℕ × ℕ) (a : Fin 4) :
    Nat.dist (qmaCrossingPortAt p a).1 (qmaPatchTranslate p (qmaCrossingPatchVertex (a.castLE (by decide)))).1+
      Nat.dist (qmaCrossingPortAt p a).2 (qmaPatchTranslate p (qmaCrossingPatchVertex (a.castLE (by decide)))).2 = 1 := by
  fin_cases a <;> norm_num [qmaCrossingPortAt,qmaPatchTranslate,qmaCrossingPatchVertex,
    Nat.add_assoc,Nat.dist_add_add_left]
  all_goals decide

theorem qmaCrossingPortAt_outside (p : ℕ × ℕ) (a : Fin 4) :
    qmaCrossingPortAt p a ∉ qmaPatchBox p := by
  fin_cases a <;> norm_num [qmaCrossingPortAt,qmaPatchBox,qmaExpandedPoint,Nat.dist_add_add_left]
  all_goals decide

end ContinuumCoulomb

end OAI
