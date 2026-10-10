import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.GraphAction
import OAI.Probability.CriticalPercolation.GraphGeometry.GraphBalls
import OAI.Probability.CriticalPercolation.Modular.RelativeModular

namespace OAI

section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def stabilizerOrbit (x y : V) : Set V :=
  MulAction.orbit (MulAction.stabilizer G.Aut x) y

lemma mem_stabilizerOrbit {x y z : V} : z ∈ G.stabilizerOrbit x y ↔
    ∃ φ : G.Aut, φ.vertex x = x ∧ φ.vertex y = z := by
  simp only [stabilizerOrbit, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨φ,hφ⟩
    exact ⟨φ,φ.property,hφ⟩
  · rintro ⟨φ,hx,hy⟩
    exact ⟨⟨φ,hx⟩,hy⟩

lemma self_mem_stabilizerOrbit (x y : V) : y ∈ G.stabilizerOrbit x y :=
  (G.mem_stabilizerOrbit).mpr ⟨1,rfl,rfl⟩

lemma stabilizerOrbit_finite (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (x y : V) : (G.stabilizerOrbit x y).Finite := by
  obtain ⟨n,hn⟩ := G.finite_subset_vertexBall hc x (Set.finite_singleton y)
  apply (G.vertexBall_finite hl x n).subset
  intro z hz
  obtain ⟨φ,hx,rfl⟩ := G.mem_stabilizerOrbit.mp hz
  rw [←hx]
  exact (Aut.vertexBall_mem G φ x y n).mpr (hn (Set.mem_singleton y))

def suborbitCard (x y : V) : ℕ := (G.stabilizerOrbit x y).ncard

lemma suborbitCard_pos (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (x y : V) : 0 < G.suborbitCard x y :=
  (Set.ncard_pos (G.stabilizerOrbit_finite hc hl x y)).mpr ⟨y,G.self_mem_stabilizerOrbit x y⟩

lemma suborbitCard_eq_relIndex (x y : V) : G.suborbitCard x y =
    (MulAction.stabilizer G.Aut y).relIndex (MulAction.stabilizer G.Aut x) := by
  have heq : (MulAction.stabilizer G.Aut y).subgroupOf (MulAction.stabilizer G.Aut x) =
      MulAction.stabilizer (MulAction.stabilizer G.Aut x) y := by
    ext φ
    rfl
  rw [Subgroup.relIndex,heq,MulAction.index_stabilizer]
  rfl

lemma Aut.stabilizerOrbit_image (φ : G.Aut) (x y : V) :
    φ.vertex '' G.stabilizerOrbit x y = G.stabilizerOrbit (φ.vertex x) (φ.vertex y) := by
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    obtain ⟨ψ,hx,hy⟩ := G.mem_stabilizerOrbit.mp hw
    apply G.mem_stabilizerOrbit.mpr
    refine ⟨φ * ψ * φ⁻¹,?_,?_⟩
    · change φ.vertex (ψ.vertex (φ.vertex.symm (φ.vertex x))) = φ.vertex x
      rw [Equiv.symm_apply_apply,hx]
    · change φ.vertex (ψ.vertex (φ.vertex.symm (φ.vertex y))) = φ.vertex w
      rw [Equiv.symm_apply_apply,hy]
  · intro hz
    obtain ⟨ψ,hx,hy⟩ := G.mem_stabilizerOrbit.mp hz
    refine ⟨φ.vertex.symm z,?_,φ.vertex.apply_symm_apply z⟩
    apply G.mem_stabilizerOrbit.mpr
    refine ⟨φ⁻¹ * ψ * φ,?_,?_⟩
    · change φ.vertex.symm (ψ.vertex (φ.vertex x)) = x
      rw [hx,Equiv.symm_apply_apply]
    · change φ.vertex.symm (ψ.vertex (φ.vertex y)) = φ.vertex.symm z
      rw [hy]

lemma Aut.suborbitCard (φ : G.Aut) (x y : V) :
    G.suborbitCard (φ.vertex x) (φ.vertex y) = G.suborbitCard x y := by
  rw [CriticalPercolation.BondGraph.suborbitCard,←Aut.stabilizerOrbit_image G φ,
      Set.ncard_image_of_injective _ φ.vertex.injective]
  rfl

def modularRatio (x y : V) : ℝ := (G.suborbitCard x y : ℝ) / (G.suborbitCard y x : ℝ)

lemma modularRatio_eq_relativeMass (x y : V) : G.modularRatio x y =
    Subgroup.relativeMass (MulAction.stabilizer G.Aut x) (MulAction.stabilizer G.Aut y) := by
  simp only [modularRatio,suborbitCard_eq_relIndex,Subgroup.relativeMass]

lemma modularRatio_pos (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (x y : V) :
    0 < G.modularRatio x y :=
  div_pos (Nat.cast_pos.mpr (G.suborbitCard_pos hc hl x y))
    (Nat.cast_pos.mpr (G.suborbitCard_pos hc hl y x))

lemma modularRatio_cocycle (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (x y z : V) : G.modularRatio x y * G.modularRatio y z = G.modularRatio x z := by
  simp only [modularRatio_eq_relativeMass]
  apply Subgroup.relativeMass_cocycle
  all_goals
    rw [←suborbitCard_eq_relIndex]
    exact ne_of_gt (G.suborbitCard_pos hc hl _ _)

lemma modularRatio_self (x : V) : G.modularRatio x x = 1 := by
  rw [modularRatio_eq_relativeMass,Subgroup.relativeMass_self]

lemma Aut.modularRatio (φ : G.Aut) (x y : V) :
    G.modularRatio (φ.vertex x) (φ.vertex y) = G.modularRatio x y := by
  simp only [CriticalPercolation.BondGraph.modularRatio,Aut.suborbitCard]

def CombinatoriallyUnimodular : Prop :=
  ∀ (φ : G.Aut) x, G.suborbitCard x (φ.vertex x) = G.suborbitCard (φ.vertex x) x

lemma CombinatoriallyUnimodular.modularRatio (hu : G.CombinatoriallyUnimodular)
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (φ : G.Aut) (x : V) :
    G.modularRatio x (φ.vertex x) = 1 := by
  simp only [CriticalPercolation.BondGraph.modularRatio,hu φ x,
    div_self (ne_of_gt (Nat.cast_pos.mpr (G.suborbitCard_pos hc hl (φ.vertex x) x)) :
      (G.suborbitCard (φ.vertex x) x : ℝ) ≠ 0)]

lemma CombinatoriallyUnimodular.rootWeight_invariant (hu : G.CombinatoriallyUnimodular)
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (o : V) (φ : G.Aut) (x : V) :
    G.modularRatio o (φ.vertex x) = G.modularRatio o x := by
  rw [← G.modularRatio_cocycle hc hl o (φ.vertex o) (φ.vertex x),
    CombinatoriallyUnimodular.modularRatio G hu hc hl φ o,one_mul,Aut.modularRatio]

lemma modularRatio_card_balance (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o x y : V) : G.modularRatio o x * (G.suborbitCard x y : ℝ) =
      G.modularRatio o y * (G.suborbitCard y x : ℝ) := by
  have hh := G.modularRatio_cocycle hc hl o x y
  unfold modularRatio at hh
  rw [← mul_div_assoc] at hh
  exact (div_eq_iff (ne_of_gt (Nat.cast_pos.mpr (G.suborbitCard_pos hc hl y x)))).mp hh

end CriticalPercolation.BondGraph
end
end

end OAI
