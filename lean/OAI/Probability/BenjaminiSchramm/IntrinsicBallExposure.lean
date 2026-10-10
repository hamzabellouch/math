import OAI.Probability.BenjaminiSchramm.IntrinsicBallGrowth
import OAI.Probability.BenjaminiSchramm.BlockExposure

namespace OAI

open MeasureTheory

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

def ballIncidentEdges (G : BondGraph V E) (B : Set V) : Set E :=
  {e | ∃ a ∈ B, a ∈ G e}

theorem intrinsicBall_mono_radius (G : BondGraph V E) (ω : Set E) (x : V)
    {m n : ℕ} (hmn : m ≤ n) : intrinsicBall G ω x m ⊆ intrinsicBall G ω x n := by
  rintro y ⟨l,hl,hlen,ho⟩
  exact ⟨l,hl,hlen.trans hmn,ho⟩

theorem along_open_of_agree_intrinsic_prefix (G : BondGraph V E)
    (ω η : Set E) (x y : V) (n : ℕ) (l : List E) (hl : Along G x l y)
    (hlen : l.length ≤ n) (ho : ∀ e ∈ l, e ∈ η)
    (hagree : ∀ e ∈ ballIncidentEdges G (intrinsicBall G ω x (n-1)), e ∈ ω ↔ e ∈ η) :
    ∀ e ∈ l, e ∈ ω := by
  rcases hl.first_outside ω with h | ⟨a,b,e,l₁,l₂,heq,h₁,he,_,hprefix,hnot⟩
  · exact h
  · exfalso
    have hlength : l₁.length ≤ n-1 := by
      rw [heq,List.length_append,List.length_cons] at hlen
      omega
    have ha : a ∈ intrinsicBall G ω x (n-1) := ⟨l₁,h₁,hlength,hprefix⟩
    have hei : e ∈ ballIncidentEdges G (intrinsicBall G ω x (n-1)) :=
      ⟨a,ha,by simp [he]⟩
    exact hnot ((hagree e hei).mpr (ho e (by rw [heq]; simp)))

theorem along_bonds_incident_intrinsic_prefix (G : BondGraph V E)
    (ω : Set E) (x y : V) (n : ℕ) (l : List E) (hl : Along G x l y)
    (hlen : l.length ≤ n) (ho : ∀ e ∈ l, e ∈ ω) :
    ∀ e ∈ l, e ∈ ballIncidentEdges G (intrinsicBall G ω x (n-1)) := by
  rcases hl.first_outside (ballIncidentEdges G (intrinsicBall G ω x (n-1))) with
    h | ⟨a,b,e,l₁,l₂,heq,h₁,he,_,_,hnot⟩
  · exact h
  · exfalso
    have hlength : l₁.length ≤ n-1 := by
      rw [heq,List.length_append,List.length_cons] at hlen
      omega
    have ha : a ∈ intrinsicBall G ω x (n-1) := ⟨l₁,h₁,hlength,fun f hf => ho f (by rw [heq]; simp [hf])⟩
    exact hnot ⟨a,ha,by simp [he]⟩

theorem intrinsicBall_eq_of_incident_agreement (G : BondGraph V E)
    (ω η : Set E) (x : V) (n : ℕ)
    (hagree : ∀ e ∈ ballIncidentEdges G (intrinsicBall G ω x (n-1)), e ∈ ω ↔ e ∈ η) :
    intrinsicBall G ω x n = intrinsicBall G η x n := by
  apply Set.Subset.antisymm
  · rintro y ⟨l,hl,hlen,ho⟩
    exact ⟨l,hl,hlen,fun e he => (hagree e
      (along_bonds_incident_intrinsic_prefix G ω x y n l hl hlen ho e he)).mp (ho e he)⟩
  · rintro y ⟨l,hl,hlen,ho⟩
    exact ⟨l,hl,hlen,along_open_of_agree_intrinsic_prefix G ω η x y n l hl hlen ho hagree⟩

theorem intrinsicBall_history_eq_of_incident_agreement (G : BondGraph V E)
    (ω η : Set E) (x : V) (n : ℕ)
    (hagree : ∀ e ∈ ballIncidentEdges G (intrinsicBall G ω x (n-1)), e ∈ ω ↔ e ∈ η) :
    ∀ i ≤ n, intrinsicBall G ω x i = intrinsicBall G η x i := by
  intro i hi
  apply intrinsicBall_eq_of_incident_agreement G ω η x i
  rintro e ⟨a,ha,he⟩
  exact hagree e ⟨a,intrinsicBall_mono_radius G ω x (by omega) ha,he⟩

theorem measurableSet_intrinsicBall_eq [Countable V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (S : Set E) (x : V) (n : ℕ) (B : Set V) :
    MeasurableSet {ω | intrinsicBall G (ω ∩ S) x n = B} := by
  have he : {ω | intrinsicBall G (ω ∩ S) x n = B} =
      ⋂ y : V, {ω | y ∈ intrinsicBall G (ω ∩ S) x n ↔ y ∈ B} := by
    ext ω
    simp only [Set.mem_ofPred_eq,Set.mem_iInter]
    exact Set.ext_iff
  rw [he]
  exact MeasurableSet.iInter (fun y =>
    ((measurableSet_mem_intrinsicBall_domain G hloc S x y n).mem.iff measurable_const).setOf)

end Percolation.BenjaminiSchramm

end OAI
