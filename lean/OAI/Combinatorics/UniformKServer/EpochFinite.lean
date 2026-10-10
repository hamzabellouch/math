import Mathlib
import OAI.Combinatorics.UniformKServer.EpochControl

namespace OAI

noncomputable section
                                  
section

namespace UniformKServer.EpochControl
open EpochShadow

def Bounded {n k : ℕ} (M : ℕ) (s : State n k) : Prop :=
  Good M (horizon k M) s.filter ∧ s.virtual.moves ≤ M+1 ∧
    (s.fallback=false → s.virtual.moves ≤ M)

theorem bounded_initial {n k : ℕ} (M : ℕ) (u : Configuration n k) :
    Bounded M (initial u) := by
  have hf := runFilter_good M u []
  rw [treeBudget_eq_horizon] at hf
  exact ⟨hf,Nat.zero_le _,fun _ => Nat.zero_le _⟩

theorem bounded_step {n k : ℕ} (hk : 0 < k) (M : ℕ) (T : Selector n k)
    (s : State n k) (r : Fin n) (hb : Bounded M s) :
    Bounded M (step hk M T s r) := by
  have hf := step_good M (horizon k M) s.filter r hb.1
  by_cases ht : s.fallback=true
  · simp only [step,ht,ite_true]
    exact ⟨hf,hb.2.1,by simp⟩
  · have ht' : s.fallback=false := Bool.eq_false_iff.mpr ht
    by_cases hc : ∀z ∈ s.filter.live,Covers z r
    · simp only [step,ht',Bool.false_eq_true,ite_false,ite_eq_left hc]
      exact ⟨hb.1,hb.2.1,fun _ => hb.2.2 ht'⟩
    · have hv := hb.2.2 ht'
      have hm : (nextEntry s.virtual r (T s.filter.kept s.virtual.position r)).moves ≤ M+1 := by
        simp only [nextEntry]
        split_ifs <;> omega
      simp only [step,ht',Bool.false_eq_true,ite_false,ite_eq_right hc]
      refine ⟨hf,hm,?_⟩
      intro hh
      have hnot : ¬ M < (nextEntry s.virtual r (T s.filter.kept s.virtual.position r)).moves :=
        of_decide_eq_false hh
      change (nextEntry s.virtual r (T s.filter.kept s.virtual.position r)).moves ≤ M
      omega

abbrev BList (A : Type*) (B : ℕ) := {l : List A // l.length ≤ B}
instance {A : Type*} [Finite A] (B : ℕ) : Finite (BList A B) :=
  (List.finite_length_le A B).to_subtype

abbrev Packed (n k M : ℕ) :=
  BList (Configuration n k × Fin (M+1)) (horizon k M) ×
  BList (Fin n) (horizon k M) × Fin (horizon k M+1) ×
  (Configuration n k × Fin (M+2)) × Finset (Fin k) × Finset (Fin n) × Bool

def pack {n k M : ℕ} (s : {s : State n k // Bounded M s}) : Packed n k M :=
  let hb := s.property
  (⟨s.val.filter.live.attach.map (fun e =>
        (e.val.position,⟨e.val.moves,Nat.lt_succ_of_le (hb.1.1 e.val e.property)⟩)),by
      simp only [List.length_map,List.length_attach]
      exact (length_le_mass M s.val.filter.live).trans (by have hh := hb.1.2.1; omega)⟩,
   ⟨s.val.filter.kept,by have hh := hb.1.2.1; omega⟩,
   ⟨s.val.filter.created,by have hh := hb.1.2.2; omega⟩,
   (s.val.virtual.position,⟨s.val.virtual.moves,by have hh := hb.2.1; omega⟩),
   s.val.marked,s.val.seen,s.val.fallback)

def unpack {n k M : ℕ} (p : Packed n k M) : State n k :=
  ⟨⟨p.1.val.map (fun e => ⟨e.1,e.2.val⟩),p.2.1.val,p.2.2.1.val⟩,
    ⟨p.2.2.2.1.1,p.2.2.2.1.2.val⟩,p.2.2.2.2.1,p.2.2.2.2.2.1,p.2.2.2.2.2.2⟩

theorem unpack_pack {n k M : ℕ} (s : {s : State n k // Bounded M s}) :
    unpack (pack s)=s.val := by
  have hl : ((s.val.filter.live.attach.map (fun e =>
      (e.val.position, (⟨e.val.moves,Nat.lt_succ_of_le (s.property.1.1 e.val e.property)⟩ : Fin (M+1))))).map
      (fun e => (⟨e.1,e.2.val⟩ : Entry n k))) = s.val.filter.live := by
    simp only [List.map_map]
    change s.val.filter.live.attach.map (fun e => e.val) = _
    simp
  simp only [pack,unpack,hl]

instance {n k M : ℕ} : Finite {s : State n k // Bounded M s} := by
  apply Finite.of_injective (@pack n k M)
  intro s t h
  apply Subtype.ext
  rw [←unpack_pack s,←unpack_pack t,h]

/-- A bounded-state one-epoch transducer. Neither its state bound nor its
transition function contains a raw word or a request horizon. -/
def boundedStep {n k : ℕ} (hk : 0 < k) (M : ℕ) (T : Selector n k)
    (s : {s : State n k // Bounded M s}) (r : Fin n) : {s : State n k // Bounded M s} :=
  ⟨step hk M T s.val r,bounded_step hk M T s.val r s.property⟩

end UniformKServer.EpochControl

end


end

end OAI
