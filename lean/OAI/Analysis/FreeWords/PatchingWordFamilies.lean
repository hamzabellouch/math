import Mathlib
import OAI.Analysis.FreeWords.PartialWords

namespace OAI

noncomputable section

namespace KKLocalPatching.PatchingWord

noncomputable section

open KKTraceTransfer KKFreeLiftFrontier

variable {A : Type*} [Ring A]

def Admissible (X : Set A) (K : Set ℤ) (N : ℕ) (w : PatchingWord A) : Prop :=
  w.left∈insert 1 X ∧ w.first∈K ∧ w.right∈insert 1 X ∧
    (∀ z∈w.middle, z.1∈X ∧ z.2∈K) ∧ w.length≤N

theorem admissible_finite {X : Set A} {K : Set ℤ} (hX : X.Finite) (hK : K.Finite) (N : ℕ) :
    {w | Admissible X K N w}.Finite := by
  classical
  let := hX.fintype
  let := hK.fintype
  let E : Set A := insert 1 X
  let : Fintype ↥E := (hX.insert 1).fintype
  let S := {l : List (↥X × ↥K) | l.length≤N}
  have hS : S.Finite := List.finite_length_le _ N
  let := hS.fintype
  let f (a : ↥E × ↥K × ↥S × ↥E) : PatchingWord A :=
    ⟨a.1.val,a.2.1.val,a.2.2.1.val.map (fun z => (z.1.val,z.2.val)),a.2.2.2.val⟩
  have hfin : (Set.range f).Finite := Set.finite_range f
  apply hfin.subset
  intro w hw
  rcases hw with ⟨hl,hk,hr,hm,hn⟩
  let l : List (↥X × ↥K) := w.middle.attach.map
    (fun z => (⟨z.val.1,(hm z.val z.property).1⟩,⟨z.val.2,(hm z.val z.property).2⟩))
  have hlen : l.length≤N := by
    simp only [l,List.length_map,List.length_attach]
    exact (Nat.le_add_left _ _).trans hn
  refine ⟨(⟨w.left,hl⟩,⟨w.first,hk⟩,⟨l,hlen⟩,⟨w.right,hr⟩),?_⟩
  have he : l.map (fun z => (z.1.val,z.2.val))=w.middle := by
    simp only [l,List.map_map,Function.comp_def]
    simp only [Prod.mk.eta, List.attach_map_subtype_val]
  cases w
  simp only [f,he]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {M : VonNeumannAlgebra H}

theorem norm_value_le_one (v : PartialUnitary (ConcreteAlgebra M))
    {X : Set (ConcreteAlgebra M)} {K : Set ℤ} {N : ℕ}
    (hX : ∀ x∈X, ‖x‖≤1) {w : PatchingWord (ConcreteAlgebra M)}
    (hw : Admissible X K N w) : ‖w.value v.power‖≤1 := by
  have hE : ∀ x∈insert (1:ConcreteAlgebra M) X, ‖x‖≤1 := by
    intro x hx
    rcases hx with rfl | hx
    · exact concrete_norm_one_le
    · exact hX x hx
  have htail : ∀ (s : List (ConcreteAlgebra M × ℤ)),
      (∀ z∈s, ‖z.1‖≤1) → ‖tailValue v.power s‖≤1 := by
    intro s
    induction s with
    | nil => intro _; exact concrete_norm_one_le
    | cons z s ih =>
      intro hs
      have hz : ‖z.1*v.power z.2‖≤1 := by
        calc
          _ ≤ ‖z.1‖*‖v.power z.2‖ := norm_mul_le _ _
          _ ≤ 1*1 := mul_le_mul (hs z List.mem_cons_self) (v.norm_power_le_one _)
            (norm_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      have ht := ih (fun a ha => hs a (List.mem_cons_of_mem _ ha))
      calc
        _ ≤ ‖z.1*v.power z.2‖*‖tailValue v.power s‖ := norm_mul_le _ _
        _ ≤ 1*1 := mul_le_mul hz ht (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
  have ht := htail w.middle (fun z hz => hX z.1 (hw.2.2.2.1 z hz).1)
  have hleft : ‖w.left*v.power w.first‖≤1 := by
    calc
      _ ≤ ‖w.left‖*‖v.power w.first‖ := norm_mul_le _ _
      _ ≤ 1*1 := mul_le_mul (hE _ hw.1) (v.norm_power_le_one _)
        (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hmid : ‖w.left*v.power w.first*tailValue v.power w.middle‖≤1 := by
    calc
      _ ≤ ‖w.left*v.power w.first‖*‖tailValue v.power w.middle‖ := norm_mul_le _ _
      _ ≤ 1*1 := mul_le_mul hleft ht (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  calc
    _ ≤ ‖w.left*v.power w.first*tailValue v.power w.middle‖*‖w.right‖ := norm_mul_le _ _
    _ ≤ 1*1 := mul_le_mul hmid (hE _ hw.2.2.1) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

end

end KKLocalPatching.PatchingWord
end

end OAI
