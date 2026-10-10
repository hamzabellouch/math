import Mathlib
import OAI.Combinatorics.SharpRamsey.Windows.PreparedWindows
import OAI.Combinatorics.SharpRamsey.Selection.BandCharges

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators
noncomputable section
variable {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β]

lemma pairInformation_symm (p : Law (ι→β)) (i j : ι) :
    pairInformation p i j=pairInformation p j i := by
  apply Subtype.ext
  change mutualInfo (p.map (fun x=>(x i,x j)))=mutualInfo (p.map (fun x=>(x j,x i)))
  have he : p.map (fun x=>(x j,x i))=(p.map (fun x=>(x i,x j))).swap := by
    rw [Law.swap_eq_map,Law.map_map]
    rfl
  rw [he]
  simp only [mutualInfo,Law.swap_fst,Law.swap_snd,entropy_swap,add_comm]

variable {A B K V : Type} [Fintype A] [Fintype B] [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

omit [FiniteDimensional K V] in
lemma reciprocalCharges_symm (p : Law (ι→A×B)) (v : B→V) (w : A→Module.Dual K V)
    (ρ : ℝ) (r s : ℕ) (i j : ι) :
    reciprocalCharges p v w ρ r s i j=reciprocalCharges p v w ρ r s j i :=
  add_comm _ _

variable {C X : Type} [Fintype C]

lemma good_charge_reversed (p : Law (ι→β)) (e : C×X↪ι) (own : ι→Option C)
    (c : ι→ι→NNReal) (hc : ∀ i j,c i j=c j i) (J D a : ℝ) (f : C→X)
    (i j : ι) (hi : i∉badIndices p e own c J D a f)
    (hj : j∈otherRepresentatives e own f i) :
    (pairInformation p j i:ℝ)+(c j i:ℝ)≤a := by
  rw [pairInformation_symm p j i,hc j i]
  exact ((not_badIndices p e own c J D a f i).mp hi).2 j hj

lemma good_charge_either (p : Law (ι→β)) (e : C×X↪ι) (own : ι→Option C)
    (c : ι→ι→NNReal) (hc : ∀ i j,c i j=c j i) (J D a : ℝ) (f : C→X)
    (i j : ι)
    (h : (i∉badIndices p e own c J D a f ∧ j∈otherRepresentatives e own f i) ∨
      (j∉badIndices p e own c J D a f ∧ i∈otherRepresentatives e own f j)) :
    (pairInformation p i j:ℝ)+(c i j:ℝ)≤a := by
  rcases h with h|h
  · exact ((not_badIndices p e own c J D a f i).mp h.1).2 j h.2
  · exact good_charge_reversed p e own c hc J D a f j i h.1 h.2

end
end SharpLogRamsey.Selection

end

end OAI
