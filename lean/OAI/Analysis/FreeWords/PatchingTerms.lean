import Mathlib
import OAI.Analysis.FreeWords.ColoredSplit
import OAI.Analysis.FreeWords.PatchingGapWords

namespace OAI

noncomputable section

namespace KKLocalPatching

open KKTraceTransfer KKFreeLiftFrontier KKUltraTrace KKProjectionSupport KKMatrixQuantization

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {M : VonNeumannAlgebra H}

abbrev PatchingTerms (W : Set (PatchingWord (ConcreteAlgebra M))) :=
  Σ w : W, {c : List (Colored.Cell (ConcreteAlgebra M)) // c∈Colored.changes w.val.raw}

instance termsFintype (W : Set (PatchingWord (ConcreteAlgebra M))) [Fintype W] : Fintype (PatchingTerms W) := by
  letI (w:W) : Fintype {c : List (Colored.Cell (ConcreteAlgebra M)) // c∈Colored.changes w.val.raw} :=
    (List.finite_toSet _).fintype
  infer_instance

namespace PatchingTerms

variable {W : Set (PatchingWord (ConcreteAlgebra M))}

def split (t : PatchingTerms W) : Colored.Split t.2.val := Colored.split t.2.property

theorem exponent_ne_zero {X : Set (ConcreteAlgebra M)} {K : Set ℤ} {N : ℕ}
    (hK : ∀ k∈K, k≠0) (hW : ∀ w∈W, PatchingWord.Admissible X K N w)
    (t : PatchingTerms W) : t.split.exponent≠0 := by
  cases he : t.split with
  | single p z s h =>
    change z.2≠0
    have hraw : t.1.val.raw=p++z::s := by
      rw [← Colored.erase_of_mem_changes t.2.property,h]
      simp [Colored.erase,Colored.old,List.map_map,Function.comp_def]
    have hz : z∈t.1.val.raw := by rw [hraw]; exact List.mem_append_right _ List.mem_cons_self
    have hw := hW t.1.val t.1.property
    rcases List.mem_cons.mp hz with hz | hz
    · rw [hz]; exact hK _ hw.2.1
    · exact hK _ (hw.2.2.2.1 z hz).2
  | multiple p z g y r h => exact one_ne_zero

theorem gap_bounds (τ : FaithfulNormalTrace M)
    {X : Set (ConcreteAlgebra M)} {K : Set ℤ} {N : ℕ}
    (hX : ∀ x∈X, τ.map x=0) (hK1 : 1∈K) (hKm1 : -1∈K)
    (hW : ∀ w∈W, PatchingWord.Admissible X K N w)
    (v : PartialUnitary (ConcreteAlgebra M)) {b : ℝ} (hb : 0≤b)
    (hv : ∀ a, PatchingWord.Admissible X K N a → ‖τ.map (a.value v.power)‖≤b)
    (t : PatchingTerms W) :
    ‖τ.map (t.split.gap v.power)‖≤b ∧ ‖τ.map (v.support*t.split.gap v.power)‖≤b := by
  cases he : t.split with
  | single p z s h => simpa only [Colored.Split.gap,mul_zero,map_zero,norm_zero] using And.intro hb hb
  | multiple p z g y r h =>
    have hraw : t.1.val.raw=p++z::(g++y::Colored.erase r) := by
      rw [← Colored.erase_of_mem_changes t.2.property,h]
      simp [Colored.erase,Colored.old,List.map_map,Function.comp_def]
    exact PatchingWord.gap_and_endpoint_bounds τ hX hK1 hKm1 v hb hv
      (hW _ t.1.property) p g (Colored.erase r) z y hraw

end PatchingTerms

end

end KKLocalPatching
end

end OAI
