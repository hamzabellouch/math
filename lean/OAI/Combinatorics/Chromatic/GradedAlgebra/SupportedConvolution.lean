import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.WeightedTorusSeries
import OAI.Combinatorics.Chromatic.Shuffle.SymmetricSpace

namespace OAI

section
namespace ElementaryPositivity.WeightedTorusSeries
open ElementaryPositivity.RawShuffle
noncomputable section
attribute [local instance] Classical.propDecidable
variable {I R M : Type*} [Fintype I] [DecidableEq I] [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (P : (I → ℕ) →+ M)

def Supported (S : Finset I) (d : I → ℕ) : Prop := ∀i,i∉S → d i=0

def restrictDim (S : Finset I) (d : I → ℕ) : I → ℕ := fun i=>if i∈S then d i else 0

omit [Fintype I] in
lemma restrictDim_supported (S : Finset I) (d : I → ℕ) : Supported S (restrictDim S d) := by
  intro i hi
  simp [restrictDim,hi]

omit [Fintype I] in
lemma restrictDim_eq (S : Finset I) (d : I → ℕ) (hd : Supported S d) : restrictDim S d=d := by
  funext i
  by_cases hi : i∈S <;> simp [restrictDim,hi,hd i]

omit [Fintype I] in
lemma supported_add (S T : Finset I) (d e : I → ℕ) (hd : Supported S d) (he : Supported T e) :
    Supported (S∪T) (d+e) := by
  intro i hi
  have H : i∉S ∧ i∉T := by simpa only [Finset.mem_union,not_or] using hi
  simp [hd i H.1,he i H.2]

omit [Fintype I] in
lemma restrictDim_split (S T : Finset I) (hST : Disjoint S T) (d : I → ℕ)
    (hd : Supported (S∪T) d) : restrictDim S d+restrictDim T d=d := by
  funext i
  by_cases hS : i∈S
  · have hT : i∉T := fun hi=>Finset.disjoint_left.mp hST hS hi
    simp [restrictDim,hS,hT]
  · by_cases hT : i∈T
    · simp [restrictDim,hS,hT]
    · simp [restrictDim,hS,hT,hd i (by simp [hS,hT])]

omit [Fintype I] in
lemma split_left_restrict (S T : Finset I) (hST : Disjoint S T) (d : I → ℕ)
    (s : DimensionSplit d) (hs : Supported S s.left) (ht : Supported T s.right) :
    s.left=restrictDim S d := by
  funext i
  by_cases hS : i∈S
  · have hT : i∉T := fun hi=>Finset.disjoint_left.mp hST hS hi
    have H:=congrFun (DimensionSplit.left_add_right s) i
    simp only [Pi.add_apply,ht i hT,add_zero] at H
    simp [restrictDim,hS,H]
  · simp [restrictDim,hS,hs i hS]

def supportedCoefficient (S : Finset I) (f : (I → ℕ) → R) (d : I → ℕ) : R := by
  classical
  exact if Supported S d then f d else 0

lemma supported_convolution (S T : Finset I) (hST : Disjoint S T)
    (f g : (I → ℕ) → R) (d : I → ℕ) :
    convolution v Ω P (supportedCoefficient S f) (supportedCoefficient T g) d=
      if Supported (S∪T) d then
        f (restrictDim S d)*g (restrictDim T d)*↑(v^(Ω (P (restrictDim S d)) (P (restrictDim T d))))
      else 0 := by
  classical
  unfold convolution
  by_cases hd : Supported (S∪T) d
  · rw [ite_eq_left hd]
    let s₀:=DimensionSplit.ofPair (restrictDim S d) (restrictDim T d) (restrictDim_split S T hST d hd)
    rw [Finset.sum_eq_single s₀]
    · simp [s₀,supportedCoefficient,restrictDim_supported]
    · intro s hs hne
      by_cases hS : Supported S s.left
      · by_cases hT : Supported T s.right
        · exact (hne (DimensionSplit.ext (split_left_restrict S T hST d s hS hT))).elim
        · simp [supportedCoefficient,hT]
      · simp [supportedCoefficient,hS]
    · simp
  · rw [ite_eq_right hd]
    apply Finset.sum_eq_zero
    intro s hs
    by_cases hS : Supported S s.left
    · have hT : ¬Supported T s.right := by
        intro hT
        have H:=supported_add S T s.left s.right hS hT
        rw [DimensionSplit.left_add_right] at H
        exact hd H
      simp [supportedCoefficient,hT]
    · simp [supportedCoefficient,hS]

end
end ElementaryPositivity.WeightedTorusSeries

end

end OAI
