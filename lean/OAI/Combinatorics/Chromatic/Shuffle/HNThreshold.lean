import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.PrimitiveBlockRows
import OAI.Combinatorics.Chromatic.Walls.ThresholdWords
import OAI.Combinatorics.Chromatic.GradedAlgebra.EnergyLaurentFinite

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open SlopeArithmetic
noncomputable section
attribute [local instance] Classical.propDecidable
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (κ : I → ℤ) (c η : I → ℝ) (hc : ∀i,0<c i)
  [Fact (∀ θ,SlopeEulerSymmetric a c η θ)]

abbrev HNWord := ThresholdWords.Word
  (fun b : RowBlock a c η hc=>b.1≠0) (fun b=>slope c η b.1)
abbrev HighHNWord (θ : ℝ) := ThresholdWords.High
  (fun b : RowBlock a c η hc=>b.1≠0) (fun b=>slope c η b.1) θ
abbrev LowHNWord (θ : ℝ) := ThresholdWords.Low
  (fun b : RowBlock a c η hc=>b.1≠0) (fun b=>slope c η b.1) θ

lemma hnOrdered_map_iff (l : List (RowBlock a c η hc)) :
    HNOrdered c η (l.map Sigma.fst) ↔
      (∀ b∈l,b.1≠0) ∧ l.Pairwise (fun b e=>slope c η e.1<slope c η b.1) := by
  simp only [HNOrdered,List.forall_mem_map,List.pairwise_map]

def hnWordEquiv (d : I → ℕ) : DecoratedHN a c η hc d ≃
    {w : HNWord a c η hc // decoratedDimension a c η hc w.val=d} where
  toFun l:=⟨⟨l.val,(hnOrdered_map_iff a c η hc l.val).mp l.property.2⟩,l.property.1⟩
  invFun w:=⟨w.val.val,⟨w.property,(hnOrdered_map_iff a c η hc w.val.val).mpr w.val.property⟩⟩
  left_inv _:=rfl
  right_inv _:=rfl

abbrev HighHNIndex (θ : ℝ) (d : I → ℕ) :=
  {w : HighHNWord a c η hc θ // decoratedDimension a c η hc w.val.val=d}
abbrev LowHNIndex (θ : ℝ) (d : I → ℕ) :=
  {w : LowHNWord a c η hc θ // decoratedDimension a c η hc w.val.val=d}

def splitHNWord (θ : ℝ) : HNWord a c η hc ≃ HighHNWord a c η hc θ × LowHNWord a c η hc θ :=
  ThresholdWords.splitEquiv _ _ θ

lemma splitHNWord_dimension (θ : ℝ) (w : HNWord a c η hc) :
    decoratedDimension a c η hc (splitHNWord a c η hc θ w).1.val.val+
    decoratedDimension a c η hc (splitHNWord a c η hc θ w).2.val.val=
    decoratedDimension a c η hc w.val := by
  rw [←decoratedDimension_append]
  exact congrArg (decoratedDimension a c η hc)
    (congrArg Subtype.val (ThresholdWords.merge_high_low _ _ θ w))

def thresholdIndexEquiv (θ : ℝ) (d : I → ℕ) : DecoratedHN a c η hc d ≃
    Σ s : DimensionSplit d,HighHNIndex a c η hc θ s.left × LowHNIndex a c η hc θ s.right :=
  (hnWordEquiv a c η hc d).trans
    (((splitHNWord a c η hc θ).subtypeEquiv (fun w=>by rw [splitHNWord_dimension])).trans
      (dimensionProduct (fun w : HighHNWord a c η hc θ=>decoratedDimension a c η hc w.val.val)
        (fun w : LowHNWord a c η hc θ=>decoratedDimension a c η hc w.val.val) d).symm)

lemma thresholdIndexEquiv_symm_energy (θ : ℝ) (d : I → ℕ)
    (z : Σ s : DimensionSplit d,HighHNIndex a c η hc θ s.left × LowHNIndex a c η hc θ s.right) :
    decoratedEnergy a κ c η hc ((thresholdIndexEquiv a c η hc θ d).symm z).val=
      decoratedEnergy a κ c η hc z.2.1.val.val.val+
        decoratedEnergy a κ c η hc z.2.2.val.val.val+
        (eulerForm a z.1.left z.1.right-eulerForm a z.1.right z.1.left) := by
  change decoratedEnergy a κ c η hc (z.2.1.val.val.val++z.2.2.val.val.val)=_
  rw [decoratedEnergy_append,z.2.1.property,z.2.2.property]

lemma thresholdIndexEquiv_energy (θ : ℝ) (d : I → ℕ) (w : DecoratedHN a c η hc d) :
    let z:=thresholdIndexEquiv a c η hc θ d w
    decoratedEnergy a κ c η hc z.2.1.val.val.val+
      decoratedEnergy a κ c η hc z.2.2.val.val.val+
      (eulerForm a z.1.left z.1.right-eulerForm a z.1.right z.1.left)=
        decoratedEnergy a κ c η hc w.val := by
  simpa only [Equiv.symm_apply_apply] using
    (thresholdIndexEquiv_symm_energy a κ c η hc θ d (thresholdIndexEquiv a c η hc θ d w)).symm

end
end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.EnergyLaurent
noncomputable section
lemma admissible_injective {A B : Type*} {e : A → ℤ} {f : B → ℤ}
    (he : Admissible e) (g : B → A) (hg : Function.Injective g)
    (hf : ∀b,e (g b)=f b) : Admissible f := by
  constructor
  · obtain ⟨K,hK⟩:=he.1
    exact ⟨K,fun b=>by rw [←hf]; exact hK (g b)⟩
  · intro E
    let := he.2 E
    exact Finite.of_injective (fun b : {b // f b=E}=>
      (⟨g b.val,by rw [hf,b.property]⟩ : {a // e a=E}))
      (fun x y H=>Subtype.ext (hg (congrArg Subtype.val H)))
end
end ElementaryPositivity.EnergyLaurent

namespace ElementaryPositivity.RawShuffle
open SlopeArithmetic EnergyLaurent
noncomputable section
attribute [local instance] Classical.propDecidable
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (κ : I → ℤ) (c η : I → ℝ) (hc : ∀i,0<c i)
  [Fact (∀ θ,SlopeEulerSymmetric a c η θ)]

abbrev highEnergy (θ : ℝ) (d : I → ℕ) (w : HighHNIndex a c η hc θ d) :=
  decoratedEnergy a κ c η hc w.val.val.val
abbrev lowEnergy (θ : ℝ) (d : I → ℕ) (w : LowHNIndex a c η hc θ d) :=
  decoratedEnergy a κ c η hc w.val.val.val

def highDecorated (θ : ℝ) (d : I → ℕ) (w : HighHNIndex a c η hc θ d) : DecoratedHN a c η hc d :=
  ⟨w.val.val.val,⟨w.property,(hnOrdered_map_iff a c η hc _).mpr w.val.val.property⟩⟩
def lowDecorated (θ : ℝ) (d : I → ℕ) (w : LowHNIndex a c η hc θ d) : DecoratedHN a c η hc d :=
  ⟨w.val.val.val,⟨w.property,(hnOrdered_map_iff a c η hc _).mpr w.val.val.property⟩⟩

lemma highEnergy_admissible (θ : ℝ) (d : I → ℕ) : Admissible (highEnergy a κ c η hc θ d) :=
  admissible_injective (decoratedEnergy_admissible a κ c η hc d) (highDecorated a c η hc θ d)
    (fun _ _ H=>Subtype.ext (Subtype.ext (Subtype.ext (congrArg (fun z : DecoratedHN a c η hc d=>z.val) H)))) (fun _=>rfl)
lemma lowEnergy_admissible (θ : ℝ) (d : I → ℕ) : Admissible (lowEnergy a κ c η hc θ d) :=
  admissible_injective (decoratedEnergy_admissible a κ c η hc d) (lowDecorated a c η hc θ d)
    (fun _ _ H=>Subtype.ext (Subtype.ext (Subtype.ext (congrArg (fun z : DecoratedHN a c η hc d=>z.val) H)))) (fun _=>rfl)

def highSeries (θ : ℝ) (d : I → ℕ) : LaurentSeries ℚ :=
  series (highEnergy a κ c η hc θ d) (highEnergy_admissible a κ c η hc θ d)
def lowSeries (θ : ℝ) (d : I → ℕ) : LaurentSeries ℚ :=
  series (lowEnergy a κ c η hc θ d) (lowEnergy_admissible a κ c η hc θ d)
def hnSeries (d : I → ℕ) : LaurentSeries ℚ :=
  series (fun w : DecoratedHN a c η hc d=>decoratedEnergy a κ c η hc w.val)
    (decoratedEnergy_admissible a κ c η hc d)

lemma hnSeries_threshold (θ : ℝ) (d : I → ℕ) :
    hnSeries a κ c η hc d = ∑s : DimensionSplit d,
      highSeries a κ c η hc θ s.left * lowSeries a κ c η hc θ s.right *
        HahnSeries.single (-(eulerForm a s.left s.right-eulerForm a s.right s.left)) 1 := by
  let f := fun s : DimensionSplit d=>fun p : HighHNIndex a c η hc θ s.left × LowHNIndex a c η hc θ s.right=>
    highEnergy a κ c η hc θ s.left p.1+lowEnergy a κ c η hc θ s.right p.2+
      (eulerForm a s.left s.right-eulerForm a s.right s.left)
  have hf : ∀s,Admissible (f s) := fun s=>
    admissible_shift (admissible_prod (highEnergy_admissible a κ c η hc θ s.left)
      (lowEnergy_admissible a κ c η hc θ s.right)) _
  have H := series_equiv (decoratedEnergy_admissible a κ c η hc d)
    (admissible_sigma f hf) (thresholdIndexEquiv a c η hc θ d)
    (thresholdIndexEquiv_energy a κ c η hc θ d)
  rw [series_sigma f hf] at H
  change hnSeries a κ c η hc d=_ at H
  rw [H]
  apply Finset.sum_congr rfl
  intro s hs
  dsimp only [f]
  rw [series_shift (admissible_prod (highEnergy_admissible a κ c η hc θ s.left)
    (lowEnergy_admissible a κ c η hc θ s.right)),
    ←series_mul (highEnergy_admissible a κ c η hc θ s.left) (lowEnergy_admissible a κ c η hc θ s.right)]
  rfl

end
end ElementaryPositivity.RawShuffle

end

end OAI
