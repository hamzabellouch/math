import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.TransformedGaussSeparation
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CenteredGrid

namespace OAI

/-! A concrete duplicate-free list of all eight Gauss labels in each cell
of the centered rectangular grid, with the exact polynomial count. -/

namespace ContinuumCoulomb.CenteredGaussLabels
open EulerRegisters (Registers)
open RationalGaussNodes (Signs)

abbrev Radii := ℕ×(ℕ×ℕ)

def integers (R : ℕ) : List ℤ :=
  (List.range (2*R+1)).map (fun j : ℕ => (j:ℤ)-(R:ℤ))
def signs : List Signs :=
  [false,true] ×ˢ ([false,true] ×ˢ [false,true])
def cells (r : Radii) : List Registers :=
  integers r.1 ×ˢ (integers r.2.1 ×ˢ integers r.2.2)
def labels (r : Radii) : List (Registers×Signs) := cells r ×ˢ signs
def radiiVector (r : Radii) : Fin 3 → ℕ := ![r.1,r.2.1,r.2.2]

theorem mem_integers (R : ℕ) (j : ℤ) : j ∈ integers R ↔ -(R:ℤ) ≤ j ∧ j ≤ R := by
  constructor
  · intro h
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp h
    have hi' := List.mem_range.mp hi
    omega
  · rintro ⟨hl,hu⟩
    refine List.mem_map.mpr ⟨(j+(R:ℤ)).toNat,List.mem_range.mpr ?_,?_⟩ <;> omega

theorem integers_nodup (R : ℕ) : (integers R).Nodup :=
  (List.nodup_range).map (by
    intro a b h
    have he : (a:ℤ)-(R:ℤ) = (b:ℤ)-(R:ℤ) := h
    omega)

theorem signs_mem (s : Signs) : s ∈ signs := by
  rcases s with ⟨a,b,c⟩
  cases a <;> cases b <;> cases c <;> simp [signs]

theorem labels_nodup (r : Radii) : (labels r).Nodup := by
  apply List.Nodup.product
  · exact (integers_nodup r.1).product ((integers_nodup r.2.1).product (integers_nodup r.2.2))
  · decide

theorem labels_length (r : Radii) :
    (labels r).length = 8*((2*r.1+1)*(2*r.2.1+1)*(2*r.2.2+1)) := by
  simp only [labels,cells,signs,integers,List.length_product,List.length_map,List.length_range]
  simp only [List.length_cons,List.length_nil]
  ring

theorem mem_labels (r : Radii) (l : Registers×Signs) :
    l ∈ labels r ↔ (RationalGaussNodes.index l.1 l.2).1 ∈ centeredGridIndices (radiiVector r) := by
  rcases l with ⟨⟨a,b,c⟩,s⟩
  rw [labels,List.mem_product]
  simp only [signs_mem,and_true,cells,List.mem_product,mem_integers]
  rw [mem_centeredGridIndices]
  constructor
  · rintro ⟨h0,h1,h2⟩ i
    fin_cases i
    · simpa [RationalGaussNodes.index,radiiVector] using h0
    · simpa [RationalGaussNodes.index,radiiVector] using h1
    · simpa [RationalGaussNodes.index,radiiVector] using h2
  · intro h
    exact ⟨by simpa [RationalGaussNodes.index,radiiVector] using h 0,
      by simpa [RationalGaussNodes.index,radiiVector] using h 1,
      by simpa [RationalGaussNodes.index,radiiVector] using h 2⟩

end ContinuumCoulomb.CenteredGaussLabels

end OAI
