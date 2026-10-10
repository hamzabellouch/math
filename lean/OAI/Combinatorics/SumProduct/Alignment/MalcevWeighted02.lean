import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.MalcevWeighted01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
noncomputable section
end
end
 

 
section
noncomputable section
namespace MalcevWeightedCoordinates

lemma exists_sorting_permutation {n : ℕ} (w : Fin n → ℕ) :
    ∃ p : Equiv.Perm (Fin n), Monotone (w ∘ p) := by
  classical
  let l := (List.finRange n).mergeSort (fun i j => decide (w i ≤ w j))
  have hl : l.Perm (List.finRange n) := List.mergeSort_perm _ _
  have hlen : l.length=n := by simpa using hl.length_eq
  have hnd : l.Nodup := hl.nodup_iff.mpr (List.nodup_finRange n)
  have hall : ∀ i : Fin n, i∈l := fun i => hl.mem_iff.mpr (List.mem_finRange i)
  let e := List.Nodup.getEquivOfForallMemList l hnd hall
  let p := (Fin.castOrderIso hlen.symm).toEquiv.trans e
  refine ⟨p,?_⟩
  have hs : l.Pairwise (fun i j => w i ≤ w j) := by
    have hh := List.pairwise_mergeSort (le := fun i j : Fin n => decide (w i ≤ w j))
      (fun a b c hab hbc => by simpa using le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc))
      (fun a b => by simpa using le_total (w a) (w b)) (List.finRange n)
    simpa only [decide_eq_true_eq] using hh
  intro i j hij
  change w (l.get (Fin.cast hlen.symm i)) ≤ w (l.get (Fin.cast hlen.symm j))
  rcases eq_or_lt_of_le hij with he|he
  · simp [he]
  · exact hs.rel_get_of_lt he

lemma exists_weight_cutoff {n : ℕ} (w : Fin n → ℕ) (hw : Monotone w) (k : ℕ) :
    ∃ r : ℕ, r ≤ n ∧ ∀ i : Fin n, w i < k ↔ i.val < r := by
  classical
  let P : ℕ → Prop := fun r => ∀ i : Fin n, r ≤ i.val → k ≤ w i
  have hex : ∃ r, P r := ⟨n,by intro i hi; omega⟩
  refine ⟨Nat.find hex,Nat.find_min' hex (show P n from by intro i hi; omega),?_⟩
  intro i
  constructor
  · intro hi
    by_contra hn
    exact (not_le_of_gt hi) (Nat.find_spec hex i (Nat.le_of_not_gt hn))
  · intro hi
    by_contra hn
    have hki : k ≤ w i := Nat.le_of_not_gt hn
    have hp : P i.val := by
      intro j hj
      exact hki.trans (hw hj)
    have hh := Nat.find_min' hex hp
    omega

end MalcevWeightedCoordinates
end
end
 

 
section
noncomputable section
namespace RationalLattice
variable {G : Type*} [Group G] [TopologicalSpace G] {n : ℕ}
variable (c : RealCoordinates G n)
variable (H : Subgroup G) (I : Set (Fin n))
variable (hH : ∀ g : G, g ∈ H ↔ ∀ i ∈ I, c.coord g i = 0)

include hH in
lemma basisFlow_mem_subspace {i : Fin n} (hi : i ∉ I) (t : ℝ) : basisFlow c i t ∈ H := by
  apply realPower_mem_of_coordinates c H I hH
  apply (hH _).mpr
  intro j hj
  have hji : j ≠ i := by intro he; exact hi (he ▸ hj)
  simp [basisElement,hji]

include hH in
lemma peel_mem_subspace {g : G} (hg : g ∈ H) (k : ℕ) : peel c g k ∈ H := by
  classical
  induction k with
  | zero => exact hg
  | succ k ih =>
    unfold peel
    split_ifs with hk
    · apply H.mul_mem _ ih
      by_cases hi : (⟨k,hk⟩ : Fin n) ∈ I
      · rw [(hH _).mp ih _ hi,neg_zero,basisFlow_zero]
        exact H.one_mem
      · exact basisFlow_mem_subspace c H I hH hi _
    · exact ih

include hH in
lemma expCoordinates_subspace (g : G) :
    g ∈ H ↔ ∀ i ∈ I, expCoordinates c g i = 0 := by
  classical
  constructor
  · intro hg i hi
    exact (hH _).mp (peel_mem_subspace c H I hH hg i.val) i hi
  · intro hg
    rw [← expProduct_expCoordinates c g]
    apply H.list_prod_mem
    intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    by_cases hi : i ∈ I
    · rw [hg i hi,basisFlow_zero]
      exact H.one_mem
    · exact basisFlow_mem_subspace c H I hH hi _

include hH in
 

theorem secondCoordinates_subspace [IsTopologicalGroup G] (g : G) :
    g ∈ H ↔ ∀ i ∈ I, (secondCoordinates c).coord g i = 0 :=
  expCoordinates_subspace c H I hH g

end RationalLattice
end
end
 

 
section
noncomputable section
namespace MalcevWeightedCoordinates
open RationalLattice MalcevCharacters CubeFaces
variable {G : Type*} [Group G] [TopologicalSpace G] {n : ℕ}
variable (c : RealCoordinates G n) (H : Filtration G)
variable (s : ℕ) (hs : H.level (s+1)=⊥)

include hs in
lemma exists_axis_out (i : Fin n) : ∃ k, axis c i 1∉H.level k := by
  refine ⟨s+1,?_⟩
  rw [hs,Subgroup.mem_bot]
  intro he
  have hf := congrArg (fun g => c.coord g i) he
  simp [axis,c.one_coord] at hf

def subspaceWeight (i : Fin n) : ℕ := by
  classical
  exact Nat.find (exists_axis_out c H s hs i)-1

variable (h0 : H.level 0=⊤)
include h0 hs in
lemma weight_lt_iff_out (i : Fin n) (k : ℕ) :
    subspaceWeight c H s hs i  <  k ↔ axis c i 1∉H.level k := by
  classical
  have hz : 0 < Nat.find (exists_axis_out c H s hs i) := by
    by_contra hn
    have he : Nat.find (exists_axis_out c H s hs i)=0 := by omega
    have hnot := Nat.find_spec (exists_axis_out c H s hs i)
    rw [he,h0] at hnot
    exact hnot (Subgroup.mem_top _)
  constructor
  · intro hk hm
    have hle : Nat.find (exists_axis_out c H s hs i) ≤ k := by
      change Nat.find (exists_axis_out c H s hs i)-1 < k at hk
      omega
    exact Nat.find_spec (exists_axis_out c H s hs i) (H.antitone hle hm)
  · intro hm
    have hle := Nat.find_min' (exists_axis_out c H s hs i) hm
    unfold subspaceWeight
    omega

lemma axis_mem_subspace_iff (A : Subgroup G) (I : Set (Fin n))
    (hA : ∀ g : G, g∈A ↔ ∀ i∈I, c.coord g i=0) (i : Fin n) :
    axis c i 1∈A ↔ i∉I := by
  classical
  constructor
  · intro hm hi
    have hz := (hA _).mp hm i hi
    simp [axis] at hz
  · intro hi
    apply (hA _).mpr
    intro j hj
    have hji : j≠i := by intro he; subst j; exact hi hj
    simp [axis,hji]

variable (hH : ∀ k : ℕ, ∃ I : Set (Fin n), ∀ g : G,
  g∈H.level k ↔ ∀ i∈I, c.coord g i=0)
include h0 hH hs in
 

theorem subspaceWeight_level (k : ℕ) (g : G) :
    g∈H.level k ↔ ∀ i : Fin n, subspaceWeight c H s hs i < k → c.coord g i=0 := by
  classical
  obtain ⟨I,hI⟩ := hH k
  have hi (i : Fin n) : subspaceWeight c H s hs i < k ↔ i∈I := by
    rw [weight_lt_iff_out c H s hs h0,axis_mem_subspace_iff c (H.level k) I hI]
    simp
  rw [hI]
  simp only [hi]

end MalcevWeightedCoordinates
end
end
 

 
section
noncomputable section
namespace MalcevWeightedCoordinates
open RationalLattice MalcevCharacters CubeFaces
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G n)
variable (H : Filtration G) (h0 : H.level 0=⊤) (h1 : H.level 1=⊤)
variable (s : ℕ) (hs : H.level (s+1)=⊥)
variable (hH : ∀ k : ℕ, ∃ I : Set (Fin n), ∀ g : G,
  g∈H.level k ↔ ∀ i∈I, c.coord g i=0)
variable (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)
include h0 h1 hs hH hΓ in
 

theorem exists_adapted_secondKind_coordinates :
    ∃ c' : RealCoordinates G n, SecondKind c' ∧
      (∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c'.coord g i=z) ∧
      ∀ k : ℕ, ∃ r : ℕ, r ≤ n ∧ ∀ g : G,
        g∈H.level k ↔ ∀ i : Fin n, i.val < r → c'.coord g i=0 := by
  classical
  let c₁ := secondCoordinates c
  have hk₁ : SecondKind c₁ := secondCoordinates_secondKind c
  have hH₁ : ∀ k : ℕ, ∃ I : Set (Fin n), ∀ g : G,
      g∈H.level k ↔ ∀ i∈I, c₁.coord g i=0 := by
    intro k
    obtain ⟨I,hI⟩ := hH k
    exact ⟨I,secondCoordinates_subspace c (H.level k) I hI⟩
  have hΓ₁ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c₁.coord g i=z :=
    expCoordinates_lattice c Γ hΓ
  let w:=subspaceWeight c₁ H s hs
  have hw : ∀ k (g : G), g∈H.level k ↔ ∀ i : Fin n, w i < k → c₁.coord g i=0 :=
    subspaceWeight_level c₁ H s hs h0 hH₁
  obtain ⟨p,hp⟩ := exists_sorting_permutation w
  let c₂ := sortedCoordinates c₁ w p hp hk₁ H h0 h1 hw
  have hcoord (g : G) (i : Fin n) : c₂.coord g i=c₁.coord g (p i) := rfl
  have hΓ₂ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c₂.coord g i=z := by
    intro g
    rw [hΓ₁]
    constructor
    · intro hg i
      exact hg (p i)
    · intro hg i
      simpa only [hcoord,Equiv.apply_symm_apply] using hg (p.symm i)
  refine ⟨secondCoordinates c₂,secondCoordinates_secondKind c₂,
    expCoordinates_lattice c₂ Γ hΓ₂,?_⟩
  intro k
  obtain ⟨r,hr,hrk⟩ := exists_weight_cutoff (w ∘ p) hp k
  refine ⟨r,hr,?_⟩
  apply secondCoordinates_adapted c₂ (H.level k) r
  intro g
  rw [hw]
  constructor
  · intro hg i hi
    exact hg (p i) ((hrk i).mpr hi)
  · intro hg i hi
    have hpi : (w ∘ p) (p.symm i) < k := by simpa using hi
    simpa only [hcoord,Equiv.apply_symm_apply] using hg (p.symm i) ((hrk _).mp hpi)

end MalcevWeightedCoordinates

end
end
end
end
end

end OAI
