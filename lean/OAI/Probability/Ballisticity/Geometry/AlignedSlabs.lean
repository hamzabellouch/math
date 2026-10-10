import Mathlib
import OAI.Probability.Ballisticity.Geometry.SignedHeight

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

lemma signedHeight_add {d : ℕ} (e : Direction d) (x y : Lattice d) :
    signedHeight e (x+y) = signedHeight e x+signedHeight e y := by
  simp only [signedHeight,Pi.add_apply]
  split <;> omega

lemma signedHeight_zsmul_step {d : ℕ} (e : Direction d) (a : ℤ) :
    signedHeight e (a • step e) = a := by
  simp only [signedHeight,Pi.smul_apply,smul_eq_mul,step,ite_true]
  split <;> simp_all

noncomputable def alignHeight {d : ℕ} (e : Direction d) (a : ℤ) (x : Lattice d) : Lattice d :=
  x+(a-signedHeight e x) • step e

lemma signedHeight_align {d : ℕ} (e : Direction d) (a : ℤ) (x : Lattice d) :
    signedHeight e (alignHeight e a x) = a := by
  rw [alignHeight,signedHeight_add,signedHeight_zsmul_step]
  omega

lemma alignHeight_eq_self {d : ℕ} (e : Direction d) (a : ℤ) (x : Lattice d)
    (hx : signedHeight e x = a) : alignHeight e a x = x := by
  simp [alignHeight,hx]

def blockRows {d : ℕ} (e : Direction d) (H i : ℕ) : Set (Lattice d) :=
  {x | (i:ℤ)*H ≤ signedHeight e x ∧ signedHeight e x < (i:ℤ)*H+H}

lemma blockRows_pairwise {d : ℕ} (e : Direction d) (H : ℕ) :
    Pairwise (fun i j => Disjoint (blockRows e H i) (blockRows e H j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hx hy
  change (i:ℤ)*H ≤ signedHeight e x ∧ signedHeight e x < (i:ℤ)*H+H at hx
  change (j:ℤ)*H ≤ signedHeight e x ∧ signedHeight e x < (j:ℤ)*H+H at hy
  rcases lt_or_gt_of_ne hij with h | h
  · have hh : (i:ℤ)+1 ≤ j := by exact_mod_cast h
    nlinarith [Int.natCast_nonneg H]
  · have hh : (j:ℤ)+1 ≤ i := by exact_mod_cast h
    nlinarith [Int.natCast_nonneg H]

lemma strip_align_blockRows {d : ℕ} (e : Direction d) (H i : ℕ) (x : Lattice d) :
    Strip (realPosition (step e)) (alignHeight e ((i:ℤ)*H) x) H = blockRows e H i := by
  ext y
  simp only [Strip,Set.mem_ofPred_eq,signedHeight_projection,signedHeight_align,blockRows]
  constructor
  · rintro ⟨h₁,h₂⟩
    exact ⟨by exact_mod_cast h₁,by exact_mod_cast h₂⟩
  · rintro ⟨h₁,h₂⟩
    exact ⟨by exact_mod_cast h₁,by exact_mod_cast h₂⟩

end DirectionalTransience

end

end

end OAI
