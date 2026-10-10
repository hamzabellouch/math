import Mathlib

namespace OAI

noncomputable section

namespace SparseBlocks

abbrev Vertex := ℤ × ℤ

end SparseBlocks

namespace SparseBlocks

attribute [local instance] Classical.propDecidable

local instance sparseColorDecidableEq (type : Sort*) : DecidableEq type :=
  Classical.typeDecidableEq type

def residue (P : ℕ) (hP : 0 < P) (a : ℤ) : Fin P :=
  ⟨(a%(P:ℤ)).toNat,by
    have hp : (0:ℤ) < P := by exact_mod_cast hP
    have h1 := Int.emod_nonneg a (ne_of_gt hp)
    have h2 := Int.emod_lt_of_pos a hp
    omega⟩

def color (P : ℕ) (hP : 0 < P) (z : Vertex) : Fin P × Fin P :=
  (residue P hP z.1,residue P hP z.2)

lemma residue_eq_dvd (P : ℕ) (hP : 0 < P) (a b : ℤ)
    (hab : residue P hP a = residue P hP b) : (P:ℤ) ∣ a-b := by
  have hp : (P:ℤ) ≠ 0 := by exact_mod_cast ne_of_gt hP
  have hh := congrArg (fun t : Fin P => (t.val:ℤ)) hab
  have hmod : a%(P:ℤ) = b%(P:ℤ) := by
    simpa only [residue,Int.toNat_of_nonneg (Int.emod_nonneg a hp),
      Int.toNat_of_nonneg (Int.emod_nonneg b hp)] using hh
  exact (Int.modEq_iff_dvd).mp hmod.symm

lemma color_distance (P : ℕ) (hP : 0 < P) (z w : Vertex)
    (hne : z ≠ w) (hc : color P hP z = color P hP w) :
    (P:ℤ) ≤ |z.1-w.1| ∨ (P:ℤ) ≤ |z.2-w.2| := by
  by_cases h1 : z.1 = w.1
  · right
    have h2 : z.2 ≠ w.2 := fun hh => hne (Prod.ext h1 hh)
    exact Int.le_abs_of_dvd (sub_ne_zero.mpr h2)
      (residue_eq_dvd P hP z.2 w.2 (congrArg Prod.snd hc))
  · left
    exact Int.le_abs_of_dvd (sub_ne_zero.mpr h1)
      (residue_eq_dvd P hP z.1 w.1 (congrArg Prod.fst hc))

def offsets (m : ℕ) : Finset Vertex :=
  Finset.Icc (-(m:ℤ)) m ×ˢ Finset.Icc (-(m:ℤ)) m

lemma offsets_mem (m : ℕ) (t : Vertex) : t ∈ offsets m ↔ |t.1| ≤ m ∧ |t.2| ≤ m := by
  simp only [offsets,Finset.mem_product,Finset.mem_Icc,abs_le]

lemma offsets_card (m : ℕ) : (offsets m).card = (2*m+1)^2 := by
  simp only [offsets,Finset.card_product,Int.card_Icc]
  have h1 : ((m:ℤ)+1- -(m:ℤ)) = (2*m+1:ℕ) := by push_cast;ring
  rw [h1,Int.toNat_natCast,pow_two]

lemma perturbed_color_distance (m : ℕ) (z w : Vertex)
    (hne : z ≠ w) (hc : color (2*m+4) (by omega) z = color (2*m+4) (by omega) w)
    (s t : offsets m) :
    3 < |(z+s.val).1-(w+t.val).1| ∨ 3 < |(z+s.val).2-(w+t.val).2| := by
  have hs := (offsets_mem m s.val).mp s.property
  have ht := (offsets_mem m t.val).mp t.property
  have hdist := color_distance (2*m+4) (by omega) z w hne hc
  have perturb (a b c d : ℤ) (hc : |c| ≤ m) (hd : |d| ≤ m)
      (hab : (2*m+4:ℕ) ≤ |a-b|) : 3 < |(a+c)-(b+d)| := by
    push_cast at hab
    simp only [abs_eq_max_neg] at hc hd hab ⊢
    omega
  rcases hdist with h | h
  · exact Or.inl (perturb _ _ _ _ hs.1 ht.1 h)
  · exact Or.inr (perturb _ _ _ _ hs.2 ht.2 h)

end SparseBlocks

end

end OAI
