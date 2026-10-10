import OAI.Probability.InvariantIsing.Haar.HaarPolynomialValue

namespace OAI

/-! Finite polynomial spaces, padded by the constant atom, for the rotation semigroup. -/
noncomputable section
open Matrix MvPolynomial
open scoped BigOperators
namespace InvariantIsing

def haarPolynomialAtom {N : ℕ} : Option (Fin N × Fin N) → MatrixPolynomial N
  | none => 1
  | some ij => X ij

def haarPolynomialWord {N d : ℕ} (w : Fin d → Option (Fin N × Fin N)) : MatrixPolynomial N :=
  ∏ k, haarPolynomialAtom (w k)

def haarPolynomialSpace (N d : ℕ) : Submodule ℝ (MatrixPolynomial N) :=
  Submodule.span ℝ (Set.range (@haarPolynomialWord N d))

instance haarPolynomialSpace_finite (N d : ℕ) : Module.Finite ℝ (haarPolynomialSpace N d) :=
  Module.Finite.span_of_finite ℝ (Set.finite_range _)

lemma haarPolynomialWord_mem {N d : ℕ} (w : Fin d → Option (Fin N × Fin N)) :
    haarPolynomialWord w ∈ haarPolynomialSpace N d :=
  Submodule.subset_span ⟨w,rfl⟩

lemma haarPolynomialWord_cons {N d : ℕ} (a : Option (Fin N × Fin N))
    (w : Fin d → Option (Fin N × Fin N)) :
    haarPolynomialWord (Fin.cons a w) = haarPolynomialAtom a*haarPolynomialWord w := by
  simp only [haarPolynomialWord,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]

lemma haarPolynomialSpace_atom_mul {N d : ℕ} (a : Option (Fin N × Fin N))
    {p : MatrixPolynomial N} (hp : p ∈ haarPolynomialSpace N d) :
    haarPolynomialAtom a*p ∈ haarPolynomialSpace N (d+1) := by
  refine Submodule.span_induction (p := fun q _ =>
    haarPolynomialAtom a*q ∈ haarPolynomialSpace N (d+1)) ?_ ?_ ?_ ?_ hp
  · intro q hq
    rcases hq with ⟨w,rfl⟩
    rw [← haarPolynomialWord_cons]
    exact haarPolynomialWord_mem _
  · simpa only [mul_zero] using (haarPolynomialSpace N (d+1)).zero_mem
  · intro p q _ _ hp hq
    rw [mul_add]
    exact (haarPolynomialSpace N (d+1)).add_mem hp hq
  · intro c p _ hp
    rw [mul_smul_comm]
    exact (haarPolynomialSpace N (d+1)).smul_mem c hp

lemma haarPolynomialSpace_le_succ (N d : ℕ) :
    haarPolynomialSpace N d ≤ haarPolynomialSpace N (d+1) := by
  intro p hp
  simpa only [haarPolynomialAtom,one_mul] using
    haarPolynomialSpace_atom_mul (none : Option (Fin N × Fin N)) hp

lemma haarPolynomialSpace_mono (N : ℕ) : Monotone (haarPolynomialSpace N) :=
  monotone_nat_of_le_succ (haarPolynomialSpace_le_succ N)

lemma one_mem_haarPolynomialSpace (N d : ℕ) :
    (1 : MatrixPolynomial N) ∈ haarPolynomialSpace N d := by
  simpa only [haarPolynomialWord,haarPolynomialAtom,Finset.prod_const_one] using
    haarPolynomialWord_mem (N := N) (d := d) (fun _ => none)

/-- Every multivariate polynomial belongs to one of the finite spaces. -/
theorem exists_mem_haarPolynomialSpace {N : ℕ} (p : MatrixPolynomial N) :
    ∃ d : ℕ, p ∈ haarPolynomialSpace N d := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    refine ⟨0,?_⟩
    rw [MvPolynomial.C_eq_smul_one]
    exact (haarPolynomialSpace N 0).smul_mem c (one_mem_haarPolynomialSpace N 0)
  | add p q hp hq =>
    obtain ⟨d,hd⟩ := hp
    obtain ⟨e,he⟩ := hq
    exact ⟨max d e,(haarPolynomialSpace N (max d e)).add_mem
      (haarPolynomialSpace_mono N (le_max_left d e) hd)
      (haarPolynomialSpace_mono N (le_max_right d e) he)⟩
  | mul_X p ij hp =>
    obtain ⟨d,hd⟩ := hp
    refine ⟨d+1,?_⟩
    simpa only [haarPolynomialAtom,mul_comm] using
      haarPolynomialSpace_atom_mul (some ij) hd

end InvariantIsing

end

end OAI
