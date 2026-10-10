import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourcePauli

namespace OAI

/-! Sparse actions of the physical Pauli matrices, retaining a rational part. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaPauliBit (μ : Fin 3) (a : Fin 2) : Fin 2 :=
  if μ = 2 then a else Equiv.swap 0 1 a

def qmaPhysicalPauliSign (μ : Fin 3) (a : Fin 2) : ℚ :=
  if μ = 0 then 1 else if a = 0 then (if μ = 1 then -1 else 1)
    else (if μ = 1 then 1 else -1)

def qmaPauliPhase (μ : Fin 3) : ℂ := if μ = 1 then Complex.I else 1

theorem qmaPauli_monomial (μ : Fin 3) (a b : Fin 2) :
    pauli μ a b = qmaPauliPhase μ*(qmaPhysicalPauliSign μ a:ℂ)*
      (if qmaPauliBit μ a = b then 1 else 0) := by
  fin_cases μ <;> fin_cases a <;> fin_cases b <;>
    norm_num [pauli,pauliX,pauliY,pauliZ,qmaPauliBit,qmaPhysicalPauliSign,qmaPauliPhase,
      Equiv.swap_apply_def]

theorem qmaLocalPauli_monomial (n : ℕ) (i : Fin n) (μ : Fin 3)
    (s t : SourceSpinBasis n) :
    sourceLocalPauli n i μ s t = qmaPauliPhase μ*(qmaPhysicalPauliSign μ (s i):ℂ)*
      (if Function.update s i (qmaPauliBit μ (s i)) = t then 1 else 0) := by
  unfold sourceLocalPauli sourceTensor
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [ite_true,qmaPauli_monomial]
  have hrest (k : Fin n) (hk : k ∈ Finset.univ.erase i) :
      (if k = i then pauli μ else 1) (s k) (t k) = if s k = t k then 1 else 0 := by
    simp [(Finset.mem_erase.mp hk).1,Matrix.one_apply]
  rw [Finset.prod_congr rfl hrest]
  by_cases h : Function.update s i (qmaPauliBit μ (s i)) = t
  · have hi := congrFun h i
    have hk (k : Fin n) (hki : k ≠ i) : s k = t k := by
      simpa only [Function.update_of_ne hki] using congrFun h k
    simp only [Function.update_self] at hi
    rw [ite_eq_left h,ite_eq_left hi,Finset.prod_eq_one (fun k hk' =>
      ite_eq_left (hk k (Finset.mem_erase.mp hk').1))]
    simp
  · rw [ite_eq_right h]
    by_cases hi : qmaPauliBit μ (s i) = t i
    · have hbad : ∃ k ∈ Finset.univ.erase i, s k ≠ t k := by
        by_contra hn
        push Not at hn
        apply h
        funext k
        by_cases hki : k = i
        · subst k
          simpa only [Function.update_self] using hi
        · simpa only [Function.update_of_ne hki] using
            hn k (Finset.mem_erase.mpr ⟨hki,Finset.mem_univ _⟩)
      obtain ⟨k,hk,hne⟩ := hbad
      rw [ite_eq_left hi,Finset.prod_eq_zero hk (ite_eq_right hne)]
      simp
    · simp [hi]

end ContinuumCoulomb

end

end OAI
