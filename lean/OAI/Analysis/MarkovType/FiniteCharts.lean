import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Pi
import Mathlib.Basic.Real.Basic

namespace OAI

namespace MarkovSuperreflexivity

abbrev Chart (Λ : Finset ℝ) (B : ℕ) := ↥Λ ↪o Fin B

noncomputable instance chartFintype (Λ : Finset ℝ) (B : ℕ) :
    Fintype (Chart Λ B) := by
  classical
  exact Fintype.ofInjective (fun C : Chart Λ B => (C : ↥Λ → Fin B))
    (by intro C D h; apply DFunLike.ext; intro x; exact congrFun h x)

namespace Chart

variable {Λ : Finset ℝ} {B : ℕ}

def Good (h : ℝ ≃o ℝ) (C C' : Chart Λ B) : Prop :=
  ∀ (x : ↥Λ) (hx : h (x : ℝ) ∈ Λ), C' x = C ⟨h (x : ℝ), hx⟩

theorem good_symm_iff (h : ℝ ≃o ℝ) (C C' : Chart Λ B) :
    Good h C C' ↔ Good h.symm C' C := by
  constructor
  · intro hgood x hx
    have hmem : h (h.symm (x : ℝ)) ∈ Λ := by
      simpa only [h.apply_symm_apply] using x.property
    have heq : (⟨h (h.symm (x : ℝ)), hmem⟩ : ↥Λ) = x := by
      apply Subtype.ext
      exact h.apply_symm_apply (x : ℝ)
    have hm := hgood ⟨h.symm (x : ℝ), hx⟩ hmem
    rw [heq] at hm
    exact hm.symm
  · intro hgood x hx
    have hmem : h.symm (h (x : ℝ)) ∈ Λ := by
      simpa only [h.symm_apply_apply] using x.property
    have heq : (⟨h.symm (h (x : ℝ)), hmem⟩ : ↥Λ) = x := by
      apply Subtype.ext
      exact h.symm_apply_apply (x : ℝ)
    have hm := hgood ⟨h (x : ℝ), hx⟩ hmem
    rw [heq] at hm
    exact hm.symm

theorem good_rank (h : ℝ ≃o ℝ) (C C' : Chart Λ B)
    (hg : Good h C C') (x : ↥Λ) (hx : h (x : ℝ) ∈ Λ) :
    (C' x).val = (C ⟨h (x : ℝ), hx⟩).val :=
  congrArg Fin.val (hg x hx)

theorem rank_lt (C : Chart Λ B) {x y : ↥Λ} (hxy : (x : ℝ) < y) :
    (C x).val < (C y).val :=
  C.strictMono hxy

end Chart

end MarkovSuperreflexivity

end OAI
