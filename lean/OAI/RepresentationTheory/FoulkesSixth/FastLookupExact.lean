import Mathlib
import OAI.RepresentationTheory.FoulkesSixth.FastLookup

namespace OAI

noncomputable section

namespace Foulkes.FastLookup
open MvPolynomial Foulkes.Strips Foulkes.Lookup

lemma compareStep_perm {n : ℕ} (ij : Fin n × Fin n) (s : State n) :
    ∃ σ : Equiv.Perm (Fin n), compareStep ij s =
      (s.1 * (Equiv.Perm.sign σ : ℤ), s.2 ∘ σ) := by
  unfold compareStep
  split_ifs with h
  · refine ⟨Equiv.swap ij.1 ij.2, ?_⟩
    have hij : ij.1 ≠ ij.2 := fun heq => by simp [heq] at h
    simp [Equiv.Perm.sign_swap hij]
  · refine ⟨1, ?_⟩
    simp

lemma run_perm {n : ℕ} (steps : List (Fin n × Fin n)) (s : State n) :
    ∃ σ : Equiv.Perm (Fin n), run steps s =
      (s.1 * (Equiv.Perm.sign σ : ℤ), s.2 ∘ σ) := by
  induction steps generalizing s with
  | nil => exact ⟨1, by simp [run]⟩
  | cons ij steps ih =>
    obtain ⟨τ,hτ⟩ := compareStep_perm ij s
    obtain ⟨σ,hσ⟩ := ih (compareStep ij s)
    refine ⟨τ * σ, ?_⟩
    change run steps (compareStep ij s) = _
    rw [hσ, hτ]
    simp only [map_mul, Units.val_mul, mul_assoc, Equiv.Perm.coe_mul]
    rfl

lemma finish_perm_exact {n : ℕ} (f : (Fin n → ℕ) → ℤ)
    (v : Fin n → ℤ) (σ : Equiv.Perm (Fin n)) (z : ℤ)
    (hz : finish f ((Equiv.Perm.sign σ : ℤ), v ∘ σ) = some z) :
    z = signedLookup f v := by
  classical
  have hnon : (∀ j, 0 ≤ v (σ j)) ↔ ∀ j, 0 ≤ v j :=
    ⟨fun h j => by simpa using h (σ.symm j), fun h j => h (σ j)⟩
  unfold finish at hz
  dsimp only [Function.comp_apply] at hz
  split_ifs at hz with hn hs hr
  · let w : Fin n → ℕ := fun j => (v j).toNat
    have hstrict : StrictAnti (w ∘ σ) := hs
    have hw : Function.Injective w := by
      intro i j hij
      have hh : σ.symm i = σ.symm j := hstrict.injective (by simpa using hij)
      exact σ.symm.injective hh
    have he : w ∘ σ = w ∘ sortDesc w :=
      Tuple.unique_antitone hstrict.antitone (sortDesc_antitone w)
    have hσ : σ = sortDesc w := Equiv.ext fun j => hw (congrFun he j)
    have hv : (fun j => (v (σ j)).toNat - staircase n j) = sortedPartition w := by
      rw [hσ]
      rfl
    have hz' := Option.some.inj hz
    rw [← hz', hv, hσ]
    simp only [signedLookup, dite_eq_left (hnon.mp hn)]
    change _ = if Function.Injective w then (Equiv.Perm.sign (sortDesc w) : ℤ) * f (sortedPartition w) else 0
    rw [ite_eq_left hw]
  · have hz' := Option.some.inj hz
    obtain ⟨i,j,hij,he⟩ := hr
    have hw : ¬Function.Injective (fun j => (v j).toNat) := by
      intro hw
      exact hij (σ.injective (hw (congrArg Int.toNat he)))
    rw [← hz']
    simp only [signedLookup, dite_eq_left (hnon.mp hn), ite_eq_right hw]
  · have hz' := Option.some.inj hz
    rw [← hz']
    simp only [signedLookup, dite_eq_right (mt hnon.mpr hn)]

theorem checkedLookup_exact {n : ℕ} (f : (Fin n → ℕ) → ℤ)
    (v : Fin n → ℤ) (z : ℤ) (hz : checkedLookup f v = some z) :
    z = signedLookup f v := by
  obtain ⟨σ,hσ⟩ := run_perm (network n) (1,v)
  unfold checkedLookup at hz
  rw [hσ] at hz
  simp only [one_mul] at hz
  exact finish_perm_exact f v σ z hz

end Foulkes.FastLookup

end

end OAI
