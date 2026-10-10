import Mathlib
import OAI.RepresentationTheory.FoulkesSixth.HomogeneousPlethysm

namespace OAI

noncomputable section

namespace Foulkes.FastLookup
open MvPolynomial Foulkes.Strips Foulkes.Lookup

lemma coeffZ_comp {n : ℕ} {p : MvPolynomial (Fin n) ℤ} (hp : Alternating p)
    (v : Fin n → ℤ) (σ : Equiv.Perm (Fin n)) :
    coeffZ (v ∘ σ) p = (Equiv.Perm.sign σ : ℤ) * coeffZ v p := by
  classical
  have hh : (∀ j, 0 ≤ v (σ j)) ↔ ∀ j, 0 ≤ v j :=
    ⟨fun h j => by simpa using h (σ.symm j), fun h j => h (σ j)⟩
  by_cases hn : ∀ j, 0 ≤ v j
  · simp only [coeffZ, Function.comp_apply, ite_eq_left hn, ite_eq_left (hh.mpr hn)]
    exact coeff_comp hp (fun j => (v j).toNat) σ
  · simp only [coeffZ, Function.comp_apply, ite_eq_right hn, ite_eq_right (mt hh.mp hn), mul_zero]

abbrev State (n : ℕ) := ℤ × (Fin n → ℤ)

def compareStep {n : ℕ} (ij : Fin n × Fin n) (s : State n) : State n :=
  if s.2 ij.1 < s.2 ij.2 then (-s.1, s.2 ∘ Equiv.swap ij.1 ij.2) else s

lemma compareStep_sound {n : ℕ} {p : MvPolynomial (Fin n) ℤ} (hp : Alternating p)
    (ij : Fin n × Fin n) (s : State n) :
    (compareStep ij s).1 * coeffZ (compareStep ij s).2 p = s.1 * coeffZ s.2 p := by
  unfold compareStep
  split_ifs with h
  · have hij : ij.1 ≠ ij.2 := fun heq => by simp [heq] at h
    dsimp only
    rw [coeffZ_comp hp, Equiv.Perm.sign_swap hij]
    simp
  · rfl

def run {n : ℕ} (steps : List (Fin n × Fin n)) (s : State n) : State n :=
  steps.foldl (fun s ij => compareStep ij s) s

lemma run_sound {n : ℕ} {p : MvPolynomial (Fin n) ℤ} (hp : Alternating p)
    (steps : List (Fin n × Fin n)) (s : State n) :
    (run steps s).1 * coeffZ (run steps s).2 p = s.1 * coeffZ s.2 p := by
  induction steps generalizing s with
  | nil => rfl
  | cons ij steps ih =>
    exact (ih (compareStep ij s)).trans (compareStep_sound hp ij s)

def network (n : ℕ) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun i =>
    ((List.finRange n).filter (fun j => i < j)).map fun j => (i,j)

def finish {n : ℕ} (f : (Fin n → ℕ) → ℤ) (s : State n) : Option ℤ :=
  if ∀ j, 0 ≤ s.2 j then
    if ∀ i j, i < j → (s.2 j).toNat < (s.2 i).toNat then
      some (s.1 * f (fun j => (s.2 j).toNat - staircase n j))
    else if ∃ i j, i ≠ j ∧ s.2 i = s.2 j then some 0 else none
  else some 0

lemma finish_sound {n : ℕ} (p : MvPolynomial (Fin n) ℤ)
    (hp : ∀ σ : Equiv.Perm (Fin n), rename σ p = p)
    (f : (Fin n → ℕ) → ℤ)
    (hf : ∀ mu, Antitone mu → f mu = schurCoeff p mu)
    (s : State n) (z : ℤ) (hz : finish f s = some z) :
    z = s.1 * coeffZ s.2 (p * alternant (staircase n)) := by
  classical
  unfold finish at hz
  split_ifs at hz with hn hs hr
  · have hstrict : StrictAnti (fun j => (s.2 j).toNat) := hs
    have ha := unshift_antitone hstrict
    have he := shifted_unshift hstrict
    have hval : f (fun j => (s.2 j).toNat - staircase n j) =
        (p * alternant (staircase n)).coeff (expVector (fun j => (s.2 j).toNat)) := by
      change f (unshift (fun j => (s.2 j).toNat)) = _
      rw [hf _ ha]
      unfold schurCoeff
      rw [he]
    have hz' := Option.some.inj hz
    rw [← hz', hval]
    simp only [coeffZ, ite_eq_left hn]
  · have hz' := Option.some.inj hz
    obtain ⟨i,j,hij,he⟩ := hr
    have ha := alternating_mul_symmetric hp (alternant_alternating (staircase n))
    have hc := coeff_repeated ha (fun j => (s.2 j).toNat) hij (congrArg Int.toNat he)
    rw [← hz']
    simp only [coeffZ, ite_eq_left hn, hc, mul_zero]
  · have hz' := Option.some.inj hz
    rw [← hz']
    simp only [coeffZ, ite_eq_right hn, mul_zero]

def checkedLookup {n : ℕ} (f : (Fin n → ℕ) → ℤ) (v : Fin n → ℤ) : Option ℤ :=
  finish f (run (network n) (1,v))

theorem checkedLookup_sound {n : ℕ} (p : MvPolynomial (Fin n) ℤ)
    (hp : ∀ σ : Equiv.Perm (Fin n), rename σ p = p)
    (f : (Fin n → ℕ) → ℤ)
    (hf : ∀ mu, Antitone mu → f mu = schurCoeff p mu)
    (v : Fin n → ℤ) (z : ℤ) (hz : checkedLookup f v = some z) :
    z = signedLookup (schurCoeff p) v := by
  rw [signedLookup_eq_coeffZ p hp]
  have ha := alternating_mul_symmetric hp (alternant_alternating (staircase n))
  calc
    z = _ := finish_sound p hp f hf _ z hz
    _ = _ := by simpa only [one_mul] using run_sound ha (network n) (1,v)

end Foulkes.FastLookup


noncomputable section

namespace Foulkes.FastLookup

example : checkedLookup (fun (_ : Fin 6 → ℕ) => (7 : ℤ)) ![1,8,5,3,2,10] = some (-7) := by
  decide +kernel
example : checkedLookup (fun (_ : Fin 6 → ℕ) => (7 : ℤ)) ![1,8,5,3,2,1] = some 0 := by
  decide +kernel
example : checkedLookup (fun (_ : Fin 6 → ℕ) => (7 : ℤ)) ![1,8,5,-3,2,10] = some 0 := by
  decide +kernel
end Foulkes.FastLookup

end
end

end OAI
