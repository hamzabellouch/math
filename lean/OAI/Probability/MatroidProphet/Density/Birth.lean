import OAI.Probability.MatroidProphet.Density.Guarded
import Mathlib.Data.Nat.Find

namespace OAI

namespace MatroidProphet
open Set
variable {α : Type*} [Fintype α]
attribute [local instance] Classical.propDecidable

def pathHorizon (h : ℕ) : ℕ := 3 * (h + 1)

lemma activation_add_horizon (h : ℕ) : activation h + (pathHorizon h : ℤ) = 0 := by
  dsimp [activation, pathHorizon]
  omega

lemma exists_nominal_member (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (e : α) :
    ∃ j : ℕ, e ∈ nominalPath M hE κ D C h (activation h + j) := by
  refine ⟨pathHorizon h, ?_⟩
  rw [activation_add_horizon, nominalPath_nonnegative M hE κ D C h (by omega)]
  trivial

noncomputable def nominalBirth (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (e : α) : ℤ :=
  activation h + Nat.find (exists_nominal_member M hE κ D C h e)

lemma nominalBirth_mem (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (e : α) :
    e ∈ nominalPath M hE κ D C h (nominalBirth M hE κ D C h e) :=
  Nat.find_spec (exists_nominal_member M hE κ D C h e)

lemma nominalBirth_bounds (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (e : α) :
    activation h ≤ nominalBirth M hE κ D C h e ∧ nominalBirth M hE κ D C h e ≤ 0 := by
  have hmem : e ∈ nominalPath M hE κ D C h (activation h + (pathHorizon h : ℤ)) := by
    rw [activation_add_horizon, nominalPath_nonnegative M hE κ D C h (by omega)]
    trivial
  have hle := Nat.find_min' (exists_nominal_member M hE κ D C h e) hmem
  have hi : (Nat.find (exists_nominal_member M hE κ D C h e) : ℤ) ≤ pathHorizon h := by
    exact_mod_cast hle
  have hh := activation_add_horizon h
  dsimp only [nominalBirth]
  omega

lemma nominalBirth_not_activation_succ (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (e : α) :
    nominalBirth M hE κ D C h e ≠ activation h + 1 := by
  intro heq
  have hm := nominalBirth_mem M hE κ D C h e
  rw [heq, nominalPath_baseline_gap] at hm
  have hm0 : e ∈ nominalPath M hE κ D C h (activation h + (0 : ℕ)) := by simpa using hm
  have hj := Nat.find_min' (exists_nominal_member M hE κ D C h e) hm0
  have hj0 : Nat.find (exists_nominal_member M hE κ D C h e) = 0 := Nat.eq_zero_of_le_zero hj
  dsimp only [nominalBirth] at heq
  rw [hj0] at heq
  omega

lemma nominalBirth_range (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (e : α) :
    nominalBirth M hE κ D C h e = activation h ∨
      (activation h + 2 ≤ nominalBirth M hE κ D C h e ∧ nominalBirth M hE κ D C h e ≤ 0) := by
  have hb := nominalBirth_bounds M hE κ D C h e
  have hg := nominalBirth_not_activation_succ M hE κ D C h e
  omega

lemma not_mem_nominal_before_birth (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (e : α) (he : e ∉ M.closure ∅)
    {k : ℤ} (hk : k < nominalBirth M hE κ D C h e) :
    e ∉ nominalPath M hE κ D C h k := by
  by_cases hka : k < activation h
  · rwa [nominalPath_early M hE κ D C h hka]
  · intro hm
    have heq : activation h + ((k - activation h).toNat : ℤ) = k := by
      rw [Int.toNat_of_nonneg (by omega)]
      omega
    have hm' : e ∈ nominalPath M hE κ D C h
        (activation h + ((k - activation h).toNat : ℤ)) := by rwa [heq]
    have hf := Nat.find_min' (exists_nominal_member M hE κ D C h e) hm'
    have hfi : (Nat.find (exists_nominal_member M hE κ D C h e) : ℤ) ≤
        ((k - activation h).toNat : ℤ) := by exact_mod_cast hf
    dsimp only [nominalBirth] at hk
    omega

lemma mem_nominal_iff_birth_le (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (e : α) (he : e ∉ M.closure ∅) (k : ℤ) :
    e ∈ nominalPath M hE κ D C h k ↔ nominalBirth M hE κ D C h e ≤ k := by
  constructor
  · intro hm
    by_contra hn
    exact not_mem_nominal_before_birth M hE κ D C h e he (by omega) hm
  · intro hk
    exact nominalPath_mono M hE κ D C h hk (nominalBirth_mem M hE κ D C h e)

lemma nominalPath_generators (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (hκ : 0 < κ) (D C : ℕ → Set α) (h : ℕ) :
    ∃ Jtotal : Set α, Jtotal ⊆ D h ∧ κ * Jtotal.ncard ≤ (D h).ncard ∧
      ∃ J : ℕ → Set α, Monotone J ∧ (∀ j ≤ pathHorizon h, J j ⊆ Jtotal) ∧
        (∀ j ≤ pathHorizon h,
          M.closure (guardedPath M hE κ D C h (activation h + j) ∪ J j) =
            nominalPath M hE κ D C h (activation h + j)) := by
  have hmono : Monotone (fun j : ℕ => guardedPath M hE κ D C h (activation h + j)) := by
    intro i j hij
    apply guardedPath_mono M hE κ D C h
    have hi : (i : ℤ) ≤ j := by exact_mod_cast hij
    omega
  obtain ⟨Jtotal, hJD, hcard, J, hJmono, hJJ, hgen⟩ :=
    densityPath_generators M hE κ hκ (D h)
      (fun j : ℕ => guardedPath M hE κ D C h (activation h + j)) hmono (pathHorizon h)
  refine ⟨Jtotal, hJD, hcard, J, hJmono, hJJ, ?_⟩
  intro j hj
  rw [nominalPath, densityEnabled, ite_eq_left (by omega)]
  exact hgen j hj

end MatroidProphet

end OAI
