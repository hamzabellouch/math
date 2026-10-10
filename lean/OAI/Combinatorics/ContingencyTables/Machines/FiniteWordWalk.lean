import OAI.Combinatorics.ContingencyTables.Transport.RationalWalks
import OAI.Combinatorics.ContingencyTables.Machines.FiniteFairBits

namespace OAI

/-! # Exact laws of a walk driven by independent fixed-length Boolean words -/

namespace ContingencyTables.FirstSuccess

open scoped BigOperators Classical
open ResidualMixture

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

def uniformMapMass {A : Type*} [Fintype A] (f : A → α) (y : α) : ℚ :=
  (∑ x, if f x = y then (1 : ℚ) else 0) / Fintype.card A

omit [Fintype α] in
theorem uniformMapMass_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (f : B → α) (y : α) : uniformMapMass (f ∘ e) y = uniformMapMass f y := by
  unfold uniformMapMass
  rw [Fintype.card_congr e]
  congr 1
  exact e.sum_comp (fun x => if f x = y then (1 : ℚ) else 0)

theorem finite_fiber_sum {A : Type*} [Fintype A] (f : A → α) (g : α → ℚ) :
    (∑ y, (∑ x, if f x = y then (1 : ℚ) else 0) * g y) = ∑ x, g (f x) := by
  simp_rw [Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem uniformMapMass_prod {A B : Type*} [Fintype A] [Fintype B]
    (f : A → α) (g : α → B → α) (y : α) :
    uniformMapMass (fun z : A × B => g (f z.1) z.2) y =
      ∑ s, uniformMapMass f s * uniformMapMass (g s) y := by
  unfold uniformMapMass
  simp only [Fintype.card_prod, Nat.cast_mul, div_mul_div_comm, ← Finset.sum_div,
    Fintype.sum_prod_type]
  rw [finite_fiber_sum]

theorem uniform_map_mass {A : Type*} [Fintype A] [Nonempty A] (f : A → α) (y : α) :
    (mapLaw (uniformLaw (α := A)) f).mass y = uniformMapMass f y := by
  change (∑ x, if f x = y then 1 / (Fintype.card A : ℚ) else 0) =
    (∑ x, if f x = y then (1 : ℚ) else 0) / Fintype.card A
  rw [Finset.sum_div]
  simp only [ite_div, zero_div]

def wordWalk {k : ℕ} (step : α → (Fin k → Bool) → α) (a : α) :
    (n : ℕ) → (Fin n → Fin k → Bool) → α
  | 0, _ => a
  | n + 1, bits => step (wordWalk step a n (Fin.init bits)) (bits (Fin.last n))

def wordWalkLaw {k : ℕ} (step : α → (Fin k → Bool) → α) (a : α) (n : ℕ) : RationalLaw α :=
  mapLaw (uniformLaw (α := Fin n → Fin k → Bool)) (wordWalk step a n)

/-- A uniform finite Boolean array realizes the independent transition-law
composition, with no random-length source or conditioning. -/
theorem wordWalkLaw_eq {k : ℕ} (step : α → (Fin k → Bool) → α) (a : α) (n : ℕ) :
    wordWalkLaw step a n = walkLaw (fun s => mapLaw (uniformLaw (α := Fin k → Bool)) (step s)) a n := by
  induction n with
  | zero =>
    apply RationalLaw.ext
    funext b
    simp [wordWalkLaw, wordWalk, walkLaw, pointLaw, mapLaw, uniformLaw, uniformMass, eq_comm]
  | succ n ih =>
    let E : ((Fin n → Fin k → Bool) × (Fin k → Bool)) ≃ (Fin (n + 1) → Fin k → Bool) :=
      (Equiv.prodComm _ _).trans (Fin.snocEquiv (fun _ => Fin k → Bool))
    have hc : (wordWalk step a (n + 1)) ∘ E =
        fun ab => step (wordWalk step a n ab.1) ab.2 := by
      funext ab
      rcases ab with ⟨pref, last⟩
      change step (wordWalk step a n (Fin.init
        (Fin.snoc (α := fun _ : Fin (n + 1) => Fin k → Bool) pref last)))
        ((Fin.snoc (α := fun _ : Fin (n + 1) => Fin k → Bool) pref last) (Fin.last n)) = _
      simp only [Fin.init_snoc, Fin.snoc_last]
    apply RationalLaw.ext
    funext b
    change (wordWalkLaw step a (n + 1)).mass b =
      (bindLaw (walkLaw (fun s => mapLaw (uniformLaw (α := Fin k → Bool)) (step s)) a n)
        (fun s => mapLaw (uniformLaw (α := Fin k → Bool)) (step s))).mass b
    rw [← ih]
    simp only [wordWalkLaw, bindLaw, uniform_map_mass]
    have he := uniformMapMass_equiv E (wordWalk step a (n + 1)) b
    rw [hc] at he
    rw [← he]
    exact uniformMapMass_prod (wordWalk step a n) step b

end

end ContingencyTables.FirstSuccess

end OAI
