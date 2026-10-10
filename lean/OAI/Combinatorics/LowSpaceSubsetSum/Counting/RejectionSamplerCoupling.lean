import OAI.Combinatorics.LowSpaceSubsetSum.Counting.FiniteSamplerCoupling
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.PrimeHashCollision

namespace OAI

/-! # The concrete range and prime calls in the finite coupling -/

noncomputable section

namespace LowSpaceSubsetSum

open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace FiniteLaw

theorem eq_of_mass {α : Type*} [Fintype α] {μ ν : FiniteLaw α}
    (h : ∀ a, μ.mass a = ν.mass a) : μ = ν := by
  cases μ
  cases ν
  congr
  exact funext h

theorem map_equiv_uniform {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] (e : α ≃ β) :
    (FiniteLaw.uniform : FiniteLaw α).map e = FiniteLaw.uniform := by
  apply eq_of_mass
  intro b
  change (FiniteLaw.uniform : FiniteLaw α).probability (fun a => e a = b) =
    1 / Fintype.card β
  rw [FiniteLaw.uniform_probability]
  rw [finiteUniformProbability_equiv e (fun a => a = b),
    ← FiniteLaw.uniform_probability, FiniteLaw.probability_eq]
  rfl

end FiniteLaw

namespace SamplerCoupling

variable {α β : Type*} [Fintype α] [Fintype β]

def map (S : SamplerCoupling α) (f : α → β) : SamplerCoupling β where
  Seed := S.Seed
  finiteSeed := inferInstance
  law := S.law
  ideal s := f (S.ideal s)
  bounded s := (S.bounded s).map f
  agrees s := by
    rcases S.agrees s with h | h
    · exact Or.inl (by simp [h])
    · exact Or.inr (by simp [h])

theorem map_failure (S : SamplerCoupling α) (f : α → β) :
    (S.map f).failure = S.failure := by
  simp only [failure, map, Option.map_eq_none_iff]
  rfl

theorem map_idealLaw (S : SamplerCoupling α) (f : α → β) :
    (S.map f).idealLaw = S.idealLaw.map f := by
  apply FiniteLaw.eq_of_mass
  intro b
  change S.law.probability (fun s => f (S.ideal s) = b) =
    S.idealLaw.probability (fun a => f a = b)
  rw [idealLaw, FiniteLaw.map_probability]

end SamplerCoupling

variable {Ω : Type}

def firstAcceptSubtype (A : Ω → Prop) [DecidablePred A] (N : ℕ)
    (f : Fin N → Ω) : Option {a : Ω // A a} :=
  match h : firstAccept A N f with
  | none => none
  | some a => some ⟨a, firstAccept_some_eligible A N f h⟩

theorem firstAcceptSubtype_none (A : Ω → Prop) [DecidablePred A] (N : ℕ)
    (f : Fin N → Ω) : firstAcceptSubtype A N f = none ↔ firstAccept A N f = none := by
  unfold firstAcceptSubtype
  split <;> simp_all

/-- The bounded marginal ignores the independent eligible backup. The ideal
completion uses it precisely on exhaustion of the fresh candidate tuple. -/
def firstAcceptCoupling [Fintype Ω] [Nonempty Ω]
    (A : Ω → Prop) [DecidablePred A] [Nonempty {a : Ω // A a}] (N : ℕ) :
    SamplerCoupling {a : Ω // A a} where
  Seed := (Fin N → Ω) × {a : Ω // A a}
  finiteSeed := inferInstance
  law := FiniteLaw.uniform
  ideal z := ⟨completedFirstAccept A N z.1 z.2, completedFirstAccept_eligible A N z.1 z.2⟩
  bounded z := firstAcceptSubtype A N z.1
  agrees z := by
    unfold firstAcceptSubtype
    split
    · exact Or.inl rfl
    · rename_i a h
      apply Or.inr
      apply congrArg some
      apply Subtype.ext
      simp [completedFirstAccept, h]

theorem firstAcceptCoupling_uniform [Fintype Ω] [Nonempty Ω]
    (A : Ω → Prop) [DecidablePred A] [Nonempty {a : Ω // A a}] (N : ℕ) :
    (firstAcceptCoupling A N).idealLaw = FiniteLaw.uniform := by
  apply FiniteLaw.eq_of_mass
  intro a
  change (FiniteLaw.uniform : FiniteLaw ((Fin N → Ω) × {b : Ω // A b})).probability
    (fun z => (⟨completedFirstAccept A N z.1 z.2, completedFirstAccept_eligible A N z.1 z.2⟩ :
      {b : Ω // A b}) = a) = 1 / Fintype.card {b : Ω // A b}
  rw [FiniteLaw.uniform_probability]
  simpa only [Subtype.ext_iff] using completedFirstAccept_uniform A N a.val a.property

theorem firstAcceptCoupling_failure [Fintype Ω] [Nonempty Ω]
    (A : Ω → Prop) [DecidablePred A] [Nonempty {a : Ω // A a}] (N : ℕ) :
    (firstAcceptCoupling A N).failure = (1 - finiteUniformProbability A) ^ N := by
  change (FiniteLaw.uniform : FiniteLaw ((Fin N → Ω) × {b : Ω // A b})).probability
    (fun z => firstAcceptSubtype A N z.1 = none) = _
  rw [FiniteLaw.uniform_probability]
  simp only [firstAcceptSubtype_none]
  rw [finiteUniformProbability_fst (Ψ := {b : Ω // A b})
    (fun f : Fin N → Ω => firstAccept A N f = none), firstAccept_failure]

def rangeEligibleEquiv (D : ℕ) : {x : Fin (2 ^ Nat.clog 2 D) // rangeEligible D x} ≃ Fin D where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, x.isLt.trans_le (Nat.le_pow_clog (by decide : 1 < 2) D)⟩, x.isLt⟩
  left_inv _ := rfl
  right_inv _ := rfl

def rangeCoupling {D : ℕ} (hD : 1 < D) (n : ℕ) : SamplerCoupling (Fin D) := by
  let : Nonempty (Fin D) := ⟨⟨0, by omega⟩⟩
  let : Nonempty {x : Fin (2 ^ Nat.clog 2 D) // rangeEligible D x} :=
    ⟨(rangeEligibleEquiv D).symm ⟨0, by omega⟩⟩
  exact (firstAcceptCoupling (rangeEligible D) (n ^ 3)).map (rangeEligibleEquiv D)

theorem rangeCoupling_uniform {D : ℕ} (hD : 1 < D) (n : ℕ) :
    (rangeCoupling hD n).idealLaw =
      @FiniteLaw.uniform (Fin D) inferInstance ⟨⟨0, by omega⟩⟩ := by
  let : Nonempty (Fin D) := ⟨⟨0, by omega⟩⟩
  let : Nonempty {x : Fin (2 ^ Nat.clog 2 D) // rangeEligible D x} :=
    ⟨(rangeEligibleEquiv D).symm ⟨0, by omega⟩⟩
  rw [rangeCoupling, SamplerCoupling.map_idealLaw, firstAcceptCoupling_uniform]
  exact FiniteLaw.map_equiv_uniform (rangeEligibleEquiv D)

theorem rangeCoupling_failure {D : ℕ} (hD : 1 < D) (n : ℕ) :
    (rangeCoupling hD n).failure ≤ 1 / (2 : ℝ) ^ (n ^ 3) := by
  let : Nonempty {x : Fin (2 ^ Nat.clog 2 D) // rangeEligible D x} :=
    ⟨(rangeEligibleEquiv D).symm ⟨0, by omega⟩⟩
  rw [rangeCoupling, SamplerCoupling.map_failure, firstAcceptCoupling_failure,
    ← firstAccept_failure]
  exact rangeSampler_failure hD n

def primeEligibleEquiv {ell : ℕ} (hell : 4 ≤ ell) :
    {x : Fin (2 ^ ell) // primeEligible ell x} ≃ ↥(primeRange ell) where
  toFun x := ⟨x.val.val, x.property⟩
  invFun p := ⟨⟨p.val, primeRange_lt hell p.property⟩, p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def primeCoupling {ell : ℕ} (hell : 4 ≤ ell) (n : ℕ) :
    SamplerCoupling ↥(primeRange ell) := by
  let : Nonempty ↥(primeRange ell) := (primeRange_nonempty hell).to_subtype
  let : Nonempty {x : Fin (2 ^ ell) // primeEligible ell x} :=
    ⟨(primeEligibleEquiv hell).symm (Classical.choice inferInstance)⟩
  exact (firstAcceptCoupling (primeEligible ell) (n ^ 3)).map (primeEligibleEquiv hell)

theorem primeCoupling_uniform {ell : ℕ} (hell : 4 ≤ ell) (n : ℕ) :
    (primeCoupling hell n).idealLaw =
      @FiniteLaw.uniform ↥(primeRange ell) inferInstance
        (primeRange_nonempty hell).to_subtype := by
  let : Nonempty ↥(primeRange ell) := (primeRange_nonempty hell).to_subtype
  let : Nonempty {x : Fin (2 ^ ell) // primeEligible ell x} :=
    ⟨(primeEligibleEquiv hell).symm (Classical.choice inferInstance)⟩
  rw [primeCoupling, SamplerCoupling.map_idealLaw, firstAcceptCoupling_uniform]
  exact FiniteLaw.map_equiv_uniform (primeEligibleEquiv hell)

theorem primeCoupling_failure {ell n : ℕ} (hell : 4 ≤ ell) (hen : ell ≤ n) :
    (primeCoupling hell n).failure ≤ Real.exp (-((n : ℝ) ^ 2 / 4)) := by
  let : Nonempty ↥(primeRange ell) := (primeRange_nonempty hell).to_subtype
  let : Nonempty {x : Fin (2 ^ ell) // primeEligible ell x} :=
    ⟨(primeEligibleEquiv hell).symm (Classical.choice inferInstance)⟩
  rw [primeCoupling, SamplerCoupling.map_failure, firstAcceptCoupling_failure,
    ← firstAccept_failure]
  exact primeSampler_failure hell hen

end LowSpaceSubsetSum

end

end OAI
