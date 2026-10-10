import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.NormNum

namespace OAI

universe uM

namespace PeriodicTilingThree

open scoped BigOperators

def shiftMultiplicity (a b : ℕ) (e : ZMod a × ZMod b) : ℕ :=
  if e.2 = 0 then
    if e.1 = 0 then 2 else if e.1 = 1 then 0 else 1
  else if e.2 = 1 then
    if e.1 = 0 then 0 else if e.1 = 1 then 2 else 1
  else 1

def shiftOmega (a b : ℕ) (e : ZMod a × ZMod b) : ℤ :=
  ((if e.1 = 0 then 1 else 0) - (if e.1 = 1 then 1 else 0)) *
    ((if e.2 = 0 then 1 else 0) - (if e.2 = 1 then 1 else 0))

abbrev ShiftIndex (a b : ℕ) :=
  Σ e : ZMod a × ZMod b, Fin (shiftMultiplicity a b e)

def shift (a b : ℕ) (δ : ShiftIndex a b) : ZMod a × ZMod b := δ.1

section Counts

variable {a b : ℕ} [NeZero a] [NeZero b]

theorem shiftMultiplicity_cast {a b : ℕ} [NeZero a] [NeZero b] (ha : 2 ≤ a) (hb : 2 ≤ b)
    (e : ZMod a × ZMod b) :
    (shiftMultiplicity a b e : ℤ) = 1 + shiftOmega a b e := by
  let : Fact (1 < a) := ⟨ha⟩
  let : Fact (1 < b) := ⟨hb⟩
  have ha01 : (0 : ZMod a) ≠ 1 := zero_ne_one
  have hb01 : (0 : ZMod b) ≠ 1 := zero_ne_one
  by_cases hα0 : e.1 = 0 <;> by_cases hα1 : e.1 = 1 <;>
    by_cases hξ0 : e.2 = 0 <;> by_cases hξ1 : e.2 = 1 <;>
    simp_all [shiftMultiplicity, shiftOmega]

@[simp] theorem shiftMultiplicity_zero {a b : ℕ} [NeZero a] [NeZero b] :
    shiftMultiplicity a b (0, 0) = 2 := by
  simp [shiftMultiplicity]

theorem sum_shiftMultiplicity_fst (ha : 2 ≤ a) (hb : 2 ≤ b)
    (ξ : ZMod b) :
    ∑ α : ZMod a, shiftMultiplicity a b (α, ξ) = a := by
  have hω : (∑ α : ZMod a, shiftOmega a b (α, ξ)) = 0 := by
    unfold shiftOmega
    dsimp only
    rw [← Finset.sum_mul (Finset.univ : Finset (ZMod a))
      (fun α : ZMod a =>
        (if α = 0 then (1 : ℤ) else 0) -
          (if α = 1 then (1 : ℤ) else 0))
      ((if ξ = 0 then (1 : ℤ) else 0) -
        (if ξ = 1 then (1 : ℤ) else 0))]
    rw [Finset.sum_sub_distrib]
    simp
  have h : (∑ α : ZMod a, (shiftMultiplicity a b (α, ξ) : ℤ)) = a := by
    simp_rw [shiftMultiplicity_cast ha hb]
    rw [Finset.sum_add_distrib, hω]
    simp [ZMod.card]
  exact_mod_cast h

theorem sum_shiftMultiplicity_snd (ha : 2 ≤ a) (hb : 2 ≤ b)
    (α : ZMod a) :
    ∑ ξ : ZMod b, shiftMultiplicity a b (α, ξ) = b := by
  have hω : (∑ ξ : ZMod b, shiftOmega a b (α, ξ)) = 0 := by
    unfold shiftOmega
    dsimp only
    rw [← Finset.mul_sum (Finset.univ : Finset (ZMod b))
      (fun ξ : ZMod b =>
        (if ξ = 0 then (1 : ℤ) else 0) -
          (if ξ = 1 then (1 : ℤ) else 0))
      ((if α = 0 then (1 : ℤ) else 0) -
        (if α = 1 then (1 : ℤ) else 0))]
    rw [Finset.sum_sub_distrib]
    simp
  have h : (∑ ξ : ZMod b, (shiftMultiplicity a b (α, ξ) : ℤ)) = b := by
    simp_rw [shiftMultiplicity_cast ha hb]
    rw [Finset.sum_add_distrib, hω]
    simp [ZMod.card]
  exact_mod_cast h

theorem sum_shiftMultiplicity (ha : 2 ≤ a) (hb : 2 ≤ b) :
    ∑ e : ZMod a × ZMod b, shiftMultiplicity a b e = a * b := by
  rw [Fintype.sum_prod_type]
  simp_rw [sum_shiftMultiplicity_snd ha hb]
  simp [ZMod.card]

theorem card_shiftIndex (ha : 2 ≤ a) (hb : 2 ≤ b) :
    Fintype.card (ShiftIndex a b) = a * b := by
  simpa only [ShiftIndex, Fintype.card_sigma, Fintype.card_fin] using
    sum_shiftMultiplicity ha hb

theorem sum_shift {M : Type uM} [AddCommMonoid M] (f : ZMod a × ZMod b → M) :
    (∑ δ : ShiftIndex a b, f (shift a b δ)) =
      ∑ e : ZMod a × ZMod b, shiftMultiplicity a b e • f e := by
  simp [ShiftIndex, shift, Fintype.sum_sigma]

private def shiftFibreEquiv (e : ZMod a × ZMod b) :
    {δ : ShiftIndex a b // shift a b δ = e} ≃ Fin (shiftMultiplicity a b e) where
  toFun δ := by
    rcases δ with ⟨⟨e', k⟩, h⟩
    change e' = e at h
    subst e'
    exact k
  invFun k := ⟨⟨e, k⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨e', k⟩, h⟩
    change e' = e at h
    subst e'
    rfl
  right_inv _ := rfl

theorem card_shift_fibre (e : ZMod a × ZMod b) :
    Fintype.card {δ : ShiftIndex a b // shift a b δ = e} =
      shiftMultiplicity a b e := by
  simpa using Fintype.card_congr (shiftFibreEquiv e)

private def shiftFibreAEquiv (ξ : ZMod b) :
    {δ : ShiftIndex a b // (shift a b δ).2 = ξ} ≃
      Σ α : ZMod a, Fin (shiftMultiplicity a b (α, ξ)) where
  toFun δ := by
    rcases δ with ⟨⟨⟨α, ξ'⟩, k⟩, h⟩
    change ξ' = ξ at h
    subst ξ'
    exact ⟨α, k⟩
  invFun δ := ⟨⟨(δ.1, ξ), δ.2⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨⟨α, ξ'⟩, k⟩, h⟩
    change ξ' = ξ at h
    subst ξ'
    rfl
  right_inv _ := rfl

private def shiftFibreBEquiv (α : ZMod a) :
    {δ : ShiftIndex a b // (shift a b δ).1 = α} ≃
      Σ ξ : ZMod b, Fin (shiftMultiplicity a b (α, ξ)) where
  toFun δ := by
    rcases δ with ⟨⟨⟨α', ξ⟩, k⟩, h⟩
    change α' = α at h
    subst α'
    exact ⟨ξ, k⟩
  invFun δ := ⟨⟨(α, δ.1), δ.2⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨⟨α', ξ⟩, k⟩, h⟩
    change α' = α at h
    subst α'
    rfl
  right_inv _ := rfl

theorem card_shift_fibreA (ha : 2 ≤ a) (hb : 2 ≤ b) (ξ : ZMod b) :
    Fintype.card {δ : ShiftIndex a b // (shift a b δ).2 = ξ} = a := by
  calc
    _ = Fintype.card (Σ α : ZMod a, Fin (shiftMultiplicity a b (α, ξ))) :=
      Fintype.card_congr (shiftFibreAEquiv ξ)
    _ = a := by
      simpa only [Fintype.card_sigma, Fintype.card_fin] using
        sum_shiftMultiplicity_fst ha hb ξ

theorem card_shift_fibreB (ha : 2 ≤ a) (hb : 2 ≤ b) (α : ZMod a) :
    Fintype.card {δ : ShiftIndex a b // (shift a b δ).1 = α} = b := by
  calc
    _ = Fintype.card (Σ ξ : ZMod b, Fin (shiftMultiplicity a b (α, ξ))) :=
      Fintype.card_congr (shiftFibreBEquiv α)
    _ = b := by
      simpa only [Fintype.card_sigma, Fintype.card_fin] using
        sum_shiftMultiplicity_snd ha hb α

end Counts

section Orderings

variable {a b : ℕ} [NeZero a] [NeZero b] (ha : 2 ≤ a) (hb : 2 ≤ b)

noncomputable def fibreOrderA (ξ : ZMod b) :
    {δ : ShiftIndex a b // (shift a b δ).2 = ξ} ≃ ZMod a :=
  Fintype.equivOfCardEq ((card_shift_fibreA ha hb ξ).trans (ZMod.card a).symm)

noncomputable def fibreOrderB (α : ZMod a) :
    {δ : ShiftIndex a b // (shift a b δ).1 = α} ≃ ZMod b :=
  Fintype.equivOfCardEq ((card_shift_fibreB ha hb α).trans (ZMod.card b).symm)

noncomputable def rhoA (δ : ShiftIndex a b) : ZMod a :=
  fibreOrderA ha hb (shift a b δ).2 ⟨δ, rfl⟩ - (shift a b δ).1

noncomputable def rhoB (δ : ShiftIndex a b) : ZMod b :=
  fibreOrderB ha hb (shift a b δ).1 ⟨δ, rfl⟩ - (shift a b δ).2

theorem fibreOrderA_apply (ξ : ZMod b)
    (δ : {δ : ShiftIndex a b // (shift a b δ).2 = ξ}) :
    fibreOrderA ha hb ξ δ = (shift a b δ.1).1 + rhoA ha hb δ.1 := by
  rcases δ with ⟨δ, h⟩
  subst ξ
  simp [rhoA]

theorem fibreOrderB_apply (α : ZMod a)
    (δ : {δ : ShiftIndex a b // (shift a b δ).1 = α}) :
    fibreOrderB ha hb α δ = (shift a b δ.1).2 + rhoB ha hb δ.1 := by
  rcases δ with ⟨δ, h⟩
  subst α
  simp [rhoB]

noncomputable def shiftOrderA : ShiftIndex a b ≃ ZMod b × ZMod a :=
  (Equiv.sigmaFiberEquiv (fun δ : ShiftIndex a b => (shift a b δ).2)).symm.trans
    (Equiv.sigmaEquivProdOfEquiv (fibreOrderA ha hb))

noncomputable def shiftOrderB : ShiftIndex a b ≃ ZMod a × ZMod b :=
  (Equiv.sigmaFiberEquiv (fun δ : ShiftIndex a b => (shift a b δ).1)).symm.trans
    (Equiv.sigmaEquivProdOfEquiv (fibreOrderB ha hb))

theorem shiftOrderA_apply (δ : ShiftIndex a b) :
    shiftOrderA ha hb δ = ((shift a b δ).2, (shift a b δ).1 + rhoA ha hb δ) := by
  change ((shift a b δ).2, fibreOrderA ha hb (shift a b δ).2 ⟨δ, rfl⟩) = _
  exact congrArg (fun z : ZMod a => ((shift a b δ).2, z))
    (fibreOrderA_apply ha hb (shift a b δ).2 ⟨δ, rfl⟩)

theorem shiftOrderB_apply (δ : ShiftIndex a b) :
    shiftOrderB ha hb δ = ((shift a b δ).1, (shift a b δ).2 + rhoB ha hb δ) := by
  change ((shift a b δ).1, fibreOrderB ha hb (shift a b δ).1 ⟨δ, rfl⟩) = _
  exact congrArg (fun z : ZMod b => ((shift a b δ).1, z))
    (fibreOrderB_apply ha hb (shift a b δ).1 ⟨δ, rfl⟩)

theorem bijective_fibreOrderA (ξ : ZMod b) :
    Function.Bijective (fun δ : {δ : ShiftIndex a b // (shift a b δ).2 = ξ} =>
      (shift a b δ.1).1 + rhoA ha hb δ.1) := by
  have he : (fun δ : {δ : ShiftIndex a b // (shift a b δ).2 = ξ} =>
      (shift a b δ.1).1 + rhoA ha hb δ.1) = (fibreOrderA ha hb ξ) := by
    funext δ
    exact (fibreOrderA_apply ha hb ξ δ).symm
  rw [he]
  exact (fibreOrderA ha hb ξ).bijective

theorem bijective_fibreOrderB (α : ZMod a) :
    Function.Bijective (fun δ : {δ : ShiftIndex a b // (shift a b δ).1 = α} =>
      (shift a b δ.1).2 + rhoB ha hb δ.1) := by
  have he : (fun δ : {δ : ShiftIndex a b // (shift a b δ).1 = α} =>
      (shift a b δ.1).2 + rhoB ha hb δ.1) = (fibreOrderB ha hb α) := by
    funext δ
    exact (fibreOrderB_apply ha hb α δ).symm
  rw [he]
  exact (fibreOrderB ha hb α).bijective

end Orderings

end PeriodicTilingThree

end OAI
