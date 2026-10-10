import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import OAI.NumberTheory.Ostmann.SharpSieve

namespace OAI

namespace Ostmann.SiftedWeights
open Finset

def unitFrequency {ι : Type*} (q : ι → ℕ) [∀ i, NeZero (q i)] {Q : ℕ}
    (hQ : ∀ i, q i ≤ Q) (x : Σ i, (ZMod (q i))ˣ) : SharpSieve.ReducedFrequency Q :=
  ⟨(q x.1, (x.2 : ZMod (q x.1)).val),
    NeZero.pos _, hQ x.1, ZMod.val_lt _, ZMod.val_coe_unit_coprime x.2⟩

theorem unitFrequency_injective {ι : Type*} (q : ι → ℕ) [∀ i, NeZero (q i)] {Q : ℕ}
    (hQ : ∀ i, q i ≤ Q) (hq : Function.Injective q) :
    Function.Injective (unitFrequency q hQ) := by
  rintro ⟨i, u⟩ ⟨k, v⟩ heq
  have hik : q i = q k := congrArg (fun f => f.val.1) heq
  have hi := hq hik
  subst k
  have huv : (u : ZMod (q i)).val = (v : ZMod (q i)).val :=
    congrArg (fun f => f.val.2) heq
  have hu : u = v := Units.ext (ZMod.val_injective (q i) huv)
  subst v
  rfl

theorem primitive_energy_sum_le {ι : Type*} [Fintype ι]
    (q : ι → ℕ) [∀ i, NeZero (q i)] {Q : ℕ}
    (hbound : ∀ i, q i ≤ Q) (hq : Function.Injective q)
    (U : Finset ℕ) (hU : ∀ n ∈ U, n ≤ Q^2) (hQ : 0 < Q) :
    (∑ i, ∑ u : (ZMod (q i))ˣ,
      ‖normalizedExpSum U (((u : ZMod (q i)).val : ℝ)/(q i))‖^2) ≤
      96*(Q : ℝ)^2/(U.card : ℝ) := by
  classical
  let F : SharpSieve.ReducedFrequency Q → ℝ := fun f => ‖normalizedExpSum U f.value‖^2
  let φ := unitFrequency q hbound
  have hinj : Function.Injective φ := unitFrequency_injective q hbound hq
  have hs : (∑ x : (Σ i, (ZMod (q i))ˣ), F (φ x)) ≤
      ∑ f : SharpSieve.ReducedFrequency Q, F f := by
    calc
      (∑ x : (Σ i, (ZMod (q i))ˣ), F (φ x)) =
          ∑ f ∈ Finset.univ.image φ, F f :=
        (Finset.sum_image (fun _ _ _ _ h => hinj h)).symm
      _ ≤ ∑ f : SharpSieve.ReducedFrequency Q, F f :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun f _ _ => sq_nonneg _)
  have hh := hs.trans (sum_normalizedExpSum_sq_le_of_le_sq U Q hU hQ)
  simpa only [Fintype.sum_sigma, F, φ, unitFrequency,
    SharpSieve.ReducedFrequency.value, SharpSieve.ReducedFrequency.numerator,
    SharpSieve.ReducedFrequency.denominator] using hh

end Ostmann.SiftedWeights

end OAI
