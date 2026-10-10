import OAI.Combinatorics.BalancedRyser.Profiles.ProfileClassLimits
import OAI.Combinatorics.BalancedRyser.Profiles.ProfileDetectionSource
import OAI.Combinatorics.BalancedRyser.Profiles.UniformDetectionMargin

namespace OAI

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace Balanced.ProfileClassMargin

open ProfileDetection ProfileDetectionLimit ProfileParameterLaw

universe u

abbrev Test := ℕ → ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
  Finset (Line F) → Finset (Line F) → ℝ

def cutoffMass (P : Profile) (νD νC : FiniteMeasure Profile) (n : ℕ) : ℝ :=
  ((νD : Measure Profile).prod (parameterLaw 1)).real
      (cutoffDetection Prod.snd (dDiscrepancy P) n) +
    ((νC : Measure Profile).prod (parameterLaw (Real.sqrt 2))).real
      (cutoffDetection Prod.snd (cDiscrepancy P) n)

def LimitLowerBound (A : ProfileClass.{u}) (test : Test.{u}) : Prop :=
  ∀ (F : ℕ → Type u) [∀ t, Field (F t)] [∀ t, Fintype (F t)]
    [∀ t, DecidableEq (F t)] (D C : ∀ t, Finset (Line (F t))),
    (∀ t, A (F t) (D t) (C t)) →
    Tendsto (fun t => Fintype.card (F t)) atTop atTop →
    ∀ (c : ℝ) (P : Profile) (νD νC : FiniteMeasure Profile),
      ProfileSequenceLimit D C c P νD νC →
      ∀ (n : ℕ) (r : ℝ), r < cutoffMass P νD νC n →
        ∀ᶠ t in atTop, r < test n (F t) (D t) (C t)

private structure Object (A : ProfileClass.{u}) where
  Carrier : Type u
  field : Field Carrier
  fintype : Fintype Carrier
  decEq : DecidableEq Carrier
  D : Finset (Line Carrier)
  C : Finset (Line Carrier)
  mem : @A Carrier field fintype decEq D C

private instance {A : ProfileClass.{u}} (x : Object A) : Field x.Carrier := x.field
private instance {A : ProfileClass.{u}} (x : Object A) : Fintype x.Carrier := x.fintype
private instance {A : ProfileClass.{u}} (x : Object A) : DecidableEq x.Carrier := x.decEq

theorem exists_uniform_margin
    (k : ℕ) (A : ProfileClass.{u})
    (hvalid : ProfileClassValid k A)
    (hgap : ∃ a : ℝ, 0 < a ∧ ProfileClassSizeGap a A)
    (hvisible : ProfileVisibleExcess A)
    (test : Test.{u})
    (hmono : ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
      (D C : Finset (Line F)), A F D C → Monotone (fun n => test n F D C))
    (hlower : LimitLowerBound A test) :
    ∃ n : ℕ, ∃ ξ : ℝ, 0 < ξ ∧ ∃ N : ℕ,
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
        (D C : Finset (Line F)), A F D C → N ≤ Fintype.card F →
        (C.card : ℝ) / (Fintype.card F : ℝ) + ξ ≤ test n F D C := by
  obtain ⟨a, _ha, hsize⟩ := hgap
  let order : Object A → ℕ := fun x => Fintype.card x.Carrier
  let tests : ℕ → Object A → ℝ := fun n x =>
    test n x.Carrier x.D x.C - (x.C.card : ℝ) / (Fintype.card x.Carrier : ℝ)
  have hm : ∀ x : Object A, Monotone (fun n => tests n x) := by
    intro x i j hij
    exact sub_le_sub_right (hmono x.Carrier x.D x.C x.mem hij) _
  have hs : ∀ xs : ℕ → Object A,
      Tendsto (fun t => order (xs t)) atTop atTop →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ n : ℕ, ∃ ε : ℝ,
        0 < ε ∧ ∀ᶠ t in atTop, ε ≤ tests n (xs (φ t)) := by
    intro xs horders
    let F := fun t => (xs t).Carrier
    let D : ∀ t, Finset (Line (F t)) := fun t => (xs t).D
    let C : ∀ t, Finset (Line (F t)) := fun t => (xs t).C
    have hclass : ∀ t, A (F t) (D t) (C t) := fun t => (xs t).mem
    obtain ⟨c, _hc, _hsizec, P, _hP, νD, νC, φ, hφ, hclass', hq', hlim, hex⟩ :=
      exists_visible_profile_subsequence k hvalid hsize hvisible D C hclass horders
    have hpairs : ∀ t, IsProfilePair k (D (φ t)) (C (φ t)) :=
      fun t => hvalid _ _ _ (hclass' t)
    obtain ⟨n, hn⟩ := ProfileDetectionSource.exists_cutoff_of_visible_excess
      k (fun t => D (φ t)) (fun t => C (φ t)) hpairs hlim hex
    change c < cutoffMass P νD νC n at hn
    let ε : ℝ := (cutoffMass P νD νC n - c) / 4
    have hε : 0 < ε := by dsimp [ε]; linarith
    have htest : ∀ᶠ t in atTop, c + 3 * ε < test n (F (φ t)) (D (φ t)) (C (φ t)) :=
      hlower (fun t => F (φ t)) (fun t => D (φ t)) (fun t => C (φ t))
        hclass' hq' c P νD νC hlim n (c + 3 * ε) (by dsimp [ε]; linarith)
    have hratio : ∀ᶠ t in atTop,
        ((C (φ t)).card : ℝ) / (Fintype.card (F (φ t)) : ℝ) < c + ε :=
      hlim.1.eventually_lt_const (by linarith)
    refine ⟨φ, hφ, n, ε, hε, ?_⟩
    filter_upwards [htest, hratio] with t ht hr
    change ε ≤ test n (F (φ t)) (D (φ t)) (C (φ t)) -
      ((C (φ t)).card : ℝ) / (Fintype.card (F (φ t)) : ℝ)
    linarith
  obtain ⟨n, ξ, hξ, N, hN⟩ :=
    UniformDetectionMargin.exists_eventual_uniform_pos order tests hm hs
  refine ⟨n, ξ, hξ, N, ?_⟩
  intro F _ _ _ D C hA hq
  let x : Object A := ⟨F, inferInstance, inferInstance, inferInstance, D, C, hA⟩
  have hx := hN x hq
  change ξ ≤ test n F D C - (C.card : ℝ) / (Fintype.card F : ℝ) at hx
  linarith

theorem exists_uniform_count_margin
    (k : ℕ) (A : ProfileClass.{u})
    (hvalid : ProfileClassValid k A)
    (hgap : ∃ a : ℝ, 0 < a ∧ ProfileClassSizeGap a A)
    (hvisible : ProfileVisibleExcess A)
    (count : Test.{u})
    (hmono : ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
      (D C : Finset (Line F)), A F D C → Monotone (fun n => count n F D C))
    (hlower : LimitLowerBound A (fun n F _ _ _ D C =>
      count n F D C / (Fintype.card F : ℝ))) :
    ∃ n : ℕ, ∃ ξ : ℝ, 0 < ξ ∧ ∃ N : ℕ,
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
        (D C : Finset (Line F)), A F D C → N ≤ Fintype.card F →
        (C.card : ℝ) + ξ * (Fintype.card F : ℝ) ≤ count n F D C := by
  obtain ⟨n, ξ, hξ, N, hN⟩ := exists_uniform_margin k A hvalid hgap hvisible
    (fun n F _ _ _ D C => count n F D C / (Fintype.card F : ℝ))
    (by
      intro F _ _ _ D C hA i j hij
      exact div_le_div_of_nonneg_right (hmono F D C hA hij) (Nat.cast_nonneg _)) hlower
  refine ⟨n, ξ, hξ, N, ?_⟩
  intro F _ _ _ D C hA hq
  have hp : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos (α := F)
  have h := (le_div_iff₀ hp).mp (hN F D C hA hq)
  simpa only [add_mul, div_mul_cancel₀ _ hp.ne'] using h

end Balanced.ProfileClassMargin

end

end OAI
