import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.BetaZ

namespace OAI

noncomputable section
open scoped BigOperators
open Finset

namespace OrdinaryCorrelations.SignedTrace

structure ClosedLine (h ℓ : ℕ) where
  offset : Fin (ℓ + 1) → ℤ
  label : Fin ℓ → ℕ
  sign : Fin ℓ → ℤ
  label_pos : ∀ i, 0 < label i
  sign_mem : ∀ i, sign i = -1 ∨ sign i = 1
  start_zero : offset 0 = 0
  end_zero : offset (Fin.last ℓ) = 0
  step : ∀ i, offset i.succ - offset i.castSucc = sign i * h * label i

namespace ClosedLine
open Classical
variable {h ℓ : ℕ}

def treeSteps (w : ClosedLine h ℓ) : Finset (Fin ℓ) :=
  univ.filter (fun i => ∀ j : Fin (ℓ+1), j.val ≤ i.val → w.offset j ≠ w.offset i.succ)

def children (w : ClosedLine h ℓ) (v : ℤ) : ℕ :=
  ((w.treeSteps).filter (fun i => w.offset i.castSucc = v)).card

def NoReturnIncidence (w : ClosedLine h ℓ) (v : ℤ) : Prop :=
  ∀ i, i ∉ w.treeSteps → w.offset i.castSucc ≠ v ∧ w.offset i.succ ≠ v

def Good (w : ClosedLine h ℓ) (e : Fin ℓ) : Prop :=
  e ∈ w.treeSteps ∧ w.children (w.offset e.castSucc) = 1 ∧
    w.children (w.offset e.succ) = 1 ∧ w.offset e.castSucc ≠ 0 ∧
    w.NoReturnIncidence (w.offset e.castSucc) ∧
    w.NoReturnIncidence (w.offset e.succ)

def Uncorrupted (w : ClosedLine h ℓ) (p : ℕ) (e : Fin ℓ) : Prop :=
  ∀ j : Fin (ℓ+1), (w.offset j : ZMod p) = (w.offset e.castSucc : ZMod p) →
    w.offset j = w.offset e.castSucc ∨ w.offset j = w.offset e.succ

def departures (w : ClosedLine h ℓ) : Fin ℓ → ℤ := fun i => w.offset i.castSucc

lemma endpoints_ne (w : ClosedLine h ℓ) (hh : 0 < h) (e : Fin ℓ) :
    w.offset e.castSucc ≠ w.offset e.succ := by
  intro heq
  have hstep := w.step e
  rw [heq, sub_self] at hstep
  have hh' : (0 : ℤ) < h := by exact_mod_cast hh
  have hd' : (0 : ℤ) < w.label e := by exact_mod_cast w.label_pos e
  rcases w.sign_mem e with hs | hs <;> rw [hs] at hstep <;> nlinarith

lemma label_residue_eq (w : ClosedLine h ℓ) {p : ℕ} (e : Fin ℓ) (hp : p ∣ w.label e) :
    (w.offset e.succ : ZMod p) = (w.offset e.castSucc : ZMod p) := by
  have hd : (w.label e : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hp
  have hs := congrArg (fun z : ℤ => (z : ZMod p)) (w.step e)
  push_cast at hs
  rw [hd, mul_zero] at hs
  exact sub_eq_zero.mp hs

lemma all_departures_eq_children (w : ClosedLine h ℓ) (v : ℤ)
    (hr : w.NoReturnIncidence v) :
    ((univ : Finset (Fin ℓ)).filter (fun i => w.departures i = v)).card =
      w.children v := by
  have hs : (univ.filter (fun i => w.departures i = v)) =
      w.treeSteps.filter (fun i => w.offset i.castSucc = v) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change w.offset i.castSucc = v ↔ i ∈ w.treeSteps ∧ w.offset i.castSucc = v
    constructor
    · intro hi
      refine ⟨?_, hi⟩
      by_contra hn
      exact (hr i hn).1 hi
    · exact And.right
  exact congrArg Finset.card hs

theorem good_singleton_two_departures (w : ClosedLine h ℓ) (hh : 0 < h)
    {p : ℕ} [NeZero p] (e : Fin ℓ) (hp : p ∣ w.label e)
    (hg : w.Good e) (hunc : w.Uncorrupted p e) :
    departureCount w.departures (activeResidue w.departures e : ZMod p) = 2 := by
  let u := w.offset e.castSucc
  let v := w.offset e.succ
  have huv : u ≠ v := w.endpoints_ne hh e
  have hres : (v : ZMod p) = (u : ZMod p) := w.label_residue_eq e hp
  let su : Finset (Fin ℓ) := univ.filter (fun j => w.departures j = u)
  let sv : Finset (Fin ℓ) := univ.filter (fun j => w.departures j = v)
  have hsu : su.card = 1 := (w.all_departures_eq_children u hg.2.2.2.2.1).trans hg.2.1
  have hsv : sv.card = 1 := (w.all_departures_eq_children v hg.2.2.2.2.2).trans hg.2.2.1
  have hdis : Disjoint su sv := disjoint_left.mpr (by
    intro j hu hv
    exact huv ((mem_filter.mp hu).2.symm.trans (mem_filter.mp hv).2))
  have hset : univ.filter (fun j : Fin ℓ =>
      (activeResidue w.departures e : ZMod p) = activeResidue w.departures j) = su ∪ sv := by
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_union, su, sv]
    constructor
    · intro ha
      apply hunc j.castSucc
      simpa only [activeResidue, departures, neg_inj] using ha.symm
    · rintro (hu | hv)
      · simp only [activeResidue, hu]
        rfl
      · simp only [activeResidue, hv]
        change -(u : ZMod p) = -(v : ZMod p)
        rw [hres]
  rw [departureCount, hset, card_union_of_disjoint hdis, hsu, hsv]

theorem good_center_prime_mean (w : ClosedLine h ℓ) (hh : 0 < h)
    {p : ℕ} [NeZero p] (e : Fin ℓ)
    (he : ∀ i, p ∣ w.label i ↔ i = e)
    (hg : w.Good e) (hunc : w.Uncorrupted p e) (hlarge : 2 * (ℓ+1) ≤ p) :
    0 ≤ primeMean (p := p) (centerPrimeFactor w.departures w.label) ∧
      |primeMean (p := p) (centerPrimeFactor w.departures w.label)| ≤ theta / (2*p) := by
  exact source_good_singleton_integral w.departures w.label e he
    (w.good_singleton_two_departures hh e ((he e).mpr rfl) hg hunc) hlarge

end ClosedLine

end OrdinaryCorrelations.SignedTrace

end

end OAI
