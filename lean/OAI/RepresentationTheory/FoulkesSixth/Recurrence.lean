import Mathlib
import OAI.RepresentationTheory.FoulkesSixth.NewtonUniqueness
import OAI.RepresentationTheory.FoulkesSixth.FastLookupExact
import OAI.RepresentationTheory.FoulkesSixth.CompositionEnumeration

namespace OAI

noncomputable section

namespace Foulkes.Checker
open Finset Foulkes.Enumeration Foulkes.FastLookup Foulkes.Lookup Foulkes.Strips

def checkedSum {α : Type*} (f : α → Option ℤ) : List α → Option ℤ
  | [] => some 0
  | a::l => do
      let x ← f a
      let y ← checkedSum f l
      some (x+y)

lemma checkedSum_sound {α : Type*} (f : α → Option ℤ) (g : α → ℤ)
    (l : List α) (h : ∀ a ∈ l, ∀ z, f a = some z → z = g a)
    (z : ℤ) (hz : checkedSum f l = some z) : z = (l.map g).sum := by
  induction l generalizing z with
  | nil => simpa [checkedSum] using hz.symm
  | cons a l ih =>
    cases hx : f a with
    | none => simp [checkedSum, hx] at hz
    | some x =>
      cases hy : checkedSum f l with
      | none => simp [checkedSum, hx, hy] at hz
      | some y =>
        have hh := ih (fun b hb => h b (List.mem_cons_of_mem a hb)) y hy
        have ha := h a (List.mem_cons_self ..) x hx
        simpa [checkedSum, hx, hy, hh, ha] using hz.symm

lemma sum_compositions (n d : ℕ) (f : (Fin n → ℕ) → ℤ) :
    ((compositions n d).map f).sum = ∑ a : Foulkes.Complete.Degree (Fin n) d,
      f (fun j => a.val j) := by
  classical
  rw [← List.sum_toFinset f (nodup_compositions n d)]
  change (∑ v ∈ compositionSet n d, f v) = _
  rw [← Finset.sum_attach (compositionSet n d) f]
  exact (Equiv.sum_comp (degreeComposition n d) (fun v => f v.val)).symm

def numerator {n : ℕ} (T : ℕ → (Fin n → ℕ) → ℤ) (b : ℕ) (mu : Fin n → ℕ) : Option ℤ :=
  checkedSum (fun i => checkedSum (fun v => checkedLookup (T (b-i))
    (fun j => (shifted mu j : ℤ) - (i : ℤ)*v j)) (compositions n 6)) (List.range' 1 b)

lemma numerator_sound {n : ℕ} (T : ℕ → (Fin n → ℕ) → ℤ)
    (b : ℕ) (mu : Fin n → ℕ) (z : ℤ) (hz : numerator T b mu = some z) :
    z = ∑ i ∈ Finset.Icc 1 b, ∑ d : Foulkes.Complete.Degree (Fin n) 6,
      signedLookup (T (b-i)) (fun j => (shifted mu j : ℤ) - (i : ℤ)*d.val j) := by
  have hinner (i : ℕ) (w : ℤ)
      (hw : checkedSum (fun v => checkedLookup (T (b-i))
        (fun j => (shifted mu j : ℤ) - (i : ℤ)*v j)) (compositions n 6) = some w) :
      w = ∑ d : Foulkes.Complete.Degree (Fin n) 6,
        signedLookup (T (b-i)) (fun j => (shifted mu j : ℤ) - (i : ℤ)*d.val j) := by
    calc
      w = ((compositions n 6).map (fun v => signedLookup (T (b-i))
        (fun j => (shifted mu j : ℤ) - (i : ℤ)*v j))).sum :=
          checkedSum_sound _ _ _ (fun v hv w hw => checkedLookup_exact _ _ w hw) w hw
      _ = _ := sum_compositions n 6 _
  have hh := checkedSum_sound _ _ (List.range' 1 b) (fun i hi => hinner i) z hz
  rw [← List.sum_toFinset _ (List.nodup_range' (s := 1) (n := b))] at hh
  have hr : (List.range' 1 b).toFinset = Finset.Icc 1 b := by
    ext i
    simp only [List.mem_toFinset, List.mem_range'_1, Finset.mem_Icc]
    omega
  rw [hr] at hh
  exact hh

def checkEntry {n : ℕ} (T : ℕ → (Fin n → ℕ) → ℤ) (b : ℕ) (mu : Fin n → ℕ) : Bool :=
  match numerator T b mu with
  | none => false
  | some z => decide ((b : ℤ)*T b mu = z)

lemma checkEntry_sound {n : ℕ} (T : ℕ → (Fin n → ℕ) → ℤ)
    (b : ℕ) (mu : Fin n → ℕ) (h : checkEntry T b mu = true) :
    (b : ℤ)*T b mu = ∑ i ∈ Finset.Icc 1 b, ∑ d : Foulkes.Complete.Degree (Fin n) 6,
      signedLookup (T (b-i)) (fun j => (shifted mu j : ℤ) - (i : ℤ)*d.val j) := by
  unfold checkEntry at h
  cases hn : numerator T b mu with
  | none => simp [hn] at h
  | some z =>
    rw [hn, decide_eq_true_eq] at h
    exact h.trans (numerator_sound T b mu z hn)

theorem checked_table_unique (n B : ℕ) (T : ℕ → (Fin n → ℕ) → ℤ)
    (hzero : ∀ mu, Antitone mu → (∑ j, mu j = 0) → T 0 mu = 1)
    (hcheck : ∀ b, 1 ≤ b → b ≤ B → ∀ mu, Antitone mu → (∑ j, mu j = 6*b) →
      checkEntry T b mu = true) :
    ∀ b, b ≤ B → ∀ mu, Antitone mu → (∑ j, mu j = 6*b) → T b mu = Q n b mu := by
  apply target_table_unique n B T hzero
  intro b hb hB mu hm hs
  exact checkEntry_sound T b mu (hcheck b hb hB mu hm hs)

end Foulkes.Checker

end

end OAI
