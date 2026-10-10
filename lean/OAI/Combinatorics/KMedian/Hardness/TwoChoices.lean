import Mathlib

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Coverage
open Finset

theorem card_two_constraints {U : Type} [Fintype U] [DecidableEq U]
    (C : U → Type) [∀ u, Fintype (C u)] [∀ u, DecidableEq (C u)] (u v : U) (huv : u ≠ v)
    (a : C u) (b : C v) :
    Fintype.card (∀ w, C w) ≤ Fintype.card (C u) * Fintype.card (C v) *
      Fintype.card {f : ∀ w, C w // f u = a ∧ f v = b} := by
  classical
  let fill (f : ∀ w, C w) := Function.update (Function.update f u a) v b
  have hf (f : ∀ w, C w) : fill f u = a ∧ fill f v = b := by
    simp [fill, Function.update_of_ne huv]
  let enc (f : ∀ w, C w) : (C u × C v) × {f : ∀ w, C w // f u = a ∧ f v = b} :=
    ((f u,f v),⟨fill f,hf f⟩)
  have hinj : Function.Injective enc := by
    intro f g h
    have hu : f u = g u := congrArg (fun z => z.1.1) h
    have hv : f v = g v := congrArg (fun z => z.1.2) h
    have hh : fill f = fill g := congrArg (fun z => z.2.val) h
    funext w
    by_cases hw : w = u
    · subst w; exact hu
    by_cases hw' : w = v
    · subst w; exact hv
    have he := congrFun hh w
    simpa [fill,Function.update_of_ne hw,Function.update_of_ne hw'] using he
  have hh := Fintype.card_le_of_injective enc hinj
  simpa only [Fintype.card_prod] using hh

theorem two_choice_event_count {U V : Type} [Fintype U] [Fintype V]
    [DecidableEq U] [DecidableEq V] (C : U → Type) [∀u, Fintype (C u)]
    (t : ℕ) (hsize : ∀ u, Fintype.card (C u) ≤ t)
    (events : (∀u, C u) → Finset V) (charged : Finset V)
    (hcharge : ∀ v ∈ charged, ∃ u w : U, u ≠ w ∧ ∃ a : C u, ∃ b : C w,
      ∀ f : ∀u, C u, f u = a → f w = b → v ∈ events f) :
    charged.card * Fintype.card (∀u, C u) ≤ t^2 * ∑ f, (events f).card := by
  classical
  have hpoint (v : V) (hv : v ∈ charged) :
      Fintype.card (∀u, C u) ≤ t^2 * (univ.filter (fun f : ∀u, C u => v ∈ events f)).card := by
    obtain ⟨u,w,huw,a,b,h⟩ := hcharge v hv
    have hc := card_two_constraints C u w huw a b
    have hsub : Fintype.card {f : ∀u, C u // f u = a ∧ f w = b} ≤
        Fintype.card {f : ∀u, C u // v ∈ events f} := by
      exact Fintype.card_le_of_injective
        (fun f => ⟨f.val,h f.val f.property.1 f.property.2⟩)
        (fun f g hh => Subtype.ext
          (congrArg (fun z : {f : ∀u, C u // v ∈ events f} => z.val) hh))
    have hm : Fintype.card (C u)*Fintype.card (C w) ≤ t^2 := by
      simpa only [pow_two] using Nat.mul_le_mul (hsize u) (hsize w)
    calc
      _ ≤ _ := hc
      _ ≤ t^2 * Fintype.card {f : ∀u, C u // v ∈ events f} := Nat.mul_le_mul hm hsub
      _ = _ := by rw [Fintype.card_subtype]
  have hd : (∑ v, (univ.filter (fun f : ∀u, C u => v ∈ events f)).card) =
      ∑ f, (events f).card := by
    simp only [card_filter]
    rw [sum_comm]
    simp only [sum_boole,filter_mem_eq_inter,univ_inter,Nat.cast_id]
  calc
    _ = ∑ v ∈ charged, Fintype.card (∀u, C u) := by simp
    _ ≤ ∑ v ∈ charged, t^2*(univ.filter (fun f : ∀u, C u => v ∈ events f)).card :=
      sum_le_sum hpoint
    _ = t^2 * ∑ v ∈ charged, (univ.filter (fun f : ∀u, C u => v ∈ events f)).card := by
      rw [mul_sum]
    _ ≤ t^2 * ∑ v, (univ.filter (fun f : ∀u, C u => v ∈ events f)).card := by
      exact Nat.mul_le_mul_left _ (sum_le_sum_of_subset (subset_univ _))
    _ = _ := by rw [hd]

theorem two_choice_event_bound {U V : Type} [Fintype U] [Fintype V]
    [DecidableEq U] [DecidableEq V] (C : U → Type) [∀u, Fintype (C u)]
    [∀u, Nonempty (C u)] (t : ℕ) (hsize : ∀ u, Fintype.card (C u) ≤ t)
    (events : (∀u, C u) → Finset V) (charged : Finset V)
    (hcharge : ∀ v ∈ charged, ∃ u w : U, u ≠ w ∧ ∃ a : C u, ∃ b : C w,
      ∀ f : ∀u, C u, f u = a → f w = b → v ∈ events f)
    (γ : ℝ) (hsound : ∀ f, ((events f).card:ℝ) ≤ γ * Fintype.card V) :
    (charged.card:ℝ) ≤ (t:ℝ)^2 * γ * Fintype.card V := by
  classical
  have hc := two_choice_event_count C t hsize events charged hcharge
  have hr : (charged.card:ℝ) * Fintype.card (∀u, C u) ≤
      (t:ℝ)^2 * ∑ f, ((events f).card:ℝ) := by exact_mod_cast hc
  have hs := sum_le_sum (s := (univ : Finset (∀u, C u))) (fun f _ => hsound f)
  simp only [sum_const,card_univ,nsmul_eq_mul] at hs
  have hm := mul_le_mul_of_nonneg_left hs (sq_nonneg (t:ℝ))
  have hp : (0:ℝ) < Fintype.card (∀u, C u) := by
    exact_mod_cast Fintype.card_pos
  nlinarith

theorem two_choice_or_trivial_event_bound {U V : Type} [Fintype U] [Fintype V]
    [DecidableEq U] [DecidableEq V] (C : U → Type) [∀u, Fintype (C u)]
    [∀u, Nonempty (C u)] {t : ℕ} (ht : 1 ≤ t)
    (hsize : ∀ u, Fintype.card (C u) ≤ t)
    (events : (∀u, C u) → Finset V) (charged : Finset V)
    (hcharge : ∀ v ∈ charged, (∀ f, v ∈ events f) ∨
      ∃ u w : U, u ≠ w ∧ ∃ a : C u, ∃ b : C w,
        ∀ f : ∀u, C u, f u = a → f w = b → v ∈ events f)
    (γ : ℝ) (hsound : ∀ f, ((events f).card:ℝ) ≤ γ * Fintype.card V) :
    (charged.card:ℝ) ≤ (t:ℝ)^2 * γ * Fintype.card V := by
  classical
  let D : U ⊕ Bool → Type := Sum.elim C (fun _ => Unit)
  let (u : U ⊕ Bool) : Fintype (D u) := by cases u <;> dsimp [D] <;> infer_instance
  let (u : U ⊕ Bool) : Nonempty (D u) := by cases u <;> dsimp [D] <;> infer_instance
  have hD (u : U ⊕ Bool) : Fintype.card (D u) ≤ t := by
    cases u with
    | inl u => exact hsize u
    | inr b => simpa [D] using ht
  let ev (f : ∀u, D u) := events (fun u => f (Sum.inl u))
  apply two_choice_event_bound D t hD ev charged _ γ (fun f => hsound _)
  intro v hv
  rcases hcharge v hv with h | ⟨u,w,huw,a,b,h⟩
  · refine ⟨Sum.inr false,Sum.inr true,by simp,(),(),?_⟩
    intro f _ _
    exact h _
  · refine ⟨Sum.inl u,Sum.inl w,(fun hh => huw (Sum.inl.inj hh)),a,b,?_⟩
    intro f hf hg
    exact h (fun u => f (Sum.inl u)) hf hg

end MetricKMedian.Coverage

end Inline_PCPInherited

end OAI
