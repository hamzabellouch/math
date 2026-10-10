import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport

namespace OAI

namespace SiegelZeros

section
namespace WeightedTorusJets

theorem exists_weight_sorted_equiv {α : Type*} [Infinite α] [Encodable α]
    (w : α → ℕ) (hfinite : ∀ B : ℕ, {a : α | w a ≤ B}.Finite) :
    ∃ e : ℕ ≃ α, Monotone (w ∘ e) := by
  classical
  let pred : α → α → Prop := fun a b =>
    w a < w b ∨ (w a = w b ∧ Encodable.encode a < Encodable.encode b)
  let F : α → Finset α := fun b => (hfinite (w b)).toFinset.filter (fun a => pred a b)
  have hmem : ∀ a b, a ∈ F b ↔ pred a b := by
    intro a b
    simp only [F, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, pred]
    omega
  let rank : α → ℕ := fun a => (F a).card
  have hrank (a b : α) (hab : pred a b) : rank a < rank b := by
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    constructor
    · intro c hc
      apply (hmem c b).mpr
      have hca := (hmem c a).mp hc
      dsimp only [pred] at *
      omega
    · intro hEq
      have ha : a ∈ F b := (hmem a b).mpr hab
      rw [← hEq] at ha
      have h := (hmem a a).mp ha
      simp only [pred, lt_self_iff_false, and_false, or_self] at h
  have hinj : Function.Injective rank := by
    intro a b hab
    by_contra hne
    have hcode : Encodable.encode a ≠ Encodable.encode b := fun h =>
      hne (Encodable.encode_injective h)
    have horder : pred a b ∨ pred b a := by
      dsimp only [pred]
      omega
    rcases horder with h | h
    · have := hrank a b h
      omega
    · have := hrank b a h
      omega
  have hweight (a b : α) (hab : rank a ≤ rank b) : w a ≤ w b := by
    by_contra h
    have hlt := hrank b a (Or.inl (Nat.lt_of_not_ge h))
    omega
  let : Infinite (Set.range rank) := (Set.infinite_range_of_injective hinj).to_subtype
  let o : ℕ ≃o Set.range rank := Nat.Subtype.orderIsoOfNat (Set.range rank)
  let r : α ≃ Set.range rank := Equiv.ofInjective rank hinj
  let e : ℕ ≃ α := o.toEquiv.trans r.symm
  have he (i : ℕ) : rank (e i) = (o i : ℕ) :=
    congrArg Subtype.val (r.apply_symm_apply (o i))
  refine ⟨e, ?_⟩
  intro i j hij
  apply hweight
  rw [he, he]
  exact o.monotone hij

theorem exists_global_weight_sorted_jet_equiv (H : ℕ) (hH : 0 < H) :
    ∃ e : ℕ ≃ (Fin 3 → ℕ),
      Monotone (fun i => (e i) 0 + H * (e i) 1 + H * (e i) 2) := by
  let : Infinite (Fin 3 → ℕ) := Infinite.of_injective
    (fun n : ℕ => fun _ : Fin 3 => n) (fun _ _ h => congrFun h 0)
  apply exists_weight_sorted_equiv (fun a : Fin 3 → ℕ => a 0 + H * a 1 + H * a 2)
  intro B
  apply (Set.Finite.pi' (fun _ : Fin 3 => Set.finite_Iic B)).subset
  intro a ha i
  change a 0 + H * a 1 + H * a 2 ≤ B at ha
  have h1 : a 1 ≤ H * a 1 := Nat.le_mul_of_pos_left _ hH
  have h2 : a 2 ≤ H * a 2 := Nat.le_mul_of_pos_left _ hH
  change a i ≤ B
  fin_cases i <;> dsimp <;> omega

noncomputable def globalWeightSortedJetEquiv (H : ℕ) (hH : 0 < H) :
    ℕ ≃ (Fin 3 → ℕ) := (exists_global_weight_sorted_jet_equiv H hH).choose

theorem globalWeightSortedJetEquiv_monotone (H : ℕ) (hH : 0 < H) :
    Monotone (fun i => (globalWeightSortedJetEquiv H hH i) 0 +
      H * (globalWeightSortedJetEquiv H hH i) 1 +
      H * (globalWeightSortedJetEquiv H hH i) 2) :=
  (exists_global_weight_sorted_jet_equiv H hH).choose_spec

end WeightedTorusJets

end

end SiegelZeros

end OAI
