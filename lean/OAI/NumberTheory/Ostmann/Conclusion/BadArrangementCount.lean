import OAI.NumberTheory.Ostmann.Conclusion.ComponentFactorials

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Conclusion

def componentIndex {r m : ℕ} (σ : Equiv.Perm (Fin r × Fin m)) :
    OverlapComponent σ ↪ Fin r where
  toFun i := ⟨(Fintype.equivFin (OverlapComponent σ) i).val,
    lt_of_lt_of_le (Fintype.equivFin _ i).isLt (overlapComponent_card_le σ)⟩
  inj' := by
    intro i j h
    apply (Fintype.equivFin (OverlapComponent σ)).injective
    apply Fin.ext
    exact congrArg (fun x : Fin r => x.val) h

def arrangementLabels {r m : ℕ} (hm : 0 < m) (σ : Equiv.Perm (Fin r × Fin m)) :
    (Fin r → Fin r) × (Fin r → Fin r) :=
  (fun a => componentIndex σ (leftComponent σ a),
   fun b => componentIndex σ (rightComponent σ hm b))

def matchingOfSameLabels {r m : ℕ} (hm : 0 < m)
    (σ τ : Equiv.Perm (Fin r × Fin m)) (h : arrangementLabels hm τ = arrangementLabels hm σ) :
    PartitionMatching (fun x : Fin r × Fin m => leftComponent σ x.1)
      (fun x : Fin r × Fin m => rightComponent σ hm x.1) := by
  refine ⟨τ,fun x => ?_⟩
  apply (componentIndex σ).injective
  have hl := congrFun (congrArg Prod.fst h) x.1
  have hr := congrFun (congrArg Prod.snd h) (τ x).1
  change componentIndex τ (leftComponent τ x.1) =
    componentIndex σ (leftComponent σ x.1) at hl
  change componentIndex τ (rightComponent τ hm (τ x).1) =
    componentIndex σ (rightComponent σ hm (τ x).1) at hr
  rw [← hl, ← hr, ← slot_component τ hm]

def badArrangementCount (r m : ℕ) : ℕ :=
  Nat.card {σ : Equiv.Perm (Fin r × Fin m) // BadArrangement σ}

theorem badArrangementCount_le {r m : ℕ} (hr : 0 < r) (hm : 0 < m) :
    (badArrangementCount r m : ℝ) ≤
      (r : ℝ)^(2*r) * ((m.factorial : ℝ)^r *
        Real.exp ((Real.log r+1)*(r : ℝ)*m/4)) := by
  classical
  let Bad := {σ : Equiv.Perm (Fin r × Fin m) // BadArrangement σ}
  let Labels := (Fin r → Fin r) × (Fin r → Fin r)
  let labels : Bad → Labels := fun σ => arrangementLabels hm σ.val
  let M : ℝ := (m.factorial : ℝ)^r * Real.exp ((Real.log r+1)*(r : ℝ)*m/4)
  have hfiber : ∀ l : Labels, (Fintype.card {σ : Bad // labels σ = l} : ℝ) ≤ M := by
    intro l
    by_cases hne : Nonempty {σ : Bad // labels σ = l}
    · obtain ⟨σ⟩ := hne
      let matchType := PartitionMatching
        (fun x : Fin r × Fin m => leftComponent σ.val.val x.1)
        (fun x : Fin r × Fin m => rightComponent σ.val.val hm x.1)
      let : Fintype matchType := Fintype.ofEquiv
        (∀ i : OverlapComponent σ.val.val,
          {x : Fin r × Fin m // leftComponent σ.val.val x.1 = i} ≃
          {x : Fin r × Fin m // rightComponent σ.val.val hm x.1 = i})
        (partitionMatchingEquiv _ _).symm
      let f : {τ : Bad // labels τ = l} → matchType := fun τ =>
        matchingOfSameLabels hm σ.val.val τ.val.val (τ.property.trans σ.property.symm)
      have hf : Function.Injective f := by
        intro τ₁ τ₂ h
        apply Subtype.ext
        apply Subtype.ext
        have hh := congrArg (fun x : matchType => x.val) h
        exact hh
      have hcard := Fintype.card_le_of_injective f hf
      have hc : (Fintype.card {τ : Bad // labels τ = l} : ℝ) ≤
          (Nat.card matchType : ℝ) := by
        rw [Nat.card_eq_fintype_card]
        exact_mod_cast hcard
      refine hc.trans ?_
      change (Nat.card (PartitionMatching _ _) : ℝ) ≤ M
      rw [component_matching_card σ.val.val hm]
      push_cast
      exact bad_component_factorial_bound σ.val.val hr σ.val.property
    · have : IsEmpty {σ : Bad // labels σ = l} := not_nonempty_iff.mp hne
      have hz : Fintype.card {σ : Bad // labels σ = l} = 0 := Fintype.card_eq_zero
      rw [hz, Nat.cast_zero]
      dsimp [M]
      positivity
  have htotal := Fintype.card_congr (Equiv.sigmaFiberEquiv labels)
  rw [Fintype.card_sigma] at htotal
  calc
    (badArrangementCount r m : ℝ) =
        ∑ l : Labels, (Fintype.card {σ : Bad // labels σ = l} : ℝ) := by
      unfold badArrangementCount
      rw [Nat.card_eq_fintype_card]
      exact_mod_cast htotal.symm
    _ ≤ ∑ _l : Labels, M := Finset.sum_le_sum fun l _ => hfiber l
    _ = (Fintype.card Labels : ℝ)*M := by simp
    _ = (r : ℝ)^(2*r)*M := by
      simp only [Labels, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
        Nat.cast_mul, Nat.cast_pow, two_mul, pow_add]

end Ostmann.Conclusion

end

end OAI
