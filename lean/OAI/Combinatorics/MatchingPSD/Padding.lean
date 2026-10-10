import OAI.Combinatorics.MatchingPSD.NormalizedFactors

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

namespace PerfectMatchingPSD
open MatchingSmoothing Matrix
open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable def colorCut {n : ℕ} {V : Type u_1} [Fintype V]
    (e : V ≃ Fin n) (z : V → Bool) (hz : Odd (Fintype.card {v // z v = true})) : OddCut n := by
  classical
  refine ⟨Finset.univ.filter (fun v => z (e.symm v) = true), ?_⟩
  have he := Fintype.card_congr (Equiv.subtypeEquivOfSubtype' (p := fun v => z v = true) e)
  have ho : Odd (Fintype.card {v : Fin n // z (e.symm v) = true}) := by
    rw [← he]
    exact hz
  simpa only [Fintype.card_subtype] using ho

lemma colorCut_slack {n : ℕ} {V : Type u_2} [Fintype V]
    (e : V ≃ Fin n) (z : V → Bool) (hz : Odd (Fintype.card {v // z v = true}))
    (M : Pairing V) :
    slack (Sum.inr (colorCut e z hz)) (fromPairing (Pairing.transport e M)) =
      tableCoordinate z (true,false) M - 1 := by
  classical
  rw [slack, crossingCount_tableCoordinate, tableCoordinate_transport]
  congr 2
  funext v
  simp [colorCut]

lemma true_card_comp_equiv {V : Type u_3} {W : Type u_4} [Fintype V] [Fintype W]
    (z : V → Bool) (e : W ≃ V) :
    Fintype.card {w // z (e w) = true} = Fintype.card {v // z v = true} :=
  Fintype.card_congr (Equiv.subtypeEquiv e (fun _ => Iff.rfl))

lemma true_card_sum_false {V : Type u_5} {W : Type u_6} [Fintype V] [Fintype W] (z : V → Bool) :
    Fintype.card {v : V ⊕ W // Sum.elim z (fun _ => false) v = true} =
      Fintype.card {v : V // z v = true} := by
  classical
  let e : {v : V ⊕ W // Sum.elim z (fun _ => false) v = true} ≃ {v : V // z v = true} :=
    { toFun := fun v => match v with
        | ⟨Sum.inl a,h⟩ => ⟨a,h⟩
        | ⟨Sum.inr _,h⟩ => nomatch h
      invFun := fun v => ⟨Sum.inl v.1,v.2⟩
      left_inv := by
        rintro ⟨v,h⟩
        cases v with
        | inl v => rfl
        | inr v => exact False.elim (Bool.false_ne_true h)
      right_inv := by intro v; rfl }
  exact Fintype.card_congr e

lemma tableCoordinate_false {V : Type u_7} [Fintype V] (M : Pairing V) :
    tableCoordinate (fun _ : V => false) (true,false) M = 0 := by
  simp [tableCoordinate]

lemma global_factors_of_factorization {n r s q : ℕ} (hn : Even n) (hnpos : 1 ≤ n)
    (hfac : HasFactorization n r) {W : Type} [Fintype W]
    (e : (GlobalVertices s q ⊕ W) ≃ Fin n) (MW : Pairing W) :
    ∃ (Q : Equiv.Perm (GlobalVertices s q) → (Fin q → Bool) → Matrix (Fin r) (Fin r) ℝ)
      (B : Pairing (GlobalVertices s q) → Matrix (Fin r) (Fin r) ℝ),
      (∀ a y, (Q a y).PosSemidef) ∧ (∀ M, (B M).PosSemidef) ∧
      (∀ a y, (Q a y).trace ≤ (n:ℝ)+1) ∧ (∀ M, (B M).trace ≤ (r:ℝ)) ∧
      ∀ a y M, (Q a y * B (Pairing.relabel a M)).trace =
        tableCoordinate (globalCutColor y) (true,false) M - 1 := by
  classical
  obtain ⟨A,B,hA,hB,hpair,htrA,htrB⟩ := normalized_factorization hn hnpos hfac
  let z (a : Equiv.Perm (GlobalVertices s q)) (y : Fin q → Bool) : GlobalVertices s q ⊕ W → Bool :=
    Sum.elim (globalCutColor y ∘ a.symm) (fun _ => false)
  have hz (a : Equiv.Perm (GlobalVertices s q)) (y : Fin q → Bool) :
      Odd (Fintype.card {v // z a y v = true}) := by
    rw [true_card_sum_false]
    change Odd (Fintype.card {v // globalCutColor y (a.symm v) = true})
    rw [true_card_comp_equiv]
    exact globalCutColor_odd s q y
  let U (a : Equiv.Perm (GlobalVertices s q)) (y : Fin q → Bool) := colorCut e (z a y) (hz a y)
  refine ⟨fun a y => A (Sum.inr (U a y)),
    fun M => B (fromPairing (Pairing.transport e (Pairing.sum M MW))),
    fun a y => hA _, fun M => hB _, fun a y => htrA _, fun M => htrB _, ?_⟩
  intro a y M
  rw [hpair, colorCut_slack, tableCoordinate_sum, tableCoordinate_false, add_zero]
  congr 1
  rw [← Pairing.transport_perm, tableCoordinate_transport]
  congr 1
  ext v
  simp

end PerfectMatchingPSD

end OAI
