import OAI.Probability.SignedSweeps.SignedTypeAngle

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {X J : Type*} [Fintype X] [Fintype J]

def routeSize (f : X → J) (j : J) : ℕ := Fintype.card {x // f x = j}

def routeEnumeration (f : X → J) : (Σ j, Fin (routeSize f j)) ≃ X :=
  (Equiv.sigmaCongrRight (fun j => (Fintype.equivFin {x // f x = j}).symm)).trans
    (Equiv.sigmaFiberEquiv f)

omit [Fintype J] in
@[simp] lemma routeEnumeration_route [Fintype J] (f : X → J) (j : J)
    (x : Fin (routeSize f j)) :
    ((Equiv.sigmaFiberEquiv f).symm (routeEnumeration f ⟨j,x⟩)).1 = j :=
  ((Fintype.equivFin {x // f x = j}).symm x).2

omit [Fintype J] in
@[simp] lemma routeEnumeration_symm_fst [Fintype J] (f : X → J) (x : X) :
    ((routeEnumeration f).symm x).1 = f x := rfl

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {J : Type*} [Fintype J] {p n : ℕ} {t : J → ℕ}

def freeRoute (E : (Σ j, Fin (t j)) ≃ Fin n) (i : Fin p ↪ Fin n) : Fin p → J :=
  fun x => (E.symm (i x)).1

def freeLineInjection (E : (Σ j, Fin (t j)) ≃ Fin n) (i : Fin p ↪ Fin n) (j : J) :
    Fin (routeSize (freeRoute E i) j) ↪ Fin (t j) where
  toFun x := (blockFiberEquiv E j).symm ⟨i (routeEnumeration (freeRoute E i) ⟨j,x⟩),
    routeEnumeration_route (freeRoute E i) j x⟩
  inj' := by
    intro x y he
    have hh := congrArg (fun z => (blockFiberEquiv E j z).1) he
    simp only [Equiv.apply_symm_apply] at hh
    have hs := (routeEnumeration (freeRoute E i)).injective (i.injective hh)
    exact eq_of_heq (Sigma.mk.inj_iff.mp hs).2

lemma freeLine_square (E : (Σ j, Fin (t j)) ≃ Fin n) (i : Fin p ↪ Fin n) :
    BlockInjectionSquare (routeEnumeration (freeRoute E i)) E i (freeLineInjection E i) := by
  intro j x
  have hh := (blockFiberEquiv E j).apply_symm_apply
    ⟨i (routeEnumeration (freeRoute E i) ⟨j,x⟩), routeEnumeration_route (freeRoute E i) j x⟩
  exact (congrArg Subtype.val hh).symm

lemma freeLineSize_le (E : (Σ j, Fin (t j)) ≃ Fin n) (i : Fin p ↪ Fin n) (j : J) :
    routeSize (freeRoute E i) j ≤ t j := by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ (freeLineInjection E i j).injective

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {A B : Type*} [Fintype A] [Fintype B] {p n : ℕ}

def occupiedBoard (e : Fin n ≃ A × B) (i : Fin p ↪ Fin n) : Finset (A × B) :=
  Finset.univ.map (i.trans e.toEmbedding)

omit [Fintype A] [Fintype B] in
@[simp] lemma occupiedBoard_card [Fintype A] [Fintype B]
    (e : Fin n ≃ A × B) (i : Fin p ↪ Fin n) :
    (occupiedBoard e i).card = p := by
  simp only [occupiedBoard, Finset.card_map, Finset.card_univ, Fintype.card_fin]

def occupiedBoardEquiv (e : Fin n ≃ A × B) (i : Fin p ↪ Fin n) :
    Fin p ≃ {x // x ∈ occupiedBoard e i} :=
  (Equiv.ofInjective (fun x => e (i x)) (e.injective.comp i.injective)).trans
    (Equiv.subtypeEquiv (Equiv.refl _) (by intro x; simp [occupiedBoard]))

omit [Fintype A] [Fintype B] in
@[simp] lemma occupiedBoardEquiv_apply [Fintype A] [Fintype B]
    (e : Fin n ≃ A × B) (i : Fin p ↪ Fin n) (x : Fin p) :
    (occupiedBoardEquiv e i x).1 = e (i x) := rfl

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical

lemma signed_word_type_angle_numbered {A B : Type} [Fintype A] [Fintype B] [Nonempty B]
    {q p : ℕ} (hq : 0 < q) (W : Finset (A × B))
    (e : Fin p ≃ {x // x ∈ W})
    {kH uH vH : B → ℕ} {kK uK vK : A → ℕ}
    (eH : (Σ j, Fin (kH j)) ≃ Fin p)
    (hHroute : ∀ k, (eH.symm k).1 = (e k).1.2)
    (eK : (Σ i, Fin (kK i)) ≃ Fin p)
    (hKroute : ∀ k, (eK.symm k).1 = (e k).1.1)
    (hH : ∀ j, uH j+vH j=kH j) (αH : ∀ j, Partition (uH j)) (βH : ∀ j, Partition (vH j))
    (hαH : ∀ j, (αH j).1.colLen 0 ≤ q) (hβH : ∀ j, (βH j).1.colLen 0 ≤ q)
    (hK : ∀ i, uK i+vK i=kK i) (αK : ∀ i, Partition (uK i)) (βK : ∀ i, Partition (vK i))
    (hαK : ∀ i, (αK i).1.colLen 0 ≤ q) (hβK : ∀ i, (βK i).1.colLen 0 ≤ q)
    {u v : ℕ} (h : u+v=p) (α : Partition u) (β : Partition v)
    (hα : α.1.colLen 0 ≤ q) (hβ : β.1.colLen 0 ≤ q) :
    ‖(groupedPairTypeProjection (C := Fin q) eH hH αH βH *
      groupedPairTypeProjection (C := Fin q) eK hK αK βK * pairTypeProjection h α β (Fin q)).toContinuousLinearMap‖^2 ≤
      min 1 ((∏ j, pairCarrierCost (Fin q) (αH j) (βH j)) *
        (∏ i, pairCarrierCost (Fin q) (αK i) (βK i)) *
        Real.exp (-signedEntropy α β) * missingCellFactor W) := by
  have hc : p = W.card := by simpa using Fintype.card_congr e
  subst hc
  exact signed_word_type_angle hq W e eH hHroute eK hKroute hH αH βH hαH hβH
    hK αK βK hαK hβK h α β hα hβ

end SignedSweeps
end

end OAI
