import OAI.Probability.SwitchChain.Definitions

namespace OAI

noncomputable section

namespace Problem315.TripleStateReindex

open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {V W : Type*} [sectionFintypeV : Fintype V] [sectionFintypeW : Fintype W]

def degreeCount (G : SimpleGraph V) (v : V) : ℕ := by
  classical
  exact (Finset.univ.filter (G.Adj v)).card

theorem degreeCount_comap (e : V ≃ W) (G : SimpleGraph W) (v : V) :
    degreeCount (G.comap e) v = degreeCount G (e v) := by
  classical
  unfold degreeCount
  apply Finset.card_bij (fun w _ => e w)
  · intro w hw
    simpa using hw
  · intro u hu w hw he
    exact e.injective he
  · intro w hw
    refine ⟨e.symm w, ?_, e.apply_symm_apply w⟩
    simpa using hw

def graphEquiv (e : V ≃ W) : SimpleGraph W ≃ SimpleGraph V where
  toFun G := G.comap e
  invFun G := G.comap e.symm
  left_inv G := by ext u v; simp
  right_inv G := by ext u v; simp

include sectionFintypeV sectionFintypeW in
@[simp] theorem graphEquiv_adj (e : V ≃ W) (G : SimpleGraph W) (u v : V) :
    (graphEquiv e G).Adj u v ↔ G.Adj (e u) (e v) := by
  have retainedsectionFintypeV := sectionFintypeV
  have retainedsectionFintypeW := sectionFintypeW
  exact Iff.rfl

def fixedDegreeEquiv (e : V ≃ W) (d : W → ℕ) :
    {G : SimpleGraph W // ∀ v, degreeCount G v = d v} ≃
      {G : SimpleGraph V // ∀ v, degreeCount G v = d (e v)} where
  toFun G := ⟨graphEquiv e G.val, fun v => by
    rw [show graphEquiv e G.val = G.val.comap e from rfl, degreeCount_comap]
    exact G.property (e v)⟩
  invFun G := ⟨(graphEquiv e).symm G.val, fun v => by
    change degreeCount (G.val.comap e.symm) v = d v
    rw [degreeCount_comap, G.property, e.apply_symm_apply]⟩
  left_inv G := by apply Subtype.ext; exact (graphEquiv e).left_inv G.val
  right_inv G := by apply Subtype.ext; exact (graphEquiv e).right_inv G.val

variable {n : ℕ} (s : Finset (Fin n)) (hs : s.card = 3)

abbrev Outside := {v : Fin n // v ∉ s}

def tripleEnum : Fin 3 ≃ ↥s :=
  (Fintype.equivFinOfCardEq (by simpa using hs)).symm

def splitEquiv : (Fin 3 ⊕ Outside s) ≃ Fin n :=
  (Equiv.sumCongr (tripleEnum s hs) (Equiv.refl _)).trans
    (Equiv.sumCompl (fun v : Fin n => v ∈ s))

@[simp] theorem splitEquiv_inl (i : Fin 3) :
    splitEquiv s hs (Sum.inl i) = (tripleEnum s hs i).val := rfl

@[simp] theorem splitEquiv_inr (v : Outside s) :
    splitEquiv s hs (Sum.inr v) = v.val := rfl

@[simp] theorem splitEquiv_inl_mem (i : Fin 3) :
    splitEquiv s hs (Sum.inl i) ∈ s := (tripleEnum s hs i).property

@[simp] theorem splitEquiv_inr_not_mem (v : Outside s) :
    splitEquiv s hs (Sum.inr v) ∉ s := v.property

def stateEquiv (d : Fin n → ℕ) : GraphState n d ≃
    {G : SimpleGraph (Fin 3 ⊕ Outside s) //
      ∀ v, degreeCount G v = d (splitEquiv s hs v)} :=
  fixedDegreeEquiv (splitEquiv s hs) d

@[simp] theorem stateEquiv_adj (d : Fin n → ℕ) (G : GraphState n d)
    (u v : Fin 3 ⊕ Outside s) :
    (stateEquiv s hs d G).val.Adj u v ↔
      G.val.Adj (splitEquiv s hs u) (splitEquiv s hs v) := Iff.rfl

@[simp] theorem stateEquiv_outside_adj (d : Fin n → ℕ) (G : GraphState n d)
    (u v : Outside s) :
    (stateEquiv s hs d G).val.Adj (Sum.inr u) (Sum.inr v) ↔
      G.val.Adj u.val v.val := Iff.rfl

theorem sum_stateEquiv (d : Fin n → ℕ)
    (f : {G : SimpleGraph (Fin 3 ⊕ Outside s) //
      ∀ v, degreeCount G v = d (splitEquiv s hs v)} → ℝ) :
    ∑ G : GraphState n d, f (stateEquiv s hs d G) = ∑ G, f G :=
  (stateEquiv s hs d).sum_comp f

theorem stateCount_eq (d : Fin n → ℕ) :
    stateCount n d = Fintype.card
      {G : SimpleGraph (Fin 3 ⊕ Outside s) //
        ∀ v, degreeCount G v = d (splitEquiv s hs v)} := by
  change Fintype.card (GraphState n d) = _
  exact Fintype.card_congr (stateEquiv s hs d)

theorem uniformAverage_stateEquiv (d : Fin n → ℕ)
    (f : {G : SimpleGraph (Fin 3 ⊕ Outside s) //
      ∀ v, degreeCount G v = d (splitEquiv s hs v)} → ℝ) :
    uniformAverage n d (fun G => f (stateEquiv s hs d G)) =
      (∑ G, f G) / (Fintype.card
        {G : SimpleGraph (Fin 3 ⊕ Outside s) //
          ∀ v, degreeCount G v = d (splitEquiv s hs v)} : ℝ) := by
  unfold uniformAverage
  rw [stateCount_eq s hs d]
  congr 1
  exact sum_stateEquiv s hs d f

theorem uniformVariance_stateEquiv (d : Fin n → ℕ)
    (f : {G : SimpleGraph (Fin 3 ⊕ Outside s) //
      ∀ v, degreeCount G v = d (splitEquiv s hs v)} → ℝ) :
    uniformVariance n d (fun G => f (stateEquiv s hs d G)) =
      (∑ G, (f G - (∑ H, f H) / (Fintype.card
        {H : SimpleGraph (Fin 3 ⊕ Outside s) //
          ∀ v, degreeCount H v = d (splitEquiv s hs v)} : ℝ)) ^ 2) /
            (Fintype.card
              {G : SimpleGraph (Fin 3 ⊕ Outside s) //
                ∀ v, degreeCount G v = d (splitEquiv s hs v)} : ℝ) := by
  unfold uniformVariance
  rw [uniformAverage_stateEquiv]
  exact uniformAverage_stateEquiv s hs d (fun G =>
    (f G - (∑ H, f H) / (Fintype.card
      {H : SimpleGraph (Fin 3 ⊕ Outside s) //
        ∀ v, degreeCount H v = d (splitEquiv s hs v)} : ℝ)) ^ 2)

end Problem315.TripleStateReindex

end

end OAI
