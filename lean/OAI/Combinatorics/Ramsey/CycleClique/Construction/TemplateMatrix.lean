import OAI.Combinatorics.Ramsey.CycleClique.Construction.FiniteTemplates

namespace OAI

/-! Soundness of a finite list of explicit extension certificates, with
both orientations of every forbidden outside path inserted in the matrix. -/

namespace CycleClique.Construction
variable {n : ℕ}

def templateEntryMatrix (T : TemplateData (Fin n)) : ForbiddenMatrix n := fun i j =>
  if (i = T.x ∧ j = T.y) ∨ (i = T.y ∧ j = T.x) then Finset.Icc T.lo T.hi else ∅

def templateMatrix : List (TemplateData (Fin n)) → ForbiddenMatrix n
  | [] => fun _ _ => ∅
  | T :: E => fun i j => templateEntryMatrix T i j ∪ templateMatrix E i j

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {Q : Finset V} {H : SimpleGraph (Fin n)}
variable {Q₀ : Finset (Fin n)} {S : ExpandedPathSystem G Q}

theorem templateMatrix_sound {k L e : ℕ} (hopt : S.IsOptimal k)
    (hk : 3 ≤ k) (hQk : Q.card ≤ k) (hQ : G.IsClique (Q : Set V))
    (hcycle : ¬ HasCycle G (k + 1)) (ha : S.amount = L) (he : S.assignedCount = e)
    (f : Fin n → V) (hf : Function.Injective f) (hfQ : ∀ v, f v ∈ Q ↔ v ∈ Q₀)
    (hfG : ∀ {i j}, H.Adj i j → G.Adj (f i) (f j))
    (hfX : ∀ i, f i ∈ Q ∨ f i ∈ S.vertices)
    (E : List (TemplateData (Fin n))) (hE : ∀ T ∈ E, T.Check H Q₀ k L e) :
    (templateMatrix E).Sound G (Q ∪ S.vertices) f := by
  induction E with
  | nil => intro i j d hd; simp only [templateMatrix, Finset.notMem_empty] at hd
  | cons T E ih =>
    apply ForbiddenMatrix.Sound.union
    · intro i j d hd
      have hpair : (i = T.x ∧ j = T.y) ∨ (i = T.y ∧ j = T.x) := by
        by_contra hn
        simp only [templateEntryMatrix, hn, ↓reduceIte, Finset.notMem_empty] at hd
      have hdist : d ∈ Finset.Icc T.lo T.hi := by simpa only [templateEntryMatrix, hpair, ↓reduceIte] using hd
      have hb := T.forbids hopt hk hQk hQ hcycle ha he f hf hfQ hfG hfX
        (hE T (by simp)) hdist
      rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simpa only [Finset.coe_union] using hb
      · intro h
        exact hb (by simpa only [Finset.coe_union] using h.reverse)
    · exact ih (fun U hU => hE U (by simp [hU]))

end CycleClique.Construction

end OAI
