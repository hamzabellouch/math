import OAI.Probability.FreeIsing.Trees.PathSideBranches

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367.PathSideBranches

@[implicit_reducible] def coordinateSigma {V A : Type*} [MeasurableSpace A] (S : Set V) :
    MeasurableSpace (V → A) :=
  MeasurableSpace.comap S.domRestrict inferInstance

theorem measurable_restrict_of_subset {V A : Type*} [MeasurableSpace A]
    {S T : Set V} (hST : S ⊆ T) :
    Measurable[coordinateSigma (A := A) T] (S.domRestrict : (V → A) → S → A) := by
  let : MeasurableSpace (V → A) := coordinateSigma (A := A) T
  apply Measurable.of_eval
  intro v
  exact (measurable_pi_apply (⟨v.1, hST v.2⟩ : T)).comp (comap_measurable T.domRestrict)

theorem coordinateSigma_mono {V A : Type*} [MeasurableSpace A]
    {S T : Set V} (hST : S ⊆ T) :
    coordinateSigma (A := A) S ≤ coordinateSigma (A := A) T :=
  (measurable_restrict_of_subset (A := A) hST).comap_le

theorem coordinateSigma_le {V A : Type*} [MeasurableSpace A] (S : Set V) :
    coordinateSigma (A := A) S ≤ (inferInstance : MeasurableSpace (V → A)) :=
  S.measurable_restrict.comap_le

theorem later_forward_subset_side_complement {d : ℕ} (hd : 3 ≤ d)
    (v : TreeVertex d) {i j : Fin v.1.length} (hij : i < j) :
    cone (ConnectedHull.takeVertex v (j.1 + 1)) ⊆ (cone (sideVertex hd v i))ᶜ :=
  fun _ hu => (Set.disjoint_right.mp (sideCone_disjoint_later_forward hd v hij)) hu

theorem measurable_later_forward_observable {d : ℕ} {A C : Type*}
    [MeasurableSpace A] [MeasurableSpace C] (hd : 3 ≤ d) (v : TreeVertex d)
    {i j : Fin v.1.length} (hij : i < j)
    (F : (cone (ConnectedHull.takeVertex v (j.1 + 1)) → A) → C)
    (hF : Measurable F) :
    Measurable[coordinateSigma (A := A) (cone (sideVertex hd v i))ᶜ]
      (fun U : TreeVertex d → A =>
        F ((cone (ConnectedHull.takeVertex v (j.1 + 1))).domRestrict U)) :=
  hF.comp (measurable_restrict_of_subset (later_forward_subset_side_complement hd v hij))

theorem measurable_later_forward_product {d : ℕ} {A : Type*} [MeasurableSpace A]
    (hd : 3 ≤ d) (v : TreeVertex d) (i : Fin v.1.length)
    (s : Finset (Fin v.1.length))
    (F : ∀ j : Fin v.1.length,
      (cone (ConnectedHull.takeVertex v (j.1 + 1)) → A) → ℝ)
    (hF : ∀ j ∈ s, Measurable (F j)) (hs : ∀ j ∈ s, i < j) :
    Measurable[coordinateSigma (A := A) (cone (sideVertex hd v i))ᶜ]
      (fun U : TreeVertex d → A => ∏ j ∈ s,
        F j ((cone (ConnectedHull.takeVertex v (j.1 + 1))).domRestrict U)) := by
  let : MeasurableSpace (TreeVertex d → A) :=
    coordinateSigma (A := A) (cone (sideVertex hd v i))ᶜ
  exact s.measurable_fun_prod (fun j hj =>
    measurable_later_forward_observable hd v (hs j hj) (F j) (hF j hj))

end Problem367.PathSideBranches

end

end OAI
