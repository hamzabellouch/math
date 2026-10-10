import OAI.Analysis.KadisonKastler.MinimalFamilyModule

namespace OAI

/-! A compact product keeps the same normalized rows for an entire family
of completely bounded maps. Minimality descends to each coordinate. -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {J : Type*} {c : J → ℝ}

abbrev WeakMapFamily (M : VonNeumannAlgebra H) {J : Type*} (c : J → ℝ) :=
  ∀ j, BoundedWeakAlgebraMap M (c j)

def familyRowAverage (hc : ∀ j, 0 ≤ c j) {n : ℕ} (r : Fin n → Algebra M)
    (hr : ∑ i, r i * star (r i) = 1) (F : WeakMapFamily M c) : WeakMapFamily M c :=
  fun j => boundedWeakRowAverage (hc j) r hr (F j)

def familyRowOrbit (hc : ∀ j, 0 ≤ c j) (F : WeakMapFamily M c) : Set (WeakMapFamily M c) :=
  {G | ∃ (n : ℕ) (r : Fin n → Algebra M) (hr : ∑ i, r i * star (r i) = 1),
    G = familyRowAverage hc r hr F}

def FamilyRowInvariant (hc : ∀ j, 0 ≤ c j) (C : Set (WeakMapFamily M c)) : Prop :=
  ∀ (n : ℕ) (r : Fin n → Algebra M) (hr : ∑ i, r i * star (r i) = 1),
    Set.MapsTo (familyRowAverage hc r hr) C C

theorem continuous_familyRowAverage (hc : ∀ j, 0 ≤ c j) {n : ℕ}
    (r : Fin n → Algebra M) (hr : ∑ i, r i * star (r i) = 1) :
    Continuous (familyRowAverage hc r hr) :=
  continuous_pi fun j => (continuous_boundedWeakRowAverage (hc j) r hr).comp
    (continuous_apply j)

theorem familyRowOrbit_self (hc : ∀ j, 0 ≤ c j) (F : WeakMapFamily M c) :
    F ∈ familyRowOrbit hc F := by
  refine ⟨1, fun _ => 1, by simp, ?_⟩
  funext j
  apply boundedWeakAlgebraMap_ext
  ext a
  simp [familyRowAverage, boundedWeakRowAverage, finiteRightAverage_apply]

theorem familyRowOrbit_invariant (hc : ∀ j, 0 ≤ c j) (F : WeakMapFamily M c) :
    FamilyRowInvariant hc (familyRowOrbit hc F) := by
  classical
  intro n r hr G hG
  obtain ⟨m, s, hs, rfl⟩ := hG
  let t : Fin n × Fin m → Algebra M := fun ij => r ij.1 * s ij.2
  let e := (Fintype.equivFin (Fin n × Fin m)).symm
  have ht : ∑ i, (t ∘ e) i * star ((t ∘ e) i) = 1 := by
    change (∑ i, t (e i) * star (t (e i))) = 1
    rw [Equiv.sum_comp e (fun j => t j * star (t j))]
    exact finiteRow_product_normalized r s hr hs
  refine ⟨_, t ∘ e, ht, ?_⟩
  funext j
  apply boundedWeakAlgebraMap_ext
  change finiteRightAverage r (finiteRightAverage s (F j).map) =
    finiteRightAverage (t ∘ e) (F j).map
  rw [finiteRightAverage_reindex, finiteRightAverage_comp]

theorem familyRowInvariant_closure_orbit (hc : ∀ j, 0 ≤ c j) (F : WeakMapFamily M c) :
    FamilyRowInvariant hc (closure (familyRowOrbit hc F)) := by
  intro n r hr G hG
  apply closure_minimal (t := {A | familyRowAverage hc r hr A ∈ closure (familyRowOrbit hc F)})
      (fun A hA => subset_closure (familyRowOrbit_invariant hc F n r hr hA))
      (isClosed_closure.preimage (continuous_familyRowAverage hc r hr)) hG

theorem exists_minimal_familyRowFamily (hc : ∀ j, 0 ≤ c j) (F : WeakMapFamily M c) :
    ∃ C : Set (WeakMapFamily M c), C ⊆ closure (familyRowOrbit hc F) ∧ C.Nonempty ∧
      IsClosed C ∧ FamilyRowInvariant hc C ∧
      ∀ D : Set (WeakMapFamily M c), D ⊆ C → D.Nonempty → IsClosed D →
        FamilyRowInvariant hc D → D = C := by
  let (j : J) : CompactSpace (BoundedWeakAlgebraMap M (c j)) :=
    isCompact_univ_iff.mp (isCompact_boundedWeakAlgebraMap M (hc j))
  let A : Set (Set (WeakMapFamily M c)) := {C | C ⊆ closure (familyRowOrbit hc F) ∧
    C.Nonempty ∧ IsClosed C ∧ FamilyRowInvariant hc C}
  have hstart : closure (familyRowOrbit hc F) ∈ A :=
    ⟨Set.Subset.refl _, ⟨F, subset_closure (familyRowOrbit_self hc F)⟩,
      isClosed_closure, familyRowInvariant_closure_orbit hc F⟩
  have hchain : ∀ T ⊆ A, IsChain (· ⊆ ·) T → T.Nonempty →
      ∃ C ∈ A, ∀ D ∈ T, C ⊆ D := by
    intro T hT hchain hne
    obtain ⟨C₀, hC₀⟩ := hne
    have hdir : DirectedOn (· ⊇ ·) T := by
      intro B hB C hC
      rcases hchain.total hB hC with h | h
      · exact ⟨B, hB, Set.Subset.refl _, h⟩
      · exact ⟨C, hC, h, Set.Subset.refl _⟩
    let : Nonempty T := ⟨⟨C₀, hC₀⟩⟩
    have hn : (⋂₀ T).Nonempty :=
      IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed hdir
        (fun C hC => (hT hC).2.1) (fun C hC => (hT hC).2.2.1.isCompact)
        (fun C hC => (hT hC).2.2.1)
    refine ⟨⋂₀ T, ⟨(Set.sInter_subset_of_mem hC₀).trans (hT hC₀).1, hn,
      isClosed_sInter (fun C hC => (hT hC).2.2.1), ?_⟩,
      fun C hC => Set.sInter_subset_of_mem hC⟩
    intro n r hr G hG
    exact Set.mem_sInter.mpr (fun C hC => (hT hC).2.2.2 n r hr
      (Set.mem_sInter.mp hG C hC))
  obtain ⟨C, _, hmin⟩ := zorn_superset_nonempty A hchain _ hstart
  refine ⟨C, hmin.prop.1, hmin.prop.2.1, hmin.prop.2.2.1, hmin.prop.2.2.2, ?_⟩
  intro D hDC hne hclosed hinv
  exact hmin.eq_of_subset ⟨hDC.trans hmin.prop.1, hne, hclosed, hinv⟩ hDC

end

end KadisonKastler

end OAI
