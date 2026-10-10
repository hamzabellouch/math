import OAI.Analysis.CircleDomains.Transfer.OrderedGridCompatibility

namespace OAI

/-! Ordered grid selection for a finite list containing both real and
masked period coordinates. It uses their actual closed level graphs. -/

open Set Function Filter MeasureTheory

namespace CircleDomainRigidity.FiniteTransfer

def reciprocalGraphLevel (R : Set (Sphere × UnitAddCircle))
    (θ : ℝ) (N : ℕ) (k : Fin (N + 1)) : Set Sphere :=
  {x | (x, ((θ + (k.val : ℝ) * reciprocalGridStep N : ℝ) : UnitAddCircle)) ∈ R}

def OrderedGraphGridCompatibility {S : Type*} {n : ℕ}
    (R : Fin n → Set (Sphere × UnitAddCircle)) (θ : Fin n → ℝ) (N : ℕ)
    (A : Set Sphere) (σ : S → Sphere) : Prop :=
  ∀ x ∈ A, x ∉ range σ → ∀ j : Fin n,
    x ∈ ⋃ k, reciprocalGraphLevel (R j) (θ j) N k →
    ∀ I : Finset (Fin n), (∀ i ∈ I, i.val < j.val) → ∀ k : Fin n → Fin (N + 1),
      ¬ (connectedComponentIn
        (⋃ i ∈ I, reciprocalGraphLevel (R i) (θ i) N (k i)) x).Nontrivial

 theorem isClosed_reciprocalGraphLevel
    {R : Set (Sphere × UnitAddCircle)} (hR : IsClosed R)
    (θ : ℝ) (N : ℕ) (k : Fin (N + 1)) :
    IsClosed (reciprocalGraphLevel R θ N k) :=
  hR.preimage (continuous_id.prodMk continuous_const)

theorem ae_ordered_graph_grid_compatibility
    {S : Type*} {n : ℕ}
    (R : Fin n → Set (Sphere × UnitAddCircle)) (B : Set Sphere) (σ : S → Sphere)
    (hnull : ∀ (j : Fin n) (d : ℕ) (labels : Fin d → Fin n),
      (∀ i, (labels i).val < j.val) →
      (volume.prod (Measure.pi (fun _ : Fin d => (volume : Measure UnitAddCircle))))
        (freeComponentFailure (B \ range σ) (R j)
          R labels) = 0)
    (N : ℕ) :
    ∀ᵐ θ ∂reciprocalGridLaw n N, OrderedGraphGridCompatibility R θ N B σ := by
  classical
  let E (d : ℕ) (labels : Fin (d + 1) → Fin n) :
      Set (UnitAddCircle × (Fin d → UnitAddCircle)) :=
    if h : ∀ i : Fin d, (labels i.succ).val < (labels 0).val then
      freeComponentFailure (B \ range σ) (R (labels 0))
        R (fun i => labels i.succ)
    else ∅
  have hE (d : ℕ) (labels : Fin (d + 1) → Fin n) (_ : Injective labels) :
      (volume.prod (Measure.pi (fun _ : Fin d => (volume : Measure UnitAddCircle))))
        (E d labels) = 0 := by
    dsimp only [E]
    split_ifs with h
    · exact hnull _ _ _ h
    · exact measure_empty
  filter_upwards [ae_reciprocal_grid_tuples_avoid_null_events N E hE] with θ hθ
  intro x hxB hxσ j hxj I hIj k hnon
  obtain ⟨kj, hxj⟩ := mem_iUnion.mp hxj
  let e := I.orderEmbOfFin rfl
  have hmem (i : Fin I.card) : e i ∈ I := I.orderEmbOfFin_mem rfl i
  have honto (l : Fin n) (hl : l ∈ I) : ∃ i : Fin I.card, e i = l := by
    let l' : I := ⟨l, hl⟩
    exact ⟨(I.orderIsoOfFin rfl).symm l',
      congrArg Subtype.val ((I.orderIsoOfFin rfl).apply_symm_apply l')⟩
  let labels : Fin (I.card + 1) → Fin n := Fin.cons j e
  have hjnot : j ∉ range e := by
    rintro ⟨i, hi⟩
    have hh := hIj (e i) (hmem i)
    rw [hi] at hh
    exact (lt_irrefl _ hh)
  have hlabels : Injective labels := Fin.cons_injective_of_injective hjnot e.injective
  let offsets : Fin (I.card + 1) → ℤ := Fin.cons (kj.val : ℤ) (fun i => (k (e i)).val)
  let t : UnitAddCircle := ((θ j + (kj.val : ℝ) * reciprocalGridStep N : ℝ) : UnitAddCircle)
  let τ : Fin I.card → UnitAddCircle := fun i =>
    ((θ (e i) + ((k (e i)).val : ℝ) * reciprocalGridStep N : ℝ) : UnitAddCircle)
  have hlt : ∀ i : Fin I.card, (labels i.succ).val < (labels 0).val := by
    intro i
    simpa only [labels, Fin.cons_succ, Fin.cons_zero] using hIj (e i) (hmem i)
  have hav := hθ I.card labels hlabels offsets
  have hnot : (t, τ) ∉ freeComponentFailure (B \ range σ) (R j)
      R e := by
    simpa only [E, dite_eq_left hlt, labels, offsets, Fin.cons_zero, Fin.cons_succ,
      Int.cast_natCast, t, τ] using hav
  apply hnot
  refine ⟨(x, t, τ), ⟨⟨hxB, hxσ⟩, hxj, ?_⟩, rfl⟩
  change (connectedComponentIn
    {z | (z, τ) ∈ finiteLevelUnionGraph R e} x).Nontrivial
  have hset : {z | (z, τ) ∈ finiteLevelUnionGraph R e} =
      ⋃ i ∈ I, reciprocalGraphLevel (R i) (θ i) N (k i) := by
    ext z
    simp only [finiteLevelUnionGraph, mem_iUnion, mem_preimage, mem_ofPred_eq]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨e i, hmem i, hi⟩
    · rintro ⟨l, hl, hz⟩
      obtain ⟨i, rfl⟩ := honto l hl
      exact ⟨i, hz⟩
  rwa [hset]

end CircleDomainRigidity.FiniteTransfer

end OAI
