import OAI.Analysis.CircleDomains.Selection.ConcatenatedResidualPieces
import OAI.Analysis.CircleDomains.Selection.ResidualPieceAssembly

namespace OAI

/-! Countable concatenation preserves each residual incidence inequality.
Only the complement of the open pieces must be countable; the pieces'
images may overlap and every parameter visit is still charged. -/

open Set Function MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {ι X Z : Type*} [Encodable ι] [MetricSpace X] [MeasurableSpace Z]

theorem concatenated_piece_incidence_bound (B : Set X) (R : Set (Z × X)) (P : Set X)
    (ν : Measure Z) (m : X → ℝ≥0∞)
    (γ : C(PathTime, X)) (a b : ι → PathTime) (hab : ∀ i, a i < b i)
    (hdis : Pairwise (Disjoint on (fun i => Ioo (a i) (b i))))
    (Γ : ι → TaggedPath X)
    (hmatch : ∀ i t, t ∈ Ioo (⊥ : PathTime) ⊤ →
      γ (affinePathTime (a i) (b i) t) = (Γ i).1 t)
    (i : ι) (c d : PathTime)
    (hbound : ResidualIncidenceBound B
      (Ioo (rescalePathTime (a i) (b i) c) (rescalePathTime (a i) (b i) d)) R P ν m (Γ i)) :
    ν (timeIncidence {q | q ∈ R ∧ q.2 ∉ P} γ
      (residualTimes B (concatenatedTaggedPath γ a b Γ) ∩ (Ioo (a i) (b i) ∩ Ioo c d))) ≤
      timeToll γ (residualTimes B (concatenatedTaggedPath γ a b Γ) ∩
        (Ioo (a i) (b i) ∩ Ioo c d)) (deletedWeight P m) := by
  rw [concatenated_piece_times B γ a b hab hdis Γ hmatch i c d,
    timeIncidence_image, timeToll_image γ _ (affinePathTime_strictMono (hab i)).injective]
  have he : EqOn (γ ∘ affinePathTime (a i) (b i)) (Γ i).1
      (residualTimes B (Γ i) ∩
        Ioo (rescalePathTime (a i) (b i) c) (rescalePathTime (a i) (b i) d)) := by
    intro t ht
    exact hmatch i t ⟨lt_of_le_of_lt bot_le ht.2.1, lt_of_lt_of_le ht.2.2 le_top⟩
  rw [timeIncidence_congr_path _ he, timeToll_congr_path _ he]
  simpa only [ResidualIncidenceBound, residualIncidence_eq_timeIncidence,
    residualToll_eq_timeToll] using hbound

theorem residualIncidenceBound_concatenated_open (B : Set X) (R : Set (Z × X)) (P : Set X)
    (ν : Measure Z) (m : X → ℝ≥0∞)
    (γ : C(PathTime, X)) (a b : ι → PathTime) (hab : ∀ i, a i < b i)
    (hdis : Pairwise (Disjoint on (fun i => Ioo (a i) (b i))))
    (hcount : (⋃ i, Ioo (a i) (b i))ᶜ.Countable)
    (Γ : ι → TaggedPath X)
    (hmatch : ∀ i t, t ∈ Ioo (⊥ : PathTime) ⊤ →
      γ (affinePathTime (a i) (b i) t) = (Γ i).1 t)
    (hpoint : ∀ x, ν {z | (z, x) ∈ R} ≤ m x)
    (hΓ : ∀ i c d, ResidualIncidenceBound B (Ioo c d) R P ν m (Γ i))
    (c d : PathTime) :
    ResidualIncidenceBound B (Ioo c d) R P ν m (concatenatedTaggedPath γ a b Γ) := by
  let S := residualTimes B (concatenatedTaggedPath γ a b Γ) ∩ Ioo c d
  let J := fun i => Ioo (a i) (b i)
  let A₀ := S \ ⋃ i, J i
  let C := fun i => S ∩ J i
  have hcover : S = A₀ ∪ ⋃ i, C i := by
    ext t
    simp only [A₀, C, mem_union, mem_sdiff, mem_iUnion, mem_inter_iff]
    tauto
  have hC : Pairwise (Disjoint on C) := by
    intro i j hij
    exact (hdis hij).mono inter_subset_right inter_subset_right
  have hd₀ : Disjoint A₀ (⋃ i, C i) := by
    apply disjoint_left.mpr
    rintro t ht hc
    obtain ⟨i, hi⟩ := mem_iUnion.mp hc
    exact ht.2 (mem_iUnion.mpr ⟨i, hi.2⟩)
  have hc₀ : (γ '' A₀).Countable := (hcount.mono (fun _ ht => ht.2)).image γ
  unfold ResidualIncidenceBound
  rw [residualIncidence_eq_timeIncidence, residualToll_eq_timeToll]
  apply timeIncidence_bound_with_countable_remainder R P γ S A₀ C ν m hpoint hcover hC hd₀ hc₀
  intro i
  have he : C i = residualTimes B (concatenatedTaggedPath γ a b Γ) ∩ (J i ∩ Ioo c d) := by
    ext t
    simp only [C, S, mem_inter_iff]
    tauto
  rw [he]
  exact concatenated_piece_incidence_bound B R P ν m γ a b hab hdis Γ hmatch i c d (hΓ i _ _)

theorem residualConstraintFamily_concatenated (B : Set X) (R : ℕ → Set (Z × X))
    (P : ℕ → ℕ → Finset X) (ν : ℕ → Measure Z) (m : ℕ → X → ℝ≥0∞)
    (γ : C(PathTime, X)) (a b : ι → PathTime) (hab : ∀ i, a i < b i)
    (hdis : Pairwise (Disjoint on (fun i => Ioo (a i) (b i))))
    (hcount : (⋃ i, Ioo (a i) (b i))ᶜ.Countable)
    (Γ : ι → TaggedPath X)
    (hmatch : ∀ i t, t ∈ Ioo (⊥ : PathTime) ⊤ →
      γ (affinePathTime (a i) (b i) t) = (Γ i).1 t)
    (hpoint : ∀ k x, ν k {z | (z, x) ∈ R k} ≤ m k x)
    (hΓ : ∀ i, ResidualConstraintFamily B R P ν m (Γ i)) :
    ResidualConstraintFamily B R P ν m (concatenatedTaggedPath γ a b Γ) := by
  intro k n c d
  apply residualIncidenceBound_closed_of_open B (R k) (P k n) (ν k) (m k)
    (concatenatedTaggedPath γ a b Γ) (hpoint k) _ c.toTime d.toTime
  intro s t
  exact residualIncidenceBound_concatenated_open B (R k) (P k n) (ν k) (m k)
    γ a b hab hdis hcount Γ hmatch (hpoint k)
      (fun i => residualConstraintFamily_open B R P ν m (Γ i) (hΓ i) k n) s t

end CircleDomainRigidity

end

end OAI
