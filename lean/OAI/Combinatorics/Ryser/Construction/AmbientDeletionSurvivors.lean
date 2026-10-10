import OAI.Combinatorics.Ryser.Construction.AmbientDeletionPoolLaw
import OAI.Combinatorics.Ryser.Construction.DeletionUnionBasic

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F] [Fintype k] [Fintype F]
  [DecidableEq k] [DecidableEq F]

def ambientPoolDeletedLines (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (a : GadgetOutcome k) (K : ℕ) (b : AmbientPool σ K) : Finset (AffineLine F) :=
  Finset.univ.biUnion (fun i => Finset.univ.biUnion
    (fun j => deletedLines σ (groupPlacement σ u v huv i) (b i j) a))

@[simp] theorem mem_ambientPoolDeletedLines (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (a : GadgetOutcome k) (K : ℕ) (b : AmbientPool σ K) (l : AffineLine F) :
    l ∈ ambientPoolDeletedLines σ u v huv a K b ↔
      ∃ i j, l ∈ deletedLines σ (groupPlacement σ u v huv i) (b i j) a := by
  simp only [ambientPoolDeletedLines, Finset.mem_biUnion, Finset.mem_univ, true_and]

def ambientPoolSurvivors (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (a : GadgetOutcome k) (K : ℕ) (b : AmbientPool σ K) : Finset (Point F) :=
  Finset.univ \ (ambientPoolDeletedLines σ u v huv a K b).biUnion linePoints

def ambientSelectedLines (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (a : GadgetOutcome k) (K : ℕ) (b : AmbientPool σ K)
    (choice : ConfigurationGroup σ → Fin K) : Finset (AffineLine F) :=
  allDeletedLines σ (groupPlacement σ u v huv) (fun i => b i (choice i)) a

@[simp] theorem mem_ambientSelectedLines (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (a : GadgetOutcome k) (K : ℕ) (b : AmbientPool σ K)
    (choice : ConfigurationGroup σ → Fin K) (l : AffineLine F) :
    l ∈ ambientSelectedLines σ u v huv a K b choice ↔
      ∃ i, l ∈ deletedLines σ (groupPlacement σ u v huv i) (b i (choice i)) a :=
  mem_allDeletedLines σ (groupPlacement σ u v huv) (fun i => b i (choice i)) a l

def ambientSelectedSurvivors (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (a : GadgetOutcome k) (K : ℕ) (b : AmbientPool σ K)
    (choice : ConfigurationGroup σ → Fin K) : Finset (Point F) :=
  Finset.univ \ (ambientSelectedLines σ u v huv a K b choice).biUnion linePoints

theorem mem_ambientSelectedSurvivors (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (a : GadgetOutcome k) (K : ℕ) (b : AmbientPool σ K)
    (choice : ConfigurationGroup σ → Fin K) (x : Point F) :
    x ∈ ambientSelectedSurvivors σ u v huv a K b choice ↔
      ∀ l ∈ ambientSelectedLines σ u v huv a K b choice, ¬Incidence x l := by
  constructor
  · intro hx l hl hxl
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_biUnion.mpr
      ⟨l, hl, (mem_linePoints x l).mpr hxl⟩)
  · intro hx
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
    intro h
    obtain ⟨l, hl, hxl⟩ := Finset.mem_biUnion.mp h
    exact hx l hl ((mem_linePoints x l).mp hxl)

theorem mem_survivors_ambientPoolConfig (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (a : GadgetOutcome k) (ha : OriginalLineDensity a) (K : ℕ) (b : AmbientPool σ K)
    (ignore : Finset (Finset (Point F))) (x : Point F) :
    x ∈ LineCover.survivors ignore (ambientPoolConfig σ u v huv a ha K b) ↔
      ∀ i j l, l ∈ deletedLines σ (groupPlacement σ u v huv i) (b i j) a →
        linePoints l ∉ ignore → ¬Incidence x l := by
  constructor
  · intro hx i j l hl hi hxl
    have ht := LineCover.mem_survivors.mp hx
      ((Fintype.equivFin (AmbientPosition σ K)) (i, j))
    rw [ambientPoolConfig_at] at ht
    apply ht
    exact (mem_deleted_ambientLineOutcome _ _ ignore x).mpr ⟨l, hl, hi, hxl⟩
  · intro h
    apply LineCover.mem_survivors.mpr
    intro t hx
    change x ∈ LineCover.deleted ignore
      (ambientTrialOutcome σ (groupPlacement σ u v huv (ambientPosition σ K t).1)
        a ha K (b (ambientPosition σ K t).1 (ambientPosition σ K t).2)) at hx
    rw [ambientTrialOutcome, mem_deleted_ambientLineOutcome] at hx
    obtain ⟨l, hl, hi, hxl⟩ := hx
    exact h (ambientPosition σ K t).1 (ambientPosition σ K t).2 l hl hi hxl

theorem ambientPoolConfig_survivors (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (a : GadgetOutcome k) (ha : OriginalLineDensity a) (K : ℕ) (b : AmbientPool σ K) :
    LineCover.survivors ∅ (ambientPoolConfig σ u v huv a ha K b) =
      ambientPoolSurvivors σ u v huv a K b := by
  ext x
  rw [mem_survivors_ambientPoolConfig]
  constructor
  · intro h
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hx
    obtain ⟨l, hl, hxl⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨i, j, hij⟩ := (mem_ambientPoolDeletedLines σ u v huv a K b l).mp hl
    exact h i j l hij (by simp) ((mem_linePoints x l).mp hxl)
  · intro hx i j l hl _ hxl
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_biUnion.mpr
      ⟨l, (mem_ambientPoolDeletedLines σ u v huv a K b l).mpr ⟨i, j, hl⟩,
        (mem_linePoints x l).mpr hxl⟩)

theorem ambientSelectedLines_subset_pool (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (a : GadgetOutcome k) (K : ℕ) (b : AmbientPool σ K)
    (choice : ConfigurationGroup σ → Fin K) :
    ambientSelectedLines σ u v huv a K b choice ⊆ ambientPoolDeletedLines σ u v huv a K b := by
  intro l hl
  obtain ⟨i, hi⟩ := (mem_ambientSelectedLines σ u v huv a K b choice l).mp hl
  exact (mem_ambientPoolDeletedLines σ u v huv a K b l).mpr ⟨i, choice i, hi⟩

theorem ambientPool_survivors_subset_selected (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (a : GadgetOutcome k) (ha : OriginalLineDensity a) (K : ℕ) (b : AmbientPool σ K)
    (choice : ConfigurationGroup σ → Fin K) :
    LineCover.survivors ∅ (ambientPoolConfig σ u v huv a ha K b) ⊆
      ambientSelectedSurvivors σ u v huv a K b choice := by
  intro x hx
  apply (mem_ambientSelectedSurvivors σ u v huv a K b choice x).mpr
  intro l hl
  obtain ⟨i, hi⟩ := (mem_ambientSelectedLines σ u v huv a K b choice l).mp hl
  exact (mem_survivors_ambientPoolConfig σ u v huv a ha K b ∅ x).mp hx
    i (choice i) l hi (by simp)

theorem ambientPool_ignored_survivors_subset_selected (σ : k →+* F)
    (u v : k) (huv : u ≠ v) (a : GadgetOutcome k) (ha : OriginalLineDensity a)
    (K : ℕ) (b : AmbientPool σ K) (choice : ConfigurationGroup σ → Fin K)
    (ell : AffineLine F) (hell : ell ∉ ambientSelectedLines σ u v huv a K b choice) :
    LineCover.survivors {linePoints ell} (ambientPoolConfig σ u v huv a ha K b) ⊆
      ambientSelectedSurvivors σ u v huv a K b choice := by
  intro x hx
  apply (mem_ambientSelectedSurvivors σ u v huv a K b choice x).mpr
  intro l hl
  obtain ⟨i, hi⟩ := (mem_ambientSelectedLines σ u v huv a K b choice l).mp hl
  apply (mem_survivors_ambientPoolConfig σ u v huv a ha K b {linePoints ell} x).mp hx
    i (choice i) l hi
  intro hignore
  have heq : l = ell := ambient_linePoints_injective (Finset.mem_singleton.mp hignore)
  exact hell (heq ▸ hl)

theorem ambientPool_goodLineCover_selected (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (a : GadgetOutcome k) (ha : OriginalLineDensity a) (K : ℕ) (b : AmbientPool σ K)
    (choice : ConfigurationGroup σ → Fin K) (δ ρ : ℝ)
    (hgood : LineCover.GoodLineCover δ ρ (ambientPoolConfig σ u v huv a ha K b)) :
    (∀ ell, ell ∉ ambientSelectedLines σ u v huv a K b choice →
      δ * Fintype.card F / 2 ≤
        ((ambientSelectedSurvivors σ u v huv a K b choice ∩ linePoints ell).card : ℝ)) ∧
    (∀ L : Finset (AffineLine F), L.card ≤ Fintype.card F →
      ambientSelectedSurvivors σ u v huv a K b choice ⊆ L.biUnion linePoints →
      ∃ p : ProjectivePoint F,
        (1 - ρ) * Fintype.card F ≤ ((LineCover.coverPencil L p).card : ℝ)) := by
  constructor
  · intro ell hell
    apply (hgood.1 ell).trans
    exact_mod_cast Finset.card_le_card (Finset.inter_subset_inter
      (ambientPool_ignored_survivors_subset_selected σ u v huv a ha K b choice ell hell)
      (Finset.Subset.refl _))
  · intro L hL hcover
    apply hgood.2 L hL
    have hsub := (ambientPool_survivors_subset_selected σ u v huv a ha K b choice).trans hcover
    rw [Finset.sdiff_eq_empty_iff_subset.mpr hsub, Finset.card_empty]
    exact Nat.zero_le _

end RyserCoveringCounterexample.Construction

end

end OAI
