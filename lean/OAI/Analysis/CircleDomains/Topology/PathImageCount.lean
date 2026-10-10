import OAI.Analysis.CircleDomains.Topology.ClosedTimeCounts

namespace OAI

/-! Distinct image intersections with a closed set. Finite separated
image witnesses make this count Borel without counting repeated visits. -/

open Set Function MeasureTheory
open scoped Topology ENNReal Classical

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

def pathImageCount (H : Set X) (γ : C(PathTime, X)) : ℝ≥0∞ :=
  ∑' x : X, if x ∈ range γ ∩ H then (1 : ℝ≥0∞) else 0

def imageHitAtLeast (H : Set X) (n : ℕ) : Set C(PathTime, X) :=
  {γ | ∃ t : Fin n → PathTime, Injective (γ ∘ t) ∧ ∀ i, γ (t i) ∈ H}

def separatedImageHits (H : Set X) (n : ℕ) (r : ℝ) : Set C(PathTime, X) :=
  {γ | ∃ t : Fin n → PathTime,
    (∀ i j, i ≠ j → r ≤ dist (γ (t i)) (γ (t j))) ∧ ∀ i, γ (t i) ∈ H}

theorem isClosed_separatedImageHits {H : Set X} (hH : IsClosed H) (n : ℕ) (r : ℝ) :
    IsClosed (separatedImageHits H n r) := by
  let E : Set (C(PathTime, X) × (Fin n → PathTime)) :=
    {p | (∀ i j, i ≠ j → r ≤ dist (p.1 (p.2 i)) (p.1 (p.2 j))) ∧
      ∀ i, p.1 (p.2 i) ∈ H}
  have he (i : Fin n) : Continuous (fun p : C(PathTime, X) × (Fin n → PathTime) =>
      p.1 (p.2 i)) := continuous_eval.comp
    (continuous_fst.prodMk ((continuous_apply i).comp continuous_snd))
  have hE : IsClosed E := by
    have hsep : IsClosed {p : C(PathTime, X) × (Fin n → PathTime) |
        ∀ i j, i ≠ j → r ≤ dist (p.1 (p.2 i)) (p.1 (p.2 j))} := by
      simp only [ofPred_forall]
      exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
        isClosed_le continuous_const ((he i).dist (he j))
    have hmem : IsClosed {p : C(PathTime, X) × (Fin n → PathTime) |
        ∀ i, p.1 (p.2 i) ∈ H} := by
      simp only [ofPred_forall]
      exact isClosed_iInter fun i => hH.preimage (he i)
    exact hsep.inter hmem
  have hp : Prod.fst '' E = separatedImageHits H n r := by
    ext γ
    constructor
    · rintro ⟨⟨_, t⟩, ht, rfl⟩
      exact ⟨t, ht⟩
    · rintro ⟨t, ht⟩
      exact ⟨(γ, t), ht, rfl⟩
  rw [← hp]
  exact isClosedMap_fst_of_compactSpace E hE

theorem imageHitAtLeast_eq_iUnion (H : Set X) (n : ℕ) :
    imageHitAtLeast H n = ⋃ m : ℕ, separatedImageHits H n (1 / ((m : ℝ) + 1)) := by
  ext γ
  constructor
  · rintro ⟨t, ht, hH⟩
    obtain ⟨m, hm⟩ := exists_reciprocal_separation (γ ∘ t) ht
    exact mem_iUnion.mpr ⟨m, t, hm, hH⟩
  · intro h
    obtain ⟨m, t, ht, hH⟩ := mem_iUnion.mp h
    refine ⟨t, ?_, hH⟩
    intro i j he
    by_contra hij
    have hd := ht i j hij
    change γ (t i) = γ (t j) at he
    rw [he, dist_self] at hd
    have : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    linarith

theorem pathImageCount_eq_iSup (H : Set X) (γ : C(PathTime, X)) :
    pathImageCount H γ = ⨆ n : ℕ,
      if γ ∈ imageHitAtLeast H n then (n : ℝ≥0∞) else 0 := by
  apply le_antisymm
  · rw [pathImageCount, ENNReal.tsum_eq_iSup_sum]
    apply iSup_le
    intro F
    let E := F.filter (fun x => x ∈ range γ ∩ H)
    let e : Fin (Fintype.card E) ≃ E := (Fintype.equivFin E).symm
    have hE (i : Fin (Fintype.card E)) : (e i).val ∈ range γ ∩ H :=
      (Finset.mem_filter.mp (e i).property).2
    choose t ht using fun i => (hE i).1
    have he : γ ∈ imageHitAtLeast H (Fintype.card E) := by
      refine ⟨t, ?_, fun i => (ht i).symm ▸ (hE i).2⟩
      intro i j hij
      apply e.injective
      apply Subtype.ext
      exact (ht i).symm.trans (hij.trans (ht j))
    have hn : (Fintype.card E : ℝ≥0∞) ≤ ⨆ n : ℕ,
        if γ ∈ imageHitAtLeast H n then (n : ℝ≥0∞) else 0 := by
      exact (ite_eq_left he).symm.le.trans (le_iSup
        (fun n : ℕ => if γ ∈ imageHitAtLeast H n then (n : ℝ≥0∞) else 0) _)
    simpa only [Finset.sum_boole, Fintype.card_coe] using hn
  · apply iSup_le
    intro n
    split
    · rename_i hn
      obtain ⟨t, ht, hH⟩ := hn
      have hm (i : Fin n) : γ (t i) ∈ range γ ∩ H := ⟨mem_range_self _, hH i⟩
      calc
        (n : ℝ≥0∞) = ∑' i : Fin n,
            if γ (t i) ∈ range γ ∩ H then (1 : ℝ≥0∞) else 0 := by
          simp only [hm, ite_true, tsum_fintype, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul, mul_one]
        _ ≤ pathImageCount H γ := ENNReal.tsum_comp_le_tsum_of_injective ht
          (fun x => if x ∈ range γ ∩ H then (1 : ℝ≥0∞) else 0)
    · exact bot_le

variable [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem measurable_pathImageCount {H : Set X} (hH : IsClosed H) :
    Measurable (pathImageCount H) := by
  change Measurable (fun γ => pathImageCount H γ)
  simp_rw [pathImageCount_eq_iSup]
  apply Measurable.iSup
  intro n
  apply measurable_const.piecewise _ measurable_const
  rw [imageHitAtLeast_eq_iUnion]
  exact MeasurableSet.iUnion fun m =>
    (isClosed_separatedImageHits hH n (1 / ((m : ℝ) + 1))).measurableSet

end CircleDomainRigidity

end

end OAI
