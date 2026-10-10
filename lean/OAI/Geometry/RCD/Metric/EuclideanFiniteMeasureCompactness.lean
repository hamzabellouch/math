import OAI.Geometry.RCD.Metric.EuclideanPairCompactness

namespace OAI

/-! # Compactness of bounded local Euclidean energy measures -/

open Set Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates

theorem euclidean_finite_measure_subsequence {n : ℕ}
    (νs : ℕ → FiniteMeasure (Euclidean n)) (C : ℝ≥0) (B : ℝ)
    (hm : ∀ k, (νs k).mass≤C)
    (hs : ∀ k, ∀ᵐ z ∂(νs k : Measure (Euclidean n)), z∈closedBall 0 B) :
    ∃ ν : FiniteMeasure (Euclidean n), ∃ t : ℕ → ℕ,
      StrictMono t ∧ Tendsto (νs ∘ t) atTop (𝓝 ν) ∧ ν.mass≤C ∧
      (∀ᵐ z ∂(ν : Measure (Euclidean n)), z∈closedBall 0 B) := by
  classical
  have hC := isCompact_setOfPred_finiteMeasure_le_of_isCompact C
    (isCompact_closedBall (0:Euclidean n) B)
  have hmem (k : ℕ) : νs k∈{ν : FiniteMeasure (Euclidean n) |
      ν.mass≤C ∧ ν (closedBall 0 B)ᶜ=0} := by
    refine ⟨hm k,?_⟩
    exact (FiniteMeasure.null_iff_toMeasure_null _ _).mpr (ae_iff.mp (hs k))
  let q₀ : ProbabilityMeasure (Euclidean n) := ⟨Measure.dirac 0,Measure.dirac.isProbabilityMeasure⟩
  let ρ : ℕ → ProbabilityMeasure (Euclidean n) := fun k =>
    if νs k=0 then q₀ else (νs k).normalize
  let A := closedBall (0:Euclidean n) B∪{0}
  have hA : IsCompact A := (isCompact_closedBall _ _).union (isCompact_singleton)
  have hρA (k : ℕ) : (ρ k : Measure (Euclidean n)) Aᶜ=0 := by
    by_cases hk : νs k=0
    · simp only [ρ,ite_eq_left hk]
      change (Measure.dirac (0:Euclidean n)) Aᶜ=0
      simp [A]
    · simp only [ρ,ite_eq_right hk]
      rw [(νs k).toMeasure_normalize_eq_of_nonzero hk,Measure.smul_apply]
      have hz : (νs k : Measure (Euclidean n)) Aᶜ=0 :=
        measure_mono_null (compl_subset_compl.mpr subset_union_left) (ae_iff.mp (hs k))
      rw [hz,smul_zero]
  have hT : IsTightMeasureSet {((q : ProbabilityMeasure (Euclidean n)) :
      Measure (Euclidean n)) | q∈range ρ} := by
    apply isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mpr
    intro ε hε
    refine ⟨A,hA,?_⟩
    rintro μ ⟨q,⟨k,rfl⟩,rfl⟩
    exact (hρA k).le.trans hε.le
  obtain ⟨q,_,a,ha,hqlim⟩ := (isCompact_closure_of_isTightMeasureSet hT).tendsto_subseq
    (fun k => subset_closure (mem_range_self k))
  obtain ⟨m,_,b,hb,hmlim⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ≥0) C)).tendsto_subseq
    (fun k => show (νs (a k)).mass∈Icc 0 C from ⟨bot_le,hm _⟩)
  let ν : FiniteMeasure (Euclidean n) := m • q.toFiniteMeasure
  have hlim : Tendsto (νs ∘ (a ∘ b)) atTop (𝓝 ν) := by
    have hq := (ProbabilityMeasure.toFiniteMeasure_continuous.tendsto q).comp
      (hqlim.comp hb.tendsto_atTop)
    have hh := hmlim.smul hq
    convert hh using 1
    funext k
    dsimp only [Function.comp_def]
    by_cases hk : νs (a (b k))=0
    · simp [ρ,hk]
    · simpa only [ρ,ite_eq_right hk] using (νs (a (b k))).self_eq_mass_smul_normalize
  have hν := hC.isClosed.mem_of_tendsto hlim (Eventually.of_forall fun k => hmem (a (b k)))
  let t := a ∘ b
  have ht : StrictMono t := ha.comp hb
  refine ⟨ν,t,ht,hlim,hν.1,?_⟩
  exact ae_iff.mpr ((FiniteMeasure.null_iff_toMeasure_null _ _).mp hν.2)

end RegularPointCoordinates

end

end OAI
