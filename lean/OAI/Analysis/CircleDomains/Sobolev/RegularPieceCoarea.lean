import OAI.Analysis.CircleDomains.Sobolev.InversePieceCoarea
import OAI.Analysis.CircleDomains.Selection.RegularMapPieces
import OAI.Analysis.CircleDomains.Sobolev.WeightedCoareaUnion

namespace OAI

/-! Coarea on a bounded regular measurable set, using its actual scalar
coordinate map and the countable bi-Lipschitz decomposition. -/
open Set Function Filter MeasureTheory Metric Bornology
open scoped Topology NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma weighted_coarea_empty (f : ℂ → ℝ) (q : ℂ → ℝ≥0∞) :
    WeightedScalarCoareaIdentity ∅ f q := by
  constructor
  · have he : weightedScalarLevelLength ∅ f q = fun _ : ℝ => 0 := by
      funext t
      simp [weightedScalarLevelLength]
    rw [he]
    exact measurable_const.aemeasurable
  · simp [weightedScalarLevelLength]

lemma regular_piece_weighted_coarea {F : ℂ → ℂ} {f : ℂ → ℝ}
    {S : Set ℂ} {L K : ℝ≥0} (hS : MeasurableSet S) (hb : IsBounded S)
    (hL : LipschitzOnWith L F S) (hK : AntilipschitzWith K (S.domRestrict F))
    (he : ∀ z, (F z).re = f z) (hd : ∀ z ∈ S, DifferentiableAt ℝ F z)
    (hi : ∀ z ∈ S, (fderiv ℝ F z).IsInvertible)
    {q : ℂ → ℝ≥0∞} (hq : Measurable q) : WeightedScalarCoareaIdentity S f q := by
  have hinj : InjOn F S := by
    intro x hx y hy hxy
    have hh : (⟨x,hx⟩ : S) = ⟨y,hy⟩ := hK.injective hxy
    exact congrArg Subtype.val hh
  have hT : MeasurableSet (F '' S) := hS.image_of_continuousOn_injOn hL.continuousOn hinj
  have hTb : IsBounded (F '' S) := by
    obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp hb
    apply Metric.isBounded_iff.mpr
    refine ⟨L*C, ?_⟩
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
    exact (hL.dist_le_mul x hx y hy).trans (mul_le_mul_of_nonneg_left (hC hx hy) L.coe_nonneg)
  have h := inverse_piece_weighted_coarea hK he hd hi hT hTb (Subset.refl _) hq
  have hinverse : (invFunOn F S) '' (F '' S) = S := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact invFunOn_mem hy
    · intro hx
      exact ⟨F x, mem_image_of_mem F hx, hinj (invFunOn_mem (mem_image_of_mem F hx)) hx (invFunOn_eq (mem_image_of_mem F hx))⟩
  rwa [hinverse] at h

lemma regular_map_weighted_coarea {F : ℂ → ℂ} {f : ℂ → ℝ}
    (hf : Continuous f) {S : Set ℂ} (hS : MeasurableSet S) (hb : IsBounded S)
    (he : ∀ z, (F z).re = f z) (hd : ∀ z ∈ S, DifferentiableAt ℝ F z)
    (hi : ∀ z ∈ S, (fderiv ℝ F z).IsInvertible)
    {q : ℂ → ℝ≥0∞} (hq : Measurable q) : WeightedScalarCoareaIdentity S f q := by
  rcases S.eq_empty_or_nonempty with h0 | hn
  · rw [h0]
    exact weighted_coarea_empty f q
  obtain ⟨B,L,K,hB,hdj,hcover,hLK⟩ := regular_map_measurable_pieces hS hn
    (fun z hz => (hd z hz).hasFDerivAt) hi
  have hBS (n : ℕ) : B n ⊆ S := by rw [← hcover]; exact subset_iUnion B n
  have hlocal (n : ℕ) : WeightedScalarCoareaIdentity (B n) f q :=
    regular_piece_weighted_coarea (hB n) (hb.subset (hBS n)) (hLK n).1 (hLK n).2 he
      (fun z hz => hd z (hBS n hz)) (fun z hz => hi z (hBS n hz)) hq
  have hh := weighted_coarea_iUnion isOpen_univ hf.continuousOn B hB hdj
    (fun _ => subset_univ _) q hlocal
  rwa [hcover] at hh

end CircleDomainRigidity

end

end OAI
