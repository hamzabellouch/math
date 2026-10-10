import OAI.Analysis.CircleDomains.Rigidity.CorrespondenceMaskContinuity

namespace OAI

/-! Retain the open plateau, raw interval membership and continuity in
one neighborhood. These are the exact data needed by Sobolev gluing. -/
open Set Function Filter Metric MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem correspondence_mask_plateau_neighborhood
    {X Y : Type*} [PseudoMetricSpace X] [TopologicalSpace Y] [CompactSpace Y]
    {R : X → Y → Prop} (hR : IsClosed {p : X × Y | R p.1 p.2})
    {s : X → Y} (hs : ∀ q, R q (s q)) {φ : Y → ℝ} (hφ : Continuous φ)
    {cutoff : ℕ → X → ℝ} (hc : ∀ j q, cutoff j q ∈ Icc (0:ℝ) 1)
    (hcc : ∀ j, Continuous (cutoff j)) (c : ℕ → X) {d ε : ℕ → ℝ}
    (hd : Tendsto d atTop (𝓝 0)) (hε : Tendsto ε atTop (𝓝 0))
    (hout : ∀ j q, d j ≤ dist q (c j) → cutoff j q = 1)
    {I : ℕ → Set ℝ} (hI : ∀ j, MeasurableSet (I j)) (hIf : ∀ j, volume (I j) ≠ ⊤)
    (hrep : ∀ j t, t ∈ I j → ∃ p, R (c j) p ∧ |t-φ p| ≤ ε j)
    {K Z : Set X} (hK : IsCompact K) (hZ : IsOpen Z) (hKZ : K ⊆ Z)
    {j : ℕ} (hzero : ∀ q ∈ Z, cutoff j q = 0)
    {A B η β : ℝ} (hη : 0 < η) (hIj : I j = Ioo A B) (hβ : β ∈ I j)
    (hmargin : ∀ q ∈ K, ∀ p, R q p → φ p ∈ Ioo (A+η) (B-η)) (a : ℝ) :
    ∃ V : Set X, IsOpen V ∧ K ⊆ V ∧
      ContinuousOn (fun q => infiniteTracePrimitive cutoff I a q (φ (s q))) V ∧
      ∀ q ∈ V, cutoff j q = 0 ∧ φ (s q) ∈ I j := by
  obtain ⟨N,V,hV,hKV,hcont,_⟩ := correspondence_mask_indexed_neighborhood hR hs hφ hc hcc c
    hd hε hout hI hIf hrep hK hZ hKZ hzero hη hIj hβ hmargin a
  obtain ⟨W,hW,hKW,hraw⟩ := closed_relation_neighborhood hR ((isOpen_Ioo : IsOpen (Ioo A B)).preimage hφ) (by
    intro q hq p hp
    have h := hmargin q hq p hp
    exact ⟨by linarith [h.1],by linarith [h.2]⟩)
  refine ⟨V ∩ Z ∩ W,(hV.inter hZ).inter hW,
    (fun q hq => ⟨⟨hKV hq,hKZ hq⟩,hKW hq⟩),hcont.mono (fun _ h => h.1.1),?_⟩
  intro q hq
  refine ⟨hzero q hq.1.2,?_⟩
  rw [hIj]
  exact hraw q hq.2 _ (hs q)

end CircleDomainRigidity

end

end OAI
