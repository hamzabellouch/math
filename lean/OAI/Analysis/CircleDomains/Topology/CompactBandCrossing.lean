import OAI.Analysis.CircleDomains.Selection.BandGraph
import Mathlib.Topology.Connected.Basic

namespace OAI

/-! A compact graph with nonempty interval fibers has the intermediate
value property along connected sets. This supplies the sign separation
argument for the closed coordinate bands, including at dust points. -/

open Set

noncomputable section
namespace CircleDomainRigidity

theorem compact_band_crossing
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {K : Set (X × ℝ)} (hK : IsCompact K) {C : Set X}
    (hC : IsPreconnected C)
    (hne : ∀ x ∈ C, {t : ℝ | (x, t) ∈ K}.Nonempty)
    (hinterval : ∀ x ∈ C, OrdConnected {t : ℝ | (x, t) ∈ K})
    {x y : X} (hx : x ∈ C) (hy : y ∈ C) {a b v : ℝ}
    (ha : (x, a) ∈ K) (hb : (y, b) ∈ K) (hav : a ≤ v) (hvb : v ≤ b) :
    ∃ z ∈ C, (z, v) ∈ K := by
  let L := Prod.fst '' (K ∩ {p : X × ℝ | p.2 ≤ v})
  let R := Prod.fst '' (K ∩ {p : X × ℝ | v ≤ p.2})
  have hL : IsClosed L :=
    ((hK.inter_right (isClosed_le continuous_snd continuous_const)).image continuous_fst).isClosed
  have hR : IsClosed R :=
    ((hK.inter_right (isClosed_le continuous_const continuous_snd)).image continuous_fst).isClosed
  have hcover : C ⊆ L ∪ R := by
    intro z hz
    obtain ⟨t, ht⟩ := hne z hz
    rcases le_total t v with h | h
    · exact Or.inl ⟨(z, t), ⟨ht, h⟩, rfl⟩
    · exact Or.inr ⟨(z, t), ⟨ht, h⟩, rfl⟩
  obtain ⟨z, hz, hzL, hzR⟩ := (isPreconnected_closed_iff.mp hC) L R hL hR hcover
    ⟨x, hx, (x, a), ⟨ha, hav⟩, rfl⟩ ⟨y, hy, (y, b), ⟨hb, hvb⟩, rfl⟩
  obtain ⟨⟨z₁, u⟩, ⟨hu, huv⟩, he₁⟩ := hzL
  obtain ⟨⟨z₂, w⟩, ⟨hw, hvw⟩, he₂⟩ := hzR
  change z₁ = z at he₁
  change z₂ = z at he₂
  subst z₁
  subst z₂
  exact ⟨z, hz, (hinterval z hz).out hu hw ⟨huv, hvw⟩⟩

theorem real_band_graph_crossing
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {G : Set X} {f : X → ℝ} {M : ℝ} (hM : ∀ z ∈ G, |f z| ≤ M)
    {C : Set X} (hC : IsPreconnected C) (hCG : C ⊆ closure G)
    {x y : X} (hx : x ∈ C) (hy : y ∈ C) {a b v : ℝ}
    (ha : (x, a) ∈ intervalFiberHull (clusterGraph G f))
    (hb : (y, b) ∈ intervalFiberHull (clusterGraph G f))
    (hav : a ≤ v) (hvb : v ≤ b) :
    ∃ z ∈ C, (z, v) ∈ intervalFiberHull (clusterGraph G f) := by
  apply compact_band_crossing (isCompact_intervalFiberHull (isCompact_clusterGraph hM))
    hC ?_ ?_ hx hy ha hb hav hvb
  · intro z hz
    obtain ⟨t, ht⟩ := clusterGraph_fiber_nonempty_of_mem_closure hM (hCG hz)
    exact ⟨t, subset_intervalFiberHull _ ht⟩
  · intro z hz
    rw [intervalFiberHull_fiber_eq_Icc (isCompact_clusterGraph hM) z
      (clusterGraph_fiber_nonempty_of_mem_closure hM (hCG hz))]
    exact ordConnected_Icc

end CircleDomainRigidity

end

end OAI
