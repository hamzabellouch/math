import OAI.Probability.FirstPassage.SpatialChunks
import OAI.Probability.FirstPassage.PathWitnesses

namespace OAI

namespace PlanarFPP
open Set

lemma negative_midpoint_spatial_witness (w : Edge → ℝ) (b m₀ am ap K η : ℝ)
    (ha : am ≤ ap) (k m : ℕ) (ih : ℤ×ℤ) (p : Vertex) (ds : List Step)
    (hin : PathIn p ds {z | z-spatialTranslate b k m ih ∈ endpointBox b 4 4 k m})
    (hc : defect w b m₀ ((am+ap)/2) p ds < -η*(2 : ℝ)^k) :
    ∃ q ∈ spatialWitnessFamily b m₀ am ap K η k m ih,
      q.start=p ∧ q.steps=ds ∧ q.Good w := by
  have hid := minimum_defect w b m₀ am ap ha p ds
  have hn : 0 ≤ ((ap-am)/2)*|transverse b (displacement ds)| := mul_nonneg (by linarith) (abs_nonneg _)
  have hmin : min (defect w b m₀ ap p ds) (defect w b m₀ am p ds) < -η*(2 : ℝ)^k := by linarith
  rcases min_lt_iff.mp hmin with hp | hm
  · refine ⟨⟨p,ds,support b m₀ ap (displacement ds)-η*(2 : ℝ)^k⟩,
      Or.inl ⟨hin,Or.inr rfl⟩,rfl,rfl,?_⟩
    change pathCost w p ds < _
    unfold defect at hp
    linarith
  · refine ⟨⟨p,ds,support b m₀ am (displacement ds)-η*(2 : ℝ)^k⟩,
      Or.inl ⟨hin,Or.inl rfl⟩,rfl,rfl,?_⟩
    change pathCost w p ds < _
    unfold defect at hm
    linarith

theorem full_chunk_transverse_witness (w : Edge → ℝ) (b m₀ am ap K η : ℝ)
    (hb : |b| ≤ 1) (ha : am ≤ ap) (hη : 0 < η) (hgap : 4*η ≤ (ap-am)/2)
    (k m : ℕ) (hs : 2 ≤ (2 : ℝ)^k) (p : Vertex) (ds : List Step)
    (hfull : FullSpatialChunk b k m ds)
    (htrans : (2 : ℝ)^k ≤ |transverse b (displacement ds)|)
    (hcheap : defect w b m₀ ((am+ap)/2) p ds < η*(2 : ℝ)^k) :
    ∃ q ∈ spatialWitnessFamily b m₀ am ap K η k m (spatialChunkIndex b k m p),
      q.start=p ∧ q.steps=ds ∧ q.Good w := by
  have hin := fullSpatialChunk_in_box b hb k m hs p ds hfull
  have hc := transverse_chunk_witness w b m₀ am ap η ((2 : ℝ)^k) ha (by positivity) hη hgap p ds htrans hcheap
  rcases hc with hp | hm
  · refine ⟨⟨p,ds,support b m₀ ap (displacement ds)-η*(2 : ℝ)^k⟩,
      Or.inl ⟨hin,Or.inr rfl⟩,rfl,rfl,?_⟩
    change pathCost w p ds < _
    unfold defect at hp
    linarith
  · refine ⟨⟨p,ds,support b m₀ am (displacement ds)-η*(2 : ℝ)^k⟩,
      Or.inl ⟨hin,Or.inl rfl⟩,rfl,rfl,?_⟩
    change pathCost w p ds < _
    unfold defect at hm
    linarith

lemma negative_longitudinal_chunk_not_cheap (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (b m₀ a η : ℝ) (hb : |b| ≤ 1) (k m : ℕ) (p : Vertex) (ds : List Step)
    (hfull : FullSpatialChunk b k m ds)
    (hx : (displacement ds).1= -2*(2 : ℤ)^m)
    (hscale : η*(2 : ℝ)^k < 2*m₀*(2 : ℝ)^m-|a| *((2 : ℝ)^k+1)) :
    η*(2 : ℝ)^k < defect w b m₀ a p ds := by
  have hr := (proper_chunk_endpoint_localization b hb k m ds hfull.1).2
  have hc := pathCost_nonneg hw p ds
  have hmul := mul_le_mul_of_nonneg_left hr (abs_nonneg a)
  have hab := le_abs_self (a*transverse b (displacement ds))
  rw [abs_mul] at hab
  unfold defect support
  rw [hx]
  push_cast
  nlinarith

end PlanarFPP

end OAI
