import OAI.Probability.GammaPassage.SpatialChunkWitness
import OAI.Probability.GammaPassage.PathColumnCrossing

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP Set

lemma spatialChunkIndex_transverse_column (b : ℝ) (k m : ℕ) (p : Vertex) (i : ℤ) :
    0 ≤ transverse b p-transverse b (spatialTranslate b k m (i,(spatialChunkIndex b k m p).2)) ∧
      transverse b p-transverse b (spatialTranslate b k m (i,(spatialChunkIndex b k m p).2)) < (2 : ℝ)^k+1 := by
  have hs : (0 : ℝ) < 2^k := by positivity
  have hl := (le_div_iff₀ hs).mp (Int.floor_le (transverse b p/(2 : ℝ)^k))
  have hu := (div_lt_iff₀ hs).mp (Int.lt_floor_add_one (transverse b p/(2 : ℝ)^k))
  have hf := Int.floor_le (b*(i*(2 : ℤ)^m))
  have hf' := Int.lt_floor_add_one (b*(i*(2 : ℤ)^m))
  rw [spatialTranslate_center]
  simp only [spatialChunkIndex,Int.cast_ofNat] at hf hf' ⊢
  constructor <;> nlinarith [hf,hf']

lemma chunk_subcrossing_region (b : ℝ) (k m : ℕ) (hs : 2 ≤ (2 : ℝ)^k)
    (p z : Vertex)
    (hx : ((spatialChunkIndex b k m p).1+1)*(2 : ℤ)^m ≤ z.1 ∧
      z.1 ≤ ((spatialChunkIndex b k m p).1+2)*(2 : ℤ)^m)
    (hr : |transverse b z-transverse b p| ≤ (2 : ℝ)^k+1) :
    z ∈ rareFastRegion b 1 8 ((2 : ℝ)^k) ((2 : ℤ)^m)
      (spatialTranslate b k m (spatialChunkIndex b k m p+(1,0))) := by
  have hcenter := spatialChunkIndex_transverse_column b k m p ((spatialChunkIndex b k m p).1+1)
  have ht : transverse b (z-spatialTranslate b k m (spatialChunkIndex b k m p+(1,0))) =
      transverse b z-transverse b (spatialTranslate b k m (spatialChunkIndex b k m p+(1,0))) := by
    simp [transverse]; ring
  have hx' : 0 ≤ (z-spatialTranslate b k m (spatialChunkIndex b k m p+(1,0))).1 ∧
      (z-spatialTranslate b k m (spatialChunkIndex b k m p+(1,0))).1 ≤ (2 : ℤ)^m := by
    simp only [spatialTranslate,Prod.fst_add,Prod.fst_sub]
    constructor <;> nlinarith [hx.1,hx.2]
  have hxR : 0 ≤ ((z-spatialTranslate b k m (spatialChunkIndex b k m p+(1,0))).1 : ℝ) ∧
      ((z-spatialTranslate b k m (spatialChunkIndex b k m p+(1,0))).1 : ℝ) ≤ (2 : ℝ)^m := by exact_mod_cast hx'
  refine ⟨by simpa using (show -(2 : ℝ)^m ≤ ((z-spatialTranslate b k m (spatialChunkIndex b k m p+(1,0))).1 : ℝ) by linarith [pow_pos (by norm_num : (0 : ℝ)<2) m]),?_,?_⟩
  · push_cast
    nlinarith [hxR.2,pow_pos (by norm_num : (0 : ℝ)<2) m]
  · rw [ht]
    have hcenter' : 0 ≤ transverse b p-transverse b (spatialTranslate b k m (spatialChunkIndex b k m p+(1,0))) ∧
        transverse b p-transverse b (spatialTranslate b k m (spatialChunkIndex b k m p+(1,0))) < (2 : ℝ)^k+1 := by
      have he : spatialChunkIndex b k m p+(1,0)=((spatialChunkIndex b k m p).1+1,(spatialChunkIndex b k m p).2) := by ext <;> simp
      rw [he]
      exact hcenter
    have hz := abs_le.mp hr
    apply abs_le.mpr
    constructor <;> nlinarith [hcenter'.1,hcenter'.2]

lemma pathEdges_append (p : Vertex) (ds es : List Step) :
    pathEdges p (ds++es)=pathEdges p ds ∪ pathEdges (p+displacement ds) es := by
  induction ds generalizing p with
  | nil => simp [pathEdges]
  | cons d ds ih => simp [pathEdges,ih,displacement_cons,add_assoc,Finset.insert_union]

lemma pathEdges_middle_subset (p : Vertex) (pre mid post : List Step) :
    pathEdges (p+displacement pre) mid ⊆ pathEdges p (pre++mid++post) := by
  rw [pathEdges_append,pathEdges_append]
  exact Finset.Subset.trans Finset.subset_union_right Finset.subset_union_left

end GammaFPP.CrossingBridge

end OAI
