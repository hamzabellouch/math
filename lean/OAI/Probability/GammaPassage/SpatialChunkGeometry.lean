import OAI.Probability.GammaPassage.SpatialWitnesses

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP Set

noncomputable def spatialChunkIndex (b : ℝ) (k m : ℕ) (p : Vertex) : ℤ×ℤ :=
  (p.1/(2 : ℤ)^m,⌊transverse b p/(2 : ℝ)^k⌋)

lemma spatialTranslate_center (b : ℝ) (k m : ℕ) (ih : ℤ×ℤ) :
    transverse b (spatialTranslate b k m ih) =
      (⌊b*(ih.1*(2 : ℤ)^m)⌋ : ℝ)-b*(ih.1*(2 : ℤ)^m)+(ih.2 : ℝ)*(2 : ℝ)^k := by
  simp [spatialTranslate,transverse]
  ring

lemma spatialChunkIndex_horizontal (b : ℝ) (k m : ℕ) (p : Vertex) :
    0 ≤ p.1-(spatialTranslate b k m (spatialChunkIndex b k m p)).1 ∧
      p.1-(spatialTranslate b k m (spatialChunkIndex b k m p)).1 < (2 : ℤ)^m := by
  have h := meshFloor_bounds p.1 ((2 : ℤ)^m) (by positivity)
  dsimp [spatialChunkIndex,spatialTranslate,meshFloor] at *
  omega

lemma spatialChunkIndex_transverse (b : ℝ) (k m : ℕ) (p : Vertex) :
    0 ≤ transverse b p-transverse b (spatialTranslate b k m (spatialChunkIndex b k m p)) ∧
      transverse b p-transverse b (spatialTranslate b k m (spatialChunkIndex b k m p)) < (2 : ℝ)^k+1 := by
  have hs : (0 : ℝ) < 2^k := by positivity
  have hl := (le_div_iff₀ hs).mp (Int.floor_le (transverse b p/(2 : ℝ)^k))
  have hu := (div_lt_iff₀ hs).mp (Int.lt_floor_add_one (transverse b p/(2 : ℝ)^k))
  have hf := Int.floor_le (b*((spatialChunkIndex b k m p).1*(2 : ℤ)^m))
  have hf' := Int.lt_floor_add_one (b*((spatialChunkIndex b k m p).1*(2 : ℤ)^m))
  rw [spatialTranslate_center]
  simp only [spatialChunkIndex,Int.cast_ofNat] at hf hf' ⊢
  constructor <;> nlinarith [hf,hf']

/-- Source chunk localization, including the possible one-unit transverse
overshoot at the first exit. -/
lemma spatial_chunk_vertex_in_box (b : ℝ) (k m : ℕ) (hs : 2 ≤ (2 : ℝ)^k) (p z : Vertex)
    (hx : |z.1-p.1| ≤ 2*(2 : ℤ)^m)
    (hr : |transverse b z-transverse b p| ≤ (2 : ℝ)^k+1) :
    z-spatialTranslate b k m (spatialChunkIndex b k m p) ∈ endpointBox b 4 4 k m := by
  have hpx := spatialChunkIndex_horizontal b k m p
  have hpr := spatialChunkIndex_transverse b k m p
  have hpxR : 0 ≤ (p.1 : ℝ)-((spatialTranslate b k m (spatialChunkIndex b k m p)).1 : ℝ) ∧
      (p.1 : ℝ)-((spatialTranslate b k m (spatialChunkIndex b k m p)).1 : ℝ) < (2 : ℝ)^m := by
    exact_mod_cast hpx
  have hxR : |(z.1 : ℝ)-(p.1 : ℝ)| ≤ 2*(2 : ℝ)^m := by exact_mod_cast hx
  have hzx := abs_le.mp hxR
  have hzr := abs_le.mp hr
  have htrans : transverse b (z-spatialTranslate b k m (spatialChunkIndex b k m p)) =
      transverse b z-transverse b (spatialTranslate b k m (spatialChunkIndex b k m p)) := by
    simp [transverse]; ring
  constructor
  · simp only [Prod.fst_sub,Int.cast_sub]
    apply abs_le.mpr
    constructor <;> linarith [hpxR.1,hpxR.2,pow_pos (by norm_num : (0 : ℝ) < 2) m]
  · rw [htrans]
    apply abs_le.mpr
    constructor <;> linarith [hpr.1,hpr.2]

lemma spatial_chunk_in_box (b : ℝ) (k m : ℕ) (hs : 2 ≤ (2 : ℝ)^k) (p : Vertex) (ds : List Step)
    (hchunk : ∀ i ≤ ds.length, |(displacement (ds.take i)).1| ≤ 2*(2 : ℤ)^m ∧
      |transverse b (displacement (ds.take i))| ≤ (2 : ℝ)^k+1) :
    PathIn p ds {z | z-spatialTranslate b k m (spatialChunkIndex b k m p) ∈ endpointBox b 4 4 k m} := by
  intro i hi
  apply spatial_chunk_vertex_in_box b k m hs p
  · simpa only [Prod.fst_add,add_sub_cancel_left] using (hchunk i hi).1
  · simpa only [transverse_add,add_sub_cancel_left] using (hchunk i hi).2

lemma spatialChunkIndex_origin (b : ℝ) (k m : ℕ) : spatialChunkIndex b k m 0=0 := by
  simp [spatialChunkIndex,transverse]

/-- Consecutive source chunk indices have coordinate increments at most 3,
so a length-N itinerary has at most 49 choices at each step. -/
lemma spatialChunkIndex_increment (b : ℝ) (k m : ℕ) (hs : 2 ≤ (2 : ℝ)^k) (p z : Vertex)
    (hx : |z.1-p.1| ≤ 2*(2 : ℤ)^m)
    (hr : |transverse b z-transverse b p| ≤ (2 : ℝ)^k+1) :
    |(spatialChunkIndex b k m z).1-(spatialChunkIndex b k m p).1| ≤ 3 ∧
      |(spatialChunkIndex b k m z).2-(spatialChunkIndex b k m p).2| ≤ 3 := by
  have hL : (0 : ℤ) < 2^m := by positivity
  have hp := meshFloor_bounds p.1 ((2 : ℤ)^m) hL
  have hz := meshFloor_bounds z.1 ((2 : ℤ)^m) hL
  have hx' := abs_le.mp hx
  constructor
  · change |z.1/(2 : ℤ)^m-p.1/(2 : ℤ)^m| ≤ 3
    dsimp [meshFloor] at hp hz
    apply abs_le.mpr
    constructor <;> nlinarith [hp.1,hp.2,hz.1,hz.2]
  · have hs0 : (0 : ℝ) < 2^k := by positivity
    have hp0 := (le_div_iff₀ hs0).mp (Int.floor_le (transverse b p/(2 : ℝ)^k))
    have hp1 := (div_lt_iff₀ hs0).mp (Int.lt_floor_add_one (transverse b p/(2 : ℝ)^k))
    have hz0 := (le_div_iff₀ hs0).mp (Int.floor_le (transverse b z/(2 : ℝ)^k))
    have hz1 := (div_lt_iff₀ hs0).mp (Int.lt_floor_add_one (transverse b z/(2 : ℝ)^k))
    have hr' := abs_le.mp hr
    have hh : |(⌊transverse b z/(2 : ℝ)^k⌋ : ℝ)-(⌊transverse b p/(2 : ℝ)^k⌋ : ℝ)| ≤ 3 := by
      apply abs_le.mpr
      constructor <;> nlinarith [hr'.1,hr'.2]
    apply (Int.cast_le (R := ℝ)).mp
    simpa only [spatialChunkIndex,Int.cast_abs,Int.cast_sub,Int.cast_ofNat] using hh

end GammaFPP.CrossingBridge

end OAI
