import OAI.GroupTheory.PolycyclicRecognition.Analysis.ParametrizedSupportPaths
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SupportVisitImage

namespace OAI

/-! # Image control from the actual prefix sheets of a generator word

The hypotheses concern only the finitely many sheets visited by the chosen
word. They do not ask for a good profile at every possible starting point.
-/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped NNReal

variable {G I : Type*} [Group G] [PseudoMetricSpace G] [IsTopologicalGroup G]
  (d f : I → ℝ → G) (hd : ∀ i, Continuous (d i)) (hf : ∀ i, Continuous (f i))
  (hd₀ : ∀ i, d i 0 = 1) (hf₀ : ∀ i, f i 0 = 1) (d₀ : G) (r : ℝ)

omit [PseudoMetricSpace G] [IsTopologicalGroup G] in
theorem indexedWordProduct_append (u v : List (I × ℝ)) :
    indexedWordProduct f (u ++ v) = indexedWordProduct f u * indexedWordProduct f v := by
  simp [indexedWordProduct]

/-- Finitely many estimates at the actual prefixes suffice for the whole
explicit word path, with the usual uniform concatenation constant. -/
theorem supportWordPath_bound_of_prefixes
    {S : Set G} {L κ : ℝ} (hL : 0 ≤ L) (hκ : 0 ≤ κ)
    (u : List (I × ℝ)) (n : G) (hbase : n * d₀ ∈ S)
    (hvisit : ∀ (v : List (I × ℝ)) (i : I) (b : ℝ) (w : List (I × ℝ)),
      u = v ++ (i, b) :: w →
      PathMetricBound (supportVisitPath (d i) (hd i) (hd₀ i) (f i) (hf i) (hf₀ i)
        (n * indexedWordProduct f v) d₀ r b) L κ ∧
      ∀ t, supportVisitPath (d i) (hd i) (hd₀ i) (f i) (hf i) (hf₀ i)
        (n * indexedWordProduct f v) d₀ r b t ∈ S) :
    PathMetricBound (supportWordPath d f hd hf hd₀ hf₀ d₀ r u n)
      (L * 2 ^ u.length) (κ * 2 ^ u.length) ∧
      ∀ t, supportWordPath d f hd hf hd₀ hf₀ d₀ r u n t ∈ S := by
  induction u generalizing n with
  | nil =>
    constructor
    · intro s t
      change dist (n * d₀) (n * d₀) ≤ _
      simp only [dist_self, List.length_nil, pow_zero, mul_one]
      positivity
    · exact fun _ => hbase
  | cons z u ih =>
    rcases z with ⟨i, b⟩
    have hs := hvisit [] i b u rfl
    rw [show indexedWordProduct f [] = 1 from rfl, mul_one] at hs
    have hbase' : (n * f i b) * d₀ ∈ S := by
      simpa using hs.2 1
    have hv' (v : List (I × ℝ)) (j : I) (c : ℝ) (w : List (I × ℝ))
        (he : u = v ++ (j, c) :: w) :
        PathMetricBound (supportVisitPath (d j) (hd j) (hd₀ j) (f j) (hf j) (hf₀ j)
          ((n * f i b) * indexedWordProduct f v) d₀ r c) L κ ∧
        ∀ t, supportVisitPath (d j) (hd j) (hd₀ j) (f j) (hf j) (hf₀ j)
          ((n * f i b) * indexedWordProduct f v) d₀ r c t ∈ S := by
      have hh := hvisit ((i, b) :: v) j c w (by simp [he])
      have he' : n * indexedWordProduct f ((i, b) :: v) =
          (n * f i b) * indexedWordProduct f v := by
        simp [indexedWordProduct, mul_assoc]
      rw [he'] at hh
      exact hh
    obtain ⟨hq, hqS⟩ := ih (n * f i b) hbase' hv'
    have hpow : 1 ≤ (2 : ℝ) ^ u.length := one_le_pow₀ (by norm_num)
    have hp := hs.1.mono
      (show L ≤ L * 2 ^ u.length by nlinarith)
      (show κ ≤ κ * 2 ^ u.length by nlinarith)
    constructor
    · have hb := hp.trans (mul_nonneg hκ (by positivity)) hq
      have he : n * indexedWordProduct f ((i, b) :: u) * d₀ =
          (n * f i b) * indexedWordProduct f u * d₀ := by
        simp [indexedWordProduct, mul_assoc]
      have hb' := hb.cast rfl he
      convert hb' using 1 <;>
        first | rfl | (simp only [List.length_cons, pow_succ]; ring)
    · exact path_trans_range_mem hs.2 hqS

/-- Controlled images on each pair of consecutive sheets, together with
the short switches between them, control the entire chosen word path. -/
theorem supportWordPath_image_bound
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (J : G → W) {K : ℝ≥0} (hJ : LipschitzWith K J)
    (u : List (I × ℝ)) (n : G) (center : W) (E : Set W)
    {B κ : ℝ} (hκ : 0 ≤ κ)
    (hbase : ∃ w ∈ E, ‖J (n * d₀) - center - r • w‖ ≤ B)
    (hsheets : ∀ (v : List (I × ℝ)) (i : I) (b : ℝ) (w : List (I × ℝ)),
      u = v ++ (i, b) :: w →
      (∀ t : unitInterval, ∃ z ∈ E,
        ‖J (((n * indexedWordProduct f v) * d₀) * d i (r * t)) -
          center - r • z‖ ≤ B) ∧
      (∀ t : unitInterval, ∃ z ∈ E,
        ‖J (((n * indexedWordProduct f v) * f i b * d₀) * d i (r * t)) -
          center - r • z‖ ≤ B))
    (hswitch : ∀ (v : List (I × ℝ)) (i : I) (b : ℝ) (w : List (I × ℝ)),
      u = v ++ (i, b) :: w → ∀ t : unitInterval,
      dist ((n * indexedWordProduct f v) * f i ((t : ℝ) * b) * (d₀ * d i r))
        (((n * indexedWordProduct f v) * d₀) * d i r) ≤ κ) :
    ∀ t, ∃ w ∈ E,
      ‖J (supportWordPath d f hd hf hd₀ hf₀ d₀ r u n t) - center - r • w‖ ≤
        B + K * κ := by
  let S := {g : G | ∃ w ∈ E, ‖J g - center - r • w‖ ≤ B + K * κ}
  have hb : n * d₀ ∈ S := by
    obtain ⟨w, hw, he⟩ := hbase
    exact ⟨w, hw, he.trans (le_add_of_nonneg_right (mul_nonneg K.coe_nonneg hκ))⟩
  have hv : ∀ (v : List (I × ℝ)) (i : I) (b : ℝ) (w : List (I × ℝ)),
      u = v ++ (i, b) :: w → ∀ t,
      supportVisitPath (d i) (hd i) (hd₀ i) (f i) (hf i) (hf₀ i)
        (n * indexedWordProduct f v) d₀ r b t ∈ S := by
    intro v i b w he
    exact supportVisitPath_image_bound (d i) (hd i) (hd₀ i) (f i) (hf i) (hf₀ i)
      J hJ (n * indexedWordProduct f v) d₀ r b center E hκ
      (hsheets v i b w he).1 (hsheets v i b w he).2 (hswitch v i b w he)
  clear hsheets hswitch hbase
  induction u generalizing n with
  | nil => exact fun _ => hb
  | cons z u ih =>
    rcases z with ⟨i, b⟩
    have hp := hv [] i b u rfl
    rw [show indexedWordProduct f [] = 1 from rfl, mul_one] at hp
    have hb' : (n * f i b) * d₀ ∈ S := by simpa using hp 1
    have hv' (v : List (I × ℝ)) (j : I) (c : ℝ) (w : List (I × ℝ))
        (he : u = v ++ (j, c) :: w) : ∀ t,
        supportVisitPath (d j) (hd j) (hd₀ j) (f j) (hf j) (hf₀ j)
          ((n * f i b) * indexedWordProduct f v) d₀ r c t ∈ S := by
      have hh := hv ((i, b) :: v) j c w (by simp [he])
      have he' : n * indexedWordProduct f ((i, b) :: v) =
          (n * f i b) * indexedWordProduct f v := by
        simp [indexedWordProduct, mul_assoc]
      rw [he'] at hh
      exact hh
    exact path_trans_range_mem hp (ih (n * f i b) hb' hv')

end PolycyclicRecognition

end

end OAI
