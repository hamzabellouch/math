import OAI.Analysis.MetricEntropy.ProfilePivots
import OAI.Analysis.MetricEntropy.ProfileMixtures
import OAI.Analysis.MetricEntropy.CompressionDecoder
import OAI.Analysis.MetricEntropy.GroupedWeights
import OAI.Analysis.MetricEntropy.SignedCompression

namespace OAI

universe uX uY uLabel

/-!
# Uniform compression of the actual logarithmic graph matrix

A single common index is chosen for all levels. Greedy pivots are replaced
by representatives fixed from their labels, and only those labels and rounded
grouped weights enter the finite code. The resulting list has no factor
depending on the number of vertices.
-/

noncomputable section

namespace MetricEntropyDuality

open scoped BigOperators Classical
open CompressionLevels ProfileMixtures

variable {X : Type uX} {Y : Type uY} [Fintype X] [Nonempty X] [Fintype Y]
variable {u q h s : ℕ} {Label : Fin u → Type uLabel}

/-- Construct an actual finite code for a nonnegative mixture of graph
profiles, including profiles at infinite distance. -/
theorem exists_compressionCode
    (L : (i : Fin u) → X → Label i) (E : FixedLabels L q)
    (v : Y → X) (T : Y → Finset (Fin u)) (μ : Y → ℝ)
    (hμ : ∀ y, 0 ≤ μ y) (hmass : ∑ y, μ y ≤ 1)
    (hu : 0 < u) (hh : 0 < h) (hs : 0 < s)
    (θ : ℝ) (hθ : 0 < θ) (hsθ : 1 ≤ (s : ℝ) * θ)
    (hprofile : Real.log 3 / Real.log ((h : ℝ) + 1) ≤ θ)
    (hcomp : ∀ y, ((Finset.univ \ T y).card : ℝ) ≤ θ * (u : ℝ)) :
    ∃ code : CompressionCode u q h s (weightCodeSize (roundingStep θ s u)),
      ∀ x, profileMixture L v T h μ x - 3 * θ ≤ compressionDecode L E h s θ code x ∧
        compressionDecode L E h s θ code x ≤ profileMixture L v T h μ x + θ := by
  obtain ⟨i, centers, assignment, homit, hassign, hrem⟩ :=
    exists_profile_pivots L v T μ hμ hmass hu θ hθ s hsθ hcomp h
  let rep : Fin h → Fin s → X := fun j k =>
    E.representative i (E.encode i (centers j k))
  have hrep (j : Fin h) (k : Fin s) :
      L i (rep j k) = L i (centers j k) :=
    E.label_representative_encode i (centers j k)
  let w : Fin h → Fin s → Finset (Fin u) → ℝ := fun j =>
    groupedWeight (assignment j) T μ
  have hw0 (j : Fin h) (k : Fin s) (t : Finset (Fin u)) : 0 ≤ w j k t :=
    groupedWeight_nonneg (assignment j) T μ hμ k t
  have hw1 (j : Fin h) (k : Fin s) (t : Finset (Fin u)) : w j k t ≤ 1 :=
    groupedWeight_le_one (assignment j) T μ hμ hmass k t
  let δ := roundingStep θ s u
  have hδ : 0 < δ := roundingStep_pos hθ hs
  let code : CompressionCode u q h s (weightCodeSize δ) :=
    ⟨i, (fun j k => E.encode i (centers j k)),
      fun j k t => weightCode δ (w j k t) hδ (hw0 j k t) (hw1 j k t)⟩
  refine ⟨code, ?_⟩
  intro x
  let A : Fin h → ℝ := fun j => assignedValue L T (rep j) (assignment j) μ j.val x
  let R : Fin h → ℝ := fun j =>
    ∑ k, ∑ t, roundWeight δ (w j k t) * ballIndicator L t (2 * j.val + 1) x (rep j k)
  have hgroup (j : Fin h) :
      (∑ k, ∑ t, w j k t * ballIndicator L t (2 * j.val + 1) x (rep j k)) = A j := by
    exact sum_groupedWeight_mul (assignment j) T μ
      (fun k t => ballIndicator L t (2 * j.val + 1) x (rep j k))
  have hlower (j : Fin h) : levelValue L v T μ j.val x - 2 * θ ≤ A j := by
    refine levelValue_sub_two_mul_le_assignedValue L v T μ hμ i j.val
      (centers j) (rep j) (assignment j) (hassign j) (hrep j) (θ := θ) ?_ ?_ x
    · refine le_trans (le_of_eq ?_) homit
      apply Finset.sum_congr
      · ext y
        simp only [Finset.mem_filter]
      · intro y hy
        rfl
    · intro z
      refine le_trans (le_of_eq ?_) (hrem j z)
      apply Finset.sum_congr
      · ext y
        simp only [Finset.mem_filter]
      · intro y hy
        rfl
  have hupper (j : Fin h) : A j ≤ levelValue L v T μ (3 * j.val + 2) x := by
    exact assignedValue_le_levelValue L v T μ hμ i j.val
      (centers j) (rep j) (assignment j) (hassign j) (hrep j) x
  have hround (j : Fin h) : 0 ≤ A j - R j ∧ A j - R j ≤ θ := by
    have he := roundWeight_level_error hθ hs (w j)
      (fun k t => ballIndicator L t (2 * j.val + 1) x (rep j k)) (hw0 j)
      (fun k t => ballIndicator_nonneg L t (2 * j.val + 1) x (rep j k))
      (fun k t => ballIndicator_le_one L t (2 * j.val + 1) x (rep j k))
    rw [hgroup] at he
    exact he
  have hdecode : compressionDecode L E h s θ code x =
      ∑ j : Fin h, LogProfile.gamma h j.val * R j := by
    rfl
  rw [hdecode]
  exact rounded_level_sum_bounds L v T μ hμ hmass hh hθ.le hprofile x
    A R hlower hupper hround

/-- The fixed decoded list uniformly approximates every nonnegative mixture
with one-sided errors. -/
theorem compressionList_bounds
    (L : (i : Fin u) → X → Label i) (E : FixedLabels L q)
    (𝒯 : Finset (Finset (Fin u)))
    (hu : 0 < u) (hh : 0 < h) (hs : 0 < s)
    (θ : ℝ) (hθ : 0 < θ) (hsθ : 1 ≤ (s : ℝ) * θ)
    (hprofile : Real.log 3 / Real.log ((h : ℝ) + 1) ≤ θ)
    (hcomp : ∀ T ∈ 𝒯, ((Finset.univ \ T).card : ℝ) ≤ θ * (u : ℝ))
    (μ : GraphProfile.Columns X 𝒯 → ℝ)
    (hμ : ∀ y, 0 ≤ μ y) (hmass : ∑ y, μ y ≤ 1) :
    ∃ a ∈ compressionList L E h s θ, ∀ x,
      columnCombination (GraphProfile.column L 𝒯 h) μ x - 3 * θ ≤ a x ∧
        a x ≤ columnCombination (GraphProfile.column L 𝒯 h) μ x + θ := by
  obtain ⟨code, hc⟩ := exists_compressionCode L E
    (fun y : GraphProfile.Columns X 𝒯 => y.1) (fun y => y.2.val) μ hμ hmass
    hu hh hs θ hθ hsθ hprofile (fun y => hcomp y.2.val y.2.property)
  exact ⟨compressionDecode L E h s θ code,
    compressionDecode_mem_compressionList L E h s θ code, hc⟩

/-- Complete positive compression from the actual partition graph and
logarithmic profile, with a fixed list and the literal finite-code bound. -/
theorem uniform_compression
    (L : (i : Fin u) → X → Label i)
    (hlabels : ∀ i, Nat.card (Set.range (L i)) ≤ q)
    (𝒯 : Finset (Finset (Fin u)))
    (hu : 0 < u) (hq : 0 < q) (hh : 0 < h) (hs : 0 < s)
    (θ : ℝ) (hθ : 0 < θ) (hsθ : 1 ≤ (s : ℝ) * θ)
    (hprofile : Real.log 3 / Real.log ((h : ℝ) + 1) ≤ θ)
    (hcomp : ∀ T ∈ 𝒯, ((Finset.univ \ T).card : ℝ) ≤ θ * (u : ℝ)) :
    ∃ A : Finset (X → ℝ), A.Nonempty ∧
      (A.card : ℝ) ≤ (u : ℝ) * (q : ℝ) ^ (h * s) *
        (1 + (s : ℝ) * 2 ^ u / θ) ^ (h * s * 2 ^ u) ∧
      SignedCompression.PositiveApproximation (GraphProfile.column L 𝒯 h) θ A := by
  let E := FixedLabels.ofCardBound L hlabels
  refine ⟨compressionList L E h s θ,
    compressionList_nonempty L E h s θ hu hq,
    compressionList_card_le L E h s θ hθ hs, ?_⟩
  intro μ hμ hmass
  obtain ⟨a, ha, hb⟩ := compressionList_bounds L E 𝒯 hu hh hs θ hθ hsθ
    hprofile hcomp μ hμ hmass
  refine ⟨a, ha, ?_⟩
  intro x
  have hx := hb x
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Signed compression is supplied by the actual difference list of the
constructed positive list; its cardinal is at most the square of that list. -/
theorem uniform_signed_compression
    (L : (i : Fin u) → X → Label i)
    (hlabels : ∀ i, Nat.card (Set.range (L i)) ≤ q)
    (𝒯 : Finset (Finset (Fin u)))
    (hu : 0 < u) (hq : 0 < q) (hh : 0 < h) (hs : 0 < s)
    (θ : ℝ) (hθ : 0 < θ) (hsθ : 1 ≤ (s : ℝ) * θ)
    (hprofile : Real.log 3 / Real.log ((h : ℝ) + 1) ≤ θ)
    (hcomp : ∀ T ∈ 𝒯, ((Finset.univ \ T).card : ℝ) ≤ θ * (u : ℝ)) :
    ∃ A B : Finset (X → ℝ), A.Nonempty ∧
      (A.card : ℝ) ≤ (u : ℝ) * (q : ℝ) ^ (h * s) *
        (1 + (s : ℝ) * 2 ^ u / θ) ^ (h * s * 2 ^ u) ∧
      B.card ≤ A.card ^ 2 ∧
      UniformApproximation (GraphProfile.column L 𝒯 h) (6 * θ) B := by
  obtain ⟨A, hA, hcard, hpos⟩ := uniform_compression L hlabels 𝒯 hu hq hh hs
    θ hθ hsθ hprofile hcomp
  exact ⟨A, SignedCompression.differenceList A, hA, hcard,
    SignedCompression.differenceList_card_le A,
    SignedCompression.uniformApproximation (GraphProfile.column L 𝒯 h) θ A hpos⟩

end MetricEntropyDuality

end

end OAI
