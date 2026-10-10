import OAI.Analysis.Nonexpansive.CompactDetector
import OAI.Analysis.Nonexpansive.CandidateThreshold
import OAI.Analysis.Nonexpansive.TailMaps
import OAI.Analysis.Nonexpansive.TreeFrontier
import OAI.Analysis.Nonexpansive.PrefixPredictionOutputs

namespace OAI

/-!
# Preparing a candidate from the completed history

The actual compact prediction set and all ancestor displacement constants
are fixed before selecting a candidate map.  Their detector scale and
finite sum determine one tail threshold.  Every map in that tail then has
a detector and satisfies the ancestor displacement budget at every input.
-/

noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace ReflexiveFixedPoints

universe u v w

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [CompleteSpace X]

/-- Prepare one tail threshold from the existing finite frontier and its
earlier outputs.  The quantified candidate map and its input occur only
after that threshold has been selected.  The detector separates the
candidate output from every point of the actual compact prediction set,
including its prescribed dense prefix.

Each ancestor constant is obtained from its `Generated` derivation.  The
same threshold controls their total displacement; no additional geometric
assumption or assumed candidate-selection law is used. -/
theorem exists_prepared_candidate_threshold
    (D : NormalizedMinimalData (X := X)) (F : TreeFrontier D.K)
    {I : Type v} {A : Type w} [Fintype I] [Fintype A]
    (parent : I → Fin F.size) (y : I → D.K)
    (b : ℕ → D.K) (U : Ultrafilter ℕ) (k : ℕ)
    (G : A → D.K → D.K)
    (hG : ∀ a, Generated D.closed D.convex D.T D.nonexpansive (G a))
    {e : ℝ} (he : 0 < e) :
    ∃ m : ℕ, 1 ≤ m ∧ ∀ g : D.K → D.K,
      g ∈ tailFamily D.closed D.convex D.T D.nonexpansive m →
      Generated D.closed D.convex D.T D.nonexpansive g ∧
        ∀ x : D.K, ∃ f : X →L[ℝ] ℝ, ‖f‖ ≤ 1 ∧
          (∀ z ∈ Prediction.Prefix.detectorSet F.convex F.map F.evaluate
            parent y D.weak_compact b U D.z k,
            1 - e ≤ f ((g x : X) - z)) ∧
          (∑ a, ‖(G a (g x) : X) - (g x : X)‖) ≤ e := by
  classical
  have hconstants : ∀ a : A, ∃ c : ℝ, 0 ≤ c ∧ ∀ x : D.K,
      ‖(G a x : X) - (x : X)‖ ≤ c * ‖(D.T x : X) - (x : X)‖ :=
    fun a => generated_displacement (hG a)
  choose c hc hdisplacement using hconstants
  have hnonempty := Prediction.Prefix.detectorSet_nonempty
    F.convex F.map F.evaluate parent y D.weak_compact b U D.z k
  have hsubset := Prediction.Prefix.detectorSet_subset
    F.convex F.map F.evaluate parent y D.weak_compact b U D.z k
  have hcompact := Prediction.Prefix.isCompact_detectorSet
    F.convex F.map F.evaluate parent y F.nonexpansive
    (fun H H' ε h => F.evaluate_norm_sub_le_of_forall H H' h)
    D.weak_compact D.norm_sub_le_one b U D.z k
  obtain ⟨δ, hδ, hdetector⟩ := D.compact_detector hnonempty hsubset hcompact he
  obtain ⟨m, hm, hdetectorScale, hancestorScale⟩ :=
    exists_candidate_threshold (C := ∑ a, c a) hδ he
  refine ⟨m, hm, ?_⟩
  intro g hg
  refine ⟨tailFamily_generated D.closed D.convex D.T D.nonexpansive hg, ?_⟩
  intro x
  have hdefect := tailFamily_defect_le D.closed D.convex D.T D.nonexpansive
    D.norm_sub_le_one hm hg x
  obtain ⟨f, hf, hseparate⟩ :=
    hdetector (g x) (hdefect.trans hdetectorScale.le)
  refine ⟨f, hf, hseparate, ?_⟩
  exact candidate_ancestor_displacement (fun a => (G a (g x) : X)) c (g x : X)
    hc (fun a => hdisplacement a (g x)) hdefect hancestorScale

end ReflexiveFixedPoints

end

end OAI
