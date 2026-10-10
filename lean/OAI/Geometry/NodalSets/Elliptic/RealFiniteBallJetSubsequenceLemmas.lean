import OAI.Geometry.NodalSets.Elliptic.RealCountableCompactness
import OAI.Geometry.NodalSets.Elliptic.RealPartialJetLipschitz

namespace OAI

noncomputable section

namespace Yau.Geometry

open Yau.Analysis Set Metric Filter
open scoped Topology NNReal ContDiff

theorem real_finite_ball_jet_subsequence (W : ℕ → Yau.Jets.Coord → ℝ)
    (hW : ∀ j, ContDiff ℝ ∞ (W j)) (y : Yau.Jets.Coord) (r : ℝ) (n : ℕ)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ j (ds : List (Fin 4)), ds.length ≤ n+1 →
      ∀ x ∈ closedBall y r, |partialJet (W j) ds x| ≤ B) :
    ∃ f : {ds : List (Fin 4) // ds.length ≤ n} → closedBall y r → ℝ,
      (∀ ds, Continuous (f ds)) ∧ ∃ nu : ℕ → ℕ, StrictMono nu ∧
        ∀ ds : {ds : List (Fin 4) // ds.length ≤ n},
          TendstoUniformly (fun j (x : closedBall y r) ↦ partialJet (W (nu j)) ds.val x)
            (f ds) atTop := by
  let F (ds : {ds : List (Fin 4) // ds.length ≤ n}) (j : ℕ) (x : closedBall y r) :=
    partialJet (W j) ds.val x
  let C : ℝ≥0 := ⟨B,hB⟩
  apply real_countable_uniform_subsequence F (fun _ ↦ B) (fun _ ↦ 4*C)
  · intro ds j x
    exact hb j ds.val (by have := ds.property; omega) x x.property
  · intro ds j
    apply LipschitzOnWith.to_restrict
    apply real_partialJet_lipschitz (W j) (hW j) ds.val y r C
    intro i x hx
    exact hb j (i::ds.val) (by simp only [List.length_cons]; have := ds.property; omega) x hx

theorem real_jet_ball_subsequence (W : ℕ → Yau.Jets.Coord → ℝ)
    (hW : ∀ j, ContDiff ℝ ∞ (W j))
    (hb : ∀ R n : ℕ, ∃ B ≥ 0, ∀ j (ds : List (Fin 4)), ds.length ≤ n →
      ∀ x ∈ closedBall (0 : Yau.Jets.Coord) (R:ℝ), |partialJet (W j) ds x| ≤ B) :
    ∃ f : ∀ R : ℕ, List (Fin 4) → closedBall (0 : Yau.Jets.Coord) (R:ℝ) → ℝ,
      (∀ R ds, Continuous (f R ds)) ∧ ∃ nu : ℕ → ℕ, StrictMono nu ∧ ∀ (R : ℕ) (ds : List (Fin 4)),
        TendstoUniformly (fun j (x : closedBall (0 : Yau.Jets.Coord) (R:ℝ)) ↦
          partialJet (W (nu j)) ds x) (f R ds) atTop := by
  choose B hB hbound using hb
  let X (i : ℕ × List (Fin 4)) := closedBall (0 : Yau.Jets.Coord) (i.1:ℝ)
  let F (i : ℕ × List (Fin 4)) (j : ℕ) (x : X i) := partialJet (W j) i.2 x
  let C (i : ℕ × List (Fin 4)) : ℝ≥0 := ⟨B i.1 (i.2.length+1),hB _ _⟩
  have hval (i : ℕ × List (Fin 4)) (j : ℕ) (x : X i) : |F i j x| ≤ (C i:ℝ) :=
    hbound _ _ j _ (by omega) x x.property
  have hLip (i : ℕ × List (Fin 4)) (j : ℕ) : LipschitzWith (4*C i) (F i j) := by
    apply LipschitzOnWith.to_restrict
    apply real_partialJet_lipschitz (W j) (hW j) i.2 0 (i.1:ℝ) (C i)
    intro k x hx
    exact hbound _ _ j _ (by simp) x hx
  obtain ⟨f,hf,nu,hnu,ht⟩ := real_countable_uniform_subsequence F (fun i ↦ (C i:ℝ))
    (fun i ↦ 4*C i) hval hLip
  exact ⟨fun R ds ↦ f (R,ds),fun R ds ↦ hf (R,ds),nu,hnu,fun R ds ↦ ht (R,ds)⟩

end Yau.Geometry

end

end OAI
