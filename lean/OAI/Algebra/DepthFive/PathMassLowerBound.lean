import OAI.Algebra.DepthFive.CompositionAntidiag
import OAI.Algebra.DepthFive.PathOccupationGroups

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

open BidegreeAverages

/-- Boolean-fiber form of the occupation lower estimate. -/
theorem bidegree_first_moment_lower_bool {σ : Type*} [Fintype σ] [DecidableEq σ]
    (side : σ → Bool) (a b : ℕ) [Fintype (Index side a b)]
    [Nonempty {x // side x = true}] [Nonempty {x // side x = false}]
    (s : Finset {x // side x = true}) (z : Finset {x // side x = false})
    (ha : 0 < a) (hb : 0 < b) (hs : 2 * s.card ≤ a) (hz : 2 * z.card ≤ b) :
    Real.exp ((-(s.card : ℝ) ^ 2 / a -
        (s.card : ℝ) ^ 2 / (2 * Fintype.card {x // side x = true})) +
      (-(z.card : ℝ) ^ 2 / b -
        (z.card : ℝ) ^ 2 / (2 * Fintype.card {x // side x = false}))) *
      (((a : ℝ) / Fintype.card {x // side x = true}) ^ s.card *
        (1 + (b : ℝ) / Fintype.card {x // side x = false}) ^ z.card) ≤
      (∑ d : Index side a b,
        (∏ i ∈ s, (d.val i : ℝ)) * (∏ i ∈ z, ((d.val i : ℝ) + 1))) /
        (Fintype.card (Index side a b) : ℝ) := by
  let : Nonempty {x // ¬ side x = true} := by
    simpa only [Bool.not_eq_true] using
      (inferInstance : Nonempty {x // side x = false})
  let e : {x // ¬ side x = true} ≃ {x // side x = false} :=
    Equiv.subtypeEquivRight (fun x => by simp)
  have hcard : Fintype.card {x // ¬ side x = true} =
      Fintype.card {x // side x = false} := Fintype.card_congr e
  have h := BidegreeAverages.bidegree_first_moment_lower side a b
    s (z.map e.symm.toEmbedding) ha hb hs (by simpa using hz)
  simpa only [Finset.card_map, hcard, Finset.prod_map,
    Equiv.coe_toEmbedding, Equiv.subtypeEquivRight_symm_apply, e] using h

/-- Each squarefree Fock path has large average squared amplitude over the
actual bidegree source. No independence of coordinates within a group is assumed. -/
theorem path_source_mass_lower {σ : Type*} [Fintype σ] [DecidableEq σ]
    (side : σ → Bool) (a b : ℕ) [Fintype (Index side a b)]
    [Nonempty {x // side x = true}] [Nonempty {x // side x = false}]
    (p : List σ) (hp : p.Nodup) (ha : 0 < a) (hb : 0 < b)
    (hs : 2 * (selectedPathCoordinates side p true).card ≤ a)
    (hz : 2 * (selectedPathCoordinates side p false).card ≤ b) :
    Real.exp ((-((selectedPathCoordinates side p true).card : ℝ) ^ 2 / a -
        ((selectedPathCoordinates side p true).card : ℝ) ^ 2 /
          (2 * Fintype.card {x // side x = true})) +
      (-((selectedPathCoordinates side p false).card : ℝ) ^ 2 / b -
        ((selectedPathCoordinates side p false).card : ℝ) ^ 2 /
          (2 * Fintype.card {x // side x = false}))) *
      (((a : ℝ) / Fintype.card {x // side x = true}) ^
          (selectedPathCoordinates side p true).card *
        (1 + (b : ℝ) / Fintype.card {x // side x = false}) ^
          (selectedPathCoordinates side p false).card) ≤
      (∑ d : Index side a b,
        ((p.map (occupationAmplitude side d.val)).prod) ^ 2) /
        (Fintype.card (Index side a b) : ℝ) := by
  simpa only [pathAmplitude_sq_split side p hp] using
    bidegree_first_moment_lower_bool side a b
      (selectedPathCoordinates side p true) (selectedPathCoordinates side p false)
      ha hb hs hz

/-- Concrete IMM per-path first moment. The loss and geometric benchmark depend
only on the selected layer counts, not on the chosen path. -/
theorem immPath_source_mass_lower (n : ℕ) (hn : 0 < n)
    (side : Fin n → Bool) (a b : ℕ)
    [Fintype (Index (fun x : Fin n × Fin n × Fin n => side x.1) a b)]
    [Nonempty {x : Fin n × Fin n × Fin n // side x.1 = true}]
    [Nonempty {x : Fin n × Fin n × Fin n // side x.1 = false}]
    (p : List (Fin n × Fin n × Fin n)) (hp : p ∈ immPaths n hn)
    (ha : 0 < a) (hb : 0 < b)
    (hs : 2 * (Finset.univ.filter (fun t : Fin n => side t = true)).card ≤ a)
    (hz : 2 * (Finset.univ.filter (fun t : Fin n => side t = false)).card ≤ b) :
    Real.exp ((-((Finset.univ.filter (fun t : Fin n => side t = true)).card : ℝ) ^ 2 / a -
        ((Finset.univ.filter (fun t : Fin n => side t = true)).card : ℝ) ^ 2 /
          (2 * Fintype.card {x : Fin n × Fin n × Fin n // side x.1 = true})) +
      (-((Finset.univ.filter (fun t : Fin n => side t = false)).card : ℝ) ^ 2 / b -
        ((Finset.univ.filter (fun t : Fin n => side t = false)).card : ℝ) ^ 2 /
          (2 * Fintype.card {x : Fin n × Fin n × Fin n // side x.1 = false}))) *
      (((a : ℝ) / Fintype.card {x : Fin n × Fin n × Fin n // side x.1 = true}) ^
          (Finset.univ.filter (fun t : Fin n => side t = true)).card *
        (1 + (b : ℝ) / Fintype.card {x : Fin n × Fin n × Fin n // side x.1 = false}) ^
          (Finset.univ.filter (fun t : Fin n => side t = false)).card) ≤
      (∑ d : Index (fun x : Fin n × Fin n × Fin n => side x.1) a b,
        ((p.map (occupationAmplitude (fun x => side x.1) d.val)).prod) ^ 2) /
        (Fintype.card (Index (fun x : Fin n × Fin n × Fin n => side x.1) a b) : ℝ) := by
  have hs' : 2 * (selectedPathCoordinates (fun x : Fin n × Fin n × Fin n => side x.1)
      p true).card ≤ a := by
    rwa [immPath_selectedCoordinates_card n hn side p hp true]
  have hz' : 2 * (selectedPathCoordinates (fun x : Fin n × Fin n × Fin n => side x.1)
      p false).card ≤ b := by
    rwa [immPath_selectedCoordinates_card n hn side p hp false]
  simpa only [immPath_selectedCoordinates_card n hn side p hp] using
    path_source_mass_lower (fun x : Fin n × Fin n × Fin n => side x.1) a b p
      (immPaths_nodup n hn p hp) ha hb hs' hz'

end Problem335

end

end OAI
