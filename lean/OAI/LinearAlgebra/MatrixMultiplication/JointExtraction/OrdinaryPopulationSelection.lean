import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.OrdinarySelection
import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.PopulationRates
import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.AmbientEntropy
import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.AmbientRateLimit
import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.CapacityAlgebra
import Mathlib.Data.Finset.Lattice.Fold

namespace OAI

/-! Joint tensor extraction, compatibility and entropy estimates. -/

noncomputable section

namespace MatrixMultiplication.JointOrdinaryPopulationSelection

open MatrixMultiplication.Foundation JointPopulation JointPopulationRates Filter
open scoped BigOperators Topology

attribute [local instance] Classical.propDecidable

variable {Hist : Type*} [Fintype Hist] [DecidableEq Hist]

def entropyRate (mass : Hist → ℝ) (p : Hist → FiniteLaw Shape) : ℝ :=
  ∑ h, mass h * finiteEntropy (p h).mass

def sideDegreeRate (mass : Hist → ℝ) (p : Hist → FiniteLaw Shape) (s : Fin 3) : ℝ :=
  ∑ h, mass h * (finiteEntropy (p h).mass - finiteEntropy (sideMass (p h).mass s))

def degreeRate (mass : Hist → ℝ) (p : Hist → FiniteLaw Shape) : ℝ :=
  max (sideDegreeRate mass p 0) (max (sideDegreeRate mass p 1) (sideDegreeRate mass p 2))

def sideCapacity (mass : Hist → ℝ) (p : Hist → FiniteLaw Shape) (s : Fin 3) : ℝ :=
  ∑ h, mass h * finiteEntropy (sideMass (p h).mass s)

omit [DecidableEq Hist] in
theorem entropyRate_sub_degreeRate_eq (mass : Hist → ℝ) (p : Hist → FiniteLaw Shape) :
    entropyRate mass p - degreeRate mass p =
      min (sideCapacity mass p 0) (min (sideCapacity mass p 1) (sideCapacity mass p 2)) := by
  exact JointCapacityAlgebra.weighted_joint_capacity mass
    (fun h => finiteEntropy (p h).mass) (fun h s => finiteEntropy (sideMass (p h).mass s))

theorem sideMass_entropy_le (p : FiniteLaw Shape) (s : Fin 3) :
    finiteEntropy (sideMass p.mass s) ≤ finiteEntropy p.mass := by
  simpa only [finiteEntropy, FiniteLaw.map_mass, sideMass] using
    p.map_entropy_le (shapeSide s)

omit [DecidableEq Hist] in
theorem sideDegreeRate_nonneg (mass : Hist → ℝ) (p : Hist → FiniteLaw Shape)
    (hmass : ∀ h, 0 ≤ mass h) (s : Fin 3) : 0 ≤ sideDegreeRate mass p s := by
  exact Finset.sum_nonneg fun h _ =>
    mul_nonneg (hmass h) (sub_nonneg.mpr (sideMass_entropy_le (p h) s))

omit [DecidableEq Hist] in
theorem degreeRate_nonneg (mass : Hist → ℝ) (p : Hist → FiniteLaw Shape)
    (hmass : ∀ h, 0 ≤ mass h) : 0 ≤ degreeRate mass p :=
  (sideDegreeRate_nonneg mass p hmass 0).trans (le_max_left _ _)

omit [DecidableEq Hist] in
theorem sideDegreeRate_le (mass : Hist → ℝ) (p : Hist → FiniteLaw Shape) (s : Fin 3) :
    sideDegreeRate mass p s ≤ degreeRate mass p := by
  unfold degreeRate
  fin_cases s
  · exact le_max_left _ _
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

def uniformDegree (counts : Hist → Shape → ℕ) (sum : Hist → ℕ) : ℕ :=
  Finset.univ.sup (fun e : Target counts =>
    (JointAmbientDegree.neighbors counts sum (triple counts e)).card)

theorem ordinary_neighbors_eq (counts : Hist → Shape → ℕ) (sum : Hist → ℕ)
    (e : JointCoarseHashing.Triple (Position counts)) :
    JointOrdinarySelection.neighbors (ambientSet counts sum) e =
      JointAmbientDegree.neighbors counts sum e := by
  unfold JointOrdinarySelection.neighbors JointAmbientDegree.neighbors
  rw [Finset.filter_congr_decidable (ambientSet counts sum)
    (fun f : JointCoarseHashing.Triple (Position counts) =>
      f ≠ e ∧ JointCoarseHashing.SharesSide e f)]
  refine @Finset.filter_congr
    (JointCoarseHashing.Triple (Position counts))
    (fun f => f ≠ e ∧ JointCoarseHashing.SharesSide e f)
    (fun f => f ≠ e ∧ JointCoarseHashing.SharesSide f e)
    _ _ (ambientSet counts sum) ?_
  intro f _
  simp only [JointCoarseHashing.SharesSide, eq_comm]

theorem neighbors_card_le_uniformDegree (counts : Hist → Shape → ℕ)
    (sum : Hist → ℕ) (e : Target counts) :
    (JointOrdinarySelection.neighbors (ambientSet counts sum) (triple counts e)).card ≤
      uniformDegree counts sum := by
  rw [ordinary_neighbors_eq]
  exact Finset.le_sup
    (f := fun e : Target counts =>
      (JointAmbientDegree.neighbors counts sum (triple counts e)).card)
    (Finset.mem_univ e)

theorem uniformDegree_attained (counts : Hist → Shape → ℕ) (sum : Hist → ℕ) :
    ∃ e : Target counts,
      (JointAmbientDegree.neighbors counts sum (triple counts e)).card =
        uniformDegree counts sum := by
  let : Nonempty (Target counts) := target_nonempty counts
  obtain ⟨e, _, he⟩ := Finset.sup_mem_of_nonempty
    (s := Finset.univ)
    (f := fun e : Target counts =>
      (JointAmbientDegree.neighbors counts sum (triple counts e)).card)
    Finset.univ_nonempty
  exact ⟨e, he⟩

theorem uniformDegree_log_upper_of_all_targets
    (counts : ℕ → Hist → Shape → ℕ) (sum : Hist → ℕ) (B : ℝ)
    (hbound : ∀ᶠ N in atTop, ∀ e : Target (counts N),
      Real.log ((JointAmbientDegree.neighbors (counts N) sum (triple (counts N) e)).card : ℝ) /
        (N : ℝ) ≤ B) :
    ∀ᶠ N in atTop, Real.log (uniformDegree (counts N) sum : ℝ) / (N : ℝ) ≤ B := by
  filter_upwards [hbound] with N hN
  obtain ⟨e, he⟩ := uniformDegree_attained (counts N) sum
  rw [← he]
  exact hN e

omit [DecidableEq Hist] in
theorem tendsto_sum_gibbsExponent
    (counts : ℕ → Hist → Shape → ℕ) (mass : Hist → ℝ)
    (p : Hist → FiniteLaw Shape) (u v w : Hist → Fin 17 → ℝ)
    (hcounts : ∀ h a, Tendsto (fun N : ℕ => (counts N h a : ℝ) / (N : ℝ))
      atTop (𝓝 (mass h * (p h).mass a))) (s : Fin 3) :
    Tendsto (fun N => (∑ h, JointAmbientDegree.classExponent (counts N) s
      (triple (counts N) (canonicalTarget (counts N))) h
      (JointAmbientEntropy.gibbsCap (counts N) h (p h) (u h) (v h) (w h))) / (N : ℝ))
      atTop (𝓝 (sideDegreeRate mass p s)) := by
  have hsize (h : Hist) := tendsto_total_div_of_coordinate_rates
    (fun N => counts N h) (mass h) (p h).mass (p h).total (hcounts h)
  have hcap (h : Hist) := JointAmbientEntropy.tendsto_classScale_mul_gibbsCap
    counts h (p h) (mass h) (u h) (v h) (w h) (hcounts h)
  have hside (h : Hist) := tendsto_weighted_target_side_entropy counts
    (fun N => canonicalTarget (counts N)) mass (fun h => (p h).mass)
    (fun h => (p h).total) hcounts h s
  have h := JointAmbientRateLimit.tendsto_sum_classExponent_div_nat counts s
    (fun N h => JointAmbientEntropy.gibbsCap (counts N) h (p h) (u h) (v h) (w h))
    mass (fun h => mass h * finiteEntropy (p h).mass)
    (fun h => mass h * finiteEntropy (sideMass (p h).mass s)) hsize
    (fun h => by
      simpa only [JointAmbientEntropy.classScale, Positions, Fintype.card_fin] using hcap h)
    (fun h => by
      simpa only [Positions, Fintype.card_fin] using hside h)
  simpa only [sideDegreeRate, mul_sub] using h

theorem uniformDegree_log_upper_of_word_support
    (counts : ℕ → Hist → Shape → ℕ) (sum : Hist → ℕ) (mass : Hist → ℝ)
    (p : Hist → FiniteLaw Shape) (u v w : Hist → Fin 17 → ℝ) (c : Hist → ℝ)
    (hmass : ∀ h, 0 ≤ mass h)
    (hsupport : ∀ᶠ N in atTop, ∀ h word,
      JointAmbientDegree.localAllowed (counts N) sum h word →
        ∀ i, 0 < (p h).mass (word i))
    (hlog : ∀ h a, 0 < (p h).mass a → Real.log ((p h).mass a) =
      u h (shapeSide 0 a) + v h (shapeSide 1 a) + w h (shapeSide 2 a) - c h)
    (hcounts : ∀ h a, Tendsto (fun N : ℕ => (counts N h a : ℝ) / (N : ℝ))
      atTop (𝓝 (mass h * (p h).mass a)))
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ N in atTop, Real.log (uniformDegree (counts N) sum : ℝ) / (N : ℝ) ≤
      degreeRate mass p + η := by
  apply uniformDegree_log_upper_of_all_targets counts sum
  apply JointAmbientRateLimit.eventually_all_target_degree_upper counts sum
    (fun N h => JointAmbientEntropy.gibbsCap (counts N) h (p h) (u h) (v h) (w h))
    (sideDegreeRate mass p) (degreeRate mass p) (degreeRate_nonneg mass p hmass)
    _ (tendsto_sum_gibbsExponent counts mass p u v w hcounts)
    (sideDegreeRate_le mass p) η hη
  filter_upwards [hsupport] with N hN
  intro h word hw
  exact JointAmbientEntropy.localAllowed_entropy_le_of_word_support
    (counts N) sum h word (p h) (u h) (v h) (w h) (c h)
    (hN h word hw) (hlog h) hw

theorem uniformDegree_log_upper
    (counts : ℕ → Hist → Shape → ℕ) (sum : Hist → ℕ) (mass : Hist → ℝ)
    (p : Hist → FiniteLaw Shape) (u v w : Hist → Fin 17 → ℝ) (c : Hist → ℝ)
    (hmass : ∀ h, 0 ≤ mass h)
    (hsupport : ∀ h (a : Shape),
      a.1.val + a.2.1.val + a.2.2.val = sum h → 0 < (p h).mass a)
    (hlog : ∀ h a, 0 < (p h).mass a → Real.log ((p h).mass a) =
      u h (shapeSide 0 a) + v h (shapeSide 1 a) + w h (shapeSide 2 a) - c h)
    (hcounts : ∀ h a, Tendsto (fun N : ℕ => (counts N h a : ℝ) / (N : ℝ))
      atTop (𝓝 (mass h * (p h).mass a)))
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ N in atTop, Real.log (uniformDegree (counts N) sum : ℝ) / (N : ℝ) ≤
      degreeRate mass p + η :=
  uniformDegree_log_upper_of_word_support counts sum mass p u v w c hmass
    (Eventually.of_forall fun _ h word hw i => hsupport h (word i) (hw.1 i))
    hlog hcounts η hη

def selectionHashRate (mass : Hist → ℝ) (p : Hist → FiniteLaw Shape) (ε : ℝ) : ℝ :=
  degreeRate mass p + ε / 2

theorem eventually_exists_selection_of_word_support
    (counts : ℕ → Hist → Shape → ℕ) (sum : Hist → ℕ) (mass : Hist → ℝ)
    (p : Hist → FiniteLaw Shape) (u v w : Hist → Fin 17 → ℝ) (c : Hist → ℝ)
    (hmass : ∀ h, 0 ≤ mass h)
    (hcountSupport : ∀ N h a, 0 < counts N h a →
      a.1.val + a.2.1.val + a.2.2.val = sum h)
    (hsupport : ∀ᶠ N in atTop, ∀ h word,
      JointAmbientDegree.localAllowed (counts N) sum h word →
        ∀ i, 0 < (p h).mass (word i))
    (hlog : ∀ h a, 0 < (p h).mass a → Real.log ((p h).mass a) =
      u h (shapeSide 0 a) + v h (shapeSide 1 a) + w h (shapeSide 2 a) - c h)
    (hcounts : ∀ h a, Tendsto (fun N : ℕ => (counts N h a : ℝ) / (N : ℝ))
      atTop (𝓝 (mass h * (p h).mass a)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop,
      ∃ (s : JointCoarseHashing.Sample (Position (counts N))
          (JointOrdinarySelection.hashLevel (selectionHashRate mass p ε) N))
        (G : Finset (Target (counts N))),
        G.card = ⌊Real.exp ((N : ℝ) * (entropyRate mass p - degreeRate mass p - ε))⌋₊ ∧
        (∀ e ∈ G, JointOrdinarySelection.Good
          (JointOrdinarySelection.hashLevel (selectionHashRate mass p ε) N)
          (JointOrdinarySelection.hashSet (selectionHashRate mass p ε) N)
          (ambientSet (counts N) sum) (triple (counts N) e) s) ∧
        (G : Set (Target (counts N))).Pairwise (fun e f =>
          ¬ JointCoarseHashing.SharesSide (triple (counts N) e) (triple (counts N) f)) := by
  have hD : 0 ≤ degreeRate mass p := degreeRate_nonneg mass p hmass
  have hH : 0 ≤ selectionHashRate mass p ε := by unfold selectionHashRate; linarith
  have hgap : degreeRate mass p < selectionHashRate mass p ε := by
    unfold selectionHashRate
    linarith
  have htarget (N : ℕ) (e : Target (counts N)) :
      triple (counts N) e ∈ ambientSet (counts N) sum := by
    apply targetSet_subset_ambient (counts N) sum (hcountSupport N)
    exact Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩
  have hpos : ∀ᶠ N in atTop, 0 < Fintype.card (Target (counts N)) :=
    Eventually.of_forall fun N => Fintype.card_pos_iff.mpr (target_nonempty (counts N))
  have htargetRate : Tendsto (fun N : ℕ =>
      Real.log (Fintype.card (Target (counts N)) : ℝ) / (N : ℝ))
      atTop (𝓝 (entropyRate mass p)) :=
    tendsto_log_target_card_div_of_coordinate_rates counts mass
      (fun h => (p h).mass) hmass (fun h => (p h).total) hcounts
  have hselection := JointOrdinarySelection.eventually_exists_selection
    (fun N => ambientSet (counts N) sum)
    (fun N (position : Position (counts N)) => sum position.1)
    (fun N => triple (counts N)) (fun N => triple_injective (counts N))
    (fun N f hf => (Finset.mem_filter.mp hf).2.1) htarget
    (fun N => uniformDegree (counts N) sum)
    (fun N e => neighbors_card_le_uniformDegree (counts N) sum e)
    hH hgap (uniformDegree_log_upper_of_word_support counts sum mass p u v w c
      hmass hsupport hlog hcounts)
    hpos htargetRate (show 0 < ε / 2 by linarith)
  have heq : entropyRate mass p - selectionHashRate mass p ε - ε / 2 =
      entropyRate mass p - degreeRate mass p - ε := by unfold selectionHashRate; ring
  simpa only [heq] using hselection

theorem eventually_exists_selection
    (counts : ℕ → Hist → Shape → ℕ) (sum : Hist → ℕ) (mass : Hist → ℝ)
    (p : Hist → FiniteLaw Shape) (u v w : Hist → Fin 17 → ℝ) (c : Hist → ℝ)
    (hmass : ∀ h, 0 ≤ mass h)
    (hcountSupport : ∀ N h a, 0 < counts N h a →
      a.1.val + a.2.1.val + a.2.2.val = sum h)
    (hsupport : ∀ h (a : Shape),
      a.1.val + a.2.1.val + a.2.2.val = sum h → 0 < (p h).mass a)
    (hlog : ∀ h a, 0 < (p h).mass a → Real.log ((p h).mass a) =
      u h (shapeSide 0 a) + v h (shapeSide 1 a) + w h (shapeSide 2 a) - c h)
    (hcounts : ∀ h a, Tendsto (fun N : ℕ => (counts N h a : ℝ) / (N : ℝ))
      atTop (𝓝 (mass h * (p h).mass a)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop,
      ∃ (s : JointCoarseHashing.Sample (Position (counts N))
          (JointOrdinarySelection.hashLevel (selectionHashRate mass p ε) N))
        (G : Finset (Target (counts N))),
        G.card = ⌊Real.exp ((N : ℝ) * (entropyRate mass p - degreeRate mass p - ε))⌋₊ ∧
        (∀ e ∈ G, JointOrdinarySelection.Good
          (JointOrdinarySelection.hashLevel (selectionHashRate mass p ε) N)
          (JointOrdinarySelection.hashSet (selectionHashRate mass p ε) N)
          (ambientSet (counts N) sum) (triple (counts N) e) s) ∧
        (G : Set (Target (counts N))).Pairwise (fun e f =>
          ¬ JointCoarseHashing.SharesSide (triple (counts N) e) (triple (counts N) f)) :=
  eventually_exists_selection_of_word_support counts sum mass p u v w c
    hmass hcountSupport
    (Eventually.of_forall fun _ h word hw i => hsupport h (word i) (hw.1 i))
    hlog hcounts hε

end MatrixMultiplication.JointOrdinaryPopulationSelection

end

end OAI
