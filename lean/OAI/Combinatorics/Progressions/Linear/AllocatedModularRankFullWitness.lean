import OAI.Combinatorics.Progressions.Lattices.AllocatedModularRankAffineFullWitness

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical
open FiniteProbabilityWeights

private theorem largestBadDepth_pullback {Ω Ξ : Type*} (A : ℕ → ℕ)
    (bad : ℕ → ℕ → Ω → Prop) (f : Ξ → Ω) (p : ℕ) (x : Ξ) :
    largestTestedBadDepth A (fun p a x => bad p a (f x)) p x =
      largestTestedBadDepth A bad p (f x) := rfl

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

noncomputable local instance actualBadSmoothFintype (inactive : LayerSamplerAxis I n → Prop) :
    Fintype (AllocatedSmoothRankCoefficientIndex X inactive L) := inferInstance
noncomputable local instance actualBadDeckFintype :
    Fintype (AllocatedDeckRankCoefficientIndex E L) := inferInstance
noncomputable local instance actualBadDeckDecidableEq :
    DecidableEq (AllocatedDeckRankCoefficientIndex E L) := Classical.decEq _

variable (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)
    (fixed : AllocatedActualCoefficientIndex G X I E n B → ℤ)

noncomputable def allocatedMixedActualCoefficientSample {N : ℕ}
    (x : AllocatedSmoothRankCoefficientIndex X inactive L → ℤ)
    (deck : AllocatedDeckRankCoefficientIndex E L → ZMod N) :
    AllocatedActualCoefficientIndex G X I E n B → ℤ :=
  Function.extend (allocatedCongruenceActualCoefficientEmbedding inactive spatial kernel block)
    (allocatedMixedSelectedValues inactive x deck) fixed

noncomputable def allocatedMixedActualBadProduct {N : ℕ}
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (A : ℕ → ℕ) (C : ℝ)
    (x : AllocatedSmoothRankCoefficientIndex X inactive L → ℤ)
    (deck : AllocatedDeckRankCoefficientIndex E L → ZMod N) : ℕ :=
  let f := allocatedMixedActualCoefficientSample inactive spatial kernel block fixed x deck
  ∏ p ∈ P, p ^ allocatedCongruenceBadDepth inactive (allocatedReadNoise f) (allocatedReadDeck f)
    (fun j a => allocatedReadProjection f ⟨j,a.val⟩) spatial kernel block P A C p

theorem allocatedMixedActualBadProduct_eq {N : ℕ}
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (A : ℕ → ℕ) (C : ℝ)
    (x : AllocatedSmoothRankCoefficientIndex X inactive L → ℤ)
    (deck : AllocatedDeckRankCoefficientIndex E L → ZMod N) :
    allocatedMixedActualBadProduct inactive spatial kernel block fixed P A C x deck =
      ∏ p ∈ P, p ^ largestTestedBadDepth A
        (allocatedCongruenceRankBad inactive (allocatedReadNoise fixed) (allocatedReadDeck fixed)
          (fun j a => allocatedReadProjection fixed ⟨j,a.val⟩) spatial kernel block P C)
        p (allocatedMixedSelectedValues inactive x deck) := by
  simp only [allocatedMixedActualBadProduct, allocatedMixedActualCoefficientSample,
    allocatedActualRefresh_badDepth]

theorem allocatedMixedActual_primePower_event {N D : ℕ} [NeZero N]
    (hm : 0 < m)
    (center width : AllocatedSmoothRankCoefficientIndex X inactive L → ℝ)
    (hwidth : ∀ j, 0 < width j) (hZ : 0 < shiftedSmoothProductMass center width)
    (P : Finset ℕ) (A : ℕ → ℕ) [∀ p : P, NeZero p.val]
    (hprime : ∀ p ∈ P, p.Prime) (hcover : ∀ p ∈ P, p ^ A p ∣ N)
    (hpositive : ∀ p ∈ P, 0 < A p)
    (hD : Fintype.card X + ∑ j : Fin m, (Fintype.card (E j) + n j) ≤ D)
    {C : ℝ} (hC : 0 ≤ C)
    (hL : ⌈2 * (C + D + 10) / modularRankSmallBallExponent m⌉₊ ≤ L)
    (hthreshold : ∀ p ∈ P, modularCoefficientPrimeThreshold m ≤ p ^ A p)
    (hlarge : ∀ j, 8 * (probabilityProfileLipschitz : ℝ) *
      (∏ p : P, p.val ^ A p.val) ≤ width j) :
    ((shiftedSmoothProductFiniteWeights center width hwidth hZ).prod
      (uniform (AllocatedDeckRankCoefficientIndex E L → ZMod N))).eventProbability
      (fun x => ∀ p : P, allocatedActualModulusBad inactive spatial kernel block C (p.val ^ A p.val)
        (allocatedMixedActualCoefficientSample inactive spatial kernel block fixed x.1.val x.2)) ≤
      1 / ((∏ p : P, p.val ^ A p.val : ℕ) : ℝ) ^ 10 +
        ∑ j, 16 * (probabilityProfileLipschitz : ℝ) *
          (∏ p : P, p.val ^ A p.val) / width j := by
  have h := allocatedMixedRank_primePower_event inactive
    (allocatedReadNoise fixed) (allocatedReadDeck fixed)
    (fun j a => allocatedReadProjection fixed ⟨j,a.val⟩) spatial kernel block hm
    center width hwidth hZ P A hprime hcover hpositive hD hC hL hthreshold hlarge
  simpa only [allocatedActualModulusBad, allocatedMixedActualCoefficientSample,
    allocatedActualRefresh_modulusBad] using h

theorem allocatedMixedActual_bad_product_probability {N D Q R : ℕ} [NeZero N]
    (hm : 0 < m)
    (center width : AllocatedSmoothRankCoefficientIndex X inactive L → ℝ)
    (hwidth : ∀ j, 0 < width j) (hZ : 0 < shiftedSmoothProductMass center width)
    (P : Finset ℕ) (A : ℕ → ℕ) [∀ p : P, NeZero p.val]
    (hprime : ∀ p ∈ P, p.Prime) (hcover : ∀ p ∈ P, p ^ A p ∣ N)
    (hQ : 1 ≤ Q) (hR : 0 < R) (hdepth : ∀ p ∈ P, p ^ A p ≤ Q)
    (hD : Fintype.card X + ∑ j : Fin m, (Fintype.card (E j) + n j) ≤ D)
    {C : ℝ} (hC : 0 ≤ C)
    (hL : ⌈2 * (C + D + 10) / modularRankSmallBallExponent m⌉₊ ≤ L)
    (hlarge : ∀ j, 8 * (probabilityProfileLipschitz : ℝ) * (max Q (R ^ 2) : ℕ) ≤ width j)
    {η : ℝ} (hη : 0 ≤ η)
    (herror : (∑ j, 16 * (probabilityProfileLipschitz : ℝ) *
      (max Q (R ^ 2) : ℕ) / width j) ≤ η) :
    ((shiftedSmoothProductFiniteWeights center width hwidth hZ).prod
      (uniform (AllocatedDeckRankCoefficientIndex E L → ZMod N))).eventProbability
      (fun x => smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) * R <
        allocatedMixedActualBadProduct inactive spatial kernel block fixed P A C x.1.val x.2) ≤
      2 / (9 * (R : ℝ) ^ 9) + ((Q : ℝ) + (R : ℝ) ^ 2) * η := by
  have h := allocatedMixedRank_bad_product_probability inactive
    (allocatedReadNoise fixed) (allocatedReadDeck fixed)
    (fun j a => allocatedReadProjection fixed ⟨j,a.val⟩) spatial kernel block hm
    center width hwidth hZ P A hprime hcover hQ hR hdepth hD hC hL hlarge hη herror
  simpa only [allocatedMixedActualBadProduct_eq, largestBadDepth_pullback] using h

theorem exists_early_allocatedMixedActual_bad_product_cutoff {D : ℕ}
    (hm : 0 < m)
    (hD : Fintype.card X + ∑ j : Fin m, (Fintype.card (E j) + n j) ≤ D)
    {C : ℝ} (hC : 0 ≤ C)
    (hL : ⌈2 * (C + D + 10) / modularRankSmallBallExponent m⌉₊ ≤ L)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ R : ℕ, 0 < R ∧ ∀ (Q N : ℕ) [NeZero N]
      (P : Finset ℕ) (A : ℕ → ℕ) [∀ p : P, NeZero p.val]
      (fixed : AllocatedActualCoefficientIndex G X I E n B → ℤ)
      (center width : AllocatedSmoothRankCoefficientIndex X inactive L → ℝ)
      (hwidth : ∀ j, 0 < width j) (hZ : 0 < shiftedSmoothProductMass center width),
      1 ≤ Q → (∀ p ∈ P, p.Prime) → (∀ p ∈ P, p ^ A p ∣ N) →
      (∀ p ∈ P, p ^ A p ≤ Q) →
      (∀ j, 8 * (probabilityProfileLipschitz : ℝ) * (max Q (R ^ 2) : ℕ) ≤ width j) →
      (∑ j, 16 * (probabilityProfileLipschitz : ℝ) * (max Q (R ^ 2) : ℕ) / width j) ≤
        δ / (2 * ((Q : ℝ) + (R : ℝ) ^ 2)) →
      ((shiftedSmoothProductFiniteWeights center width hwidth hZ).prod
        (uniform (AllocatedDeckRankCoefficientIndex E L → ZMod N))).eventProbability
        (fun x => smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) * R <
          allocatedMixedActualBadProduct inactive spatial kernel block fixed P A C x.1.val x.2) ≤ δ := by
  obtain ⟨R, hR, hradius⟩ := exists_early_badPrime_radius hδ
  refine ⟨R, hR, ?_⟩
  intro Q N _ P A _ fixed center width hwidth hZ hQ hprime hcover hdepth hlarge herror
  exact (allocatedMixedActual_bad_product_probability inactive spatial kernel block fixed hm
    center width hwidth hZ P A hprime hcover hQ hR hdepth hD hC hL hlarge
    (hradius Q hQ).1.le herror).trans (hradius Q hQ).2

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical
open FiniteProbabilityWeights
attribute [local irreducible] allocatedActualModulusBad allocatedMixedFullArray independentProductPMF

private theorem decide_eq_classical (p : Prop) [d : Decidable p] :
    @decide p d = @decide p (Classical.propDecidable p) := by
  cases Subsingleton.elim d (Classical.propDecidable p)
  rfl

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

noncomputable local instance fullWitnessSmoothFintype :
    Fintype (AllocatedFullSmoothCoefficientIndex G X I n B) := inferInstance
noncomputable local instance fullWitnessSmoothDecidableEq :
    DecidableEq (AllocatedFullSmoothCoefficientIndex G X I n B) := Classical.decEq _
noncomputable local instance fullWitnessSelectedSmoothDecidableEq (inactive : LayerSamplerAxis I n → Prop) :
    DecidableEq (AllocatedSmoothRankCoefficientIndex X inactive L) := Classical.decEq _
noncomputable local instance fullWitnessDeckFintype :
    Fintype (CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E) := inferInstance
noncomputable local instance fullWitnessDeckDecidableEq :
    DecidableEq (CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E) := Classical.decEq _
noncomputable local instance fullWitnessSelectedSmoothFintype (inactive : LayerSamplerAxis I n → Prop) :
    Fintype (AllocatedSmoothRankCoefficientIndex X inactive L) := inferInstance
noncomputable local instance fullWitnessSelectedDeckFintype :
    Fintype (AllocatedDeckRankCoefficientIndex E L) := inferInstance
noncomputable local instance fullWitnessSelectedDeckDecidableEq :
    DecidableEq (AllocatedDeckRankCoefficientIndex E L) := Classical.decEq _

theorem allocatedFullMixed_witness_iff
    (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)
    (C : ℝ) (P : Finset ℕ) [∀ p : P, NeZero p.val] (A : ℕ → ℕ)
    (N : ℕ) [NeZero N] (hdiv : ∀ p : P, p.val ^ A p.val ∣ N)
    (smooth : AllocatedFullSmoothCoefficientIndex G X I n B → ℤ)
    (deck : CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E → ZMod N)
    (continuous : AllocatedFullContinuousCoefficientIndex G I n B → ℤ) :
    allocatedResiduePrimePowerWitness inactive C P A N hdiv
      (allocatedMixedFullArray (fun i => (smooth i : ZMod N)) deck
        (fun i => (continuous i : ZMod N))) ↔
      ∀ p : P, allocatedActualModulusBad inactive spatial kernel block C (p.val ^ A p.val)
        (allocatedMixedFullArray smooth (fun i => (deck i).val) continuous) := by
  rw [← allocatedMixedFullArray_reduce]
  exact allocatedResiduePrimePowerWitness_iff_actual inactive spatial kernel block C P A N hdiv _

theorem allocatedFullMixed_primePower_event
    (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)
    (continuous : AllocatedFullContinuousCoefficientIndex G I n B → ℤ)
    {N D : ℕ} [NeZero N] (hm : 0 < m)
    (center width : AllocatedFullSmoothCoefficientIndex G X I n B → ℝ)
    (hwidth : ∀ j, 0 < width j) (hZ : 0 < shiftedSmoothProductMass center width)
    (P : Finset ℕ) (A : ℕ → ℕ) [∀ p : P, NeZero p.val]
    (hprime : ∀ p ∈ P, p.Prime) (hcover : ∀ p ∈ P, p ^ A p ∣ N)
    (hpositive : ∀ p ∈ P, 0 < A p)
    (hD : Fintype.card X + ∑ j : Fin m, (Fintype.card (E j) + n j) ≤ D)
    {C : ℝ} (hC : 0 ≤ C)
    (hL : ⌈2 * (C + D + 10) / modularRankSmallBallExponent m⌉₊ ≤ L)
    (hthreshold : ∀ p ∈ P, modularCoefficientPrimeThreshold m ≤ p ^ A p)
    (hlarge : ∀ j, 8 * (probabilityProfileLipschitz : ℝ) *
      (∏ p : P, p.val ^ A p.val) ≤ width (allocatedSmoothFullEmbedding inactive spatial block j)) :
    ((shiftedSmoothProductFiniteWeights center width hwidth hZ).prod
      (uniform (CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E → ZMod N))).eventProbability
      (fun x => ∀ p : P, allocatedActualModulusBad inactive spatial kernel block C (p.val ^ A p.val)
        (allocatedMixedFullArray x.1.val (fun i => (x.2 i).val) continuous)) ≤
      1 / ((∏ p : P, p.val ^ A p.val : ℕ) : ℝ) ^ 10 +
        ∑ j : AllocatedSmoothRankCoefficientIndex X inactive L,
          16 * (probabilityProfileLipschitz : ℝ) * (∏ p : P, p.val ^ A p.val) /
            width (allocatedSmoothFullEmbedding inactive spatial block j) := by
  let e := allocatedSmoothFullEmbedding (X := X) inactive spatial block
  let d := allocatedDeckFullEmbedding (E := E) (I := I) (n := n) (B := B) kernel
  apply mixedSmoothUniform_refresh_event_probability_le e d center width hwidth hZ N
    (fun x deck => ∀ p : P,
      allocatedActualModulusBad inactive spatial kernel block C (p.val ^ A p.val)
        (allocatedMixedFullArray x (fun i => (deck i).val) continuous))
  · exact add_nonneg (by positivity) (Finset.sum_nonneg (fun j _ =>
      div_nonneg (by positivity) (hwidth _).le))
  · intro fixed fixedDeck
    have h := allocatedMixedActual_primePower_event inactive spatial kernel block
      (allocatedMixedFullArray fixed (fun i => (fixedDeck i).val) continuous) hm
      (fun i => center (e i)) (fun i => width (e i)) (fun i => hwidth (e i))
      (shiftedSmoothProductMass_restrict_pos e center width hwidth hZ)
      P A hprime hcover hpositive hD hC hL hthreshold hlarge
    simpa only [e, d, allocatedMixedFullArray_refresh_selected,
      allocatedMixedActualCoefficientSample] using h

theorem allocatedProductMixed_primePower_event
    (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)
    (continuous : AllocatedFullContinuousCoefficientIndex G I n B → ℤ)
    (laws : AllocatedFullSmoothCoefficientIndex G X I n B → PMF ℤ)
    {N D : ℕ} [NeZero N] (hm : 0 < m)
    (center width : AllocatedSmoothRankCoefficientIndex X inactive L → ℝ)
    (hwidth : ∀ j, 0 < width j) (hZ : 0 < shiftedSmoothProductMass center width)
    (hcoordinate : ∀ i, laws (allocatedSmoothFullEmbedding inactive spatial block i) =
      shiftedSmoothCoefficientPMF (center i) (width i) (hwidth i)
        (shiftedSmoothProductMass_coordinate_pos center width hwidth hZ i))
    (P : Finset ℕ) (A : ℕ → ℕ) [∀ p : P, NeZero p.val]
    (hprime : ∀ p ∈ P, p.Prime) (hcover : ∀ p ∈ P, p ^ A p ∣ N)
    (hpositive : ∀ p ∈ P, 0 < A p)
    (hD : Fintype.card X + ∑ j : Fin m, (Fintype.card (E j) + n j) ≤ D)
    {C : ℝ} (hC : 0 ≤ C)
    (hL : ⌈2 * (C + D + 10) / modularRankSmallBallExponent m⌉₊ ≤ L)
    (hthreshold : ∀ p ∈ P, modularCoefficientPrimeThreshold m ≤ p ^ A p)
    (hlarge : ∀ j, 8 * (probabilityProfileLipschitz : ℝ) *
      (∏ p : P, p.val ^ A p.val) ≤ width j) :
    (((independentProductPMF laws).bind
      (fun x => (PMF.uniformOfFintype
        (CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E → ZMod N)).map
        (fun deck => decide (∀ p : P,
          allocatedActualModulusBad inactive spatial kernel block C (p.val ^ A p.val)
            (allocatedMixedFullArray x (fun i => (deck i).val) continuous))))) true).toReal ≤
      1 / ((∏ p : P, p.val ^ A p.val : ℕ) : ℝ) ^ 10 +
        ∑ j, 16 * (probabilityProfileLipschitz : ℝ) * (∏ p : P, p.val ^ A p.val) / width j := by
  let e := allocatedSmoothFullEmbedding (X := X) inactive spatial block
  let d := allocatedDeckFullEmbedding (E := E) (I := I) (n := n) (B := B) kernel
  let bad : (AllocatedFullSmoothCoefficientIndex G X I n B → ℤ) →
      (CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E → ZMod N) → Prop :=
    fun x deck => ∀ p : P,
    allocatedActualModulusBad inactive spatial kernel block C (p.val ^ A p.val)
      (allocatedMixedFullArray x (fun i => (deck i).val) continuous)
  let δ : ℝ := 1 / ((∏ p : P, p.val ^ A p.val : ℕ) : ℝ) ^ 10 +
    ∑ j, 16 * (probabilityProfileLipschitz : ℝ) * (∏ p : P, p.val ^ A p.val) / width j
  have hδ : 0 ≤ δ := add_nonneg (by positivity)
    (Finset.sum_nonneg (fun j _ => div_nonneg (by positivity) (hwidth _).le))
  have hconditional : ∀ (fixed : AllocatedFullSmoothCoefficientIndex G X I n B → ℤ)
      (fixedDeck : CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E → ZMod N),
      ((shiftedSmoothProductFiniteWeights center width hwidth hZ).prod
        (uniform (AllocatedDeckRankCoefficientIndex E L → ZMod N))).eventProbability
        (fun z => bad (Function.extend e z.1.val fixed) (Function.extend d z.2 fixedDeck)) ≤ δ := by
    intro fixed fixedDeck
    have h := allocatedMixedActual_primePower_event inactive spatial kernel block
      (allocatedMixedFullArray fixed (fun i => (fixedDeck i).val) continuous) hm
      center width hwidth hZ P A hprime hcover hpositive hD hC hL hthreshold hlarge
    simpa only [bad, e, d, δ, allocatedMixedFullArray_refresh_selected,
      allocatedMixedActualCoefficientSample] using h
  have h := independentProduct_uniform_smooth_selected_event_probability_le
    e d laws center width hwidth hZ hcoordinate N bad hδ hconditional
  simpa only [bad, δ, decide_eq_classical] using h

end Erdos3.VectorPolynomial

end

end OAI
