import Mathlib
import OAI.LinearAlgebra.MatrixFields.Extraction.InitialHash
import OAI.LinearAlgebra.MatrixFields.Histories.InitialOrbit

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldInitialGibbs

open AllFieldParameters AllFieldHistory AllFieldInitialEntropy AllFieldInitialOrbit
open MatrixMultiplication.Foundation
open scoped BigOperators

def coordinateWeight (k : Fin 17) : ℝ :=
  (weight (initialInteger k.val) : ℝ)

def orderedWeight (u : JointPopulation.Shape) : ℝ :=
  ∏ s : Fin 3, coordinateWeight (JointPopulation.shapeSide s u)

def initialNormalizer : ℝ := ((sortedInitial.map initialWeight).sum : ℚ)

def initialPotential (k : Fin 17) : ℝ := Real.log (coordinateWeight k)

def initialLogNormalizer : ℝ := Real.log initialNormalizer

theorem coordinateWeight_pos (k : Fin 17) : 0 < coordinateWeight k := by
  apply Rat.cast_pos.mpr
  apply weight_positive_of_argument_bound
  exact assigned_argument_bound _ tablea initial_table_arguments_bounded _

theorem orderedWeight_pos (u : JointPopulation.Shape) : 0 < orderedWeight u :=
  Finset.prod_pos (fun _ _ => coordinateWeight_pos _)

theorem initialNormalizer_pos : 0 < initialNormalizer := by
  apply Rat.cast_pos.mpr
  exact list_sum_map_positive _ _ (by decide +kernel)
    (fun s _ => initialWeight_positive s)

theorem orderedWeight_source (p : PlacedInitial) :
    orderedWeight (initialShapeCode p) =
      ∏ s : Fin 3, (weight (initialInteger (sortedInitial.get p.1 s)) : ℝ) := by
  simp only [orderedWeight, coordinateWeight, initialShapeCode_side]
  exact p.2.symm.prod_comp
    (fun s : Fin 3 => (weight (initialInteger (sortedInitial.get p.1 s)) : ℝ))

theorem initialWeight_source (p : PlacedInitial) :
    (initialWeight (sortedInitial.get p.1) : ℝ) =
      (initialMultiplicity (sortedInitial.get p.1) : ℝ) *
        orderedWeight (initialShapeCode p) := by
  rw [orderedWeight_source]
  simp only [initialWeight]
  push_cast
  rfl

theorem placedInitialLaw_mass (p : PlacedInitial) :
    placedInitialLaw.mass p =
      (initialMultiplicity (sortedInitial.get p.1) : ℝ) *
        orderedWeight (initialShapeCode p) / initialNormalizer / 6 := by
  change (initialLaw (sortedInitial.get p.1) : ℝ) / 6 = _
  rw [initialLaw, ite_eq_left (List.get_mem _ _), Rat.cast_div, initialWeight_source p]
  rfl

theorem orderedInitialLaw_mass (u : JointPopulation.Shape)
    (hu : u.1.val + u.2.1.val + u.2.2.val = 16) :
    orderedInitialLaw.mass u = orderedWeight u / initialNormalizer := by
  classical
  have hcount : (∑ p : PlacedInitial,
      if initialShapeCode p = u then
        (initialMultiplicity (sortedInitial.get p.1) : ℝ) else 0) = 6 := by
    exact_mod_cast weighted_fiber_count u hu
  simp only [orderedInitialLaw, FiniteLaw.map_mass, placedInitialLaw_mass]
  calc
    _ = (∑ p : PlacedInitial, if initialShapeCode p = u then
          (initialMultiplicity (sortedInitial.get p.1) : ℝ) else 0) *
        (orderedWeight u / initialNormalizer / 6) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : initialShapeCode p = u
      · simp only [hp, ite_true]
        ring
      · simp only [hp, ite_false, zero_mul]
    _ = _ := by rw [hcount]; ring

theorem orderedInitialLaw_zero (u : JointPopulation.Shape)
    (hu : u.1.val + u.2.1.val + u.2.2.val ≠ 16) :
    orderedInitialLaw.mass u = 0 := by
  classical
  simp only [orderedInitialLaw, FiniteLaw.map_mass]
  apply Finset.sum_eq_zero
  intro p _
  apply ite_eq_right
  intro hp
  have ht := source_total p
  rw [hp] at ht
  exact hu ht

theorem orderedInitialLaw_mass_eq (u : JointPopulation.Shape) :
    orderedInitialLaw.mass u =
      if u.1.val + u.2.1.val + u.2.2.val = 16
        then orderedWeight u / initialNormalizer else 0 := by
  split_ifs with hu
  · exact orderedInitialLaw_mass u hu
  · exact orderedInitialLaw_zero u hu

theorem orderedInitialLaw_positive (u : JointPopulation.Shape)
    (hu : u.1.val + u.2.1.val + u.2.2.val = 16) :
    0 < orderedInitialLaw.mass u := by
  rw [orderedInitialLaw_mass u hu]
  exact div_pos (orderedWeight_pos u) initialNormalizer_pos

theorem orderedInitialLaw_support (u : JointPopulation.Shape)
    (hu : 0 < orderedInitialLaw.mass u) :
    u.1.val + u.2.1.val + u.2.2.val = 16 := by
  by_contra hn
  rw [orderedInitialLaw_zero u hn] at hu
  exact lt_irrefl _ hu

theorem log_orderedWeight (u : JointPopulation.Shape) :
    Real.log (orderedWeight u) =
      initialPotential (JointPopulation.shapeSide 0 u) +
        initialPotential (JointPopulation.shapeSide 1 u) +
        initialPotential (JointPopulation.shapeSide 2 u) := by
  rw [orderedWeight, Real.log_prod
    (fun s _ => ne_of_gt (coordinateWeight_pos (JointPopulation.shapeSide s u)))]
  simp only [Fin.sum_univ_three, initialPotential]

theorem orderedInitialLaw_log (u : JointPopulation.Shape)
    (hu : 0 < orderedInitialLaw.mass u) :
    Real.log (orderedInitialLaw.mass u) =
      initialPotential (JointPopulation.shapeSide 0 u) +
        initialPotential (JointPopulation.shapeSide 1 u) +
        initialPotential (JointPopulation.shapeSide 2 u) - initialLogNormalizer := by
  rw [orderedInitialLaw_mass u (orderedInitialLaw_support u hu),
    Real.log_div (ne_of_gt (orderedWeight_pos u)) (ne_of_gt initialNormalizer_pos),
    log_orderedWeight]
  rfl

end MatrixMultiplication.AllFieldInitialGibbs

namespace MatrixMultiplication.AllFieldInitialFamily

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory AllFieldFiniteFamily
open AllFieldInitialEntropy JointOrdinaryPopulationSelection Filter
open scoped BigOperators Topology

attribute [local instance] Classical.propDecidable

variable {K : ℕ} (allocation : Allocation)

def grid : ℕ := populationLength (K := K) allocation 1

theorem grid_pos : 0 < grid (K := K) allocation :=
  AllFieldPopulationCounts.blockLength_pos (amount (K := K) allocation) (by decide)

theorem populationLength_eq_mul_grid (dilation : ℕ) :
    populationLength (K := K) allocation dilation = dilation * grid (K := K) allocation := by
  simp only [grid, populationLength, AllFieldPopulationCounts.blockLength, one_mul]

theorem initialJointCounts_dilation_ratio {dilation : ℕ} (hd : 0 < dilation)
    (j : Fin K) (u : JointPopulation.Shape) :
    (initialJointCounts allocation dilation j u : ℝ) / (dilation : ℝ) =
      (grid (K := K) allocation : ℝ) * orderedInitialLaw.mass u := by
  rw [initialJointCounts_cast, populationLength_eq_mul_grid, Nat.cast_mul, mul_assoc]
  have hd' : (dilation : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)
  exact mul_div_cancel_left₀ _ hd'

theorem initialJointCounts_dilation_rate (j : Fin K) (u : JointPopulation.Shape) :
    Tendsto (fun dilation : ℕ =>
      (initialJointCounts allocation dilation j u : ℝ) / (dilation : ℝ)) atTop
      (𝓝 ((grid (K := K) allocation : ℝ) * orderedInitialLaw.mass u)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with dilation hd
  exact (initialJointCounts_dilation_ratio allocation hd j u).symm

theorem native_dilation_capacity :
    entropyRate (fun _ : Fin K => (grid (K := K) allocation : ℝ))
      (fun _ => orderedInitialLaw) -
    degreeRate (fun _ : Fin K => (grid (K := K) allocation : ℝ))
      (fun _ => orderedInitialLaw) =
      (grid (K := K) allocation : ℝ) * ((K : ℝ) * nativeH0) := by
  simp only [entropyRate, degreeRate, sideDegreeRate, orderedInitialLaw_side_entropy,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, max_self]
  ring

def hashRate (ε : ℝ) : ℝ :=
  selectionHashRate (fun _ : Fin K => (grid (K := K) allocation : ℝ))
    (fun _ => orderedInitialLaw) ((grid (K := K) allocation : ℝ) * ε)

theorem selection_exponent (ε : ℝ) (dilation : ℕ) :
    (dilation : ℝ) *
        (entropyRate (fun _ : Fin K => (grid (K := K) allocation : ℝ))
            (fun _ => orderedInitialLaw) -
          degreeRate (fun _ : Fin K => (grid (K := K) allocation : ℝ))
            (fun _ => orderedInitialLaw) - (grid (K := K) allocation : ℝ) * ε) =
      (populationLength (K := K) allocation dilation : ℝ) * ((K : ℝ) * nativeH0 - ε) := by
  rw [native_dilation_capacity, populationLength_eq_mul_grid, Nat.cast_mul]
  ring

abbrev Sample (ε : ℝ) (dilation : ℕ) :=
  JointCoarseHashing.Sample (JointPopulation.Position
    (initialJointCounts (K := K) allocation dilation))
    (JointOrdinarySelection.hashLevel (hashRate (K := K) allocation ε) dilation)

def Good (ε : ℝ) (dilation : ℕ)
    (s : Sample (K := K) allocation ε dilation)
    (e : JointPopulation.Target (initialJointCounts (K := K) allocation dilation)) : Prop :=
  JointOrdinarySelection.Good
    (JointOrdinarySelection.hashLevel (hashRate (K := K) allocation ε) dilation)
    (JointOrdinarySelection.hashSet (hashRate (K := K) allocation ε) dilation)
    (JointPopulation.ambientSet (initialJointCounts allocation dilation) (fun _ => 16))
    (JointPopulation.triple (initialJointCounts allocation dilation) e) s

def executionWithWidth (F : Type*) [Field F] (ε residentWidth : ℝ) (dilation : ℕ)
    (s : Sample (K := K) allocation ε dilation)
    (G : Finset (JointPopulation.Target (initialJointCounts (K := K) allocation dilation)))
    (hgood : ∀ e ∈ G, Good allocation ε dilation s e) :
    Execution (cwSource F K (populationLength (K := K) allocation dilation))
      (Tensor.directSum (fun _ : AllFieldInitialHash.SelectedTargets
          (initialJointCounts (K := K) allocation dilation) G =>
        stateTensor F (K := K) allocation dilation residentWidth 0)) :=
  AllFieldInitialState.execution allocation dilation F residentWidth
    (AllFieldInitialHash.selectedExecution (F := F)
      (initialJointCounts allocation dilation) (initialJointCounts_sum allocation dilation)
      (initialJointCounts_support allocation dilation)
      (JointOrdinarySelection.hashLevel (hashRate (K := K) allocation ε) dilation)
      (JointOrdinarySelection.hashSet (hashRate (K := K) allocation ε) dilation)
      (JointOrdinarySelection.hashSet_AP (hashRate (K := K) allocation ε) dilation)
      s G hgood)

@[simp] theorem executionWithWidth_copies (F : Type*) [Field F]
    (ε residentWidth : ℝ) (dilation : ℕ)
    (s : Sample (K := K) allocation ε dilation)
    (G : Finset (JointPopulation.Target (initialJointCounts (K := K) allocation dilation)))
    (hgood : ∀ e ∈ G, Good allocation ε dilation s e) :
    Fintype.card
      (executionWithWidth allocation F ε residentWidth dilation s G hgood).Copies = 1 := rfl

def execution (F : Type*) [Field F] (ε : ℝ) (dilation : ℕ)
    (s : Sample (K := K) allocation ε dilation)
    (G : Finset (JointPopulation.Target (initialJointCounts (K := K) allocation dilation)))
    (hgood : ∀ e ∈ G, Good allocation ε dilation s e) :
    Execution (cwSource F K (populationLength (K := K) allocation dilation))
      (Tensor.directSum (fun _ : AllFieldInitialHash.SelectedTargets
          (initialJointCounts (K := K) allocation dilation) G =>
        stateTensor F (K := K) allocation dilation ε 0)) :=
  executionWithWidth allocation F ε ε dilation s G hgood

@[simp] theorem execution_copies (F : Type*) [Field F] (ε : ℝ) (dilation : ℕ)
    (s : Sample (K := K) allocation ε dilation)
    (G : Finset (JointPopulation.Target (initialJointCounts (K := K) allocation dilation)))
    (hgood : ∀ e ∈ G, Good allocation ε dilation s e) :
    Fintype.card (execution allocation F ε dilation s G hgood).Copies = 1 := rfl

theorem eventually_exists_execution_with_width (F : Type*) [Field F]
    (residentWidth : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ dilation in atTop,
      ∃ (s : Sample (K := K) allocation ε dilation)
        (G : Finset (JointPopulation.Target (initialJointCounts (K := K) allocation dilation))),
        G.card = ⌊Real.exp ((populationLength (K := K) allocation dilation : ℝ) *
          ((K : ℝ) * nativeH0 - ε))⌋₊ ∧
        (∀ e ∈ G, Good allocation ε dilation s e) ∧
        ∃ E : Execution (cwSource F K (populationLength (K := K) allocation dilation))
            (Tensor.directSum (fun _ : AllFieldInitialHash.SelectedTargets
                (initialJointCounts (K := K) allocation dilation) G =>
              stateTensor F (K := K) allocation dilation residentWidth 0)),
          Fintype.card E.Copies = 1 := by
  have hslack : 0 < (grid (K := K) allocation : ℝ) * ε :=
    mul_pos (by exact_mod_cast grid_pos (K := K) allocation) hε
  have hselection := JointOrdinaryPopulationSelection.eventually_exists_selection
    (fun dilation => initialJointCounts (K := K) allocation dilation) (fun _ => 16)
    (fun _ : Fin K => (grid (K := K) allocation : ℝ)) (fun _ => orderedInitialLaw)
    (fun _ => AllFieldInitialGibbs.initialPotential)
    (fun _ => AllFieldInitialGibbs.initialPotential)
    (fun _ => AllFieldInitialGibbs.initialPotential)
    (fun _ => AllFieldInitialGibbs.initialLogNormalizer)
    (fun _ => Nat.cast_nonneg _)
    (fun dilation => initialJointCounts_support allocation dilation)
    (fun _ => AllFieldInitialGibbs.orderedInitialLaw_positive)
    (fun _ => AllFieldInitialGibbs.orderedInitialLaw_log)
    (initialJointCounts_dilation_rate allocation) hslack
  filter_upwards [hselection] with dilation hd
  obtain ⟨s, G, hcard, hgood, _hpairwise⟩ := hd
  rw [selection_exponent allocation ε dilation] at hcard
  exact ⟨s, G, hcard, hgood,
    executionWithWidth allocation F ε residentWidth dilation s G hgood,
    executionWithWidth_copies allocation F ε residentWidth dilation s G hgood⟩

theorem eventually_exists_execution (F : Type*) [Field F] {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ dilation in atTop,
      ∃ (s : Sample (K := K) allocation ε dilation)
        (G : Finset (JointPopulation.Target (initialJointCounts (K := K) allocation dilation))),
        G.card = ⌊Real.exp ((populationLength (K := K) allocation dilation : ℝ) *
          ((K : ℝ) * nativeH0 - ε))⌋₊ ∧
        (∀ e ∈ G, Good allocation ε dilation s e) ∧
        ∃ E : Execution (cwSource F K (populationLength (K := K) allocation dilation))
            (Tensor.directSum (fun _ : AllFieldInitialHash.SelectedTargets
                (initialJointCounts (K := K) allocation dilation) G =>
              stateTensor F (K := K) allocation dilation ε 0)),
          Fintype.card E.Copies = 1 :=
  eventually_exists_execution_with_width allocation F ε hε

end MatrixMultiplication.AllFieldInitialFamily

end

end MatrixAllFields

end OAI
