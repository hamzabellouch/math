import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.InitialHash
import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.InitialState
import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.InitialGibbs

namespace OAI

/-! Tensor extraction over arbitrary fields and its asymptotic rate. -/

noncomputable section

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

end OAI
