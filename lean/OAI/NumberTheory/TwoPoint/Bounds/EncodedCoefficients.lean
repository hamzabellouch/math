import OAI.NumberTheory.TwoPoint.Circuits.BitMarginals
import OAI.NumberTheory.TwoPoint.Bounds.SampleDensity
import OAI.NumberTheory.TwoPoint.Bounds.FourierMass
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

namespace OAI

/-!
# Low-order coefficients of the actual encoded interval law

A Walsh coefficient only uses the residue coordinates touched by its bits.
All other independent jitters integrate out. The remaining observable is
bounded by one, so CRT gives the product of its selected moduli divided by
the interval length as an explicit coefficient bound.
-/

namespace TwoPointCorrelations

open Finset

lemma finiteRandomKernel_expectation {α β J : Type*} [Fintype β] [DecidableEq β]
    [Fintype J] (F : α → J → β) (u : β → ℝ) (x : α) :
    (∑ y, finiteRandomKernel F x y * u y) = uniformAverage (fun j => u (F x j)) := by
  unfold finiteRandomKernel uniformAverage
  simp_rw [div_mul_eq_mul_div, Finset.sum_mul]
  rw [← Finset.sum_div, Finset.sum_comm]
  simp

lemma kernelTransport_expectation {α β : Type*} [Fintype α] [Fintype β]
    (K : α → β → ℝ) (p : α → ℝ) (u : β → ℝ) :
    (∑ y, kernelTransport K p y * u y) = ∑ x, p x * ∑ y, K x y * u y := by
  unfold kernelTransport
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

lemma crtJitterBits_uniformAverage {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℕ) [∀ i, NeZero (s i)] (B : ℕ)
    (u : (ι → BooleanCube B) → ℝ) :
    uniformAverage (fun r : ∀ i, ZMod (s i) =>
      uniformAverage (fun j : ι → Fin (2 ^ B) => u (crtJitterBits s B r j))) =
        uniformAverage u := by
  rw [← crtUniform_expectation s]
  simp_rw [← finiteRandomKernel_expectation (crtJitterBits s B) u]
  rw [← kernelTransport_expectation]
  simp_rw [crtJitterBits_uniform]
  unfold uniformAverage
  rw [← Finset.mul_sum]
  ring

/-- Flatten bit blocks in the same order as the standard product equivalence
`Fin m × Fin B ≃ Fin (m*B)`. -/
def flattenBitBlocks (m B : ℕ) : (Fin m → BooleanCube B) ≃ BooleanCube (m * B) :=
  (Equiv.curry (Fin m) (Fin B) Bool).symm.trans
    (Equiv.arrowCongr finProdFinEquiv (Equiv.refl Bool))

@[simp] lemma flattenBitBlocks_apply {m B : ℕ} (z : Fin m → BooleanCube B)
    (k : Fin (m * B)) : flattenBitBlocks m B z k = z k.divNat k.modNat := rfl

/-- Residue coordinates on which a given Walsh character depends. -/
def bitSources {m B : ℕ} (S : Finset (Fin (m * B))) : Finset (Fin m) :=
  S.image (fun k => k.divNat)

lemma card_bitSources_le {m B : ℕ} (S : Finset (Fin (m * B))) :
    (bitSources S).card ≤ S.card := Finset.card_image_le

lemma bitSource_mem {m B : ℕ} (S : Finset (Fin (m * B))) {k : Fin (m * B)} (hk : k ∈ S) :
    k.divNat ∈ bitSources S := Finset.mem_image_of_mem _ hk

/-- Extend selected blocks by zero bits outside the selection. -/
def extendBitBlocks {m B : ℕ} (C : Finset (Fin m)) (z : C → BooleanCube B) : Fin m → BooleanCube B :=
  fun i => if h : i ∈ C then z ⟨i, h⟩ else fun _ => false

noncomputable def selectedWalsh {m B : ℕ} (S : Finset (Fin (m * B)))
    (z : bitSources S → BooleanCube B) : ℝ :=
  walsh S (flattenBitBlocks m B (extendBitBlocks (bitSources S) z))

lemma selectedWalsh_restrict {m B : ℕ} (S : Finset (Fin (m * B)))
    (z : Fin m → BooleanCube B) :
    selectedWalsh S (fun i : bitSources S => z i) = walsh S (flattenBitBlocks m B z) := by
  unfold selectedWalsh walsh
  apply Finset.prod_congr rfl
  intro k hk
  simp only [flattenBitBlocks_apply, extendBitBlocks, dite_eq_left (bitSource_mem S hk)]

lemma abs_selectedWalsh {m B : ℕ} (S : Finset (Fin (m * B)))
    (z : bitSources S → BooleanCube B) : |selectedWalsh S z| = 1 := abs_walsh _ _

/-- The actual bits sampled from one uniformly chosen integer origin and
independent finite jitters in every residue coordinate. -/
noncomputable def integerBitSample {m : ℕ} (s : Fin m → ℕ) [∀ i, NeZero (s i)]
    (B a : ℕ) {N : ℕ} (x : Fin N × (Fin m → Fin (2 ^ B))) : BooleanCube (m * B) :=
  flattenBitBlocks m B (crtJitterBits s B (fun i => (a + x.1.val : ZMod (s i))) x.2)

noncomputable def integerBitDensity {m : ℕ} (s : Fin m → ℕ) [∀ i, NeZero (s i)]
    (B a N : ℕ) : BooleanCube (m * B) → ℝ :=
  sampleDensity (@integerBitSample m s _ B a N)

lemma integerBitDensity_nonneg {m : ℕ} (s : Fin m → ℕ) [∀ i, NeZero (s i)]
    (B a N : ℕ) (x : BooleanCube (m * B)) : 0 ≤ integerBitDensity s B a N x :=
  sampleDensity_nonneg _ x

lemma integerBitDensity_mean {m : ℕ} (s : Fin m → ℕ) [∀ i, NeZero (s i)]
    (B a N : ℕ) (hN : 0 < N) : cubeAverage (integerBitDensity s B a N) = 1 := by
  let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  let : Nonempty (Fin (2 ^ B)) := ⟨⟨0, by positivity⟩⟩
  exact sampleDensity_mean _

/-- The bounded observable on precisely the touched residue coordinates. -/
noncomputable def selectedWalshMean {m B : ℕ} (s : Fin m → ℕ)
    [∀ i, NeZero (s i)] (S : Finset (Fin (m * B)))
    (r : ∀ i : bitSources S, ZMod (s i)) : ℝ :=
  uniformAverage (fun j : bitSources S → Fin (2 ^ B) =>
    selectedWalsh S (crtJitterBits (fun i : bitSources S => s i) B r j))

lemma abs_selectedWalshMean_le_one {m B : ℕ} (s : Fin m → ℕ) [∀ i, NeZero (s i)]
    (S : Finset (Fin (m * B))) (r : ∀ i : bitSources S, ZMod (s i)) :
    |selectedWalshMean s S r| ≤ 1 := by
  apply abs_uniformAverage_le_one
  intro j
  exact (abs_selectedWalsh _ _).le

lemma crtJitterBits_restrict {m B : ℕ} (s : Fin m → ℕ) [∀ i, NeZero (s i)]
    (C : Finset (Fin m)) (r : ∀ i, ZMod (s i)) (j : Fin m → Fin (2 ^ B)) :
    (fun i : C => crtJitterBits s B r j i) =
      crtJitterBits (fun i : C => s i) B (fun i : C => r i) (fun i : C => j i) := rfl

lemma selectedWalshMean_eq_full {m B : ℕ} (s : Fin m → ℕ) [∀ i, NeZero (s i)]
    (S : Finset (Fin (m * B))) (r : ∀ i, ZMod (s i)) :
    selectedWalshMean s S (fun i : bitSources S => r i) =
      uniformAverage (fun j : Fin m → Fin (2 ^ B) =>
        walsh S (flattenBitBlocks m B (crtJitterBits s B r j))) := by
  let : Nonempty (Fin (2 ^ B)) := ⟨⟨0, by positivity⟩⟩
  rw [selectedWalshMean, ← uniformAverage_restrict (fun _ : Fin m => Fin (2 ^ B)) (bitSources S)]
  apply congrArg uniformAverage
  funext j
  rw [← crtJitterBits_restrict, selectedWalsh_restrict]

lemma selectedWalshMean_average_zero {m B : ℕ} (s : Fin m → ℕ) [∀ i, NeZero (s i)]
    (S : Finset (Fin (m * B))) (hS : S.Nonempty) : uniformAverage (selectedWalshMean s S) = 0 := by
  rw [← uniformAverage_restrict (fun i : Fin m => ZMod (s i)) (bitSources S)]
  simp_rw [selectedWalshMean_eq_full]
  rw [crtJitterBits_uniformAverage s B (fun z => walsh S (flattenBitBlocks m B z))]
  have heq := uniformAverage_equiv (flattenBitBlocks m B) (walsh S)
  rw [heq]
  exact cubeAverage_walsh hS

/-- Each low-order coefficient is the actual selected-coordinate observable
along the integer interval. -/
lemma integerBitDensity_coefficient {m B : ℕ} (s : Fin m → ℕ) [∀ i, NeZero (s i)]
    (a N : ℕ) (hN : 0 < N) (S : Finset (Fin (m * B))) :
    walshCoefficient (integerBitDensity s B a N) S =
      uniformAverage (fun j : Fin N =>
        selectedWalshMean s S (fun i : bitSources S => (a + j.val : ZMod (s i)))) := by
  let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  let : Nonempty (Fin (2 ^ B)) := ⟨⟨0, by positivity⟩⟩
  rw [integerBitDensity, sampleDensity_walshCoefficient,
    uniformAverage_prod (fun (j : Fin N) (noise : Fin m → Fin (2 ^ B)) =>
      walsh S (integerBitSample s B a (j, noise)))]
  apply congrArg uniformAverage
  funext j
  change uniformAverage (fun noise : Fin m → Fin (2 ^ B) =>
      walsh S (flattenBitBlocks m B
        (crtJitterBits s B (fun i => (a + j.val : ZMod (s i))) noise))) = _
  exact (selectedWalshMean_eq_full s S (fun i => (a + j.val : ZMod (s i)))).symm

/-- The Fourier error for a set of bits is bounded by the product of the
moduli of the residue coordinates touched by those bits, divided by length. -/
theorem integerBitDensity_coefficient_bound {m B : ℕ} (s : Fin m → ℕ) [∀ i, NeZero (s i)]
    (hcop : Pairwise (fun i j => (s i).Coprime (s j)))
    (a N : ℕ) (hN : 0 < N) (S : Finset (Fin (m * B))) (hS : S.Nonempty) :
    |walshCoefficient (integerBitDensity s B a N) S| ≤
      (∏ i : bitSources S, s i : ℕ) / (N : ℝ) := by
  have hcopS : Pairwise (fun i j : bitSources S => (s i).Coprime (s j)) := by
    intro i j hij
    exact hcop (fun h => hij (Subtype.ext h))
  have h := crt_observable_difference (fun i : bitSources S => s i) hcopS
    (a : ZMod (∏ i : bitSources S, s i)) N hN (selectedWalshMean s S)
    (abs_selectedWalshMean_le_one s S)
  have hvec (j : Fin N) :
      ZMod.prodEquivPi (fun i : bitSources S => s i) hcopS
          ((a : ZMod (∏ i : bitSources S, s i)) + (j.val : ZMod (∏ i : bitSources S, s i))) =
        (fun i : bitSources S => (a + j.val : ZMod (s i))) := by
    funext i
    simp only [ZMod.prodEquivPi_apply, map_add, map_natCast]
  simp_rw [hvec, selectedWalshMean_average_zero s S hS, sub_zero] at h
  rw [integerBitDensity_coefficient s a N hN S]
  exact h

lemma selected_modulus_product_le {m B : ℕ} (s : Fin m → ℕ)
    (S : Finset (Fin (m * B))) (M : ℝ) (hM : 1 ≤ M)
    (hs : ∀ i, (s i : ℝ) ≤ M) (t : ℕ) (ht : S.card ≤ t) :
    ((∏ i : bitSources S, s i : ℕ) : ℝ) ≤ M ^ t := by
  calc
    ((∏ i : bitSources S, s i : ℕ) : ℝ) = ∏ i : bitSources S, (s i : ℝ) := by push_cast; rfl
    _ ≤ ∏ _i : bitSources S, M :=
      Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun i _ => hs i)
    _ = M ^ (bitSources S).card := by simp
    _ ≤ M ^ t := pow_le_pow_right₀ hM ((card_bitSources_le S).trans ht)

lemma integerBitDensity_low_coefficients {m B : ℕ} (s : Fin m → ℕ) [∀ i, NeZero (s i)]
    (hcop : Pairwise (fun i j => (s i).Coprime (s j)))
    (a N : ℕ) (hN : 0 < N) (M : ℝ) (hM : 1 ≤ M) (hs : ∀ i, (s i : ℝ) ≤ M) (t : ℕ) :
    ∀ S ∈ lowWalshSets (m * B) t,
      |walshCoefficient (integerBitDensity s B a N) S| ≤ M ^ t / (N : ℝ) := by
  intro S hS
  have hdata := (Finset.mem_filter.mp hS).2
  exact (integerBitDensity_coefficient_bound s hcop a N hN S hdata.1).trans
    (div_le_div_of_nonneg_right (selected_modulus_product_le s S M hM hs t hdata.2)
      (Nat.cast_nonneg N))

/-- Finite-parameter encoded residue comparison derived from the published
Braverman input, with all Fourier errors discharged by the actual interval
sampling law. Only the final numerical error budget is left to choose. -/
theorem BravermanDepth22Input.encoded_interval_comparison (hBraverman : BravermanDepth22Input) :
    ∃ K C : ℕ, 0 < K ∧ 0 < C ∧ ∀ (m B : ℕ), 0 < m * B →
      ∀ (s : Fin m → ℕ) [∀ i, NeZero (s i)],
      Pairwise (fun i j => (s i).Coprime (s j)) →
      ∀ (c : AC0Circuit (m * B)), c.depth ≤ 22 →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∀ t : ℕ,
        (K : ℝ) * (Real.log ((c.size : ℝ) / ε)) ^ C ≤ (t : ℝ) →
        ∀ (a N : ℕ), 0 < N → ∀ M A : ℝ, 1 ≤ M → (∀ i, (s i : ℝ) ≤ M) →
          (M ^ t / (N : ℝ)) * ((t + 1 : ℕ) : ℝ) * ((m * B : ℕ) : ℝ) ^ t ≤ A →
          |uniformAverage (fun x : Fin N × (Fin m → Fin (2 ^ B)) =>
              c.indicator (integerBitSample s B a x)) - cubeAverage c.indicator| ≤
            3 * A / 2 + ε := by
  obtain ⟨K, C, hK, hC, hbound⟩ := hBraverman.coefficient_comparison
  refine ⟨K, C, hK, hC, ?_⟩
  intro m B hn s _hpos hcop c hc ε hε hεmax t ht a N hN M A hM hs hA
  let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  let : Nonempty (Fin (2 ^ B)) := ⟨⟨0, by positivity⟩⟩
  have h := hbound (m * B) hn c hc ε hε hεmax t ht (integerBitDensity s B a N)
    (M ^ t / (N : ℝ)) A (integerBitDensity_nonneg s B a N)
    (integerBitDensity_mean s B a N hN) (by positivity)
    (integerBitDensity_low_coefficients s hcop a N hN M hM hs t) hA
  simpa only [integerBitDensity, sampleDensity_expectation] using h

end TwoPointCorrelations

end OAI
