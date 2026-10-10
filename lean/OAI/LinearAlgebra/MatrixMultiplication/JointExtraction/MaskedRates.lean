import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.MaskedAssignment
import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.OrdinarySelection

namespace OAI

/-! Joint tensor extraction, compatibility and entropy estimates. -/

noncomputable section

namespace MatrixMultiplication.JointMaskedRates

open Filter JointCoarseHashing JointExtractionRates JointMaskedSelection
open JointOrdinarySelection (hashLevel hashSet)
open scoped Topology

attribute [local instance] Classical.propDecidable

def errorBound (degree : ℕ → ℕ) (B p : ℕ) (H : ℝ) (N : ℕ) : ℝ :=
  (degree N : ℝ) / (hashModulus H N : ℝ) *
    (1 + (B : ℝ) * ((N : ℝ) + 1) ^ p * (N : ℝ))

theorem polynomialFactor_le (B p N : ℕ) :
    1 + (B : ℝ) * ((N : ℝ) + 1) ^ p * (N : ℝ) ≤
      ((B : ℝ) + 1) * ((N : ℝ) + 1) ^ (p + 1) := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hx : (0 : ℝ) ≤ (N : ℝ) + 1 := by linarith
  have hpower : (1 : ℝ) ≤ ((N : ℝ) + 1) ^ (p + 1) :=
    one_le_pow₀ (by linarith : (1 : ℝ) ≤ (N : ℝ) + 1)
  calc
    _ ≤ 1 + (B : ℝ) * ((N : ℝ) + 1) ^ p * ((N : ℝ) + 1) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (by linarith)
        (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx _)))
    _ = 1 + (B : ℝ) * ((N : ℝ) + 1) ^ (p + 1) := by rw [pow_succ]; ring
    _ ≤ ((N : ℝ) + 1) ^ (p + 1) + (B : ℝ) * ((N : ℝ) + 1) ^ (p + 1) :=
      add_le_add hpower le_rfl
    _ = _ := by ring

theorem eventually_errorBound_le_half (degree : ℕ → ℕ) (B p : ℕ)
    {D H : ℝ} (hH : 0 ≤ H) (hgap : D < H)
    (hdegreeRate : ∀ η : ℝ, 0 < η →
      ∀ᶠ N in atTop, Real.log (degree N : ℝ) / (N : ℝ) ≤ D + η) :
    ∀ᶠ N in atTop, errorBound degree B p H N ≤ 1 / 2 := by
  let c : ℝ := (H - D) / 2
  have hc : 0 < c := by dsimp [c]; linarith
  have hclt : c < H - D := by dsimp [c]; linarith
  have hratio := eventually_degree_div_hashModulus_le_exp hH hdegreeRate hclt
  apply eventually_error_le_half ((B : ℝ) + 1) (p + 1) hc
  filter_upwards [hratio] with N hN
  have hx : (0 : ℝ) ≤ (N : ℝ) + 1 := add_nonneg (Nat.cast_nonneg N) zero_le_one
  have hfactor : 0 ≤ 1 + (B : ℝ) * ((N : ℝ) + 1) ^ p * (N : ℝ) :=
    add_nonneg zero_le_one
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx _)) (Nat.cast_nonneg _))
  calc
    errorBound degree B p H N ≤ Real.exp (-c * (N : ℝ)) *
        (1 + (B : ℝ) * ((N : ℝ) + 1) ^ p * (N : ℝ)) :=
      mul_le_mul_of_nonneg_right hN hfactor
    _ ≤ Real.exp (-c * (N : ℝ)) * (((B : ℝ) + 1) * ((N : ℝ) + 1) ^ (p + 1)) :=
      mul_le_mul_of_nonneg_left (polynomialFactor_le B p N) (Real.exp_pos _).le
    _ = ((B : ℝ) + 1) * (((N : ℝ) + 1) ^ (p + 1) * Real.exp (-c * (N : ℝ))) := by ring

theorem count_error_le_envelope {P E O V : Type*} (d : OrbitData P E O V)
    (e : E) (degree B p N M : ℕ)
    (heligibility : (d.eligibilityCompetitors e).card ≤ degree)
    (horbits : (d.orbits e).card ≤ B * (N + 1) ^ p) :
    ((d.eligibilityCompetitors e).card : ℝ) / (M : ℝ) +
      ((d.orbits e).card : ℝ) * (N : ℝ) * ((degree : ℝ) / (M : ℝ)) ≤
    (degree : ℝ) / (M : ℝ) * (1 + (B : ℝ) * ((N : ℝ) + 1) ^ p * (N : ℝ)) := by
  have hdegreeR : ((d.eligibilityCompetitors e).card : ℝ) ≤ (degree : ℝ) := by
    exact_mod_cast heligibility
  have horbitsR : ((d.orbits e).card : ℝ) ≤ (B : ℝ) * ((N : ℝ) + 1) ^ p := by
    exact_mod_cast horbits
  have hratio : (0 : ℝ) ≤ (degree : ℝ) / (M : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  calc
    _ ≤ (degree : ℝ) / (M : ℝ) +
        ((B : ℝ) * ((N : ℝ) + 1) ^ p) * (N : ℝ) * ((degree : ℝ) / (M : ℝ)) :=
      add_le_add (div_le_div_of_nonneg_right hdegreeR (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right horbitsR (Nat.cast_nonneg _)) hratio)
    _ = _ := by ring

theorem eventually_exists_selection
    {P E O V : ℕ → Type*} [∀ N, Fintype (P N)] [∀ N, Fintype (E N)]
    (d : ∀ N, OrbitData (P N) (E N) (O N) (V N))
    (hinj : ∀ N, Function.Injective (d N).coarse)
    (degree : ℕ → ℕ) (B p : ℕ)
    (heligibility : ∀ N e, ((d N).eligibilityCompetitors e).card ≤ degree N)
    (hdegree : ∀ N e, ∀ o ∈ (d N).orbits e, ∀ v ∈ (d N).passing e o,
      ((d N).competitors e o v).card ≤ degree N)
    (horbits : ∀ N e, ((d N).orbits e).card ≤ B * (N + 1) ^ p)
    {A D H C₀ : ℝ} (hH : 0 ≤ H) (hgap : D < H)
    (hdegreeRate : ∀ η : ℝ, 0 < η →
      ∀ᶠ N in atTop, Real.log (degree N : ℝ) / (N : ℝ) ≤ D + η)
    (hdet : ∀ᶠ N in atTop, ∀ e, ∀ o ∈ (d N).orbits e,
      JointLossCounts.deterministicLossFraction ((d N).full e o) ((d N).passing e o) ≤
        C₀ / (N : ℝ))
    (hpos : ∀ᶠ N in atTop, 0 < Fintype.card (E N))
    (hE : Tendsto (fun N => Real.log (Fintype.card (E N) : ℝ) / (N : ℝ)) atTop (𝓝 A))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∃ (s : Sample (P N) (hashLevel H N)) (G : Finset (E N)),
      G.card = ⌊Real.exp ((N : ℝ) * (A - H - ε))⌋₊ ∧
      (∀ e ∈ G, (d N).Good (hashLevel H N) (hashSet H N) (N : ℝ) e s) ∧
      (∀ e ∈ G, ∀ f ∈ G, e ≠ f → ((d N).coarse e).1 ≠ ((d N).coarse f).1) ∧
      ∀ e ∈ G, ∀ o ∈ (d N).orbits e,
        JointLossCounts.missingFraction ((d N).full e o) ((d N).passing e o)
          ((d N).variableBad (hashLevel H N) (hashSet H N) e o) s ≤ (C₀ + 1) / (N : ℝ) := by
  classical
  have huniform := eventually_errorBound_le_half degree B p hH hgap hdegreeRate
  have hsmall : ∀ᶠ N in atTop, ∀ e,
      (((d N).eligibilityCompetitors e).card : ℝ) / (hashModulus H N : ℝ) +
        (((d N).orbits e).card : ℝ) * (N : ℝ) *
          ((degree N : ℝ) / (hashModulus H N : ℝ)) ≤ 1 / 2 := by
    filter_upwards [huniform] with N hN e
    exact (count_error_le_envelope (d N) e (degree N) B p N (hashModulus H N)
      (heligibility N e) (horbits N e)).trans hN
  have hpositive : ∀ᶠ N : ℕ in atTop, (0 : ℝ) < N := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    exact_mod_cast hN
  let good := fun N (s : Sample (P N) (hashLevel H N)) (e : E N) =>
    (d N).Good (hashLevel H N) (hashSet H N) (N : ℝ) e s
  have hinc : ∀ᶠ N in atTop, ∀ e,
      (((JointAPFree.modularSet (hashModulus H N)).card : ℝ) /
        (hashModulus H N : ℝ) ^ 2 / 2) *
        (Fintype.card (Sample (P N) (hashLevel H N)) : ℝ) ≤
          (goodIncidence (good N) e : ℝ) := by
    filter_upwards [hsmall, hpositive] with N hN hNpos e
    rw [show goodIncidence (good N) e =
        ((d N).goodEvent (hashLevel H N) (hashSet H N) (N : ℝ) e).card from
      (d N).goodIncidence_eq _ _ _ _]
    exact (d N).goodEvent_card_lower (hashLevel H N) (hashSet H N) (N : ℝ) hNpos e
      (degree N) (hdegree N e) (hN e)
  have hyield := eventually_exists_many_good_explicit good hH hpos hinc hE hε
  have hselection := eventually_exists_good_subfamily good
    (fun N => ⌊Real.exp ((N : ℝ) * (A - H - ε))⌋₊) hyield
  filter_upwards [hselection, hdet] with N hN hdetN
  obtain ⟨s, G, hcard, hgood⟩ := hN
  refine ⟨s, G, hcard, hgood, ?_, ?_⟩
  · intro e he f hf hne
    exact (d N).good_no_shared_x (hashLevel H N) (hashSet H N) (N : ℝ) f e s
      (hgood f hf) (hgood e he) (fun h => hne ((hinj N) h))
  · intro e he o ho
    exact (d N).good_missingFraction_le (hashLevel H N) (hashSet H N) C₀ (N : ℝ) e s
      (hgood e he) (hdetN e) o ho

end MatrixMultiplication.JointMaskedRates

end

end OAI
