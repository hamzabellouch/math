import OAI.NumberTheory.JointDickman.Amplification.SignedLocalRegularity
import OAI.NumberTheory.JointDickman.Counting.DyadicScaleWindow

namespace OAI

/-! # Published regularity loss on the actual compact tensor boxes -/

namespace JointDickman
open Finset Filter
open scoped Topology

noncomputable def tensorIntervalLower (X : ℝ) : ℕ := ⌊(1/4 : ℝ)*X⌋₊+1
noncomputable def tensorIntervalUpper (X : ℝ) : ℕ := ⌊(17/4 : ℝ)*X⌋₊+1

theorem tensorInterval_width {X : ℝ} (hX : 1 ≤ X) :
    3*X ≤ (tensorIntervalUpper X : ℝ)-tensorIntervalLower X ∧
      (tensorIntervalUpper X : ℝ)-tensorIntervalLower X ≤ 5*X := by
  have hl := Nat.floor_le (show 0 ≤ (1/4 : ℝ)*X by linarith)
  have hl' := Nat.lt_floor_add_one ((1/4 : ℝ)*X)
  have hu := Nat.floor_le (show 0 ≤ (17/4 : ℝ)*X by linarith)
  have hu' := Nat.lt_floor_add_one ((17/4 : ℝ)*X)
  simp only [tensorIntervalUpper,tensorIntervalLower,Nat.cast_add,Nat.cast_one]
  constructor <;> linarith

theorem tensorInterval_order {X : ℝ} (hX : 0 ≤ X) :
    tensorIntervalLower X ≤ tensorIntervalUpper X := by
  unfold tensorIntervalLower tensorIntervalUpper
  exact Nat.add_le_add_right (Nat.floor_mono (by linarith : (1/4 : ℝ)*X ≤ (17/4 : ℝ)*X)) 1

theorem tensorInterval_point {X : ℝ} (hX : 0 ≤ X) {n : ℕ}
    (hn : n ∈ Ico (tensorIntervalLower X) (tensorIntervalUpper X)) :
    X/4 ≤ n ∧ (n : ℝ) ≤ (17/4 : ℝ)*X := by
  obtain ⟨hlo,hhi⟩ := mem_Ico.mp hn
  have hl : ⌊(1/4 : ℝ)*X⌋₊ < n := by
    change ⌊(1/4 : ℝ)*X⌋₊+1 ≤ n at hlo
    omega
  have hl' := (Nat.floor_lt (show 0 ≤ (1/4 : ℝ)*X by positivity)).mp hl
  have hu : n ≤ ⌊(17/4 : ℝ)*X⌋₊ := by
    change n < ⌊(17/4 : ℝ)*X⌋₊+1 at hhi
    omega
  have hu' : (n : ℝ) ≤ ⌊(17/4 : ℝ)*X⌋₊ := by exact_mod_cast hu
  exact ⟨by linarith,hu'.trans (Nat.floor_le (by positivity))⟩

open Classical in
/-- At a fixed dyadic box, the published three-form sieve bound has the
normalization 1/(B*T) required before summing the dyadic partition. -/
theorem tensorBox_signed_regularity_loss
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ L : ℕ, ∀ τ : ℝ, 0 < L → 0 < τ →
      ∃ ε : ℕ → ℝ, (∀ B, 0 ≤ ε B) ∧ Tendsto ε atTop (𝓝 0) ∧
        ∀ᶠ B : ℕ in atTop, ∀ (C N T : ℝ) (j : ℕ),
          0 ≤ C → 1 ≤ N → 0 < T → 1 ≤ N/T → j ≠ 0 →
          Real.exp ((1/2 : ℝ)*B) ≤ 3*N →
          Real.exp ((1/2 : ℝ)*B) ≤ 3*(N/T) →
          (17/4 : ℝ)*N ≤ Real.exp ((16/5 : ℝ)*B) →
          ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
          (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
          ∀ W : ℕ → ℕ → ℕ → ℝ,
          (∀ a ∈ Ico (tensorIntervalLower N) (tensorIntervalUpper N),
            ∀ b ∈ Ico (tensorIntervalLower N) (tensorIntervalUpper N),
            ∀ c ∈ Ico (tensorIntervalLower (N/T)) (tensorIntervalUpper (N/T)), |W a b c| ≤ 1) →
          signedLocalRegularityError B L j τ C
            (Ico (tensorIntervalLower N) (tensorIntervalUpper N))
            (Ico (tensorIntervalLower (N/T)) (tensorIntervalUpper (N/T))) g h W ≤
              K/((B : ℝ)*T)*singularFactor 24 j*(ε B+Real.exp (-(1/10 : ℝ)*C)) := by
  obtain ⟨K₀,hK₀,hpoint⟩ := signed_local_regularity_domination hM
  obtain ⟨K₁,hK₁,hbox⟩ := signed_coefficient_regularity_loss hFord hM
    (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (1/2 : ℝ) ≤ 32)
  refine ⟨400*K₀^2*K₁,by positivity,?_⟩
  intro L τ hL hτ
  obtain ⟨ε,hε0,hε,hbox⟩ := hbox L τ hL hτ
  refine ⟨ε,hε0,hε,?_⟩
  filter_upwards [hpoint,hbox,eventually_gt_atTop 0] with B hp hb hB
  intro C N T j hC hN hT hNT hj hlen hlen' hsize g h hg hh W hW
  have hN0 : 0 < N := by linarith
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hwidth := tensorInterval_width hN
  have hwidth' := tensorInterval_width hNT
  have hbound := hb C j (tensorIntervalLower N) (tensorIntervalUpper N)
    (tensorIntervalLower (N/T)) (tensorIntervalUpper (N/T)) hC
    (by exact_mod_cast hj) (tensorInterval_order hN0.le)
    (tensorInterval_order (div_pos hN0 hT).le) (hlen.trans hwidth.1) (hlen'.trans hwidth'.1)
  have hpoint := hp L j τ C (N/4) (by positivity) _ _
    (fun n hn => by
      have hn' := tensorInterval_point hN0.le hn
      exact ⟨hn'.1,hn'.2.trans hsize⟩) g h hg hh W hW
  have he0 : 0 ≤ ε B+Real.exp (-(1/10 : ℝ)*C) := add_nonneg (hε0 B) (Real.exp_pos _).le
  have hs0 : 0 ≤ singularFactor 24 j := zero_le_one.trans (singularFactor_one_le (by norm_num) j)
  calc
    _ ≤ K₀^2/((B : ℝ)*(N/4)^2)*
        (K₁*((tensorIntervalUpper N : ℝ)-tensorIntervalLower N)*
          ((tensorIntervalUpper (N/T) : ℝ)-tensorIntervalLower (N/T))*
          singularFactor 24 j*(ε B+Real.exp (-(1/10 : ℝ)*C))) :=
      hpoint.trans (mul_le_mul_of_nonneg_left hbound (by positivity))
    _ ≤ K₀^2/((B : ℝ)*(N/4)^2)*
        (K₁*(5*N)*(5*(N/T))*singularFactor 24 j*
          (ε B+Real.exp (-(1/10 : ℝ)*C))) := by
      gcongr
      · linarith [hwidth'.1]
      · exact hwidth.2
      · exact hwidth'.2
    _ = _ := by field_simp; ring

end JointDickman

end OAI
