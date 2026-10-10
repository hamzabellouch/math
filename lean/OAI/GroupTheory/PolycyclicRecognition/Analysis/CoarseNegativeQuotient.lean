import OAI.GroupTheory.PolycyclicRecognition.Analysis.FactorQuotientChainDecay
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CocycleGrowth
import Mathlib.Topology.MetricSpace.IsometricSMul

namespace OAI

/-! # Quotient asymptotics of actual negative-height chains

Sublinear height error preserves a linear negative margin on a linear ball.
Polynomial metric factor bounds and compact unit increments then give
asymptotic equality of the projected endpoints.
-/

noncomputable section
namespace PolycyclicRecognition

open Module LieModule Filter Set
open scoped Manifold Topology

/-- A continuous linear functional preserves a global sublinear error.
The constant is chosen before the scale, including for the zero functional. -/
theorem scalar_sublinear_error
    {X W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (length : X → ℝ) (hlen : ∀ x, 0 ≤ length x)
    (u v : X → W) (α : W →L[ℝ] ℝ)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ x,
      ‖u x - v x‖ ≤ ε * length x + B) :
    ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ x,
      |α (u x) - α (v x)| ≤ ε * length x + B := by
  intro ε hε
  have hd : 0 < ‖α‖ + 1 := by positivity
  obtain ⟨B, hB, hb⟩ := hsub (ε / (‖α‖ + 1)) (div_pos hε hd)
  refine ⟨‖α‖ * B, by positivity, ?_⟩
  intro x
  have hcoef : ‖α‖ * (ε / (‖α‖ + 1)) ≤ ε := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hd).mpr
    nlinarith
  calc
    _ = ‖α (u x - v x)‖ := by rw [map_sub, Real.norm_eq_abs]
    _ ≤ ‖α‖ * ‖u x - v x‖ := α.le_opNorm _
    _ ≤ ‖α‖ * ((ε / (‖α‖ + 1)) * length x + B) :=
      mul_le_mul_of_nonneg_left (hb x) (norm_nonneg _)
    _ = (‖α‖ * (ε / (‖α‖ + 1))) * length x + ‖α‖ * B := by ring
    _ ≤ ε * length x + ‖α‖ * B :=
      add_le_add (mul_le_mul_of_nonneg_right hcoef (hlen x)) le_rfl

variable {S N D G E Q J : Type*} [MetricSpace S] [One S]
  [Group N] [Group D] [Group G] [MetricSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace Q] [ChartedSpace E Q] [Group Q]
  [LieGroup (𝓘(ℝ, E)) ⊤ Q] [T2Space Q] [Fintype J]

/-- A coarse map preserves enough negative height for every polynomial
chain in a linear ball. The factors are selected from the actual metric
factorization theorem, and the quotient increments are those of the map. -/
theorem coarse_negative_chain_quotient_difference_tendsto_one
    (ι : N →* G) (κ : D →* G) (π : N →* Q)
    (α : D →* MulAut Q) (act : G →* Equiv.Perm Q)
    (hact : ∀ u d q, act (ι u * κ d) q = π u * α d q)
    (dynkin : NilpotentDynkinExpansionInput E Q)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) Q → Q) (hExp : IsGroupExponential Exp)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) Q ≃ₜ Q) (hchart : ∀ v, chart v = Exp v)
    {c : ℕ} (hc : lowerCentralSeries ℝ (GroupLieAlgebra (𝓘(ℝ, E)) Q)
      (GroupLieAlgebra (𝓘(ℝ, E)) Q) c = ⊥)
    (b : Basis J ℝ (GroupLieAlgebra (𝓘(ℝ, E)) Q))
    (size height : D → ℝ) (sourceHeight : S → ℝ) (targetHeight : G → ℝ)
    (f : S → G) {L error : ℝ} (hL : 0 ≤ L)
    (hf : ∀ x y, dist (f x) (f y) ≤ L * dist x y + error)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ x,
      |targetHeight (f x) - sourceHeight x| ≤ ε * dist 1 x + B)
    {B : ℝ} (hB : 0 ≤ B) (degree : ℕ)
    (hfactor : ∀ g : G, ∃ u d, ι u * κ d = g ∧
      0 ≤ size d ∧ size d ≤ B * (3 + dist 1 g) ^ degree ∧ height d = targetHeight g)
    (K : Set Q)
    (hK : ∀ g : G, dist 1 g ≤ L + error → act g 1 ∈ K)
    {A rate : ℝ} (hA : 0 ≤ A) (hrate : 0 < rate) (p : ℕ)
    (hcontract : ∀ d, height d ≤ 0 → ∀ q ∈ K,
      ‖b.equivFun (chart.symm (α d q))‖ ≤
        A * (1 + size d) ^ p * Real.exp (rate * height d))
    (m : ℕ → ℕ) (z : ℕ → ℕ → S)
    {R gap count : ℝ} (hR : 0 ≤ R) (hgap : 0 < gap) (countDegree : ℕ)
    (hcount : ∀ᶠ n in atTop, (m n : ℝ) ≤ count * (1 + (n : ℝ)) ^ countDegree)
    (hball : ∀ᶠ n in atTop, ∀ i ≤ m n, dist 1 (z n i) ≤ R * n)
    (hnegative : ∀ᶠ n in atTop, ∀ i ≤ m n, sourceHeight (z n i) ≤ -gap * n)
    (hstep : ∀ᶠ n in atTop, ∀ i < m n, dist (z n i) (z n (i + 1)) ≤ 1) :
    Tendsto (fun n => (act (f (z n 0)) 1)⁻¹ * act (f (z n (m n))) 1)
      atTop (𝓝 (1 : Q)) := by
  classical
  choose u d hd using hfactor
  obtain ⟨r₀, _, hsmall⟩ := uniform_sublinear_on_balls (fun x : S => dist 1 x)
    (b := fun x => targetHeight (f x) - sourceHeight x) hsub hR
    (gap / 2) (half_pos hgap)
  have hlarge : ∀ᶠ n : ℕ in atTop, r₀ ≤ (n : ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually
      (eventually_ge_atTop r₀)
  let T := 3 + dist 1 (f 1) + L * R + |error|
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hfactorSize (n : ℕ) (i : ℕ) (hi : dist 1 (z n i) ≤ R * n) :
      size (d (f (z n i))) ≤ (B * T ^ degree) * (1 + (n : ℝ)) ^ degree := by
    have hdist : dist 1 (f (z n i)) ≤ dist 1 (f 1) + L * (R * n) + error := by
      have hh := hf 1 (z n i)
      have hh' := mul_le_mul_of_nonneg_left hi hL
      linarith [dist_triangle (1 : G) (f 1) (f (z n i))]
    have ht : 3 + dist 1 (f (z n i)) ≤ T * (1 + (n : ℝ)) := by
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hLR : 0 ≤ L * R := mul_nonneg hL hR
      have hdn : 0 ≤ dist (1 : G) (f 1) := dist_nonneg
      have he : error ≤ |error| := le_abs_self _
      dsimp [T]
      nlinarith [abs_nonneg error]
    calc
      _ ≤ B * (3 + dist 1 (f (z n i))) ^ degree := (hd _).2.2.1
      _ ≤ B * (T * (1 + (n : ℝ))) ^ degree := by gcongr
      _ = _ := by rw [mul_pow]; ring
  apply factor_quotient_chain_difference_tendsto_one ι κ π α act hact
    dynkin Exp hExp chart hchart hc b size height K hA hrate p hcontract m
    (fun n i => f (z n i)) (fun n i => u (f (z n i))) (fun n i => d (f (z n i)))
    (B := B * T ^ degree) (by positivity) (half_pos hgap) degree countDegree hcount
  · filter_upwards [hball, hnegative, hlarge] with n hn hneg hlarge
    intro i hi
    have hi' : i ≤ m n := hi.le
    refine ⟨(hd _).1, (hd _).2.1, hfactorSize n i (hn i hi'), ?_⟩
    rw [(hd _).2.2.2]
    have herr := hsmall n hlarge (z n i) (hn i hi')
    have hh := hneg i hi'
    have hupper := le_abs_self (targetHeight (f (z n i)) - sourceHeight (z n i))
    rw [Real.norm_eq_abs] at herr
    nlinarith
  · filter_upwards [hstep] with n hn
    intro i hi
    apply hK
    have he : dist (1 : G) ((f (z n i))⁻¹ * f (z n (i + 1))) =
        dist (f (z n i)) (f (z n (i + 1))) := by
      simpa only [mul_one, mul_inv_cancel_left] using
        (dist_mul_left (f (z n i)) (1 : G) ((f (z n i))⁻¹ * f (z n (i + 1)))).symm
    rw [he]
    exact (hf _ _).trans (by nlinarith [hn i hi])

/-- Compact-set contraction in the quotient, independent of a choice of basis. -/
theorem coarse_negative_chain_quotient_difference_of_compact_contraction
    (ι : N →* G) (κ : D →* G) (π : N →* Q)
    (α : D →* MulAut Q) (act : G →* Equiv.Perm Q)
    (hact : ∀ u d q, act (ι u * κ d) q = π u * α d q)
    (dynkin : NilpotentDynkinExpansionInput E Q)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) Q → Q) (hExp : IsGroupExponential Exp)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) Q ≃ₜ Q) (hchart : ∀ v, chart v = Exp v)
    (hnil : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, E)) Q))
    (size height : D → ℝ) (sourceHeight : S → ℝ) (targetHeight : G → ℝ)
    (f : S → G) {L error : ℝ} (hL : 0 ≤ L)
    (hf : ∀ x y, dist (f x) (f y) ≤ L * dist x y + error)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ x,
      |targetHeight (f x) - sourceHeight x| ≤ ε * dist 1 x + B)
    {B : ℝ} (hB : 0 ≤ B) (degree : ℕ)
    (hfactor : ∀ g : G, ∃ u d, ι u * κ d = g ∧
      0 ≤ size d ∧ size d ≤ B * (3 + dist 1 g) ^ degree ∧ height d = targetHeight g)
    (K : Set Q)
    (hK : ∀ g : G, dist 1 g ≤ L + error → act g 1 ∈ K)
    (hcompact : IsCompact K)
    (hcontract : ∃ (b : Basis J ℝ (GroupLieAlgebra (𝓘(ℝ, E)) Q))
      (p : ℕ) (rate : ℝ), 0 < rate ∧
      ∀ K : Set Q, IsCompact K → ∃ A : ℝ, 0 ≤ A ∧
        ∀ d, height d ≤ 0 → ∀ q ∈ K,
          ‖b.equivFun (chart.symm (α d q))‖ ≤
            A * (1 + size d) ^ p * Real.exp (rate * height d))
    (m : ℕ → ℕ) (z : ℕ → ℕ → S)
    {R gap count : ℝ} (hR : 0 ≤ R) (hgap : 0 < gap) (countDegree : ℕ)
    (hcount : ∀ᶠ n in atTop, (m n : ℝ) ≤ count * (1 + (n : ℝ)) ^ countDegree)
    (hball : ∀ᶠ n in atTop, ∀ i ≤ m n, dist 1 (z n i) ≤ R * n)
    (hnegative : ∀ᶠ n in atTop, ∀ i ≤ m n, sourceHeight (z n i) ≤ -gap * n)
    (hstep : ∀ᶠ n in atTop, ∀ i < m n, dist (z n i) (z n (i + 1)) ≤ 1) :
    Tendsto (fun n => (act (f (z n 0)) 1)⁻¹ * act (f (z n (m n))) 1)
      atTop (𝓝 (1 : Q)) := by
  obtain ⟨b, p, rate, hrate, hb⟩ := hcontract
  obtain ⟨A, hA, hbound⟩ := hb K hcompact
  obtain ⟨c, hc⟩ := (LieModule.isNilpotent_iff ℝ
    (GroupLieAlgebra (𝓘(ℝ, E)) Q) (GroupLieAlgebra (𝓘(ℝ, E)) Q)).mp hnil
  exact coarse_negative_chain_quotient_difference_tendsto_one ι κ π α act hact
    dynkin Exp hExp chart hchart hc b size height sourceHeight targetHeight f hL hf hsub
    hB degree hfactor K hK hA hrate p hbound m z hR hgap countDegree
    hcount hball hnegative hstep

end PolycyclicRecognition

end

end OAI
