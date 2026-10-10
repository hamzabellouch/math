import Mathlib
import OAI.Computability.MaxCut.Analysis.CubePerm

namespace OAI

noncomputable section
namespace OptimalMaxCut.LongCode
open scoped BigOperators
open Finset MaxCutGames.Foundations.Hastad OptimalMaxCut.Analytic
open OptimalMaxCut.GaussianBellman OptimalMaxCut.MISProof

 theorem stability_nonneg {n : ℕ} (t : ℝ) (ht : 0 ≤ t) (f : Cube (Fin n) → ℝ) :
    0 ≤ stability t f := by
  exact sum_nonneg (fun s _ => mul_nonneg (pow_nonneg ht _) (sq_nonneg _))

 theorem stability_le_one {n : ℕ} (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (f : Cube (Fin n) → ℝ) (hf : ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1) :
    stability t f ≤ 1 := by
  apply le_trans _ (spectral_energy_le_one f hf)
  apply sum_le_sum
  intro s _
  exact mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ ht.1 ht.2)

 theorem corrAverage_sub (t : ℝ) (n : ℕ) (F G : BitCube n → BitCube n → ℝ) :
    corrAverage t n (fun x y => F x y - G x y) = corrAverage t n F - corrAverage t n G := by
  have he (x y : BitCube n) : F x y - G x y = F x y + G x y * (-1) := by ring
  simp_rw [he, corrAverage_add, corrAverage_mul_const]
  ring

 theorem corrAverage_swap (t : ℝ) (n : ℕ) (F : BitCube n → BitCube n → ℝ) :
    corrAverage t n (fun x y => F y x) = corrAverage t n F := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [corrAverage]
    rw [ih]
    congr 1
    funext x y
    rw [sum_comm]
    apply sum_congr rfl
    intro a _
    apply sum_congr rfl
    intro b _
    congr 1
    simp only [bitPairWeight]
    ring

 theorem correlation_antipode (t : ℝ) {n : ℕ} (f : Cube (Fin n) → ℝ) :
    corrAverage t n (fun x y => f x * f (antipode y)) =
      stability t (evenPart f) - stability t (oddPart f) := by
  have hp (x y : Cube (Fin n)) : f x * f (antipode y) =
      (evenPart f x * evenPart f y - oddPart f x * oddPart f y) +
        (oddPart f x * evenPart f y - evenPart f x * oddPart f y) := by
    unfold evenPart oddPart
    ring
  have hs : corrAverage t n (fun x y => oddPart f x * evenPart f y) =
      corrAverage t n (fun x y => evenPart f x * oddPart f y) := by
    simpa only [mul_comm] using corrAverage_swap t n (fun x y => evenPart f x * oddPart f y)
  simp_rw [hp]
  rw [corrAverage_add, corrAverage_sub, corrAverage_sub, hs,
    corrAverage_stability, corrAverage_stability]
  ring

namespace Game
variable {X Y E : Type*} [Fintype X] [Fintype Y] [Fintype E] {q : ℕ}

 theorem oddPart_averageCode (G : Game X Y E q) (f : X → Cube (Fin q) → ℝ) (y : Y) :
    oddPart (G.averageCode f y) = G.averageCode (fun x => oddPart (f x)) y := by
  funext z
  simp only [oddPart, averageCode, reindex, Law.avg_div, Law.avg_sub]
  rfl

/-- Value of the usual correlated long-code Max-Cut test, before aggregating
its finite rational outcomes into graph weights. -/
noncomputable def testCut (G : Game X Y E q) (t : ℝ) (f : X → Cube (Fin q) → ℝ) : ℝ :=
  G.rightLaw.avg (fun y => (1 - corrAverage t q (fun z z' =>
    G.averageCode f y z * G.averageCode f y (antipode z'))) / 2)

 theorem testCut_stability (G : Game X Y E q) (t : ℝ) (f : X → Cube (Fin q) → ℝ) :
    G.testCut t f = 1 / 2 +
      G.rightLaw.avg (fun y => stability t (G.averageCode (fun x => oddPart (f x)) y)) / 2 -
      G.rightLaw.avg (fun y => stability t (evenPart (G.averageCode f y))) / 2 := by
  unfold testCut
  simp_rw [correlation_antipode, oddPart_averageCode]
  simp only [Law.avg_div, Law.avg_sub, Law.avg_const]
  ring

 theorem testCut_le_stability (G : Game X Y E q) (t : ℝ) (ht : 0 ≤ t)
    (f : X → Cube (Fin q) → ℝ) :
    G.testCut t f ≤ (1 +
      G.rightLaw.avg (fun y => stability t (G.averageCode (fun x => oddPart (f x)) y))) / 2 := by
  rw [testCut_stability]
  have h : 0 ≤ G.rightLaw.avg (fun y => stability t (evenPart (G.averageCode f y))) :=
    G.rightLaw.avg_nonneg (fun _ => stability_nonneg t ht _)
  linarith

/-- Dimension-uniform soundness, with an actual Fourier-influence decoding
proof. Every input game soundness bound feeds the finite long-code cut test. -/
 theorem stability_soundness (G : Game X Y E q) (hq : 0 < q)
    {t ξ τ : ℝ} {K : ℕ} (ht : 0 < t) (ht1 : t < 1) (hξ : 0 < ξ) (hτ : 0 < τ)
    (hMIS : ∀ (n : ℕ) (h : Cube (Fin n) → ℝ),
      (∀ x, -1 ≤ h x ∧ h x ≤ 1) → (𝔼 x, h x) = 0 →
      (∀ i, cutoffInfluence K i h < τ) → stability t h ≤ 2 / Real.pi * Real.arcsin t + ξ)
    (f : X → Cube (Fin q) → ℝ) (hf : ∀ x z, f x z ∈ Set.Icc (-1 : ℝ) 1)
    (hm : ∀ x, (𝔼 z, f x z) = 0) (δ : ℝ) (hsound : G.Sound δ) :
    G.rightLaw.avg (fun y => stability t (G.averageCode f y)) ≤
      2 / Real.pi * Real.arcsin t + ξ + (K : ℝ) * δ / τ := by
  classical
  let : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  have hp (y : Y) : ∃ i : Fin q, ∀ j,
      cutoffInfluence K j (G.averageCode f y) ≤ cutoffInfluence K i (G.averageCode f y) := by
    obtain ⟨i, _, hi⟩ := exists_max_image univ (fun i => cutoffInfluence K i (G.averageCode f y)) univ_nonempty
    exact ⟨i, fun j => hi j (mem_univ _)⟩
  choose ly hly using hp
  have hB : 0 ≤ 2 / Real.pi * Real.arcsin t + ξ := by
    have h := Real.arcsin_nonneg.mpr ht.le
    positivity
  have hy (y : Y) : stability t (G.averageCode f y) ≤ 2 / Real.pi * Real.arcsin t + ξ +
      cutoffInfluence K (ly y) (G.averageCode f y) / τ := by
    by_cases h : ∀ i, cutoffInfluence K i (G.averageCode f y) < τ
    · have hmis := hMIS q (G.averageCode f y) (G.averageCode_bounded f hf y)
        (G.averageCode_mean f hm y) h
      have hnon : 0 ≤ cutoffInfluence K (ly y) (G.averageCode f y) / τ :=
        div_nonneg (cutoffInfluence_nonneg _ _ _) hτ.le
      linarith
    · push Not at h
      obtain ⟨i, hi⟩ := h
      have hmτ := hi.trans (hly y i)
      have hratio : 1 ≤ cutoffInfluence K (ly y) (G.averageCode f y) / τ :=
        (le_div_iff₀ hτ).mpr (by simpa using hmτ)
      have hstab := stability_le_one t ⟨ht.le, ht1.le⟩ (G.averageCode f y) (G.averageCode_bounded f hf y)
      linarith
  calc
    _ ≤ G.rightLaw.avg (fun y => 2 / Real.pi * Real.arcsin t + ξ +
        cutoffInfluence K (ly y) (G.averageCode f y) / τ) := G.rightLaw.avg_mono hy
    _ = 2 / Real.pi * Real.arcsin t + ξ +
        G.rightLaw.avg (fun y => cutoffInfluence K (ly y) (G.averageCode f y)) / τ := by
      rw [Law.avg_add, Law.avg_const, Law.avg_div]
    _ ≤ 2 / Real.pi * Real.arcsin t + ξ +
        G.rightLaw.avg (fun y => (G.edgeLaw y).avg (fun e =>
          cutoffInfluence K ((G.permutation e).symm (ly y)) (f (G.source e)))) / τ := by
      gcongr
      exact G.rightLaw.avg_mono (fun y => G.averageCode_influence f K y (ly y))
    _ ≤ _ := by
      gcongr
      exact G.decoding_bound hq K f hf δ hsound ly

/-- The MIS threshold and low-degree cutoff are actually proved, not supplied
as assumptions. This theorem is the soundness component of the main reduction. -/
 theorem exists_test_soundness (t ξ : ℝ) (ht : 0 < t) (ht1 : t < 1) (hξ : 0 < ξ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ {X Y E : Type} [Fintype X] [Fintype Y] [Fintype E]
      (q : ℕ) (_hq : 0 < q) (G : Game X Y E q), G.Sound δ →
      ∀ f : X → Cube (Fin q) → ℝ, (∀ x z, f x z ∈ Set.Icc (-1 : ℝ) 1) →
        G.testCut t f ≤ (1 + 2 / Real.pi * Real.arcsin t) / 2 + ξ := by
  obtain ⟨K, hK, τ, hτ, hMIS⟩ := majority_is_stablest t ht ht1 ξ hξ
  have hKr : 0 < (K : ℝ) := by exact_mod_cast hK
  refine ⟨ξ * τ / K, by positivity, ?_⟩
  intro X Y E _ _ _ q hq G hs f hf
  have ho (x : X) (z : Cube (Fin q)) := oddPart_bounded (f x) (hf x) z
  have hb := G.stability_soundness hq ht ht1 hξ hτ hMIS (fun x => oddPart (f x)) ho
    (fun x => oddPart_mean (f x)) (ξ * τ / K) hs
  have he : (K : ℝ) * (ξ * τ / K) / τ = ξ := by field_simp
  rw [he] at hb
  have hc := G.testCut_le_stability t ht.le f
  linarith

end Game
end OptimalMaxCut.LongCode

end

end OAI
