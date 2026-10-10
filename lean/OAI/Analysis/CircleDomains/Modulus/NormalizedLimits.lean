import OAI.Analysis.CircleDomains.Modulus.NormalFamilyInputs
import OAI.Analysis.CircleDomains.Topology.MarkedDiskLimits

namespace OAI

/-!
# Normalized limits on exhausting retained cores

The uniform finite-model bounds give local boundedness. The common
decaying exterior remainder passes to the limit and prevents a constant
limit on any retained core containing the exterior. Hurwitz then gives
global injectivity. A further subsequence retains all these conclusions
and converges for every marked complementary disk simultaneously.
-/

open Set Filter Function Asymptotics Bornology Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem exterior_decay_le_radius {R t : ℝ} (hR : 0 < R) (ht : 2 * R ≤ t) :
    2 * R ^ 2 / t ≤ R := by
  apply (div_le_iff₀ (by linarith : 0 < t)).mpr
  nlinarith

theorem not_constant_of_exterior_decay
    {D : Set ℂ} {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hD : {z : ℂ | 2 * R ≤ ‖z‖} ⊆ D)
    (hbound : ∀ z : ℂ, 2 * R ≤ ‖z‖ → ‖f z - z‖ ≤ 2 * R ^ 2 / ‖z‖) :
    ¬ ∃ c : ℂ, ∀ z ∈ D, f z = c := by
  rintro ⟨c, hc⟩
  let t : ℝ := 2 * R + ‖c‖ + 1
  have ht : 0 < t := by dsimp only [t]; positivity
  have htn : ‖(t : ℂ)‖ = t := by simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  have hlarge : 2 * R ≤ ‖(t : ℂ)‖ := by
    rw [htn]
    dsimp only [t]
    linarith [norm_nonneg c]
  have hb := (hbound (t : ℂ) hlarge).trans (exterior_decay_le_radius hR hlarge)
  rw [hc _ (hD hlarge)] at hb
  have hnorm := norm_le_norm_sub_add (t : ℂ) c
  rw [norm_sub_rev, htn] at hnorm
  dsimp only [t] at hnorm
  linarith

theorem principal_remainder_of_exterior_decay
    {f : ℂ → ℂ} {R : ℝ}
    (hbound : ∀ z : ℂ, 2 * R ≤ ‖z‖ → ‖f z - z‖ ≤ 2 * R ^ 2 / ‖z‖) :
    (fun z => f z - z) =O[cobounded ℂ] (fun z => z⁻¹) := by
  apply isBigO_iff.mpr
  refine ⟨2 * R ^ 2, ?_⟩
  filter_upwards [eventually_cobounded_le_norm (E := ℂ) (2 * R)] with z hz
  simpa only [norm_inv, div_eq_mul_inv] using hbound z hz

theorem exists_normalized_univalent_limit
    (hmontel : MontelExhaustion) (hhurwitz : HurwitzUnivalentLimit)
    {D : ℕ → Set ℂ} {F : ℕ → ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hD : ∀ n, IsOpen (D n)) (hconn : ∀ n, IsConnected (D n))
    (hmono : Monotone D) (hF : ∀ n, DifferentiableOn ℂ (F n) (D n))
    (hFi : ∀ n, InjOn (F n) (D n))
    (hext : {z : ℂ | 2 * R ≤ ‖z‖} ⊆ D 0)
    (hbounded : ∀ n z, z ∈ D n → ‖z‖ ≤ 4 * R → ‖F n z‖ ≤ 5 * R)
    (hdecay : ∀ n z, 2 * R ≤ ‖z‖ → ‖F n z - z‖ ≤ 2 * R ^ 2 / ‖z‖) :
    ∃ (s : ℕ → ℕ) (f : ℂ → ℂ), StrictMono s ∧
      TendstoLocallyUniformlyOn (fun n => F (s n)) f atTop (⋃ n, D n) ∧
      DifferentiableOn ℂ f (⋃ n, D n) ∧ InjOn f (⋃ n, D n) ∧
      (fun z => f z - z) =O[cobounded ℂ] (fun z => z⁻¹) ∧
      ∀ z : ℂ, 2 * R ≤ ‖z‖ → ‖f z - z‖ ≤ 2 * R ^ 2 / ‖z‖ := by
  have hlocal : ∀ K : Set ℂ, IsCompact K → K ⊆ ⋃ n, D n →
      ∃ M : ℝ, ∀ n z, z ∈ K → z ∈ D n → ‖F n z‖ ≤ M := by
    intro K hK _
    obtain ⟨A, hA⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
    refine ⟨A + 5 * R, ?_⟩
    intro n z hzK hzD
    have hzA : ‖z‖ ≤ A := by simpa only [mem_closedBall, dist_zero_right] using hA hzK
    by_cases hz : ‖z‖ ≤ 4 * R
    · linarith [hbounded n z hzD hz, norm_nonneg z]
    · have hlarge : 2 * R ≤ ‖z‖ := by linarith
      have hb := (hdecay n z hlarge).trans (exterior_decay_le_radius hR hlarge)
      have hn := norm_le_norm_sub_add (F n z) z
      linarith
  obtain ⟨s, f, hs, hlim⟩ := hmontel D F hD hmono hF hlocal
  have hlimdecay : ∀ z : ℂ, 2 * R ≤ ‖z‖ → ‖f z - z‖ ≤ 2 * R ^ 2 / ‖z‖ := by
    intro z hz
    have hzU : z ∈ ⋃ n, D n := mem_iUnion.mpr ⟨0, hext hz⟩
    exact le_of_tendsto ((hlim.tendsto_at hzU).sub tendsto_const_nhds).norm
      (Eventually.of_forall (fun n => hdecay (s n) z hz))
  have hnonconst (n : ℕ) : ¬ ∃ c : ℂ, ∀ z ∈ D n, f z = c :=
    not_constant_of_exterior_decay hR (hext.trans (hmono (Nat.zero_le n))) hlimdecay
  exact ⟨s, f, hs, hlim, holomorphic_limit_on_exhaustion hD hmono hF hs hlim,
    univalent_limit_on_exhaustion hhurwitz hD hconn hmono hF hFi hs hlim hnonconst,
    principal_remainder_of_exterior_decay hlimdecay, hlimdecay⟩

theorem locally_uniform_subsequence
    {D : Set ℂ} {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {s : ℕ → ℕ}
    (hlim : TendstoLocallyUniformlyOn F f atTop D) (hs : StrictMono s) :
    TendstoLocallyUniformlyOn (fun n => F (s n)) f atTop D := by
  intro u hu z hz
  obtain ⟨O, hO, h⟩ := hlim u hu z hz
  exact ⟨O, hO, hs.tendsto_atTop.eventually h⟩

theorem exists_normalized_marked_limit
    (hmontel : MontelExhaustion) (hhurwitz : HurwitzUnivalentLimit)
    {D : ℕ → Set ℂ} {F : ℕ → ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hD : ∀ n, IsOpen (D n)) (hconn : ∀ n, IsConnected (D n))
    (hmono : Monotone D) (hF : ∀ n, DifferentiableOn ℂ (F n) (D n))
    (hFi : ∀ n, InjOn (F n) (D n))
    (hext : {z : ℂ | 2 * R ≤ ‖z‖} ⊆ D 0)
    (hbounded : ∀ n z, z ∈ D n → ‖z‖ ≤ 4 * R → ‖F n z‖ ≤ 5 * R)
    (hdecay : ∀ n z, 2 * R ≤ ‖z‖ → ‖F n z - z‖ ≤ 2 * R ^ 2 / ‖z‖)
    {B : Type*} [Countable B] (c : ℕ → B → ℂ) (r : ℕ → B → ℝ) {L : ℝ}
    (hc : ∀ n b, ‖c n b‖ ≤ L) (hr : ∀ n b, r n b ∈ Icc 0 L) :
    ∃ (s : ℕ → ℕ) (f : ℂ → ℂ) (c₀ : B → ℂ) (r₀ : B → ℝ),
      StrictMono s ∧
      TendstoLocallyUniformlyOn (fun n => F (s n)) f atTop (⋃ n, D n) ∧
      DifferentiableOn ℂ f (⋃ n, D n) ∧ InjOn f (⋃ n, D n) ∧
      (fun z => f z - z) =O[cobounded ℂ] (fun z => z⁻¹) ∧
      (∀ b, ‖c₀ b‖ ≤ L ∧ r₀ b ∈ Icc 0 L) ∧
      ∀ b, Tendsto (fun n => hausdorffDist (closedBall (c (s n) b) (r (s n) b))
        (closedBall (c₀ b) (r₀ b))) atTop (𝓝 0) := by
  obtain ⟨s, f, hs, hlim, hf, hfi, hnorm, _⟩ := exists_normalized_univalent_limit
    hmontel hhurwitz hR hD hconn hmono hF hFi hext hbounded hdecay
  obtain ⟨t, c₀, r₀, ht, hb, hdisks⟩ :=
    exists_marked_disk_hausdorff_limits (fun n => c (s n)) (fun n => r (s n))
      (fun n b => hc (s n) b) (fun n b => hr (s n) b)
  exact ⟨s ∘ t, f, c₀, r₀, hs.comp ht,
    locally_uniform_subsequence (F := fun n => F (s n)) (s := t) hlim ht,
    hf, hfi, hnorm, hb, hdisks⟩

end CircleDomainRigidity

end

end OAI
