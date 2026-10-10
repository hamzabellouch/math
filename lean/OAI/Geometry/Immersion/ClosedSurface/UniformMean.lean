import OAI.Geometry.Immersion.ClosedSurface.ModeScaling

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseMean ClosedSurfaceR4.RootMean
open ClosedSurfaceR4.WeightedEstimates ClosedSurfaceR4.FiniteMean Set


theorem finite_free_mean_adjustment_uniform {ι : Type*} (a : Finset ι)
    {U V S : ι → Set Base} {s r₀ r₁ ρ R : ℝ} {reference H : Base → PhaseMean.Tensor}
    {F : ι → RField 4} {ψ : ι → Base → ℝ} {Q : ι → Base → PhaseMean.Tensor →L[ℝ] ℝ}
    {χ e : ι → Base → Base}
    (h : ∀ i ∈ a, LocalBounds (U i) (V i) s r₁ ρ R reference (F i) (ψ i) (Q i) (χ i) (e i))
    (d : ∀ i ∈ a, Budgets (U i) (V i) s (F i) (ψ i) (Q i) (χ i) (e i))
    (hs : 0 < s) (hs1 : s ≤ 1) (hρ : 0 < ρ) (hgap : r₀ < r₁)
    (hS : ∀ i ∈ a, IsClosed (S i)) (hSU : ∀ i ∈ a, S i ⊆ U i)
    (hsp : ∀ i ∈ a, ∀ p ∈ U i, χ i p ∈ tsupport (ψ i) → p ∈ S i)
    (hdecomp : ∀ A : Base → PhaseMean.Tensor, InTrialBall univ reference r₁ A →
      ∀ p, (∑ i ∈ a, (U i).indicator
        (chartLeadingTensor (phaseAmplitude (ψ i) (coefficient (Q i) (e i) A)) (χ i)) p) = A p)
    (q n : ℕ) {C : ℕ → ℝ}
    (hC : ∀ m, 1 ≤ C m) (hH : ContDiff ℝ ∞ H)
    (hH0 : ∀ p, ‖H p - reference p‖ ≤ r₀)
    (hbH : ∀ m, WeightedBound univ s m (C m) H) :
    ∃ B K : ℕ → ℝ → ℝ, ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ ≤ 1 ∧
      ∀ η, 0 < η → η ≤ η₀ → ∀ j ≤ n, ∃ A : Base → PhaseMean.Tensor,
        ContDiff ℝ ∞ A ∧ InTrialBall univ reference r₁ A ∧
        (∀ δ : ℝ, ∀ i ∈ a, ContDiff ℝ ∞ (phaseFreeFamily U δ (η * s) F ψ Q χ e q A i) ∧
          tsupport (phaseFreeFamily U δ (η * s) F ψ Q χ e q A i) ⊆ S i) ∧
        (∀ m, WeightedBound univ s m (sizeBound (q + 2) C B j m) A) ∧
        (∀ δ : ℝ, ∀ m, WeightedBound univ s m
          (δ ^ 2 * (differenceBound (q + 2) C B K j m * η ^ (j + 1)))
          (fun p => (∑ i ∈ a, phaseZeroTensor (η * s) (fun p => (χ i p).1)
            (phaseFreeFamily U δ (η * s) F ψ Q χ e q A i) p) - δ ^ 2 • H p)) := by
  obtain ⟨B, K, η₀, hη₀, hη₁, ht⟩ := finite_free_mean_adjustment a h d hs hs1 hρ hgap
    hS hSU hsp hdecomp (δ := 1) (by norm_num) q n hC hH hH0 hbH
  refine ⟨B, K, η₀, hη₀, hη₁, ?_⟩
  intro η hη hηsmall j hj
  obtain ⟨A, hA, hball, hsm, hsize, hres⟩ := ht η hη hηsmall j hj
  refine ⟨A, hA, hball, ?_, hsize, ?_⟩
  · intro δ
    exact phaseFreeFamily_smooth a h hρ hA hball hS hSU hsp δ (η * s) q
  · intro δ m
    have hb := hres m
    simp only [one_pow, inv_one, one_smul] at hb
    have hmean : ContDiff ℝ ∞ (fun p => ∑ i ∈ a,
        phaseZeroTensor (η * s) (fun p => (χ i p).1)
          (phaseFreeFamily U 1 (η * s) F ψ Q χ e q A i) p) := by
      rw [finite_free_mean a h hρ hA hball hS hSU hsp (hdecomp A hball)
        (δ := 1) (by norm_num) (mul_ne_zero hη.ne' hs.ne') q]
      simp only [one_pow, one_smul]
      obtain ⟨B0, K0, hm⟩ := assembledMean_bounds a h d hs hs1 hρ hS hSU hsp (δ := 1) (by norm_num) q
      exact hA.add (contDiffOn_univ.mp
        (hm.smooth η hη (hηsmall.trans hη₁) A hA.contDiffOn hball))
    have hh := hb.const_smul isOpen_univ.uniqueDiffOn (hmean.sub hH).contDiffOn (δ ^ 2)
    rw [abs_of_nonneg (sq_nonneg δ)] at hh
    apply hh.congr
    intro p _
    dsimp only
    rw [congrFun (phaseFreeZero_scale a h hρ hA hball hS hSU hsp δ (η * s) q) p]
    exact (smul_sub _ _ _).symm

end ClosedSurfaceR4.RealModes

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseMean ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.FiniteMean Set
open ClosedSurfaceR4.RootMean



lemma weighted_coordDeriv_of_jets {U : Set Base} (hU : IsOpen U)
    {f : Base → Base} (hf : ContDiffOn ℝ ∞ f U) {τ D : ℝ} {m : ℕ}
    (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (hD : 0 ≤ D)
    (hb : ∀ j, 1 ≤ j → j ≤ m + 1 → ∀ p ∈ U,
      ‖iteratedFDerivWithin ℝ j f U p‖ ≤ D) (v : Base) (hv : ‖v‖ ≤ 1) :
    WeightedBound U τ m D (coordDeriv v f) := by
  have hd : WeightedBound U τ m D (fderivWithin ℝ f U) := by
    intro j hj p hp
    rw [norm_iteratedFDerivWithin_fderivWithin hU.uniqueDiffOn hp]
    exact (mul_le_mul_of_nonneg_left (hb (j+1) (by omega) (by omega) p hp)
      (pow_nonneg hτ j)).trans (mul_le_of_le_one_left hD (pow_le_one₀ hτ hτ1))
  have hh := hd.clm_apply_const hU.uniqueDiffOn hτ
    (hf.fderivWithin hU.uniqueDiffOn le_rfl) v
  apply (hh.mono_const (mul_le_of_le_one_left hD hv)).congr
  intro p hp
  simp only [coordDeriv, fderivWithin_of_isOpen hU hp]



def meanFreeBudget {F : RField 4} {φ ψ : Base → ℝ} {S : Set Base}
    (c : SupportedFreeChart F φ ψ S) {s r ρ R : ℝ} {reference A : Base → PhaseMean.Tensor}
    {Q : Base → PhaseMean.Tensor →L[ℝ] ℝ}
    (h : LocalBounds c.U c.V s r ρ R reference (F ∘ c.e) ψ Q c.χ c.e)
    (d : Budgets c.U c.V s (F ∘ c.e) ψ Q c.χ c.e)
    {τ C : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hρ : 0 < ρ) (hC : 0 ≤ C)
    (hA : ContDiffOn ℝ ∞ A c.U) (hball : InTrialBall c.U reference r A)
    (q m : ℕ) (hbA : WeightedBound c.V s (m + q + 1) C
      (phaseAmplitude ψ (coefficient Q c.e A))) :
    FreeBudget c (coefficient Q c.e A) τ s q m where
  K := d.mode (m + q + 1)
  C := C
  N := d.normal (m + q + 1)
  J := d.chi m
  D := d.chi (m + 1)
  nonnegK := zero_le_one.trans (d.mode_pos _)
  nonnegC := hC
  nonnegN := zero_le_one.trans (d.normal_pos _)
  oneLEJ := d.chi_pos _
  nonnegD := zero_le_one.trans (d.chi_pos _)
  smoothAmplitude := h.amplitude_smooth hρ hA hball
  coefficients := d.mode_bound _
  amplitude := hbA
  normal := d.normal_bound _
  coordinate := d.chi_bound _
  coordinateDerivative := weighted_coordDeriv_of_jets c.openU c.smoothχ hτ.le hτ1
    (zero_le_one.trans (d.chi_pos _)) (d.chi_bound _)



theorem LocalBounds.uniform_freeBudget {F : RField 4} {φ ψ : Base → ℝ} {S : Set Base}
    (c : SupportedFreeChart F φ ψ S) {s r ρ R : ℝ} {reference : Base → PhaseMean.Tensor}
    {Q : Base → PhaseMean.Tensor →L[ℝ] ℝ}
    (h : LocalBounds c.U c.V s r ρ R reference (F ∘ c.e) ψ Q c.χ c.e)
    (d : Budgets c.U c.V s (F ∘ c.e) ψ Q c.χ c.e)
    (hs : 0 < s) (hs1 : s ≤ 1) (hρ : 0 < ρ) (q m : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    ∃ A0 : ℝ, 1 ≤ A0 ∧ ∀ τ : ℝ, 0 < τ → τ ≤ s → ∀ A : Base → PhaseMean.Tensor,
      ContDiffOn ℝ ∞ A c.U → InTrialBall c.U reference r A →
      WeightedBound c.U s (m + q + 1) C A →
      ∃ b : FreeBudget c (coefficient Q c.e A) τ s q m,
        b.K = d.mode (m + q + 1) ∧ b.C = A0 ∧ b.N = d.normal (m + q + 1) ∧
        b.J = d.chi m ∧ b.D = d.chi (m + 1) := by
  obtain ⟨A0, hA0, hh⟩ := h.amplitude_bounds d hs hs1 hρ (m + q + 1) C
  refine ⟨A0, hA0, ?_⟩
  intro τ hτ hτs A hA hball hbA
  have hz : WeightedBound c.U s (m + q + 1) 0 (A - A) := by
    apply (weightedBound_zero c.U s (m + q + 1)).congr
    intro p hp
    simp
  have hb := (hh A A 0 hC le_rfl hA hA hball hball hbA hbA hz).1
  exact ⟨meanFreeBudget c h d hτ (hτs.trans hs1) hρ (zero_le_one.trans hA0)
    hA hball q m hb, rfl, rfl, rfl, rfl, rfl⟩

end ClosedSurfaceR4.RealModes

end

end OAI
