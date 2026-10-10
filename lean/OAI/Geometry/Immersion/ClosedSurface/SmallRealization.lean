import OAI.Geometry.Immersion.ClosedSurface.UniformMean
import OAI.Geometry.Immersion.ClosedSurface.UniformIncrement

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseMean ClosedSurfaceR4.RootMean
open ClosedSurfaceR4.WeightedEstimates ClosedSurfaceR4.FiniteMean Set
open ClosedSurfaceR4.QuadraticMean (sumDisplacement)



theorem trial_family_free_budgets {ι α : Type*} {F : RField 4}
    {φ ψ : ι → Base → ℝ} {S : ι → Set Base}
    (c : ∀ i, SupportedFreeChart F (φ i) (ψ i) (S i))
    {s r ρ R : ℝ} {reference : Base → PhaseMean.Tensor}
    {Q : ι → Base → PhaseMean.Tensor →L[ℝ] ℝ}
    (h : ∀ i, LocalBounds (c i).U (c i).V s r ρ R reference
      (F ∘ (c i).e) (ψ i) (Q i) (c i).χ (c i).e)
    (d : ∀ i, Budgets (c i).U (c i).V s (F ∘ (c i).e) (ψ i) (Q i) (c i).χ (c i).e)
    (hs : 0 < s) (hs1 : s ≤ 1) (hρ : 0 < ρ) (q m : ℕ)
    (A : α → Base → PhaseMean.Tensor) (hA : ∀ a, ContDiff ℝ ∞ (A a))
    (hball : ∀ a, InTrialBall univ reference r (A a)) {C : ℝ} (hC : 0 ≤ C)
    (hbA : ∀ a, WeightedBound univ s (m + q + 1) C (A a)) (a₀ : α) :
    ∃ b : ∀ a i, FreeBudget (c i) (coefficient (Q i) (c i).e (A a)) s s q m,
      ∀ a i, (b a i).K = (b a₀ i).K ∧ (b a i).C = (b a₀ i).C ∧
        (b a i).N = (b a₀ i).N ∧ (b a i).J = (b a₀ i).J ∧ (b a i).D = (b a₀ i).D := by
  classical
  choose D hD get using fun i =>
    ClosedSurfaceR4.RealModes.LocalBounds.uniform_freeBudget (c i) (h i) (d i) hs hs1 hρ q m hC
  have hb (a : α) (i : ι) := get i s hs le_rfl (A a) (hA a).contDiffOn
    (fun p _ => hball a p (mem_univ p)) ((hbA a).restrict_open (c i).openU)
  choose b hK hC' hN hJ hD' using hb
  refine ⟨b, ?_⟩
  intro a i
  exact ⟨(hK a i).trans (hK a₀ i).symm, (hC' a i).trans (hC' a₀ i).symm,
    (hN a i).trans (hN a₀ i).symm, (hJ a i).trans (hJ a₀ i).symm,
    (hD' a i).trans (hD' a₀ i).symm⟩





theorem finite_small_realization {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : RField 4} (hF : ContDiff ℝ ∞ F) {φ ψ : ι → Base → ℝ}
    {S : ι → Set Base} (c : ∀ i, SupportedFreeChart F (φ i) (ψ i) (S i))
    (v : ∀ l : QuadraticLabel ι, SupportedSolveChart F (quadraticPhase φ l) (quadraticSupport S l))
    {s r₀ r₁ ρ R : ℝ} {reference H : Base → PhaseMean.Tensor}
    {Q : ι → Base → PhaseMean.Tensor →L[ℝ] ℝ}
    (h : ∀ i, LocalBounds (c i).U (c i).V s r₁ ρ R reference
      (F ∘ (c i).e) (ψ i) (Q i) (c i).χ (c i).e)
    (d : ∀ i, Budgets (c i).U (c i).V s (F ∘ (c i).e) (ψ i) (Q i) (c i).χ (c i).e)
    (hs : 0 < s) (hs1 : s ≤ 1) (hρ : 0 < ρ) (hgap : r₀ < r₁)
    (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) (q : ℕ)
    (g : ∀ m l, ForcedGeometryBudget (v l) s s q (m + 1))
    {P : ℕ → ℝ} (hP : ∀ m, 0 ≤ P m)
    (hbφ : ∀ m i w, ‖w‖ ≤ 1 → WeightedBound univ s (m + 1 + q + 1)
      (P m) (coordDeriv w (φ i)))
    (hdecomp : ∀ A : Base → PhaseMean.Tensor, InTrialBall univ reference r₁ A →
      ∀ p, (∑ i, (c i).U.indicator
        (chartLeadingTensor (phaseAmplitude (ψ i) (coefficient (Q i) (c i).e A)) (c i).χ) p) = A p)
    {C₀ : ℕ → ℝ} (hC₀ : ∀ m, 1 ≤ C₀ m) (hH : ContDiff ℝ ∞ H)
    (hH0 : ∀ p, ‖H p - reference p‖ ≤ r₀)
    (hbH : ∀ m, WeightedBound univ s m (C₀ m) H) :
    ∃ η₀ : ℝ, ∃ C E T : ℕ → ℝ, 0 < η₀ ∧ η₀ ≤ 1 ∧
      (∀ m, 0 ≤ C m ∧ 0 ≤ E m ∧ 0 ≤ T m) ∧
      ∀ η, 0 < η → η ≤ η₀ → ∀ δ, 0 ≤ δ → δ ≤ η * s →
      ∃ U : RField 4, ContDiff ℝ ∞ U ∧ tsupport U ⊆ ⋃ i, S i ∧
        (∀ m, WeightedBound univ (η * s) m (C m * (δ * (η * s))) U) ∧
        (∀ m, WeightedBound univ (η * s) m
          (E m * δ * η ^ (q + 1) + T m * (δ ^ 3 / (η * s)))
          (fun p => realMetricTensor (fun x => F x + U x) p - realMetricTensor F p - δ ^ 2 • H p)) := by
  classical
  obtain ⟨B, K, η₀, hη₀, hη₁, ht⟩ := finite_free_mean_adjustment_uniform Finset.univ
    (fun i _ => h i) (fun i _ => d i) hs hs1 hρ hgap
    (fun i _ => (c i).closedS) (fun i _ => (c i).supportU) (fun i _ => (c i).cutoff)
    (fun A hb p => hdecomp A hb p) q q hC₀ hH hH0 hbH
  let α := {η : ℝ // 0 < η ∧ η ≤ η₀}
  let a₀ : α := ⟨η₀, hη₀, le_rfl⟩
  have ha (a : α) := ht a.val a.property.1 a.property.2 q le_rfl
  choose A hA hball hsm hsize hres using ha
  have hb (m : ℕ) := trial_family_free_budgets c h d hs hs1 hρ q
    (m + 1 + q + 1 + 1) A hA hball
    (abs_nonneg (sizeBound (q + 2) C₀ B q ((m + 1 + q + 1 + 1) + q + 1)))
    (fun a => (hsize a _).mono_const (le_abs_self _)) a₀
  choose b hnum using hb
  have hi (m : ℕ) := constructed_finite_increment_uniform hF c v hs hs1 (hP m) hφ q m a₀
    (b m) (g m) (hnum m) (hbφ m)
  choose C E T hC hE hT hi using hi
  let D : ℕ → ℝ := fun m => |differenceBound (q + 2) C₀ B K q m|
  refine ⟨η₀, C, (fun m => E m + D m), T, hη₀, hη₁,
    (fun m => ⟨hC m, add_nonneg (hE m) (abs_nonneg _), hT m⟩), ?_⟩
  intro η hη hηsmall δ hδ hδτ
  let a : α := ⟨η, hη, hηsmall⟩
  have hτ : 0 < η * s := mul_pos hη hs
  have hτs : η * s ≤ s := mul_le_of_le_one_left hs.le (hηsmall.trans hη₁)
  let Z := fun i => (c i).amplitude (coefficient (Q i) (c i).e (A a)) δ (η * s) q
  let X := sumDisplacement (η * s) φ Z
  let V := fun p => ∑ l, (v l).solve (η * s) (quadraticAmplitude (η * s) φ Z l) q p
  let U := fun p => X p + V p
  have hinc (m) := hi m a (η * s) hτ hτs δ hδ hδτ
  refine ⟨U, (hinc 0).1, (hinc 0).2.1, (fun m => (hinc m).2.2.1), ?_⟩
  intro m
  have hZ (i) : ContDiff ℝ ∞ (Z i) :=
    (c i).amplitude_smooth ((h i).amplitude_smooth hρ (hA a).contDiffOn
      (fun p _ => hball a p (mem_univ p))) δ (η * s) q |>.1
  have hzero := contDiff_zeroPhaseSum hφ hZ (η * s)
  have heq : zeroPhaseSum (η * s) φ Z = fun p => ∑ i,
      phaseZeroTensor (η * s) (fun p => ((c i).χ p).1)
        (phaseFreeFamily (fun i => (c i).U) δ (η * s) (fun i => F ∘ (c i).e) ψ Q
          (fun i => (c i).χ) (fun i => (c i).e) q (A a) i) p := by
    funext p
    apply Finset.sum_congr rfl
    intro i hi'
    exact congrFun ((c i).mean_phase ((h i).amplitude_smooth hρ (hA a).contDiffOn
      (fun p _ => hball a p (mem_univ p))) δ (η * s) q) p
  have hr := (hres a δ m).shrink_scale hτ.le hτs
  change WeightedBound univ (η * s) m
    (δ ^ 2 * (differenceBound (q + 2) C₀ B K q m * η ^ (q + 1)))
    (fun p => (∑ i, phaseZeroTensor (η * s) (fun p => ((c i).χ p).1)
      (phaseFreeFamily (fun i => (c i).U) δ (η * s) (fun i => F ∘ (c i).e) ψ Q
        (fun i => (c i).χ) (fun i => (c i).e) q (A a) i) p) - δ ^ 2 • H p) at hr
  simp only [← congrFun heq] at hr
  have hb1 := (hinc m).2.2.2
  rw [mul_div_cancel_right₀ η hs.ne'] at hb1
  have hleft := ((contDiffOn_realMetricTensor isOpen_univ (hF.add (hinc m).1).contDiffOn).sub
    (contDiffOn_realMetricTensor isOpen_univ hF.contDiffOn)).sub hzero.contDiffOn
  have hadd := WeightedBound.add isOpen_univ.uniqueDiffOn hτ.le hleft
    (hzero.sub ((contDiff_const (c := δ ^ 2)).smul hH)).contDiffOn hb1 hr
  have hδ1 : δ ≤ 1 := hδτ.trans (hτs.trans hs1)
  have hdd : δ ^ 2 ≤ δ := by nlinarith
  have hbmean : δ ^ 2 * (differenceBound (q + 2) C₀ B K q m * η ^ (q + 1)) ≤
      D m * δ * η ^ (q + 1) := by
    calc
      _ ≤ δ ^ 2 * (D m * η ^ (q + 1)) := by gcongr; exact le_abs_self _
      _ ≤ δ * (D m * η ^ (q + 1)) := mul_le_mul_of_nonneg_right hdd
        (mul_nonneg (abs_nonneg _) (pow_nonneg hη.le _))
      _ = _ := by ring
  have hc : E m * δ * η ^ (q + 1) + T m * (δ ^ 3 / (η * s)) +
      δ ^ 2 * (differenceBound (q + 2) C₀ B K q m * η ^ (q + 1)) ≤
      (E m + D m) * δ * η ^ (q + 1) + T m * (δ ^ 3 / (η * s)) := by nlinarith [hbmean]
  apply (hadd.mono_const hc).congr
  intro p hp
  simp only
  abel

end ClosedSurfaceR4.RealModes

end

end OAI
