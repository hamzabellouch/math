import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.BoundedL1PoissonBarrier
import OAI.Analysis.CoulombIonization.Localization.PosteriorSubmeanBarrier
import OAI.Analysis.CoulombIonization.FieldAnalysis.WeakPoissonOscillationBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_OriginalFieldOscillation_barrier_scope

open MeasureTheory Filter Set Metric Laplacian InnerProductSpace
open scoped Topology ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombObservation CoulombBarrier

lemma originalQueryField_continuousOn_punctured {N K : ℕ} (F : fermionGraph N)
    (Z lam r : ℝ) (j : ℕ) {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr₀ : 0 < r₀)
    (hs : 0 < s) (hrs : r₀ ≤ s)
    (z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) :
    ContinuousOn (originalQueryField F Z lam r j c₁ r₀ s z) {0}ᶜ := by
  obtain ⟨M,hM,hρ⟩ := originalQueryDensity_bounded_L1 F r j hc hr₀ hs hrs
  have hp := (bounded_L1_potential_lipschitz (hρ z).1 (hρ z).2.1 hM
    (hρ z).2.2.1 (hρ z).2.2.2).continuous
  apply ((continuousOn_const.div continuous_norm.continuousOn ?_).sub continuousOn_const).sub hp.continuousOn
  intro x hx
  exact norm_ne_zero_iff.mpr hx

lemma originalQueryField_punctured_poisson {N K : ℕ} (F : fermionGraph N)
    (Z lam r : ℝ) (j : ℕ) {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr₀ : 0 < r₀)
    (hs : 0 < s) (hrs : r₀ ≤ s)
    (z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) :
    PuncturedPoisson (originalQueryField F Z lam r j c₁ r₀ s z)
      (fun y => 4*Real.pi*originalQueryDensity F r j c₁ r₀ s z y) := by
  obtain ⟨M,hM,hρ⟩ := originalQueryDensity_bounded_L1 F r j hc hr₀ hs hrs
  intro g hg hcg hsg
  have hg0 : g 0 = 0 := by
    by_contra hn0
    exact hsg (subset_tsupport g hn0) rfl
  have hiN := locallyIntegrable_mul_test (nuclearField_locallyIntegrable Z)
    (tfLaplacian_continuous hg) (tfLaplacian_compact hg hcg)
  have hiL : Integrable (fun x : Space => lam*Δ g x) :=
    (continuous_const.mul (tfLaplacian_continuous hg)).integrable_of_hasCompactSupport
      (tfLaplacian_compact hg hcg).mul_left
  have hiP := locallyIntegrable_mul_test
    (bounded_L1_potential_lipschitz (hρ z).1 (hρ z).2.1 hM
      (hρ z).2.2.1 (hρ z).2.2.2).continuous.locallyIntegrable
    (tfLaplacian_continuous hg) (tfLaplacian_compact hg hcg)
  have hL := compact_laplacian_green (f := fun _ : Space => lam) contDiff_const hg hcg
  simp only [laplacian_const,Pi.zero_apply,zero_mul,integral_zero] at hL
  change Integrable (fun x : Space => Z/‖x‖*Δ g x) at hiN
  have hiNL : Integrable (fun x : Space => Z/‖x‖*Δ g x-lam*Δ g x) := by
    exact (hiN.sub hiL).congr (ae_of_all _ (fun _ => rfl))
  simp only [originalQueryField,sub_mul]
  rw [integral_sub hiNL hiP,integral_sub hiN hiL,hL,
    show (∫ x, Z/‖x‖*Δ g x) = -(4*Real.pi*Z)*g 0 from
      nuclearField_weak_laplacian Z hg hcg,hg0,mul_zero,sub_zero,zero_sub,
    bounded_L1_weak_poisson (hρ z).1 (hρ z).2.1 hM (hρ z).2.2.1 (hρ z).2.2.2 hg hcg]
  simp only [mul_assoc,integral_const_mul]
  ring

theorem exists_original_field_oscillation_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ {N K : ℕ} (F : fermionGraph N)
      (Z lam r : ℝ) (j : ℕ) {c₁ r₀ s : ℝ},
      0 < c₁ → 0 < r₀ → 0 < s → r₀ ≤ s →
      ∀ (z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))
        (y : Space) (R B M : ℝ), 0 < R → R < ‖y‖ → 0 ≤ B → 0 ≤ M →
      (∀ x ∈ ball y R, originalQueryDensity F r j c₁ r₀ s z x ≤ M) →
      (∀ x ∈ closedBall y R, originalQueryField F Z lam r j c₁ r₀ s z x ≤ B) →
      ∀ x : Space, ‖x-y‖ ≤ R/6 →
        |originalQueryField F Z lam r j c₁ r₀ s z x-
          originalQueryField F Z lam r j c₁ r₀ s z y| ≤
          C/R*‖x-y‖*(B+M*R^2+max (-originalQueryField F Z lam r j c₁ r₀ s z y) 0) := by
  obtain ⟨C,hC,hbound⟩ := exists_local_poisson_oscillation_constant
  refine ⟨C,hC,?_⟩
  intro N K F Z lam r j c₁ r₀ s hc hr₀ hs hrs z y R B M hR hRy hB hM hden hcap x hx
  obtain ⟨M₀,hM₀,hρ⟩ := originalQueryDensity_bounded_L1 F r j hc hr₀ hs hrs
  have hsub : closedBall y R ⊆ ({0}ᶜ : Set Space) := by
    intro t ht ht0
    have he : t = 0 := ht0
    subst t
    have hh : ‖y‖ ≤ R := by simpa only [mem_closedBall,dist_zero_left] using ht
    exact (not_le_of_gt hRy) hh
  apply hbound _ _ y R B M hR hB hM
    ((originalQueryField_continuousOn_punctured F Z lam r j hc hr₀ hs hrs z).mono hsub)
    (hρ z).1 (fun t _ => (hρ z).2.2.1 t) hden hcap
    (fun g hg hcg hsg => ?_) x hx
  have hh := originalQueryField_punctured_poisson F Z lam r j hc hr₀ hs hrs z g hg hcg
    (hsg.trans (ball_subset_closedBall.trans hsub))
  simpa only [mul_assoc,integral_const_mul] using hh

end CoulombAtom

end Work_OriginalFieldOscillation_barrier_scope

open MeasureTheory Filter Set Metric

namespace CoulombAnalysis
open CoulombAtom

lemma norm_fourth_difference_le {r : ℝ} (_hr : 0 < r) {x y : Space}
    (hx : ‖x‖ ≤ 2*r) (hy : ‖y‖ ≤ 2*r) :
    |‖x‖^4-‖y‖^4| ≤ 32*r^3*‖x-y‖ := by
  have hp := abs_pow_sub_pow_le (a := ‖x‖) (b := ‖y‖) (n := 4)
  simp only [abs_of_nonneg (norm_nonneg x),abs_of_nonneg (norm_nonneg y)] at hp
  calc
    _ ≤ |‖x‖-‖y‖| *4*(max ‖x‖ ‖y‖)^3 := by simpa only [Nat.cast_ofNat] using hp
    _ ≤ ‖x-y‖*4*(2*r)^3 := by
      gcongr
      · exact abs_norm_sub_norm_le x y
      · exact max_le hx hy
    _ = _ := by ring

lemma normalized_field_difference {φ : Space → ℝ} {x y : Space} {r A B M : ℝ}
    (hr : 0 < r) (hA : 0 ≤ A) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hx : ‖x‖ ≤ 2*r) (hyl : r ≤ ‖y‖) (hy : ‖y‖ ≤ 2*r)
    (hcap : φ y ≤ B)
    (hosc : |φ x-φ y| ≤ A/r*‖x-y‖*(B+M*r^2+max (-φ y) 0)) :
    |‖x‖^4*φ x-‖y‖^4*φ y| ≤
      (16*A+32)/r*‖x-y‖*(r^4*B+r^6*M+max (-(‖y‖^4*φ y)) 0) := by
  let t : ℝ := max (-φ y) 0
  let V : ℝ := max (-(‖y‖^4*φ y)) 0
  let Q : ℝ := r^4*B+r^6*M+V
  have ht : 0 ≤ t := le_max_right _ _
  have hV : 0 ≤ V := le_max_right _ _
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hneg : r^4*t ≤ V := by
    calc
      _ ≤ ‖y‖^4*t := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr.le hyl 4) ht
      _ = V := by dsimp [t,V]; rw [mul_max_of_nonneg _ _ (pow_nonneg (norm_nonneg y) 4),mul_zero]; congr 1; ring
  have habs : |φ y| ≤ B+t := by
    apply abs_le.mpr
    have hh : -φ y ≤ t := le_max_left _ _
    constructor <;> linarith
  have hxp : ‖x‖^4 ≤ 16*r^4 := by
    calc
      _ ≤ (2*r)^4 := pow_le_pow_left₀ (norm_nonneg x) hx 4
      _ = _ := by ring
  have hfirst : ‖x‖^4*|φ x-φ y| ≤ (16*A)/r*‖x-y‖*Q := by
    calc
      _ ≤ (16*r^4)*(A/r*‖x-y‖*(B+M*r^2+t)) :=
        mul_le_mul hxp hosc (abs_nonneg _) (by positivity)
      _ = (16*A)/r*‖x-y‖*(r^4*B+r^6*M+r^4*t) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by dsimp [Q]; linarith) (by positivity)
  have hsecond : |‖x‖^4-‖y‖^4| *|φ y| ≤ 32/r*‖x-y‖*Q := by
    calc
      _ ≤ (32*r^3*‖x-y‖)*(B+t) :=
        mul_le_mul (norm_fourth_difference_le hr hx hy) habs (abs_nonneg _) (by positivity)
      _ = 32/r*‖x-y‖*(r^4*B+r^4*t) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (by dsimp [Q]; nlinarith [mul_nonneg (pow_nonneg hr.le 6) hM]) (by positivity)
  calc
    _ = |‖x‖^4*(φ x-φ y)+(‖x‖^4-‖y‖^4)*φ y| := by congr 1; ring
    _ ≤ |‖x‖^4*(φ x-φ y)|+|(‖x‖^4-‖y‖^4)*φ y| := abs_add_le _ _
    _ = ‖x‖^4*|φ x-φ y|+|‖x‖^4-‖y‖^4| *|φ y| := by
      rw [abs_mul,abs_of_nonneg (pow_nonneg (norm_nonneg x) 4),abs_mul]
    _ ≤ (16*A)/r*‖x-y‖*Q+32/r*‖x-y‖*Q := add_le_add hfirst hsecond
    _ = _ := by dsimp [Q,V]; ring

end CoulombAnalysis

end

end OAI
