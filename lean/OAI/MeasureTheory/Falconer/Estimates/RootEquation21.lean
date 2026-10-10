import OAI.MeasureTheory.Falconer.Graphs.RootParentEnergy
import OAI.MeasureTheory.Falconer.Fourier.RootUniformFourier
import OAI.MeasureTheory.Falconer.Shells.HighShellErrorPower
import OAI.MeasureTheory.Falconer.Shells.ShellApproximationError

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
namespace RootShellData

theorem uniform_parent_bound {sig δ L eps T : ℝ}
    (hsig : 0 < sig) (hsmall : sig ≤ 1/4) (hδ : 0 < δ) (hL : 0 < L) (heps : 0 < eps) :
    ∃ n N₀ : ℕ, ∀ d : RootShellData,
    ∀ [IsProbabilityMeasure d.left.ρ] [IsProbabilityMeasure d.right.ρ],
    N₀ ≤ d.N → d.sig = sig → 0 < d.left.Q.side → 0 < d.right.Q.side →
    d.left.S.card ≤ (d.N+1)^3+1 → d.right.S.card ≤ (d.N+1)^3+1 →
    (∀ b ∈ d.left.S, descriptorLength b ≤ d.N/2) →
    (∀ b ∈ d.right.S, descriptorLength b ≤ d.N/2) →
    0 < d.U.side → 0 < d.V.side →
    (∀ᵐ x ∂d.left.ρ, x ∈ d.U.carrier) → (∀ᵐ y ∂d.right.ρ, y ∈ d.V.carrier) →
    (∀ x ∈ d.U.carrier, ∀ y ∈ d.V.carrier, δ ≤ dist x y ∧ dist x y ≤ L) →
    ∀ s : ℝ, d.U.side ≤ s → d.V.side ≤ s → 100*s ≤ dist d.U.center d.V.center →
    ∀ Ψ : ℝ → ℝ, Measurable Ψ → (∀ x, 0 ≤ Ψ x) →
    (∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4) →
    ∀ W : ℝ, 0 ≤ W → (∀ x, Ψ x ≤ W) → (∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) →
    ∀ H : ℝ, 0 ≤ H →
    (∀ j ∈ Finset.range (n+1), ∀ b ∈ inverseLeibnizTerms j d.indices, ∀ ξ,
      (d.inversePhasedHF d.N Ψ b.2 ξ).toReal ≤ H) →
    (∫ r in Icc ((2:ℝ)^((d.N:ℝ)-1)) ((2:ℝ)^((d.N:ℝ)+1)), ‖charFun d.measure r‖^2) ≤
      ((2:ℝ)^d.N)^eps*H+((2:ℝ)^d.N)^(-T) := by
  obtain ⟨n,N₁,h₁⟩ := uniform_root_fourier_error (T := (T+3)/2) hsig hsmall hδ
  obtain ⟨N₂,h₂⟩ := uniform_root_spatialLeibniz_sum_subpower δ L hδ hL
    (show 0 < eps/4 by linarith) n
  obtain ⟨N₃,h₃⟩ := fixed_constant_absorbed (half_pos heps) 4
  refine ⟨n,max 1 (max N₁ (max N₂ N₃)),?_⟩
  intro d inst₁ inst₂ hN hsig' hd he hc₁ hc₂ hl₁ hl₂ hU hV hcarry₁ hcarry₂ hsep s hUs hVs hstrong Ψ hΨ hpos hs W hW hΨW hone H hH0 hH
  subst sig
  have hN1 : N₁ ≤ d.N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN2 : N₂ ≤ d.N := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hN3 : N₃ ≤ d.N := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hdist : ∀ᵐ z ∂d.left.ρ.prod d.right.ρ, δ ≤ dist z.1 z.2 := by
    filter_upwards [root_pair_ae_patches d.left d.right d.U d.V hcarry₁ hcarry₂] with z hz
    exact (hsep z.1 hz.1 z.2 hz.2).1
  let : IsFiniteMeasure d.measure := rootWeightedDistance_isFinite d.left d.right d.N d.sig hd he hδ hdist
  let R : ℝ := (2:ℝ)^d.N
  let μ := volume.restrict (Icc ((2:ℝ)^((d.N:ℝ)-1)) ((2:ℝ)^((d.N:ℝ)+1)))
  let err := R^(-((T+3)/2))
  have herr : ∀ᵐ r ∂μ, ‖charFun d.measure r-d.mainF n r‖ ≤ err := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact (h₁ d.N hN1 d.left d.right hd he hc₁ hc₂ hl₁ hl₂ d.U d.V hU hV hcarry₁ hcarry₂
      (fun x hx y hy => (hsep x hx y hy).1) s hUs hVs hstrong r hr.1).2
  have hi : Integrable (fun r => ‖charFun d.measure r‖^2) μ :=
    integrable_norm_square_bounded μ _ measurable_charFun measureReal_nonneg
      (Eventually.of_forall (fun r => norm_charFun_le r))
  have hsq := (shell_square_approximation μ _ _
    (rootNormalizedF_measurable d.left d.right d.N d.sig n d.U d.V)
    hi (show 0 ≤ err by dsimp [err]; positivity) herr).2
  have hmain := d.mainF_parent_energy δ L hδ hL hd he hsig.le hl₁ hl₂ hcarry₁ hcarry₂ hsep n
    Ψ hΨ hpos hs hW hΨW hone hH0 hH
  let S := ∑ j ∈ Finset.range (n+1), d.cost δ L hδ hL j
  have hS : S ≤ R^(eps/4) := h₂ d.N hN2 d.left d.right hc₁ hc₂
  have hS0 : 0 ≤ S := by
    apply Finset.sum_nonneg
    intro j hj
    apply mul_nonneg (spatialFourierCost_nonneg ..)
    apply mul_nonneg _ (by positivity)
    apply List.sum_nonneg
    intro x hx
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx
    positivity
  have hcost : 4*S^2 ≤ R^eps := by
    calc
      _ ≤ R^(eps/2)*(R^(eps/4))^2 :=
        mul_le_mul (h₃ d.N hN3) (pow_le_pow_left₀ hS0 hS 2) (sq_nonneg _) (by positivity)
      _ = _ := by
        rw [← Real.rpow_mul_natCast (show 0 ≤ R by dsimp [R]; positivity),
          ← Real.rpow_add (show 0 < R by dsimp [R]; positivity)]
        congr 1
        norm_num
        ring
  have herror : 2*err^2*μ.real univ ≤ R^(-T) := by
    simpa only [Nat.cast_zero,neg_zero,Real.rpow_zero,one_mul] using
      high_shell_error_power d.N 0 ((le_max_left _ _).trans hN) (v := (d.N:ℝ)) le_rfl T
  calc
    _ ≤ 2*(∫ r, ‖d.mainF n r‖^2 ∂μ)+2*err^2*μ.real univ := hsq
    _ ≤ 2*(2*S^2*H)+R^(-T) :=
      add_le_add (mul_le_mul_of_nonneg_left hmain (by norm_num)) herror
    _ ≤ R^eps*H+R^(-T) := by nlinarith [mul_le_mul_of_nonneg_right hcost hH0]

end RootShellData

end PlanarFalconer

end OAI
