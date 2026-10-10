import OAI.Geometry.RuledCovering.Main

namespace OAI

noncomputable section
open Set MeasureTheory

namespace RuledApproximation.HyperbolicBoundaryCertificates

theorem physical_weight_integrable {D : Set Plane} {v : Plane → Plane}
    (hD : IsCompact D) (hv : SmoothNear 1 D v) (h : ℝ) :
    IntegrableOn (fun p => physicalWeight h (v p)) D := by
  obtain ⟨U, hU, hDU, hv⟩ := hv
  exact ((physicalWeight_continuous h).comp_continuousOn
    (hv.continuousOn.mono hDU)).integrableOn_compact hD

theorem physical_weight_integral_pos_iff {D : Set Plane} {v : Plane → Plane}
    (hD : IsCompact D) (hv : SmoothNear 1 D v) (h : ℝ) :
    (0 < ∫ p in D, physicalWeight h (v p)) ↔ 0 < volume D := by
  have hs : Function.support (fun p => physicalWeight h (v p)) = univ := by
    ext p
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (physicalWeight_pos h (v p)).ne'
  simpa only [hs, univ_inter] using
    (setIntegral_pos_iff_support_of_nonneg_ae
      (Filter.Eventually.of_forall (fun p => (physicalWeight_pos h (v p)).le))
      (physical_weight_integrable hD hv h))

theorem physical_weight_integral_eq_zero_iff {D : Set Plane} {v : Plane → Plane}
    (hD : IsCompact D) (hv : SmoothNear 1 D v) (h : ℝ) :
    (∫ p in D, physicalWeight h (v p)) = 0 ↔ volume D = 0 := by
  have hn : 0 ≤ ∫ p in D, physicalWeight h (v p) :=
    integral_nonneg (fun p => (physicalWeight_pos h (v p)).le)
  have hp := physical_weight_integral_pos_iff hD hv h
  constructor
  · intro hz
    by_contra hvol
    have := hp.mpr (bot_lt_iff_ne_bot.mpr hvol)
    linarith
  · intro hvol
    apply le_antisymm _ hn
    by_contra hneg
    have := hp.mp (lt_of_not_ge hneg)
    simp [hvol] at this

theorem empty_labels_zero_count (h L : ℝ) (v : Plane → Plane)
    (F : Space ≃ᵢ Space) :
    ∃ C : Fin 0 → Cylinder,
      (∀ i, (C i).parallelogram) ∧ familyArea C = 0 ∧
      F '' physicalRuled h ∅ v L ⊆ familySet C := by
  refine ⟨Fin.elim0, fun i => i.elim0, ?_, ?_⟩
  · simp [familyArea]
  · simp [physicalRuled_empty]

theorem null_labels_physical_cover {h L : ℝ} {D : Set Plane} {v : Plane → Plane}
    (hh : 0 < h) (hL : 0 < L) (hD : IsCompact D) (hv : SmoothNear 1 D v)
    (hH : ∀ p ∈ D, HyperbolicAt L v p) (hnull : volume D = 0)
    {eps : ℝ} (heps : 0 < eps) (F : Space ≃ᵢ Space) :
    HasFiniteCover Cylinder.parallelogram (F '' physicalRuled h D v L) eps := by
  have hc := physicalHyperbolic h L D v hh hL hD hv hH eps heps F
  have hz := (physical_weight_integral_eq_zero_iff hD hv h).mpr hnull
  simpa [hz] using hc

theorem strict_physical_cover {h L A : ℝ} {D : Set Plane} {v : Plane → Plane}
    (hh : 0 < h) (hL : 0 < L) (hD : IsCompact D) (hv : SmoothNear 1 D v)
    (hH : ∀ p ∈ D, HyperbolicAt L v p)
    (hbudget : h * (∫ p in D, physicalWeight h (v p)) < A)
    (F : Space ≃ᵢ Space) :
    ∃ n : ℕ, ∃ C : Fin n → Cylinder,
      (∀ i, (C i).parallelogram ∧ IsCompact (C i).base ∧ MeasurableSet (C i).base) ∧
      F '' physicalRuled h D v L ⊆ familySet C ∧ familyArea C < A := by
  let eps := (A - h * (∫ p in D, physicalWeight h (v p))) / 2
  have heps : 0 < eps := half_pos (sub_pos.mpr hbudget)
  obtain ⟨n, C, hC, hcov, hcost⟩ := physicalHyperbolic h L D v hh hL hD hv hH eps heps F
  refine ⟨n, C, fun i => ⟨hC i, (hC i).isCompact, (hC i).isCompact.measurableSet⟩,
    hcov, ?_⟩
  dsimp [eps] at hcost
  linarith

theorem strict_physical_cover_with_residual {h L A B : ℝ}
    {D : Set Plane} {v : Plane → Plane} {R : Set Space}
    (hh : 0 < h) (hL : 0 < L) (hD : IsCompact D) (hv : SmoothNear 1 D v)
    (hH : ∀ p ∈ D, HyperbolicAt L v p)
    (hresidual : HasFiniteCover Cylinder.parallelogram R B)
    (hbudget : h * (∫ p in D, physicalWeight h (v p)) + B < A)
    (F : Space ≃ᵢ Space) :
    ∃ n : ℕ, ∃ C : Fin n → Cylinder,
      (∀ i, (C i).parallelogram) ∧
      (F '' physicalRuled h D v L) ∪ R ⊆ familySet C ∧ familyArea C < A := by
  let eps := (A - (h * (∫ p in D, physicalWeight h (v p)) + B)) / 2
  have heps : 0 < eps := half_pos (sub_pos.mpr hbudget)
  have hc := physicalHyperbolic h L D v hh hL hD hv hH eps heps F
  obtain ⟨n, C, hC, hcov, hcost⟩ := hc.union hresidual
  refine ⟨n, C, hC, hcov, ?_⟩
  dsimp [eps] at hcost
  linarith

end RuledApproximation.HyperbolicBoundaryCertificates

end

end OAI
