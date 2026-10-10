import OAI.Analysis.SphereIsometry.KuratowskiBasic
import OAI.Analysis.SphereIsometry.ReturnMapBounds
import OAI.Analysis.SphereIsometry.ScalarBins
import Mathlib.Data.Fintype.Prod

namespace OAI

/-!
# The return map contracts noncompactness on every subset

Finite scalar bins refine diameter covers after each piece is intersected
with the given subset. A positive-error argument then passes to the exact
Kuratowski infimum. Neither the subset nor its covering pieces need be compact.
-/

noncomputable section

namespace Tingley

/-- A finite refinement by two bounded scalar observables. -/
theorem finiteDiameterCover_image_of_scalar_bins
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {C H : Set X} {g : X → Y} {p u : X → ℝ} {U a γ δ η : ℝ}
    (hHC : H ⊆ C) (hU : 0 ≤ U) (ha : 0 < a) (hγ : 0 ≤ γ)
    (hp : ∀ v ∈ C, p v ∈ Set.Icc 0 U)
    (hu : ∀ v ∈ C, u v ∈ Set.Icc 0 U)
    (hpair : ∀ v ∈ C, ∀ v' ∈ C,
      dist (g v) (g v') ≤ γ * dist v v' +
        (2 / a) * (|u v - u v'| + |p v - p v'|))
    (hc : FiniteDiameterCover H δ) (hη : 0 < η) :
    FiniteDiameterCover (g '' H) (γ * δ + 4 * η / a) := by
  obtain ⟨n, A, hcover, hdiam⟩ := hc
  obtain ⟨N, B, hBcover, hBdiam⟩ := exists_finite_scalar_bins hU hη
  let Q : (Fin n × Fin N × Fin N) → Set X := fun ijk =>
    H ∩ A ijk.1 ∩ p ⁻¹' B ijk.2.1 ∩ u ⁻¹' B ijk.2.2
  apply FiniteDiameterCover.of_fintype (fun ijk => g '' Q ijk)
  · rintro y ⟨v, hvH, rfl⟩
    obtain ⟨i, hvi⟩ := Set.mem_iUnion.mp (hcover hvH)
    obtain ⟨j, hvj⟩ := Set.mem_iUnion.mp (hBcover (hp v (hHC hvH)))
    obtain ⟨k, hvk⟩ := Set.mem_iUnion.mp (hBcover (hu v (hHC hvH)))
    exact Set.mem_iUnion.mpr
      ⟨(i, j, k), v, ⟨⟨⟨hvH, hvi⟩, hvj⟩, hvk⟩, rfl⟩
  · rintro ijk y ⟨v, hv, rfl⟩ z ⟨v', hv', rfl⟩
    change v ∈ H ∩ A ijk.1 ∩ p ⁻¹' B ijk.2.1 ∩ u ⁻¹' B ijk.2.2 at hv
    change v' ∈ H ∩ A ijk.1 ∩ p ⁻¹' B ijk.2.1 ∩ u ⁻¹' B ijk.2.2 at hv'
    rcases hv with ⟨⟨⟨hvH, hvA⟩, hvp⟩, hvu⟩
    rcases hv' with ⟨⟨⟨hvH', hvA'⟩, hvp'⟩, hvu'⟩
    have hpd : |p v - p v'| ≤ η := hBdiam ijk.2.1 _ hvp _ hvp'
    have hud : |u v - u v'| ≤ η := hBdiam ijk.2.2 _ hvu _ hvu'
    have herr : (2 / a) * (|u v - u v'| + |p v - p v'|) ≤ 4 * η / a := by
      calc
        (2 / a) * (|u v - u v'| + |p v - p v'|) ≤ (2 / a) * (η + η) :=
          mul_le_mul_of_nonneg_left (add_le_add hud hpd) (div_nonneg zero_le_two ha.le)
        _ = 4 * η / a := by ring
    exact (hpair v (hHC hvH) v' (hHC hvH')).trans
      (add_le_add (mul_le_mul_of_nonneg_left (hdiam ijk.1 v hvA v' hvA') hγ) herr)

/-- The exact all-subsets contraction, including the empty subset. The scalar
relations and the two-point estimate are supplied by the actual return map. -/
theorem chi_return_image_le
    {X : Type*} [PseudoMetricSpace X]
    {C : Set X} {g : X → X} {p s u r : X → ℝ} {t M : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (hM : 0 < M)
    (hCne : C.Nonempty) (hCb : Bornology.IsBounded C)
    (_hgC : Set.MapsTo g C C)
    (hbounds : ∀ v ∈ C,
      (1 - t ≤ p v ∧ p v ≤ 1 + t) ∧
      (1 - t ≤ s v ∧ s v ≤ 1 + t) ∧
      (1 - t ≤ u v ∧ u v ≤ 1 + t) ∧
      (1 - t ≤ r v ∧ r v ≤ 1 + t))
    (hs : ∀ v ∈ C, s v = p v + M)
    (hr : ∀ v ∈ C, r v = u v + M)
    (hpair : ∀ v ∈ C, ∀ v' ∈ C,
      dist (g v) (g v') ≤
        (u v * p v / (r v * s v)) * dist v v' +
        2 * |u v - u v'| / r v +
        2 * u v * |p v - p v'| / (r v * s v))
    {H : Set X} (hHC : H ⊆ C) :
    chi (g '' H) ≤ (1 - M / (1 + t)) ^ 2 * chi H := by
  let γ : ℝ := (1 - M / (1 + t)) ^ 2
  have ha : 0 < 1 - t := sub_pos.mpr ht1
  have hU : 0 ≤ 1 + t := by linarith
  have hfactor := return_contraction_factor_mem_Ico ht0 ht1 hM hCne
    (fun v hv => (hbounds v hv).1.1)
    (fun v hv => (hbounds v hv).2.1.2) hs
  have hγ : 0 ≤ γ := hfactor.1
  have hγ1 : γ ≤ 1 := hfactor.2.le
  have hp : ∀ v ∈ C, p v ∈ Set.Icc 0 (1 + t) := by
    intro v hv
    exact ⟨ha.le.trans (hbounds v hv).1.1, (hbounds v hv).1.2⟩
  have hu : ∀ v ∈ C, u v ∈ Set.Icc 0 (1 + t) := by
    intro v hv
    exact ⟨ha.le.trans (hbounds v hv).2.2.1.1, (hbounds v hv).2.2.1.2⟩
  have hpair' : ∀ v ∈ C, ∀ v' ∈ C,
      dist (g v) (g v') ≤ γ * dist v v' +
        (2 / (1 - t)) * (|u v - u v'| + |p v - p v'|) := by
    intro v hv v' hv'
    exact return_pair_uniform_bound ha hM.le (hp v hv).1 (hu v hv).1
      (hbounds v hv).2.2.2.1 (hbounds v hv).2.1.1
      (hbounds v hv).2.2.2.2 (hbounds v hv).2.1.2
      (hr v hv) (hs v hv) dist_nonneg (abs_nonneg _) (abs_nonneg _)
      (hpair v hv v' hv')
  have happrox : ∀ ε : ℝ, 0 < ε → chi (g '' H) ≤ γ * chi H + ε := by
    intro ε hε
    have hε2 : 0 < ε / 2 := half_pos hε
    obtain ⟨δ, hδ0, hδ, hc⟩ := exists_cover_of_chi_lt (hCb.subset hHC)
      (show chi H < chi H + ε / 2 by linarith)
    let η : ℝ := ε * (1 - t) / 8
    have hη : 0 < η := div_pos (mul_pos hε ha) (by norm_num)
    have hc' := finiteDiameterCover_image_of_scalar_bins hHC hU ha hγ hp hu hpair' hc hη
    have hR : 0 ≤ γ * δ + 4 * η / (1 - t) :=
      add_nonneg (mul_nonneg hγ hδ0.le)
        (div_nonneg (mul_nonneg (by norm_num) hη.le) ha.le)
    have herror : 4 * η / (1 - t) = ε / 2 := by
      dsimp only [η]
      field_simp [ne_of_gt ha]
      ring
    calc
      chi (g '' H) ≤ γ * δ + 4 * η / (1 - t) := chi_le_of_cover hR hc'
      _ = γ * δ + ε / 2 := by rw [herror]
      _ ≤ γ * (chi H + ε / 2) + ε / 2 :=
        add_le_add_left (mul_le_mul_of_nonneg_left hδ.le hγ) _
      _ ≤ γ * chi H + ε := by
        have hh := mul_le_mul_of_nonneg_right hγ1 hε2.le
        nlinarith
  change chi (g '' H) ≤ γ * chi H
  by_contra hnot
  have hgap : 0 < chi (g '' H) - γ * chi H := sub_pos.mpr (lt_of_not_ge hnot)
  have hh := happrox ((chi (g '' H) - γ * chi H) / 2) (half_pos hgap)
  linarith

end Tingley

end

end OAI
