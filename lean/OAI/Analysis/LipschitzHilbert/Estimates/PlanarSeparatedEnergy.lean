import OAI.Analysis.LipschitzHilbert.Fourier.PlanarSliceFourierSupport
import OAI.Analysis.LipschitzHilbert.Fourier.BandOrthogonality

namespace OAI

/-! Orthogonality of separated reference-frequency strips on the plane.
The proof uses the actual Fourier transform of each affine line slice,
then integrates the one-dimensional Plancherel identity. -/

noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert

theorem schwartz_energy_fourier_disjoint {ι : Type*} [Fintype ι]
    (f : ι → SchwartzMap ℝ ℂ)
    (hdisjoint : ∀ ξ i j, i ≠ j → 𝓕 (f i) ξ = 0 ∨ 𝓕 (f j) ξ = 0) :
    (∫ x, ‖∑ i, f i x‖^2) = ∑ i, ∫ x, ‖f i x‖^2 := by
  let F : SchwartzMap ℝ ℂ := ∑ i, f i
  have hsum (x : ℝ) : F x = ∑ i, f i x := by simp [F]
  have hfourier (ξ : ℝ) : 𝓕 F ξ = ∑ i, 𝓕 (f i) ξ := by
    change (SchwartzMap.fourierTransformCLM ℂ (∑ i, f i)) ξ = _
    rw [map_sum]
    simp
  calc
    _ = ∫ x, ‖F x‖^2 := by simp only [hsum]
    _ = ∫ ξ, ‖𝓕 F ξ‖^2 := (SchwartzMap.integral_norm_sq_fourier F).symm
    _ = ∫ ξ, ∑ i, ‖𝓕 (f i) ξ‖^2 := by
      apply integral_congr_ae
      filter_upwards [] with ξ
      rw [hfourier,norm_sum_square_of_disjoint _ (hdisjoint ξ)]
    _ = ∑ i, ∫ ξ, ‖𝓕 (f i) ξ‖^2 :=
      integral_finsetSum _ (fun i _ => ((𝓕 (f i)).memLp 2).integrable_norm_pow (by decide))
    _ = _ := by simp only [SchwartzMap.integral_norm_sq_fourier]

theorem planar_energy_of_slice_fourier_disjoint {ι : Type*} [Fintype ι]
    (f : ι → SchwartzMap (ℝ×ℝ) ℂ) (slope : ℝ)
    (hdisjoint : ∀ y ξ i j, i ≠ j →
      𝓕 (planarSchwartzSlice (f i) y slope) ξ = 0 ∨
        𝓕 (planarSchwartzSlice (f j) y slope) ξ = 0) :
    (∫ z, ‖∑ i, f i z‖^2 ∂volume.prod volume) =
      ∑ i, ∫ z, ‖f i z‖^2 ∂volume.prod volume := by
  let F : SchwartzMap (ℝ×ℝ) ℂ := ∑ i, f i
  have hF (z : ℝ×ℝ) : F z = ∑ i, f i z := by simp [F]
  have hi (i : ι) : Integrable
      (fun z => ‖f i (slopeShear slope z)‖^2) (volume.prod volume) :=
    (slopeShear_measurePreserving slope).integrable_comp_of_integrable
      (((f i).memLp 2 (volume.prod volume)).integrable_norm_pow (by decide : 2 ≠ 0))
  have hFi : Integrable (fun z => ‖F (slopeShear slope z)‖^2) (volume.prod volume) :=
    (slopeShear_measurePreserving slope).integrable_comp_of_integrable
      ((F.memLp 2 (volume.prod volume)).integrable_norm_pow (by decide : 2 ≠ 0))
  have hline (y : ℝ) : (∫ x, ‖F (x,y+slope*x)‖^2) =
      ∑ i, ∫ x, ‖f i (x,y+slope*x)‖^2 := by
    simpa only [hF,planarSchwartzSlice_apply] using
      schwartz_energy_fourier_disjoint (fun i => planarSchwartzSlice (f i) y slope)
        (hdisjoint y)
  calc
    _ = ∫ z, ‖F z‖^2 ∂volume.prod volume := by simp only [hF]
    _ = ∫ z, ‖F (slopeShear slope z)‖^2 ∂volume.prod volume :=
      (integral_slopeShear slope (fun z => ‖F z‖^2)).symm
    _ = ∫ y, ∫ x, ‖F (x,y+slope*x)‖^2 := integral_prod_symm _ hFi
    _ = ∫ y, ∑ i, ∫ x, ‖f i (x,y+slope*x)‖^2 := by simp_rw [hline]
    _ = ∑ i, ∫ y, ∫ x, ‖f i (x,y+slope*x)‖^2 :=
      integral_finsetSum _ (fun i _ => (hi i).integral_prod_right)
    _ = ∑ i, ∫ z, ‖f i (slopeShear slope z)‖^2 ∂volume.prod volume := by
      apply Finset.sum_congr rfl
      intro i _
      exact (integral_prod_symm _ (hi i)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      exact integral_slopeShear slope (fun z => ‖f i z‖^2)

theorem planar_separated_strip_energy {N : ℕ}
    (f : Fin N → SchwartzMap (ℝ×ℝ) ℂ) (slope : ℝ) (lo hi : Fin N → ℝ)
    (hgap : ∀ i j, i < j → hi i < lo j)
    (hspectrum : ∀ i ξ η, planarFourier (f i) (ξ,η) ≠ 0 →
      lo i ≤ |ξ+slope*η| ∧ |ξ+slope*η| ≤ hi i) :
    (∫ z, ‖∑ i, f i z‖^2 ∂volume.prod volume) =
      ∑ i, ∫ z, ‖f i z‖^2 ∂volume.prod volume := by
  apply planar_energy_of_slice_fourier_disjoint f slope
  intro y ξ i j hij
  have hout (i : Fin N) (hξ : |ξ| < lo i ∨ hi i < |ξ|) :
      𝓕 (planarSchwartzSlice (f i) y slope) ξ = 0 := by
    apply planarSchwartzSlice_fourier_eq_zero
    intro η
    by_contra hne
    have hs := hspectrum i (ξ-slope*η) η hne
    have he : ξ-slope*η+slope*η = ξ := by ring
    rw [he] at hs
    rcases hξ with hl | hu
    · exact (not_lt_of_ge hs.1) hl
    · exact (not_lt_of_ge hs.2) hu
  rcases lt_or_gt_of_ne hij with hij | hji
  · by_cases hj : |ξ| < lo j
    · exact Or.inr (hout j (Or.inl hj))
    · exact Or.inl (hout i (Or.inr ((hgap i j hij).trans_le (le_of_not_gt hj))))
  · by_cases hi : |ξ| < lo i
    · exact Or.inl (hout i (Or.inl hi))
    · exact Or.inr (hout j (Or.inr ((hgap j i hji).trans_le (le_of_not_gt hi))))

theorem planar_separated_strip_vector_energy {N : ℕ} {κ : Type*} [Fintype κ]
    (f : Fin N → κ → SchwartzMap (ℝ×ℝ) ℂ) (slope : ℝ) (lo hi : Fin N → ℝ)
    (hgap : ∀ i j, i < j → hi i < lo j)
    (hspectrum : ∀ i k ξ η, planarFourier (f i k) (ξ,η) ≠ 0 →
      lo i ≤ |ξ+slope*η| ∧ |ξ+slope*η| ≤ hi i) :
    (∫ z, ‖∑ j, (WithLp.toLp 2 (fun k => f j k z) : EuclideanSpace ℂ κ)‖^2
      ∂volume.prod volume) =
      ∑ j, ∫ z, ‖(WithLp.toLp 2 (fun k => f j k z) : EuclideanSpace ℂ κ)‖^2
        ∂volume.prod volume := by
  simp only [EuclideanSpace.norm_sq_eq,WithLp.ofLp_sum,Finset.sum_apply]
  have hs (k : κ) : Integrable (fun z => ‖∑ j, f j k z‖^2) (volume.prod volume) := by
    let F : SchwartzMap (ℝ×ℝ) ℂ := ∑ j, f j k
    have heq (z : ℝ×ℝ) : F z = ∑ j, f j k z := by simp [F]
    simpa only [heq] using (F.memLp 2 (volume.prod volume)).integrable_norm_pow (by decide : 2 ≠ 0)
  rw [integral_finsetSum _ (fun k _ => hs k)]
  simp_rw [planar_separated_strip_energy (fun j => f j _) slope lo hi hgap
    (fun i ξ η => hspectrum i _ ξ η)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  exact (integral_finsetSum _ (fun k _ =>
    ((f j k).memLp 2 (volume.prod volume)).integrable_norm_pow (by decide : 2 ≠ 0))).symm

end LipschitzHilbert

end

end OAI
