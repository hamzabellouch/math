import OAI.NumberTheory.CubicMoment.Angular.AngularSmoothShortContinuity
import OAI.NumberTheory.CubicMoment.Estimates.TruncatedProductMoment
import OAI.NumberTheory.CubicMoment.Angular.AngularBalancedSmoothNeighborhood

namespace OAI

/-! Central Mellin transfer preserving the proved conductor neighborhood. -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_balanced_truncated_neighborhood_moment (hpub : PrimitiveAngularHeckeInput) (ℓ : ℤ)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    {D : ℝ} (hD : 0 < D) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/10000 ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ Y₀ : ℝ, ∀ (F Y : ℝ) (X : ι → ℝ)
      (A : ι → EisensteinArithmeticFunction) (q : ι → Eisenstein)
      (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ) (P : Finset (Eisenstein × Eisenstein))
      (V : ℝ → ℂ) (Z : ℝ),
      Y₀ ≤ Y → F ≤ D*Y → (∀ i, ShortArithmeticFactor F (A i)) → (∀ i, 1 ≤ X i) →
      Y/D ≤ ∏ i, X i → (∏ i, X i) ≤ D*Y →
      (∀ i, q i ≠ 0) → (∀ i, AngularUnitCompatible (q i) (η i) ℓ) →
      (∀ i, norm (q i) ≤ Y^(1/100000:ℝ)) → (∀ i, |t i| ≤ Y^(361/1000:ℝ)) →
      (∀ a ∈ P, PrimarySquarefreePair a ∧ norm a.1 ≤ Y^(1/3+κ) ∧
        norm a.2 ≤ Y^(1/3+κ) ∧ Y^(1/1000:ℝ) ≤ norm a.1) → HasCompactSupport V → tsupport V ⊆ Ioi 0 →
      ContDiff ℝ ∞ V → 0 < Z →
      (∑ a : P, ‖∫ τ in Icc (-(Y^(9/25:ℝ))) (Y^(9/25:ℝ)),
        zeroLineMellinWeight V Z τ*
          ∏ i, primaryAngularShortSmoothSum ℓ (A i) (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 (q i) (η i) normPartitionWeight (X i/2) (t i-τ)‖^2) ≤
        (zeroLineMellinMass V)^2*Y^(7/3-ε) := by
  obtain ⟨κ,hκ,hκhi,ε,hε,T,hbound⟩ := angular_balanced_smooth_product_neighborhood hpub ℓ hHuxley
    (fun _ : ι => normPartitionWeight) (fun _ => normPartitionWeight_compact)
    (fun _ => normPartitionWeight_positive_support) (fun _ => normPartitionWeight_smooth)
    (fun _ _ hx => normPartitionWeight_low hx) (fun _ _ hx => normPartitionWeight_high hx)
    (fun _ => normPartitionWeight_norm) hGI hGQ hD
  obtain ⟨T₁,hheight⟩ := eventual_shifted_height_bound
  refine ⟨κ,hκ,hκhi,ε,hε,max 1 (max T T₁),?_⟩
  intro F Y X A q η t P V Z hY hF hA hX hlo hhi hq hη hqY ht hP hV hpos hsm hZ
  have hY1 : 1 ≤ Y := (le_max_left _ _).trans hY
  have hYT : T ≤ Y := (le_max_left _ _).trans ((le_max_right _ _).trans hY)
  have hYT₁ : T₁ ≤ Y := (le_max_right _ _).trans ((le_max_right _ _).trans hY)
  let f : P → ℝ → ℂ := fun a τ =>
    ∏ i, primaryAngularShortSmoothSum ℓ (A i) (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 (q i) (η i) normPartitionWeight (X i/2) (t i-τ)
  have hf (a : P) : Continuous (f a) := by
    apply continuous_finsetProd
    intro i _
    exact (continuous_primaryAngularShortSmoothSum ℓ (A i) (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 (q i) (η i) normPartitionWeight
      (by linarith [hX i]) (fun _ hx => normPartitionWeight_high hx)).comp
        (continuous_const.sub continuous_id)
  have hb (τ : ℝ) (hτ : τ ∈ Icc (-(Y^(9/25:ℝ))) (Y^(9/25:ℝ))) :
      (∑ a : P, ‖f a τ‖^2) ≤ Y^(7/3-ε) := by
    have hτabs : |τ| ≤ Y^(9/25:ℝ) := abs_le.mpr hτ
    have hm := hbound F Y X A q η (fun i => t i-τ) P hYT hF hA hX hlo hhi hq hη hqY
      (fun i => hheight Y hYT₁ (t i) τ (ht i) hτabs) hP
    change (∑ a ∈ P.attach, ‖f a τ‖^2) ≤ _
    dsimp only [f]
    rw [Finset.sum_attach (f := fun a : Eisenstein × Eisenstein =>
      ‖∏ i, primaryAngularShortSmoothSum ℓ (A i) (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 (q i) (η i)
        normPartitionWeight (X i/2) (t i-τ)‖^2)]
    exact hm
  have hm := finite_interval_integral_moment f hf (zeroLineMellinWeight V Z)
    (zeroLineMellinWeight_integrable V hV hpos hsm hZ) (Y^(9/25:ℝ))
    (Y^(7/3-ε)) (Real.rpow_nonneg (zero_le_one.trans hY1) _) hb
  rwa [zeroLineMellinWeight_mass V hZ] at hm

end CubicFirstMoment

end

end OAI
