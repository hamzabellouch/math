import OAI.Analysis.PureInfiniteness.FiniteJointSubalgebra
import OAI.Analysis.CStarAlgebra.PureInfiniteness.Cutoffs

namespace OAI

/-! Cutting both factors of a small positive commuting product gives zero.
This is the exact spectral step used to turn tensor excision estimates into
elementary tensors in a closed ideal. -/

noncomputable section
open scoped ComplexOrder IsMulCommutative

namespace WeakPureInfiniteness

theorem commutative_positive_cut_product_zero {D : Type*} [CommCStarAlgebra D]
    [PartialOrder D] [StarOrderedRing D] (a b : D) (ha : 0 ≤ a) (hb : 0 ≤ b)
    {t : ℝ} (ht : 0 < t) (hn : ‖a * b‖ ≤ t ^ 2) :
    cfc (fun x : ℝ => max (x - t) 0) a *
      cfc (fun x : ℝ => max (x - t) 0) b = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm ?_ (norm_nonneg _)
  apply norm_le_of_spectralCharacters _ 0 le_rfl
  intro χ
  let φ := spectralCharacter χ
  let x : ℝ := (φ a).re
  let y : ℝ := (φ b).re
  have hx : 0 ≤ x := (map_nonneg φ ha).1
  have hy : 0 ≤ y := (map_nonneg φ hb).1
  have hxy : x * y ≤ t ^ 2 := by
    have h := (NonUnitalStarAlgHom.norm_apply_le φ.toNonUnitalStarAlgHom (a * b)).trans hn
    change ‖φ (a * b)‖ ≤ t ^ 2 at h
    rw [map_mul, scalarStarHom_eq_real φ ha.isSelfAdjoint,
      scalarStarHom_eq_real φ hb.isSelfAdjoint, ← Complex.ofReal_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hx hy)] at h
    exact h
  have hcut : max (x - t) 0 * max (y - t) 0 = 0 := by
    by_cases hxt : x ≤ t
    · rw [max_eq_right (sub_nonpos.mpr hxt), zero_mul]
    · have hyt : y ≤ t := by
        by_contra h
        have htx : t < x := lt_of_not_ge hxt
        have hty : t < y := lt_of_not_ge h
        nlinarith [mul_pos (sub_pos.mpr htx) (sub_pos.mpr hty)]
      rw [max_eq_right (sub_nonpos.mpr hyt), mul_zero]
  change ‖φ _‖ ≤ 0
  rw [map_mul, scalarStarHom_cfc φ _ a ha.isSelfAdjoint (by fun_prop),
    scalarStarHom_cfc φ _ b hb.isSelfAdjoint (by fun_prop), ← Complex.ofReal_mul]
  change ‖((max (x - t) 0 * max (y - t) 0 : ℝ) : ℂ)‖ ≤ 0
  rw [hcut, Complex.ofReal_zero, norm_zero]

private theorem commutative_mainGap_cut_product_zero {D : Type*} [CommCStarAlgebra D]
    [PartialOrder D] [StarOrderedRing D] (a b : D) (ha : 0 ≤ a) (hb : 0 ≤ b)
    {t : ℝ} (ht : 0 < t) (hn : ‖a * b‖ ≤ t ^ 2) :
    MainGap.cut a t * MainGap.cut b t = 0 := by
  unfold MainGap.cut
  rw [cfcₙ_eq_cfc (hf := by fun_prop) (hf0 := by simp [ht.le]),
    cfcₙ_eq_cfc (hf := by fun_prop) (hf0 := by simp [ht.le])]
  exact commutative_positive_cut_product_zero a b ha hb ht hn

theorem positive_commuting_cut_product_zero {D : Type*} [NonUnitalCStarAlgebra D]
    [PartialOrder D] [StarOrderedRing D] (a b : D) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : Commute a b) {t : ℝ} (ht : 0 < t) (hn : ‖a * b‖ ≤ t ^ 2) :
    MainGap.cut a t * MainGap.cut b t = 0 := by
  let v : Fin 2 → D := ![a, b]
  have hvp (i : Fin 2) : 0 ≤ v i := by
    fin_cases i
    · exact ha
    · exact hb
  have hvc (i j : Fin 2) : Commute (v i) (v j) := by
    fin_cases i <;> fin_cases j
    · exact Commute.refl _
    · exact hc
    · exact hc.symm
    · exact Commute.refl _
  let J := jointSpectralAlgebra v
  let _ : IsMulCommutative J :=
    jointSpectralAlgebra_commutative v (fun i => (hvp i).isSelfAdjoint) hvc
  let _ : CommCStarAlgebra J := inferInstance
  let x : J := jointSpectralGenerator v 0
  let y : J := jointSpectralGenerator v 1
  have hx : 0 ≤ x := jointSpectralGenerator_nonneg v hvp 0
  have hy : 0 ≤ y := jointSpectralGenerator_nonneg v hvp 1
  have hxy : ‖x * y‖ ≤ t ^ 2 := by
    change ‖(a : Unitization ℂ D) * (b : Unitization ℂ D)‖ ≤ t ^ 2
    rw [← Unitization.inr_mul, Unitization.norm_inr]
    exact hn
  have hz : MainGap.cut x t * MainGap.cut y t = 0 :=
    commutative_mainGap_cut_product_zero x y hx hy ht hxy
  let π := J.subtype.toNonUnitalStarAlgHom
  have he := congrArg π hz
  rw [map_mul, MainGap.map_cut π hx ht.le, MainGap.map_cut π hy ht.le, map_zero] at he
  apply Unitization.inr_injective (R := ℂ)
  change (Unitization.inrNonUnitalStarAlgHom ℂ D) (MainGap.cut a t * MainGap.cut b t) =
    (Unitization.inrNonUnitalStarAlgHom ℂ D) 0
  rw [map_mul, MainGap.map_cut _ ha ht.le, MainGap.map_cut _ hb ht.le, map_zero]
  exact he

end WeakPureInfiniteness

end

end OAI
