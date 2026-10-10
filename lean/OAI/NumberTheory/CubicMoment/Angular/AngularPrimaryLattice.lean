import OAI.NumberTheory.CubicMoment.Angular.AngularLatticeCoset
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticHeight

namespace OAI

/-! Cancellation on the actual primary congruence class. The annulus
has zero area, and scaled coset Poisson summation controls every length. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff SchwartzMap
namespace CubicFirstMoment

def primaryAngularLattice (ℓ : ℤ) (W : ℝ → ℂ) (Y : ℝ) : ℂ :=
  ∑' u : PrimaryArgument, theta ℓ u*W (norm u/Y)

lemma angularPlanePhase_pos_mul (ℓ : ℤ) {s : ℝ} (hs : 0 < s) (z : ℂ) :
    angularPlanePhase ℓ ((s:ℂ)*z) = angularPlanePhase ℓ z := by
  rw [angularPlanePhase_mul]
  have he : angularPlanePhase ℓ (s:ℂ) = 1 := by
    simp [angularPlanePhase,Complex.norm_real,abs_of_pos hs,hs.ne']
  rw [he,one_mul]

lemma angularAnnulus_scaled (ℓ : ℤ) (W : ℝ → ℂ) {Y : ℝ} (hY : 0 < Y)
    (a : Eisenstein) :
    angularAnnulus ℓ W (((1/Real.sqrt Y:ℝ):ℂ)*(a:ℂ)) =
      theta ℓ a*W (norm a/Y) := by
  have hs : 0 < 1/Real.sqrt Y := by positivity
  have hn : Complex.normSq (((1/Real.sqrt Y:ℝ):ℂ)*(a:ℂ)) = norm a/Y := by
    rw [Complex.normSq_mul,Complex.normSq_ofReal]
    change (1/Real.sqrt Y)*(1/Real.sqrt Y)*norm a = norm a/Y
    rw [one_div,←mul_inv,←pow_two,Real.sq_sqrt hY.le]
    ring
  rw [angularAnnulus,angularPlanePhase_pos_mul ℓ hs,angularPlanePhase_coe,hn]

lemma primary_scaled_coset (F : ℂ → ℂ) (s : ℂ) :
    (∑' u : PrimaryArgument, F (s*(u:ℂ))) =
      ∑' a : Eisenstein, F (s+(s*3)*(a:ℂ)) := by
  let e := Equiv.ofBijective (primaryCosetMap 1 primary_one)
    (primaryCosetMap_bijective 1 primary_one)
  have he := e.tsum_eq (fun u : PrimaryArgument => F (s*(u:ℂ)))
  change (∑' a : Eisenstein, F (s*((primaryCosetMap 1 primary_one a:PrimaryArgument):ℂ))) = _ at he
  have h3 : ((3:Eisenstein):ℂ) = 3 := map_ofNat eisensteinRing.val 3
  simpa [primaryCosetMap,mul_add,mul_assoc,h3] using he.symm

/-- A strong smooth-coset estimate, sufficient for the elementary
square-divisor inversion in the angular model. -/
theorem primaryAngularLattice_decay {ℓ : ℤ} (hℓ : ℓ ≠ 0)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) :
    ∃ K : ℝ, 0 < K ∧ ∀ Y : ℝ, 0 < Y → ‖primaryAngularLattice ℓ W Y‖ ≤ K/Y := by
  let F := angularAnnulusSchwartz ℓ W hW hpos hsm
  have hF : (∫ z : ℂ, F z) = 0 := integral_angularAnnulus_eq_zero hℓ W
  obtain ⟨C,hC,hbound⟩ := schwartz_zero_area_coset_bound F hF
  refine ⟨9*C,by positivity,?_⟩
  intro Y hY
  let s : ℝ := 1/Real.sqrt Y
  have hs : 0 < s := by dsimp [s]; positivity
  have hq : (s:ℂ)*3 ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hs.ne') (by norm_num)
  have hn : Complex.normSq ((s:ℂ)*3) = 9/Y := by
    rw [Complex.normSq_mul,Complex.normSq_ofReal]
    norm_num
    dsimp [s]
    rw [one_div,←pow_two,inv_pow,Real.sq_sqrt hY.le]
    ring
  have he : primaryAngularLattice ℓ W Y = ∑' u : PrimaryArgument, F ((s:ℂ)*(u:ℂ)) := by
    apply tsum_congr
    intro u
    exact (angularAnnulus_scaled ℓ W hY u).symm
  rw [he,primary_scaled_coset]
  exact (hbound _ hq _).trans_eq (by rw [hn]; ring)

/-- Uniform over the length parameter, including the empty short range. -/
theorem primaryAngularLattice_bounded {ℓ : ℤ} (hℓ : ℓ ≠ 0)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) :
    ∃ K : ℝ, 0 < K ∧ ∀ Y : ℝ, 0 < Y → ‖primaryAngularLattice ℓ W Y‖ ≤ K := by
  obtain ⟨C,hC,hbound⟩ := primaryAngularLattice_decay hℓ W hW hpos hsm
  obtain ⟨S₀,hS₀⟩ := hW.isCompact.isBounded.exists_norm_le
  let S := max S₀ 1
  have hS : 0 < S := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hcut : ∀ x : ℝ, S < x → W x = 0 := by
    intro x hx
    by_contra hn
    have hb := hS₀ x (subset_tsupport W hn)
    rw [Real.norm_eq_abs] at hb
    have hh : S₀ ≤ S := le_max_left _ _
    linarith [le_abs_self x]
  refine ⟨C*S,mul_pos hC hS,?_⟩
  intro Y hY
  by_cases he : 1 ≤ S*Y
  · apply (hbound Y hY).trans
    apply (div_le_iff₀ hY).mpr
    nlinarith
  · have hz : primaryAngularLattice ℓ W Y = 0 := by
      have ht (u : PrimaryArgument) : theta ℓ u*W (norm u/Y) = 0 := by
        have hn := one_le_norm (primary_ne_zero u.property)
        have hw : W (norm u/Y) = 0 := hcut _ ((lt_div_iff₀ hY).mpr ((lt_of_not_ge he).trans_le hn))
        simp only [hw,mul_zero]
      simp only [primaryAngularLattice,ht,tsum_zero]
    rw [hz,norm_zero]
    positivity

end CubicFirstMoment

end

end OAI
