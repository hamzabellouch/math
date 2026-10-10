import OAI.Dynamics.StandardMap.CocycleAlgebra

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma PlaneAreaPreserving.injective {A : ℂ →L[ℝ] ℂ} (hA : PlaneAreaPreserving A) :
    Function.Injective A := by
  intro x y hxy
  have hh:=hA.norm_lower (x-y)
  rw [map_sub,hxy,sub_self,norm_zero,mul_zero] at hh
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hh (norm_nonneg _)))
lemma PlaneAreaPreserving.surjective {A : ℂ →L[ℝ] ℂ} (hA : PlaneAreaPreserving A) :
    Function.Surjective A := LinearMap.surjective_of_injective (f := A.toLinearMap) hA.injective

lemma transfer_angle_bounds {A B C : ℂ →L[ℝ] ℂ}
    (hA : PlaneAreaPreserving A) (hB : PlaneAreaPreserving B) (hC : PlaneAreaPreserving C)
    (he : ∀ z, C (B z)=A z)
    (a b : ℂ) (ha : ‖a‖=1) (hb : ‖b‖=1) (hAa : ‖A a‖=‖A‖) (hBb : ‖B b‖=‖B‖) :
    max |wedge a b| (max (‖A‖⁻¹^2) (‖B‖⁻¹^2)) ≤ ‖C‖/(‖A‖*‖B‖) ∧
    ‖C‖/(‖A‖*‖B‖) ≤ |wedge a b|+‖A‖⁻¹^2+‖B‖⁻¹^2 := by
  have hDA : 1 ≤ ‖A‖ := hA.singular_pair.choose_spec.2.2.2.2
  have hDB : 1 ≤ ‖B‖ := hB.singular_pair.choose_spec.2.2.2.2
  have hAp : 0 < ‖A‖ := by linarith
  have hBp : 0 < ‖B‖ := by linarith
  have hbperp : ‖B (quarterTurn b)‖=‖B‖⁻¹ := by
    have hs:=hB.norm_map_sq b hb hBb (quarterTurn b)
    rw [dot_quarterTurn,wedge_quarterTurn,hb] at hs
    apply (sq_eq_sq₀ (norm_nonneg _) (inv_nonneg.mpr (norm_nonneg _))).mp
    simpa using hs
  have angle : ‖A‖*|wedge a b| ≤ ‖C‖*‖B‖⁻¹ := by
    have hh:=expanded_projection_bound hA a ha hAa (quarterTurn b)
    rw [dot_quarterTurn_right,abs_neg,← he] at hh
    exact hh.trans (by simpa [hbperp] using C.le_opNorm (B (quarterTurn b)))
  have normAB : ‖A‖ ≤ ‖C‖*‖B‖ := hB.norm_le_product he
  have normBA : ‖B‖ ≤ ‖C‖*‖A‖ := by
    apply B.opNorm_le_bound (by positivity)
    intro z
    have hh:=hC.norm_lower (B z)
    rw [he] at hh
    calc
      _ ≤ ‖C‖*‖A z‖ := hh
      _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (A.le_opNorm z) (norm_nonneg C)
  have upper : ‖C‖ ≤ ‖A‖/‖B‖+‖A‖*‖B‖*|wedge a b|+‖B‖/‖A‖ := by
    apply C.opNorm_le_bound (by positivity)
    intro z
    obtain ⟨y,rfl⟩:=hB.surjective z
    rw [he]
    have hdot : |dot b y| ≤ ‖B y‖/‖B‖ := by
      apply (le_div_iff₀ hBp).mpr
      simpa [mul_comm] using expanded_projection_bound hB b hb hBb y
    have hwedge : |wedge b y| ≤ ‖B‖*‖B y‖ := by
      have hh : |wedge b y| ≤ ‖y‖ := by simpa only [hb,one_mul] using abs_wedge_le_norm_mul b y
      exact hh.trans (hB.norm_lower y)
    have hwb : |wedge a (quarterTurn b)| ≤ 1 := by
      simpa [ha,hb,norm_quarterTurn] using abs_wedge_le_norm_mul a (quarterTurn b)
    have hAperp : ‖A (quarterTurn b)‖ ≤ ‖A‖*|wedge a b|+‖A‖⁻¹ := by
      have hh:=two_singular_upper hA a ha hAa (quarterTurn b)
      rw [dot_quarterTurn_right,abs_neg] at hh
      exact hh.trans (add_le_add_right (by simpa using mul_le_mul_of_nonneg_left hwb (inv_nonneg.mpr (norm_nonneg A))) _)
    calc
      ‖A y‖ = ‖dot b y • A b+wedge b y • A (quarterTurn b)‖ := by
        conv_lhs => rw [unit_expansion b y hb]
        rw [map_add,map_smul,map_smul]
      _ ≤ |dot b y| *‖A b‖+|wedge b y| *‖A (quarterTurn b)‖ := by
        simpa only [norm_smul,Real.norm_eq_abs] using norm_add_le (dot b y • A b) (wedge b y • A (quarterTurn b))
      _ ≤ (‖B y‖/‖B‖)*‖A‖+(‖B‖*‖B y‖)*(‖A‖*|wedge a b|+‖A‖⁻¹) := by
        gcongr
        simpa [hb] using A.le_opNorm b
      _ = _ := by ring
  constructor
  · apply max_le
    · apply (le_div_iff₀ (mul_pos hAp hBp)).mpr
      have hh:=mul_le_mul_of_nonneg_right angle hBp.le
      simp only [mul_assoc,inv_mul_cancel₀ hBp.ne',mul_one] at hh
      nlinarith only [hh]
    · apply max_le
      · apply (le_div_iff₀ (mul_pos hAp hBp)).mpr
        apply (mul_le_mul_iff_right₀ hAp).mp
        calc
          _ = ‖B‖ := by field_simp [hAp.ne',hBp.ne']
          _ ≤ _ := by simpa only [mul_comm] using normBA
      · apply (le_div_iff₀ (mul_pos hAp hBp)).mpr
        apply (mul_le_mul_iff_right₀ hBp).mp
        calc
          _ = ‖A‖ := by field_simp [hAp.ne',hBp.ne']
          _ ≤ _ := by simpa only [mul_comm] using normAB
  · apply (div_le_iff₀ (mul_pos hAp hBp)).mpr
    calc
      _ ≤ _ := upper
      _ = _ := by field_simp [hAp.ne',hBp.ne']; ring

lemma normalized_transfer_fourpoint {ι : Type*}
    (A : ι → (ℂ →L[ℝ] ℂ)) (T : ι → ι → (ℂ →L[ℝ] ℂ))
    (hA : ∀ i, PlaneAreaPreserving (A i)) (hT : ∀ i j, PlaneAreaPreserving (T i j))
    (hcomp : ∀ i j z, T i j (A j z)=A i z) (j l p : ι) :
    ‖T j p‖/(‖A j‖*‖A p‖) ≤
      6*max (‖T j l‖/(‖A j‖*‖A l‖)) (‖T l p‖/(‖A l‖*‖A p‖)) := by
  choose a ha hnorm horth hperp hD using fun i => (hA i).singular_pair
  have hs (i q : ι) := transfer_angle_bounds (hA i) (hA q) (hT i q)
    (hcomp i q) (a i) (a q) (ha i) (ha q) (hnorm i) (hnorm q)
  have hjl:=hs j l
  have hlp:=hs l p
  have hjp:=hs j p
  have hangle:=wedge_sine_triangle (a j) (a l) (a p) (ha j) (ha l) (ha p)
  have hj : ‖A j‖⁻¹^2 ≤ ‖T j l‖/(‖A j‖*‖A l‖) :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hjl.1)
  have hp : ‖A p‖⁻¹^2 ≤ ‖T l p‖/(‖A l‖*‖A p‖) :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hlp.1)
  have ha1 : |wedge (a j) (a l)| ≤ ‖T j l‖/(‖A j‖*‖A l‖) := (le_max_left _ _).trans hjl.1
  have ha2 : |wedge (a l) (a p)| ≤ ‖T l p‖/(‖A l‖*‖A p‖) := (le_max_left _ _).trans hlp.1
  have hm1 := le_max_left (‖T j l‖/(‖A j‖*‖A l‖)) (‖T l p‖/(‖A l‖*‖A p‖))
  have hm2 := le_max_right (‖T j l‖/(‖A j‖*‖A l‖)) (‖T l p‖/(‖A l‖*‖A p‖))
  have hnon : 0 ≤ max (‖T j l‖/(‖A j‖*‖A l‖)) (‖T l p‖/(‖A l‖*‖A p‖)) := by positivity
  linarith [hjp.2]
end StandardMapEntropy

end OAI
