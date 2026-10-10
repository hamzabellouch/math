import Mathlib
import OAI.Analysis.CoulombIonization.FormDomain.FormBottom

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
namespace CoulombAtom
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def InUnboundedResolvent (A : H →ₗ.[ℂ] H) (z : ℂ) : Prop :=
  ∃ B : H →L[ℂ] H,
    (∀ y, (B y, y + z • B y) ∈ A.graph) ∧
    ∀ x y, (x, y) ∈ A.graph → B (y - z • x) = x

def unboundedSpectrum (A : H →ₗ.[ℂ] H) : Set ℂ := {z | ¬ InUnboundedResolvent A z}

def inverseShift (R : H →L[ℂ] H) (b : ℝ) : H →ₗ.[ℂ] H :=
  (-(b : ℂ) • (LinearMap.id : H →ₗ[ℂ] H)) +ᵥ inverseOperator R

omit [CompleteSpace H] in
lemma vadd_graph_iff (f : H →ₗ[ℂ] H) (A : H →ₗ.[ℂ] H) (x y : H) :
    (x, y) ∈ (f +ᵥ A).graph ↔ (x, y - f x) ∈ A.graph := by
  simp only [LinearPMap.mem_graph_iff, LinearPMap.vadd_domain]
  constructor
  · rintro ⟨u, rfl, hu⟩
    refine ⟨u, rfl, ?_⟩
    change f u + A u = y at hu
    exact (eq_sub_iff_add_eq).mpr (by simpa only [add_comm] using hu)
  · rintro ⟨u, rfl, hu⟩
    refine ⟨u, rfl, ?_⟩
    change f u + A u = y
    rw [hu]
    abel

omit [CompleteSpace H] in
lemma inverseShift_graph (R : H →L[ℂ] H) (hinj : Function.Injective R) (b : ℝ)
    (x y : H) :
    (x, y) ∈ (inverseShift R b).graph ↔ R (y + (b : ℂ) • x) = x := by
  rw [inverseShift, vadd_graph_iff, inverseOperator_graph hinj]
  change R (y - (-(b : ℂ)) • x) = x ↔ R (y + (b : ℂ) • x) = x
  simp only [neg_smul, sub_neg_eq_add]

omit [CompleteSpace H] in
lemma inverseShift_domain (R : H →L[ℂ] H) (b : ℝ) :
    (inverseShift R b).domain = R.range := by
  rw [inverseShift, LinearPMap.vadd_domain, inverseOperator_domain]

theorem inverseShift_selfAdjoint (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (hinj : Function.Injective R) (b : ℝ) : IsSelfAdjoint (inverseShift R b) := by
  have hd : Dense ((inverseShift R b).domain : Set H) := by
    rw [inverseShift_domain]
    exact selfAdjoint_denseRange hR hinj
  rw [LinearPMap.isSelfAdjoint_def]
  apply LinearPMap.eq_of_eq_graph
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint hd]
  ext p
  rcases p with ⟨x, y⟩
  rw [Submodule.mem_adjoint_iff, inverseShift_graph R hinj]
  constructor
  · intro h
    apply ext_inner_left ℂ
    intro z
    have hz : (R z, z - (b : ℂ) • R z) ∈ (inverseShift R b).graph := by
      rw [inverseShift_graph R hinj]
      simp only [sub_add_cancel]
    have hh := h _ _ hz
    simp only [inner_sub_left, inner_smul_left, Complex.conj_ofReal] at hh
    rw [← R.adjoint_inner_right, ← R.adjoint_inner_right, hR.adjoint_eq] at hh
    rw [map_add, map_smul, inner_add_right, inner_smul_right]
    linear_combination -hh
  · intro h a d had
    have he := (inverseShift_graph R hinj b a d).mp had
    have hs : ⟪R (d + (b : ℂ) • a), y + (b : ℂ) • x⟫_ℂ =
        ⟪d + (b : ℂ) • a, R (y + (b : ℂ) • x)⟫_ℂ :=
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hR) _ _
    rw [he, h] at hs
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      Complex.conj_ofReal] at hs
    linear_combination -hs

omit [CompleteSpace H] in

theorem inverseShift_resolvent_iff (R : H →L[ℂ] H) (hinj : Function.Injective R)
    (b : ℝ) (z : ℂ) :
    InUnboundedResolvent (inverseShift R b) z ↔
      IsUnit (1 - (z + (b : ℂ)) • R) := by
  let t : ℂ := z + (b : ℂ)
  let C : H →L[ℂ] H := 1 - t • R
  have hC (x : H) : C x = x - t • R x := rfl
  constructor
  · rintro ⟨B, hB₁, hB₂⟩
    have hBr (y : H) : R (y + t • B y) = B y := by
      have hh := (inverseShift_graph R hinj b (B y) (y + z • B y)).mp (hB₁ y)
      convert hh using 1
      simp only [t, add_smul, add_assoc]
    have hBc (y : H) : B (C y) = R y := by
      have hg : (R y, y - (b : ℂ) • R y) ∈ (inverseShift R b).graph := by
        rw [inverseShift_graph R hinj]
        simp only [sub_add_cancel]
      have hh := hB₂ _ _ hg
      convert hh using 1
      congr 1
      rw [hC]
      dsimp [t]
      module
    let D : H →L[ℂ] H := 1 + t • B
    have hCD : C * D = 1 := by
      ext y
      change C (y + t • B y) = y
      rw [hC, hBr]
      abel
    have hDC : D * C = 1 := by
      ext y
      change C y + t • B (C y) = y
      rw [hBc, hC]
      abel
    exact ⟨⟨C, D, hCD, hDC⟩, rfl⟩
  · intro h
    obtain ⟨U, hU⟩ := h
    let D : H →L[ℂ] H := ↑U⁻¹
    have hCD : C * D = 1 := by
      change (1 - t • R) * D = 1
      rw [← hU]
      exact U.mul_inv
    have hDC : D * C = 1 := by
      change D * (1 - t • R) = 1
      rw [← hU]
      exact U.inv_mul
    let B : H →L[ℂ] H := D.comp R
    refine ⟨B, ?_, ?_⟩
    · intro y
      rw [inverseShift_graph R hinj]
      have hh := congrArg (fun T : H →L[ℂ] H => T (R y)) hCD
      change C (B y) = R y at hh
      rw [hC] at hh
      rw [map_add, map_add, map_smul, map_smul]
      change (R y + z • R (B y)) + (b : ℂ) • R (B y) = B y
      dsimp [t] at hh
      rw [add_smul] at hh
      rw [← hh]
      module
    · intro x y hxy
      have hh := (inverseShift_graph R hinj b x y).mp hxy
      have he : R (y - z • x) = C x := by
        rw [hC, map_sub, map_smul]
        rw [map_add, map_smul] at hh
        dsimp [t]
        rw [add_smul]
        calc
          R y - z • R x = (R y + (b : ℂ) • R x) - (z • R x + (b : ℂ) • R x) := by module
          _ = x - (z • R x + (b : ℂ) • R x) := by rw [hh]
      change D (R (y - z • x)) = x
      rw [he]
      exact congrArg (fun T : H →L[ℂ] H => T x) hDC

omit [CompleteSpace H] in
lemma unit_one_sub_smul_iff (R : H →L[ℂ] H) {t : ℂ} (ht : t ≠ 0) :
    IsUnit (1 - t • R) ↔ IsUnit (algebraMap ℂ (H →L[ℂ] H) t⁻¹ - R) := by
  have he : (Units.mk0 t ht) • (algebraMap ℂ (H →L[ℂ] H) t⁻¹ - R) = 1 - t • R := by
    change t • (algebraMap ℂ (H →L[ℂ] H) t⁻¹ - R) = 1 - t • R
    rw [Algebra.algebraMap_eq_smul_one, smul_sub, smul_smul, mul_inv_cancel₀ ht, one_smul]
  rw [← he, isUnit_smul_iff]

omit [CompleteSpace H] in
lemma inverseShift_spectrum_iff (R : H →L[ℂ] H) (hinj : Function.Injective R)
    (b : ℝ) {z : ℂ} (hz : z + (b : ℂ) ≠ 0) :
    z ∈ unboundedSpectrum (inverseShift R b) ↔ (z + (b : ℂ))⁻¹ ∈ spectrum ℂ R := by
  change (¬ InUnboundedResolvent (inverseShift R b) z) ↔ _
  rw [inverseShift_resolvent_iff R hinj, spectrum.mem_iff, unit_one_sub_smul_iff R hz]

omit [CompleteSpace H] in
lemma inverseShift_spectrum_ne (R : H →L[ℂ] H) (hinj : Function.Injective R)
    (b : ℝ) {z : ℂ} (hz : z ∈ unboundedSpectrum (inverseShift R b)) :
    z + (b : ℂ) ≠ 0 := by
  intro h
  apply hz
  rw [inverseShift_resolvent_iff R hinj, h]
  simp

omit [CompleteSpace H] in
lemma inverseShift_real_spectrum_iff (R : H →L[ℂ] H) (hinj : Function.Injective R)
    (b : ℝ) {r : ℝ} (hr : r + b ≠ 0) :
    (r : ℂ) ∈ unboundedSpectrum (inverseShift R b) ↔ (r + b)⁻¹ ∈ spectrum ℝ R := by
  rw [inverseShift_spectrum_iff R hinj b (by exact_mod_cast hr)]
  simpa only [Complex.coe_algebraMap, ← Complex.ofReal_add, ← Complex.ofReal_inv] using
    (spectrum.algebraMap_mem_iff ℂ (R := ℝ) (a := R) (r := (r + b)⁻¹))

lemma inverseShift_spectrum_real (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (hinj : Function.Injective R) (b : ℝ) {z : ℂ}
    (hz : z ∈ unboundedSpectrum (inverseShift R b)) : z.im = 0 := by
  have ht := inverseShift_spectrum_ne R hinj b hz
  have hh := (inverseShift_spectrum_iff R hinj b ht).mp hz
  have he := congrArg Inv.inv (hR.mem_spectrum_eq_re hh)
  simp only [inv_inv] at he
  rw [← Complex.ofReal_inv] at he
  have hi := congrArg Complex.im he
  simpa only [Complex.add_im, Complex.ofReal_im, add_zero] using hi

theorem inverseShift_spectral_bottom [Nontrivial H] (R : H →L[ℂ] H)
    (hR : 0 ≤ R) (hinj : Function.Injective R) (b : ℝ) :
    sInf {r : ℝ | (r : ℂ) ∈ unboundedSpectrum (inverseShift R b)} = ‖R‖⁻¹ - b := by
  have hn : 0 < ‖R‖ := injective_norm_pos R hinj
  let S := {r : ℝ | (r : ℂ) ∈ unboundedSpectrum (inverseShift R b)}
  have hmem : ‖R‖⁻¹ - b ∈ S := by
    change ((‖R‖⁻¹ - b : ℝ) : ℂ) ∈ unboundedSpectrum (inverseShift R b)
    rw [inverseShift_real_spectrum_iff R hinj b (by simpa using (inv_ne_zero hn.ne'))]
    simpa only [sub_add_cancel, inv_inv] using CStarAlgebra.norm_mem_spectrum_of_nonneg R hR
  have hl : ∀ r ∈ S, ‖R‖⁻¹ - b ≤ r := by
    intro r hr
    have ht : r + b ≠ 0 := by
      intro he
      apply inverseShift_spectrum_ne R hinj b hr
      exact_mod_cast he
    have hh := (inverseShift_real_spectrum_iff R hinj b ht).mp hr
    have hp : 0 < r + b := lt_of_le_of_ne (inv_nonneg.mp (spectrum_nonneg_of_nonneg hR hh))
      (Ne.symm ht)
    have hb : (r + b)⁻¹ ≤ ‖R‖ := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hp.le)] using
        (spectrum.norm_le_norm_of_mem hh)
    have hm := mul_le_mul_of_nonneg_right hb hp.le
    rw [inv_mul_cancel₀ ht] at hm
    have hi : ‖R‖⁻¹ ≤ r + b := (inv_le_iff_one_le_mul₀' hn).mpr hm
    linarith
  exact le_antisymm (csInf_le ⟨_, hl⟩ hmem) (le_csInf ⟨_, hmem⟩ hl)

end CoulombAtom

end

end OAI
