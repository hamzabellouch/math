import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import OAI.Geometry.NodalSets.Elliptic.SeedCoordinateField
import OAI.Geometry.NodalSets.Spectral.CompactOperatorBounds

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

theorem seedCoordinateField_residual_polynomial_bound {Q U : Set Coord}
    (hQ : IsCompact Q) (hQB : Q ⊆ seedCoordBranch)
    (hU : IsOpen U) (hQU : Q ⊆ U) (hUn : U.Nonempty)
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (hg : ContDiffOn ℝ ∞ g U)
    (hs : ∀ x ∈ U, ∀ u v, g x u v = g x v u)
    (hp : ∀ x ∈ U, ∀ v, v ≠ 0 → 0 < g x v v)
    (w : Coord → ℝ) (hw : ContDiffOn ℝ ∞ w U) (hwp : ∀ x ∈ U, 0 < w x)
    (k : ℕ) :
    ∃ C > 0, ∀ N : ℕ, 0 < N → ∀ x ∈ Q,
      DerivativeBound k (fun z ↦ sourceWeightedOperator g w
        (fun y ↦ (seedCoordinateField N y:ℂ)) z+
          (seedEigenvalue N:ℂ)*(seedCoordinateField N z:ℂ)) x
        (C*(N:ℝ)^(k+4)*Real.exp ((N:ℝ)*seedCoordReal x)) := by
  obtain ⟨C,hC,hbound⟩ := source_residual_compact_derivative_bound hQ hU hQU hUn g hg hs hp w hw hwp k
  obtain ⟨B,hB,hseed⟩ := seedCoordinateField_derivativeBound hQ hQB (k+2)
  refine ⟨(C+10)*B,by positivity,?_⟩
  intro N hN x hx j hj
  have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hn2 : (1:ℝ) ≤ (N:ℝ)^2 := one_le_pow₀ hn
  have hlam : ‖(seedEigenvalue N:ℂ)‖ ≤ 10*(N:ℝ)^2 := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (seedEigenvalue_pos hN)]
    dsimp only [seedEigenvalue]
    nlinarith [mul_nonneg (sub_nonneg.mpr hn) (show (0:ℝ) ≤ N by positivity)]
  have hfactor : C+‖(seedEigenvalue N:ℂ)‖ ≤ (C+10)*(N:ℝ)^2 := by
    nlinarith [mul_le_mul_of_nonneg_left hn2 hC.le]
  have hh := hbound _ (Complex.ofRealCLM.contDiff.comp (seedCoordinateField_smooth N)) x hx
    (B*(N:ℝ)^(k+2)*Real.exp ((N:ℝ)*seedCoordReal x)) (by positivity)
    (hseed N hN x hx) (seedEigenvalue N:ℂ) j hj
  refine hh.trans ?_
  calc
    _ ≤ ((C+10)*(N:ℝ)^2)*(B*(N:ℝ)^(k+2)*Real.exp ((N:ℝ)*seedCoordReal x)) := by gcongr
    _ = _ := by rw [show k+4 = (k+2)+2 by omega,pow_add]; ring

lemma polynomial_envelope_gap {Q : Set Coord} (S S0 : Coord → ℝ)
    {δ : ℝ} (hδ : 0 < δ) (hgap : ∀ x ∈ Q, S0 x+δ ≤ S x)
    (C : ℝ) (hC : 0 ≤ C) (p K : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ x ∈ Q,
      C*(n:ℝ)^p*Real.exp ((n:ℝ)*S0 x) ≤
        ε*(n:ℝ)^(-(K:ℝ))*Real.exp ((n:ℝ)*S x) := by
  have ht : Tendsto (fun n : ℕ ↦ C*((n:ℝ)^(p+K)*Real.exp (-δ*(n:ℝ)))) atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((p+K:ℕ):ℝ) δ hδ).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n:ℝ)) atTop atTop)
    simpa only [Function.comp_def,Real.rpow_natCast,mul_zero] using h.const_mul C
  filter_upwards [ht.eventually (gt_mem_nhds hε),eventually_gt_atTop (0:ℕ)] with n hn hnpos
  intro x hx
  have hn0 : (0:ℝ) < n := by exact_mod_cast hnpos
  have hexp : Real.exp ((n:ℝ)*S0 x) ≤ Real.exp (-δ*(n:ℝ))*Real.exp ((n:ℝ)*S x) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left (hgap x hx) hn0.le
    nlinarith
  have hpow : (n:ℝ)^(p+K)*(n:ℝ)^(-(K:ℝ)) = (n:ℝ)^p := by
    rw [← Real.rpow_natCast,← Real.rpow_add hn0,show ((p+K:ℕ):ℝ)+ -(K:ℝ) = (p:ℝ) by push_cast; ring,
      Real.rpow_natCast]
  calc
    _ ≤ C*(n:ℝ)^p*(Real.exp (-δ*(n:ℝ))*Real.exp ((n:ℝ)*S x)) := by gcongr
    _ = (C*((n:ℝ)^(p+K)*Real.exp (-δ*(n:ℝ))))*
        ((n:ℝ)^(-(K:ℝ))*Real.exp ((n:ℝ)*S x)) := by rw [← hpow]; ring
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hn.le
        (by positivity : 0 ≤ (n:ℝ)^(-(K:ℝ))*Real.exp ((n:ℝ)*S x))

theorem seedCoordinateField_residual_gap_bound {Q U : Set Coord}
    (hQ : IsCompact Q) (hQB : Q ⊆ seedCoordBranch)
    (hU : IsOpen U) (hQU : Q ⊆ U) (hUn : U.Nonempty)
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (hg : ContDiffOn ℝ ∞ g U)
    (hs : ∀ x ∈ U, ∀ u v, g x u v = g x v u)
    (hp : ∀ x ∈ U, ∀ v, v ≠ 0 → 0 < g x v v)
    (w : Coord → ℝ) (hw : ContDiffOn ℝ ∞ w U) (hwp : ∀ x ∈ U, 0 < w x)
    (S : Coord → ℝ) {δ : ℝ} (hδ : 0 < δ) (hgap : ∀ x ∈ Q, seedCoordReal x+δ ≤ S x)
    (k K' : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ x ∈ Q,
      DerivativeBound k (fun z ↦ sourceWeightedOperator g w
        (fun y ↦ (seedCoordinateField N y:ℂ)) z+
          (seedEigenvalue N:ℂ)*(seedCoordinateField N z:ℂ)) x
        (ε*(N:ℝ)^(-(K':ℝ))*Real.exp ((N:ℝ)*S x)) := by
  obtain ⟨C,hC,hb⟩ := seedCoordinateField_residual_polynomial_bound hQ hQB hU hQU hUn g hg hs hp w hw hwp k
  filter_upwards [polynomial_envelope_gap S seedCoordReal hδ hgap C hC.le (k+4) K' hε,
    eventually_gt_atTop (0:ℕ)] with N hsmall hN
  intro x hx j hj
  exact (hb N hN x hx j hj).trans (hsmall x hx)

end
end Yau.Target

end OAI
