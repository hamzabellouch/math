import Mathlib
import OAI.Geometry.PrescribedPotential.CompletedResolvent
import OAI.Geometry.PrescribedPotential.ComplexKernel
import OAI.Geometry.PrescribedPotential.GlobalSmooth

namespace OAI

/-! Quantitative Resolvent. -/

section

 

noncomputable section
open Set Filter Topology
open scoped ContDiff Classical
namespace Anticanonical.SourceSmooth.KaehlerMetric
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [CompactSpace X]
  {A : ComplexAtlas d X}

lemma positive_eigenfunction_nonpos (g : KaehlerMetric A) (φ : SmoothRealFunction A)
    {a : ℝ} (ha : 0 < a)
    (he : ∀ i z, z ∈ (A.chart i).target →
      g.linearizedMongeAmpere φ i z = a * φ.localExpression i z) :
    ∀ x, φ.value x ≤ 0 := by
  intro y
  let : Nonempty X := ⟨y⟩
  obtain ⟨x, _, hx⟩ := isCompact_univ.exists_isMaxOn univ_nonempty φ.continuous.continuousOn
  obtain ⟨i, hi⟩ := A.covers x
  have hn := g.linearized_nonpos_at_globalMax φ (fun z => hx (mem_univ z)) i hi
  rw [he i _ ((A.chart i).mapsTo hi)] at hn
  have hv : φ.localExpression i (A.chart i x) = φ.value x := by
    simp only [SmoothRealFunction.localExpression, Function.comp_apply, (A.chart i).left_inv hi]
  rw [hv] at hn
  exact (hx (mem_univ y)).trans (by nlinarith)

lemma positive_eigenfunction_zero (g : KaehlerMetric A) (φ : SmoothRealFunction A)
    {a : ℝ} (ha : 0 < a)
    (he : ∀ i z, z ∈ (A.chart i).target →
      g.linearizedMongeAmpere φ i z = a * φ.localExpression i z) :
    ∀ x, φ.value x = 0 := by
  have hp := g.positive_eigenfunction_nonpos φ ha he
  have hn := g.positive_eigenfunction_nonpos (φ.realSMul (-1)) ha (by
    intro i z hz
    rw [g.linearizedMongeAmpere_realSMul, he i z hz]
    change -1 * (a * φ.localExpression i z) = a * (-1 * φ.localExpression i z)
    ring)
  intro x
  have hnx : -1 * φ.value x ≤ 0 := hn x
  exact le_antisymm (hp x) (by linarith)

end Anticanonical.SourceSmooth.KaehlerMetric
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [CompactSpace X]
  {A : ComplexAtlas d X}

lemma shifted_complex_kernel (g : KaehlerMetric A) {a : ℝ} (ha : 0 < a)
    (u : Smooth A) (hu : a • u - complexL g u = 0) : u = 0 := by
  have he : complexL g u = a • u := (sub_eq_zero.mp hu).symm
  have hp (p : ℂ →L[ℝ] ℝ) (hpart : ∀ x,
      p (complexL g u x) = (g.laplacian (u.part p)).value x) :
      ∀ x, p (u x) = 0 := by
    apply g.positive_eigenfunction_zero (u.part p) ha
    intro i z hz
    rw [← g.laplacian_localExpression _ i hz]
    change (g.laplacian (u.part p)).value ((A.chart i).symm z) = _
    rw [← hpart, he]
    exact p.map_smul a (u ((A.chart i).symm z))
  have hr := hp Complex.reCLM (fun x => complexL_re g u x)
  have hi := hp Complex.imCLM (fun x => complexL_im g u x)
  ext x
  exact Complex.ext (hr x) (hi x)

variable [T2Space X] {ι : Type*} [Fintype ι]
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)

lemma shiftedOperator_embed (m : ℝ) (f : Smooth A) :
    D.shiftedOperator m (D.localizers.embed 2 f) =
      D.localizers.embed 0 ((m^2 : ℝ) • f - complexL g f) := by
  simp only [shiftedOperator, completedL, sub_apply,
    smul_apply, D.localizers.lower_embed (by norm_num : (0:ℝ) ≤ 2),
    D.localizers.extendCore_embed D.complexL_bound, map_sub, map_smul]

lemma completedResolvent_left (m : ℝ) (hm : 1 ≤ m) (he : ‖D.completedError m hm‖ < 1)
    (v : D.localizers.Sobolev 2) :
    D.completedResolvent m hm he (D.shiftedOperator m v) = v := by
  have hfun : (D.completedResolvent m hm he) ∘ D.shiftedOperator m = id := by
    apply (D.localizers.embed_dense 2).equalizer (by fun_prop) continuous_id
    funext f
    simp only [Function.comp_apply]
    rw [D.shiftedOperator_embed]
    obtain ⟨u, hu⟩ := D.allRegular_smooth (D.completedResolvent_regular m hm he
      ((m^2 : ℝ) • f - complexL g f))
    have hu2 : D.localizers.embed 2 u = D.completedResolvent m hm he
        (D.localizers.embed 0 ((m^2 : ℝ) • f - complexL g f)) := by
      apply D.localizers.lower_injective (by norm_num : (0 : ℝ) ≤ 2)
      rw [D.localizers.lower_embed (by norm_num : (0 : ℝ) ≤ 2), hu]
    have hs := D.completedResolvent_equation m hm he
      (D.localizers.embed 0 ((m^2 : ℝ) • f - complexL g f))
    rw [← hu2, D.shiftedOperator_embed] at hs
    have hh := D.localizers.embed_injective 0 hs
    have hk : (m^2 : ℝ) • (u-f) - complexL g (u-f) = 0 := by
      rw [map_sub, smul_sub]
      calc
        (m^2 : ℝ) • u - (m^2 : ℝ) • f - (complexL g u - complexL g f) =
            ((m^2 : ℝ) • u - complexL g u) - ((m^2 : ℝ) • f - complexL g f) := by abel
        _ = 0 := sub_eq_zero.mpr hh
    have hef : u = f := sub_eq_zero.mp (shifted_complex_kernel g (by positivity) (u-f) hk)
    rw [← hu2, hef]
    rfl
  exact congr_fun hfun v

lemma shiftedOperator_bijective (m : ℝ) (hm : 1 ≤ m) (he : ‖D.completedError m hm‖ < 1) :
    Function.Bijective (D.shiftedOperator m) :=
  ⟨Function.LeftInverse.injective (D.completedResolvent_left m hm he),
    Function.RightInverse.surjective (D.completedResolvent_equation m hm he)⟩

 
theorem elliptic_estimate (m : ℝ) (hm : 1 ≤ m) (he : ‖D.completedError m hm‖ < 1)
    (u : D.localizers.Sobolev 2) :
    ‖u‖ ≤ ‖D.completedResolvent m hm he‖ *
      ((m^2 : ℝ) * ‖D.localizers.lower 2 0 u‖ + ‖D.completedL u‖) := by
  calc
    ‖u‖ = ‖D.completedResolvent m hm he (D.shiftedOperator m u)‖ :=
      congrArg norm (D.completedResolvent_left m hm he u).symm
    _ ≤ ‖D.completedResolvent m hm he‖ * ‖D.shiftedOperator m u‖ :=
      (D.completedResolvent m hm he).le_opNorm _
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg (D.completedResolvent m hm he))
      change ‖(m^2 : ℝ) • D.localizers.lower 2 0 u - D.completedL u‖ ≤ _
      exact (norm_sub_le _ _).trans (by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg m)])

end GluingData
end GlobalElliptic

end
end

end OAI
