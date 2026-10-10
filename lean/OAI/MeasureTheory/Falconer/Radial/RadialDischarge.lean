import OAI.MeasureTheory.Falconer.Radial.RadialTestMoment
import OAI.MeasureTheory.Falconer.Radial.PublishedRadialMoment
import OAI.MeasureTheory.Falconer.Radial.RadialMomentParameters

namespace OAI

/-! Independent proof of the precise published radial input, using the actual
Euclidean surface measure, orthogonal slices, and smooth approximation. -/
namespace Falconer
open Set MeasureTheory PlanarFalconer
open scoped ENNReal

theorem finite_euclidean_radial_moment (n : ℕ)
    (α : ProbabilityMeasure (Space (n+1))) (β : Measure (Space (n+1))) [IsFiniteMeasure β]
    {K L : Set (Space (n+1))} (hK : IsCompact K) (hL : IsCompact L)
    (hα : ∀ᵐ z ∂(α : Measure (Space (n+1))), z ∈ K) (hβ : ∀ᵐ z ∂β, z ∈ L)
    {s t p q : ℝ} (hs0 : 0 < s) (hs : (n : ℝ) < s) (hsn : s < n+1) (hs2 : s < 2*n)
    (ht : 0 < t) (hpq : p.HolderConjugate q) (hp2 : p < 2)
    (hupt : (2*n-s)*p < t) (htr : t/(2-p) < n)
    (hEα : rieszEnergyOn (α : Measure (Space (n+1))) s < ∞)
    (hEβ : rieszEnergyOn β t < ∞) :
    (∀ᵐ x ∂β, (α : Measure (Space (n+1))).map (radialDirection x) ≪ surfaceMeasure (n+1)) ∧
    (∫⁻ x, ∫⁻ w, ((α : Measure (Space (n+1))).map (radialDirection x)).rnDeriv
      (surfaceMeasure (n+1)) w ^ p ∂surfaceMeasure (n+1) ∂β) < ∞ := by
  let := nullSingletonClass_of_finite_rieszEnergy (α : Measure (Space (n+1))) hs0 hEα
  have hf := finite_euclidean_radial_testNorm_moment n (α : Measure (Space (n+1))) β
    hK hL hα hβ hs0 hs hsn hs2 ht hpq hp2 hupt htr hEα hEβ
  have hm := (surfaceTestNorm_atomless_radial_measurable (α : Measure (Space (n+1))) q).pow_const p
  have ha := ae_lt_top hm hf.ne
  have hN : ∀ᵐ x ∂β, surfaceTestNorm q ((α : Measure (Space (n+1))).map (radialDirection x)) ≠ ∞ := by
    filter_upwards [ha] with x hx he
    simp only [he, ENNReal.top_rpow_of_pos hpq.pos, lt_self_iff_false] at hx
  refine ⟨hN.mono (fun x hx => surfaceTestNorm_absolutelyContinuous _
    (Real.holderConjugate_iff.mp hpq.symm).1.le hx), ?_⟩
  apply lt_of_le_of_lt (lintegral_mono_ae ?_) hf
  filter_upwards [hN] with x hx
  rw [radial_rnDeriv_moment_eq_norm α (surfaceMeasure (n+1)) x hpq.pos]
  exact ENNReal.rpow_le_rpow (surfaceTestNorm_rnDeriv_eLpNorm_le _ hpq hx) hpq.nonneg

theorem published_radial_moment : PublishedRadialMoment := by
  intro n hn α β δ hδ hδ1 hα hβ _hsep hEα hEβ
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  obtain ⟨hs,hsn,ht,_htn,_hut,hp,hpt,hps⟩ := radial_moment_parameters hn1 hδ hδ1
  have hu0 : 0 < 2*(n : ℝ)-((n : ℝ)+δ/2) := by linarith
  have hs0 : 0 < (n : ℝ)+δ/2 := by linarith
  have hs2 : (n : ℝ)+δ/2 < 2*n := by linarith
  have hp2 : 1+δ/(8*(n : ℝ)) < 2 :=
    hpt.trans_le (sub_le_self _ (div_nonneg ht.le hn0.le))
  have hupt : (2*(n : ℝ)-((n : ℝ)+δ/2))*(1+δ/(8*(n : ℝ))) < (n : ℝ)-δ/4 :=
    by simpa only [mul_comm] using (lt_div_iff₀ hu0).mp hps
  have htr : ((n : ℝ)-δ/4)/(2-(1+δ/(8*(n : ℝ)))) < n := by
    apply (div_lt_iff₀ (by linarith)).mpr
    have hh := mul_lt_mul_of_pos_right hpt hn0
    have he : (((n : ℝ)-δ/4)/(n : ℝ))*(n : ℝ) = (n : ℝ)-δ/4 :=
      div_mul_cancel₀ _ hn0.ne'
    nlinarith
  have hpq : (1+δ/(8*(n : ℝ))).HolderConjugate
      ((1+δ/(8*(n : ℝ)))/((1+δ/(8*(n : ℝ)))-1)) :=
    (Real.holderConjugate_iff_eq_conjExponent hp).mpr rfl
  exact finite_euclidean_radial_moment n α (β : Measure (Space (n+1))) hα hβ
    (α : Measure (Space (n+1))).support_mem_ae (β : Measure (Space (n+1))).support_mem_ae
    hs0 hs hsn hs2 ht hpq hp2 hupt htr hEα hEβ

end Falconer

end OAI
