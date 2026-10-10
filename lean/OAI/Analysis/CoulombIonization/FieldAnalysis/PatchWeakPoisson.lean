import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.RetainedFieldIdentity
import OAI.Analysis.CoulombIonization.Variational.CoulombTestCharge
import OAI.Analysis.CoulombIonization.RadialBounds.ShellCoulombDuality

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian
open scoped BigOperators ContDiff

namespace CoulombAnalysis

lemma compact_laplacian_mass {g : TFSpace → ℝ}
    (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g) :
    (∫ x, Δ g x) = 0 := by
  simpa using compact_laplacian_green (f := fun _ => (1 : ℝ)) contDiff_const hg hcg

theorem tfBallPotential_weak_laplacian (R : ℝ) (f : TFLp (ballMeasure R))
    {g : TFSpace → ℝ} (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g)
    (hs : tsupport g ⊆ ball 0 R) :
    (∫ x, tfBallPotential R f x*Δ g x ∂ballMeasure R) =
      -(4*Real.pi)*(∫ x, f x*g x ∂ballMeasure R) := by
  obtain ⟨q,hq,hpot⟩ := exists_patch_density R
    ((tfLaplacian_continuous hg).memLp_of_hasCompactSupport (tfLaplacian_compact hg hcg))
    ((tfLaplacian_support hg).trans hs)
  calc
    _ = tfCoulombL R f q := by
      rw [tfCoulombL_potential]
      exact integral_congr_ae (hq.mono fun x hx => by simp only [hx])
    _ = tfCoulombL R q f := tfCoulombL_symmetric R f q
    _ = ∫ x, tfPotential (Δ g) x*f x ∂ballMeasure R := by
      rw [tfCoulombL_potential]
      simp_rw [hpot]
    _ = -(4*Real.pi)*(∫ x, f x*g x ∂ballMeasure R) := by
      simp_rw [tfPotential_laplacian hg hcg]
      rw [← integral_const_mul]
      congr 1
      funext x
      ring

lemma tfBallPotential_laplacian_integrable (R : ℝ) (f : TFLp (ballMeasure R))
    {g : TFSpace → ℝ} (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g)
    (hs : tsupport g ⊆ ball 0 R) :
    Integrable (fun x => tfBallPotential R f x*Δ g x) (ballMeasure R) := by
  obtain ⟨q,hq,_⟩ := exists_patch_density R
    ((tfLaplacian_continuous hg).memLp_of_hasCompactSupport (tfLaplacian_compact hg hcg))
    ((tfLaplacian_support hg).trans hs)
  exact (tfBallPotential_mul_integrable R f q).congr
    (hq.mono fun x hx => by simp only [hx])

end CoulombAnalysis
namespace CoulombAtom
open CoulombAnalysis

theorem normalizedCoreField_weak_laplacian {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevVector ψ) {g : Space → ℝ}
    (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g) (Z lam : ℝ) :
    (∫ y, normalizedCoreField Z lam ψ y*Δ g y) =
      (Z*formMass ψ*(-(4*Real.pi*g 0))-
        ∑ s, ∑ i : Fin N, ∫ x, ‖ψ.value s x‖^2*(-(4*Real.pi*g (x i))))/formMass ψ := by
  obtain ⟨B,hB⟩ := (tfLaplacian_compact hg hcg).exists_bound_of_continuous (tfLaplacian_continuous hg)
  rw [normalizedCoreField_pairing hψ (tfLaplacian_continuous hg).measurable hcg
    (tfLaplacian_support hg) (fun x => by simpa only [Real.norm_eq_abs] using hB x),
    compact_laplacian_mass hg hcg,mul_zero,sub_zero,tfPotential_laplacian hg hcg]
  simp only [coreDensityInteraction]
  simp_rw [tfPotential_laplacian hg hcg]

theorem normalizedCoreField_weak_harmonic {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevVector ψ) {g : Space → ℝ}
    (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g) (h0 : g 0 = 0)
    (A : Set Space) (hcore : ∀ x i, x i ∉ A → FormZeroAt ψ x)
    (hgA : ∀ z ∈ A, g z = 0) (Z lam : ℝ) :
    (∫ y, normalizedCoreField Z lam ψ y*Δ g y) = 0 := by
  rw [normalizedCoreField_weak_laplacian hψ hg hcg Z lam,h0]
  have hz : ∀ s, ∀ i : Fin N, (∫ x, ‖ψ.value s x‖^2*(-(4*Real.pi*g (x i)))) = 0 := by
    intro s i
    apply integral_eq_zero_of_ae
    filter_upwards [] with x
    by_cases hx : x i ∈ A
    · simp [hgA (x i) hx]
    · simp [(hcore x i hx s).1]
  simp only [hz,Finset.sum_const_zero,mul_zero,neg_zero,sub_self,zero_div]

end CoulombAtom

open MeasureTheory Filter Set Metric Laplacian
open scoped BigOperators ContDiff

namespace CoulombAtom
open CoulombAnalysis

lemma normalizedCoreField_weak_harmonic_ball {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevVector ψ) (A : Set Space)
    (hcore : ∀ x i, x i ∉ A → FormZeroAt ψ x)
    (y : Space) (R : ℝ) (hnuc : (0 : Space) ∉ ball y R)
    (hsep : ∀ a ∈ A, a ∉ ball y R)
    {g : Space → ℝ} (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g)
    (hs : tsupport g ⊆ ball 0 R) (Z lam : ℝ) :
    (∫ x, normalizedCoreField Z lam ψ (y+x)*Δ g x ∂ballMeasure R) = 0 := by
  let G : Space → ℝ := fun z => g (-y+z)
  have hG : ContDiff ℝ 2 G := hg.comp (contDiff_const.add contDiff_id)
  have hcG : HasCompactSupport G := hcg.comp_homeomorph (Homeomorph.addLeft (-y))
  have hz (a : Space) (ha : a ∉ ball y R) : G a = 0 := by
    apply Function.notMem_support.mp
    intro hn
    have hh := hs (subset_tsupport g hn)
    apply ha
    simpa only [mem_ball,dist_eq_norm,sub_zero,neg_add_eq_sub] using hh
  have he := normalizedCoreField_weak_harmonic hψ hG hcG (hz 0 hnuc) A hcore
    (fun a ha => hz a (hsep a ha)) Z lam
  have hl : Δ G = fun z => Δ g (-y+z) := tfLaplacian_translate g (-y)
  rw [hl] at he
  have hi := integral_add_left_eq_self (μ := volume)
    (fun z => normalizedCoreField Z lam ψ z*Δ g (-y+z)) y
  have he' : (∫ x, normalizedCoreField Z lam ψ (y+x)*Δ g x) = 0 := by
    simpa only [neg_add_cancel_left] using hi.trans he
  rw [ballMeasure,← integral_indicator measurableSet_ball]
  convert he' using 1
  congr 1
  funext x
  by_cases hx : x ∈ ball (0 : Space) R
  · simp [hx]
  · have hx0 : Δ g x = 0 := Function.notMem_support.mp
      (fun hh => hx (hs (tfLaplacian_support hg hh)))
    simp [hx,hx0]

end CoulombAtom

end

end OAI
