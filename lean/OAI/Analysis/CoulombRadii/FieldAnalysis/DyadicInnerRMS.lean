import Mathlib
import OAI.Analysis.CoulombRadii.Localization.AnnularHistory
import OAI.Analysis.CoulombRadii.RandomFields.InnerFieldRMS

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace Coulomb

theorem annular_dyadic_inner_field : ∀ C₀ : ℝ, 0≤C₀ → ∃ C : ℝ, 0≤C ∧
    ∀ {J n : ℕ} (S : Nuclei J), (∀ i, S.position i=0) →
    ∀ (ψ : H1Vector n), Antisymmetric ψ → mass ψ=1 →
    ∀ {E : ℝ}, (E:EReal)≤unrestrictedFormBottom S → form S ψ≤E →
    ∀ {t : ℝ}, 0<t → ∀ ell : ℕ, ∀ T : RecordedEnsemble n,
      T.Conserves ψ → T.CoreFermionic →
      T.OutSupported {x : Space | ((2:ℝ)^ell*t)/2<‖x‖ ∧ ‖x‖<4*((2:ℝ)^ell*t)} →
      T.totalMass=mass ψ → T.totalForm S≤form S ψ+C₀*screenMass 0 ((2:ℝ)^ell*t)/((2:ℝ)^ell*t)^2 →
      ∀ y : Space, ((2:ℝ)^ell*t)/2≤‖y‖ → ‖y‖≤4*((2:ℝ)^ell*t) →
      Real.sqrt (T.innerSquare S (t/4) y) ≤
        C*screenMass 0 (t/4)*((ell:ℝ)+1)/((2:ℝ)^ell*t) := by
  intro C₀ hC₀
  obtain ⟨Cs,hCs,Hs⟩ := annular_ensemble_positive_field C₀ hC₀
  obtain ⟨Cc,hCc,Hc⟩ := atomic_dyadic_count_RMS
  obtain ⟨Cr,hCr,Hr⟩ := atomic_radial_tail_second_moment
  refine ⟨10*(Cs+5000*Cc+2*Cr),by positivity,?_⟩
  intro J n S hatom ψ hψ hm E hE hstate t ht ell T hlaw hf hsupp hmass hform y hylo hyhi
  let u : ℝ := (2:ℝ)^ell*t
  have hu : 0<u := by dsimp [u]; positivity
  have hpow : (1:ℝ)≤2^ell := one_le_pow₀ (by norm_num)
  have htu : t≤u := by dsimp [u]; nlinarith
  have hh : 0<t/4 := by positivity
  have hhu : t/4≤u := by linarith
  have hhu8 : t/4≤8*u := by linarith
  have Hs1 := Hs S hatom ψ hψ hm hE (by simpa only [add_zero] using hstate)
    (le_refl 0) hu T hlaw hf hsupp hmass hform y hylo hyhi
  have Hs2 : Real.sqrt (T.rawSquare S y (atomicCellScale y))≤Cs*screenMass 0 (t/4)/u :=
    Hs1.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (screenMass_zero_mono hh hhu) hCs) hu.le)
  have Hc1 := Hc S hatom ψ hψ hm hE hstate hh (ell+5)
  have hrad : (2:ℝ)^(ell+5)*(t/4)=8*u := by rw [pow_add]; norm_num; dsimp [u]; ring
  rw [hrad] at Hc1
  have Hr1 := Hr S hatom ψ hψ hm hE (by simpa only [add_zero] using hstate) (le_refl 0) (show 0<8*u by positivity)
  have Hr2 : rawRMS ψ (arrayStatistic (radialTailKernel (8*u)))≤Cr*screenMass 0 (t/4)/u := by
    apply Hr1.trans
    calc
      _ ≤ Cr*screenMass 0 (t/4)/(8*u) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (screenMass_zero_mono hh hhu8) hCr) (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg hCr (screenMass_pos _ _).le) hu (by linarith)
  have Ha := rawRMS_annularAddback ψ hu (t/4)
  have Hab : rawRMS ψ (arrayStatistic (annularAddbackKernel (t/4) u)) ≤
      (5000/u)*(Cc*((ell:ℝ)+5)*screenMass 0 (t/4))+2*(Cr*screenMass 0 (t/4)/u) := by
    apply Ha.trans
    apply add_le_add
    · apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [Nat.cast_add,Nat.cast_ofNat] using Hc1
    · exact mul_le_mul_of_nonneg_left Hr2 (by norm_num)
  have HI := hlaw.innerSquare_addback S hu (show t/4≤u/4 by linarith) hylo hyhi
  have Hfin := HI.trans (mul_le_mul_of_nonneg_left (add_le_add Hs2 Hab) (by norm_num : (0:ℝ)≤2))
  apply Hfin.trans
  have hc : 0≤Cs+5000*Cc+2*Cr := by positivity
  have hel : 0≤(ell:ℝ) := by positivity
  have hcoeff : 2*(Cs+5000*Cc*((ell:ℝ)+5)+2*Cr) ≤
      10*(Cs+5000*Cc+2*Cr)*((ell:ℝ)+1) := by
    nlinarith [mul_nonneg hCs hel,mul_nonneg hCc hel,mul_nonneg hCr hel]
  have H := mul_le_mul_of_nonneg_right hcoeff (div_nonneg (screenMass_pos 0 (t/4)).le hu.le)
  convert H using 1 <;> ring

end Coulomb
end

end

end OAI
