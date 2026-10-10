import Mathlib
import OAI.Analysis.CoulombIonization.Model
import OAI.Analysis.CoulombIonization.Fermionic.FreqCut

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
open MeasureTheory Filter
open scoped ENNReal
namespace CoulombLT
lemma dyadic_power_sq (n : ℕ) : ((2:ℝ)^n)^2 = (4:ℝ)^n := by
  rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
  norm_num
lemma dyadic_power_cube (n : ℕ) : ((2:ℝ)^n)^3 = (8:ℝ)^n := by
  rw [← pow_mul, Nat.mul_comm n 3, pow_mul]
  norm_num

lemma dyadic_sum_bound (r : ℝ) (_hr : 0 ≤ r) (M : ℕ) :
    (∑ n ∈ Finset.range M, if (2:ℝ)^n ≤ r then (4:ℝ)^n else 0) ≤ (4/3:ℝ)*r^2 := by
  have hgeom (M : ℕ) :
      (∑ n ∈ Finset.range M, if (2:ℝ)^n ≤ r then (4:ℝ)^n else 0) ≤
        ((4:ℝ)^M-1)/3 := by
    have h := Finset.sum_le_sum (s := Finset.range M)
      (f := fun n => if (2:ℝ)^n ≤ r then (4:ℝ)^n else 0)
      (g := fun n => (4:ℝ)^n) (fun n _ => by split_ifs; rfl; positivity)
    have he := geom_sum_mul (4:ℝ) M
    nlinarith
  induction M with
  | zero => simp; positivity
  | succ M ih =>
    rw [Finset.sum_range_succ]
    split_ifs with h
    · have hp := pow_le_pow_left₀ (by positivity : 0 ≤ (2:ℝ)^M) h 2
      rw [dyadic_power_sq] at hp
      linarith [hgeom M]
    · simpa using ih

lemma dyadic_tsum_bound (r : ℝ) (hr : 0 ≤ r) :
    (∑' n : ℕ, ENNReal.ofReal (if (2:ℝ)^n ≤ r then (4:ℝ)^n else 0)) ≤
      ENNReal.ofReal ((4/3:ℝ)*r^2) := by
  apply ENNReal.tsum_le_of_sum_range_le
  intro M
  rw [← ENNReal.ofReal_sum_of_nonneg (fun n _ => by split_ifs <;> positivity)]
  exact ENNReal.ofReal_le_ofReal (dyadic_sum_bound r hr M)

lemma rpow_two_thirds_cube {r : ℝ} (hr : 0 ≤ r) :
    (r^3) ^ (2/3:ℝ) = r^2 := by
  rw [← Real.rpow_natCast_mul hr]
  norm_num

lemma dyadic_density_bound {ρ : ℝ} (hρ : 0 ≤ ρ) (H : ℕ → ℝ)
    (_hH : ∀ n, 0 ≤ H n)
    (hsplit : ∀ n, ρ ≤ 16*((2:ℝ)^n)^3 + 2*H n) :
    ENNReal.ofReal (ρ^(5/3:ℝ)) ≤
      16*ENNReal.ofReal ρ + 256*(∑' n : ℕ, ENNReal.ofReal ((4:ℝ)^n*H n)) := by
  have hpow : ρ^(5/3:ℝ) = ρ * ρ^(2/3:ℝ) := by
    by_cases hzero : ρ = 0
    · simp [hzero]
    · rw [show (5/3:ℝ) = 1+2/3 by norm_num, Real.rpow_add (lt_of_le_of_ne hρ (Ne.symm hzero)), Real.rpow_one]
  by_cases hsmall : ρ ≤ 64
  · have hp : ρ^(2/3:ℝ) ≤ 16 := by
      calc
        _ ≤ ((4:ℝ)^3)^(2/3:ℝ) := Real.rpow_le_rpow hρ (by norm_num; exact hsmall) (by norm_num)
        _ = 16 := by rw [rpow_two_thirds_cube (by norm_num)]; norm_num
    have h := ENNReal.ofReal_le_ofReal (show ρ^(5/3:ℝ) ≤ 16*ρ by rw [hpow]; nlinarith)
    have he : ENNReal.ofReal (16*ρ) = 16*ENNReal.ofReal ρ := by rw [ENNReal.ofReal_mul (by norm_num)]; norm_num
    rw [he] at h
    exact h.trans (le_add_right le_rfl)
  · have hbig : 1 ≤ ρ/64 := by linarith
    obtain ⟨n,hn,hn'⟩ := exists_nat_pow_near hbig (by norm_num : (1:ℝ)<8)
    have hp : ρ^(2/3:ℝ) ≤ 64*(4:ℝ)^n := by
      have hx : ρ ≤ (8*(2:ℝ)^n)^3 := by
        rw [mul_pow,dyadic_power_cube]
        rw [pow_succ] at hn'
        norm_num only [show (8:ℝ)^3 = 512 by norm_num]
        linarith
      calc
        _ ≤ ((8*(2:ℝ)^n)^3)^(2/3:ℝ) := Real.rpow_le_rpow hρ hx (by norm_num)
        _ = 64*(4:ℝ)^n := by
          rw [rpow_two_thirds_cube (by positivity),mul_pow,dyadic_power_sq]
          norm_num
    have hlow : 64*((2:ℝ)^n)^3 ≤ ρ := by rw [dyadic_power_cube]; linarith
    have hhigh : ρ ≤ 4*H n := by nlinarith [hsplit n]
    have hbound : ρ^(5/3:ℝ) ≤ 256*((4:ℝ)^n*H n) := by
      rw [hpow]
      calc
        _ ≤ ρ*(64*(4:ℝ)^n) := mul_le_mul_of_nonneg_left hp hρ
        _ ≤ (4*H n)*(64*(4:ℝ)^n) := mul_le_mul_of_nonneg_right hhigh (by positivity)
        _ = _ := by ring
    have he : ENNReal.ofReal (256*((4:ℝ)^n*H n)) =
        256*ENNReal.ofReal ((4:ℝ)^n*H n) := by
      rw [ENNReal.ofReal_mul (by norm_num)]; norm_num
    calc
      _ ≤ ENNReal.ofReal (256*((4:ℝ)^n*H n)) := ENNReal.ofReal_le_ofReal hbound
      _ = 256*ENNReal.ofReal ((4:ℝ)^n*H n) := he
      _ ≤ 256*(∑' n : ℕ, ENNReal.ofReal ((4:ℝ)^n*H n)) := by
        gcongr
        exact ENNReal.le_tsum (f := fun index : ℕ => ENNReal.ofReal ((4:ℝ)^index*H index)) n
      _ ≤ _ := le_add_left le_rfl

open CoulombAtom Metric
abbrev Space := EuclideanSpace ℝ (Fin 3)

lemma ball_volume_le (R : ℝ) (hR : 0 ≤ R) :
    (volume : Measure Space).real (ball 0 R) ≤ 8*R^3 := by
  rw [Measure.real,EuclideanSpace.volume_ball_fin_three,ENNReal.toReal_mul,
    ENNReal.toReal_pow,ENNReal.toReal_ofReal hR,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi*4/3)]
  have h := Real.pi_lt_four
  nlinarith [pow_nonneg hR 3]

variable {ι : Type*} [Fintype ι]
def familyDensity (f : ι → Lp ℂ 2 (volume : Measure Space)) (x : Space) : ℝ :=
  ∑ j, ‖f j x‖^2

def highDensity (f : ι → Lp ℂ 2 (volume : Measure Space)) (n : ℕ) (x : Space) : ℝ :=
  ∑ j, ‖f j x - lowPart ((2:ℝ)^n) (f j) x‖^2

lemma familyDensity_nonneg (f : ι → Lp ℂ 2 (volume : Measure Space)) (x : Space) :
    0 ≤ familyDensity f x := Finset.sum_nonneg fun _ _ => sq_nonneg _
lemma highDensity_nonneg (f : ι → Lp ℂ 2 (volume : Measure Space)) (n : ℕ) (x : Space) :
    0 ≤ highDensity f n x := Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma familyDensity_integrable (f : ι → Lp ℂ 2 (volume : Measure Space)) :
    Integrable (familyDensity f) := by
  apply integrable_finsetSum
  intro j _
  exact memLp_two_iff_integrable_sq_norm (Lp.memLp (f j)).aestronglyMeasurable |>.mp (Lp.memLp (f j))

lemma highPart_integrable (R : ℝ) (f : Lp ℂ 2 (volume : Measure Space)) :
    Integrable (fun x => ‖f x - lowPart R f x‖^2) := by
  have hi : (fun x => (f - 𝓕⁻ (freqCut R (𝓕 f)) : Lp ℂ 2 volume) x) =ᵐ[volume]
      (fun x => f x - lowPart R f x) := by
    filter_upwards [Lp.coeFn_sub f (𝓕⁻ (freqCut R (𝓕 f))), lowPart_ae R f] with x hx hy
    simpa only [Pi.sub_apply,hy] using hx
  have hm := MemLp.ae_eq hi (Lp.memLp (f - 𝓕⁻ (freqCut R (𝓕 f))))
  exact (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm

lemma highDensity_integrable (f : ι → Lp ℂ 2 (volume : Measure Space)) (n : ℕ) :
    Integrable (highDensity f n) :=
  integrable_finsetSum Finset.univ (fun j _ => highPart_integrable _ (f j))

lemma familyDensity_pointwise {f : ι → Lp ℂ 2 (volume : Measure Space)}
    (hf : BesselFamily f) (x : Space) :
    ENNReal.ofReal (familyDensity f x ^(5/3:ℝ)) ≤
      16*ENNReal.ofReal (familyDensity f x) +
      256*(∑' n : ℕ, ENNReal.ofReal ((4:ℝ)^n*highDensity f n x)) := by
  apply dyadic_density_bound (familyDensity_nonneg f x) _ (fun n => highDensity_nonneg f n x)
  intro n
  have h := family_density_split f ((2:ℝ)^n) x
  have hb := (hf.low_bound ((2:ℝ)^n) x).trans (ball_volume_le _ (by positivity))
  change familyDensity f x ≤ 16*((2:ℝ)^n)^3 + 2*highDensity f n x
  dsimp [familyDensity,highDensity]
  linarith

lemma highPart_lintegral (R : ℝ) (f : Lp ℂ 2 (volume : Measure Space)) :
    (∫⁻ x, ENNReal.ofReal (‖f x-lowPart R f x‖^2)) =
      ∫⁻ ξ in (ball 0 R)ᶜ, ENNReal.ofReal (‖(𝓕 f : Lp ℂ 2 volume) ξ‖^2) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (highPart_integrable R f)
    (Filter.Eventually.of_forall fun _ => sq_nonneg _),highPart_norm_sq]
  apply ofReal_integral_eq_lintegral_ofReal
  · exact ((memLp_two_iff_integrable_sq_norm (Lp.memLp (𝓕 f)).aestronglyMeasurable).mp
      (Lp.memLp (𝓕 f))).restrict
  · exact Filter.Eventually.of_forall fun _ => sq_nonneg _

lemma highDensity_lintegral (f : ι → Lp ℂ 2 (volume : Measure Space)) (n : ℕ) :
    (∫⁻ x, ENNReal.ofReal (highDensity f n x)) =
      ∫⁻ ξ in (ball 0 ((2:ℝ)^n))ᶜ, ENNReal.ofReal (familyDensity (fun j => 𝓕 (f j)) ξ) := by
  calc
    _ = ∫⁻ x, ∑ j, ENNReal.ofReal (‖f j x - lowPart ((2:ℝ)^n) (f j) x‖^2) := by
      apply lintegral_congr
      intro x
      exact ENNReal.ofReal_sum_of_nonneg (fun j _ => sq_nonneg _)
    _ = ∑ j, ∫⁻ x, ENNReal.ofReal (‖f j x - lowPart ((2:ℝ)^n) (f j) x‖^2) := by
      apply lintegral_finsetSum'
      intro j _
      exact (highPart_integrable _ (f j)).aestronglyMeasurable.aemeasurable.ennreal_ofReal
    _ = ∑ j, ∫⁻ ξ in (ball 0 ((2:ℝ)^n))ᶜ,
        ENNReal.ofReal (‖(𝓕 (f j) : Lp ℂ 2 volume) ξ‖^2) := by
      apply Finset.sum_congr rfl
      intro j _
      exact highPart_lintegral _ (f j)
    _ = ∫⁻ ξ in (ball 0 ((2:ℝ)^n))ᶜ,
        ∑ j, ENNReal.ofReal (‖(𝓕 (f j) : Lp ℂ 2 volume) ξ‖^2) := by
      symm
      apply lintegral_finsetSum'
      intro j _
      exact (((Lp.memLp (𝓕 (f j))).aestronglyMeasurable.norm.pow 2).aemeasurable.ennreal_ofReal).restrict
    _ = _ := by
      apply lintegral_congr
      intro ξ
      exact (ENNReal.ofReal_sum_of_nonneg (fun j _ => sq_nonneg _)).symm

lemma density_mass (f : ι → Lp ℂ 2 (volume : Measure Space)) :
    (∫⁻ x, ENNReal.ofReal (familyDensity f x)) =
      ENNReal.ofReal (∑ j, ‖f j‖^2) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (familyDensity_integrable f)
    (Filter.Eventually.of_forall (familyDensity_nonneg f))]
  congr 1
  change (∫ x, ∑ j, ‖f j x‖^2) = _
  rw [integral_finsetSum Finset.univ (fun j _ =>
    (memLp_two_iff_integrable_sq_norm (Lp.memLp (f j)).aestronglyMeasurable).mp (Lp.memLp (f j)))]
  simp only [← l2_norm_sq_eq_integral]

lemma dyadic_kinetic_bound (f : ι → Lp ℂ 2 (volume : Measure Space)) :
    (∑' n : ℕ, ENNReal.ofReal ((4:ℝ)^n) * ∫⁻ x, ENNReal.ofReal (highDensity f n x)) ≤
      ENNReal.ofReal (4/3:ℝ) *
      ∫⁻ ξ, ENNReal.ofReal (‖ξ‖^2 * familyDensity (fun j => 𝓕 (f j)) ξ) := by
  let d := familyDensity (fun j => 𝓕 (f j))
  have hm : AEMeasurable (fun ξ => ENNReal.ofReal (d ξ)) volume :=
    (familyDensity_integrable _).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hpoint (ξ : Space) :
      (∑' n : ℕ, (ball 0 ((2:ℝ)^n))ᶜ.indicator
        (fun ξ => ENNReal.ofReal ((4:ℝ)^n) * ENNReal.ofReal (d ξ)) ξ) ≤
        ENNReal.ofReal (4/3:ℝ) * ENNReal.ofReal (‖ξ‖^2*d ξ) := by
    have he (n : ℕ) :
        (ball 0 ((2:ℝ)^n))ᶜ.indicator
          (fun ξ => ENNReal.ofReal ((4:ℝ)^n) * ENNReal.ofReal (d ξ)) ξ =
        ENNReal.ofReal (if (2:ℝ)^n ≤ ‖ξ‖ then (4:ℝ)^n else 0) * ENNReal.ofReal (d ξ) := by
      by_cases h : (2:ℝ)^n ≤ ‖ξ‖
      · simp [Set.indicator,Metric.mem_ball,dist_zero_right,not_lt.mpr h,h]
      · simp [Set.indicator,Metric.mem_ball,dist_zero_right,not_le.mp h,h]
    simp_rw [he]
    rw [ENNReal.tsum_mul_right]
    have hb := dyadic_tsum_bound ‖ξ‖ (norm_nonneg ξ)
    calc
      _ ≤ ENNReal.ofReal ((4/3:ℝ)*‖ξ‖^2) * ENNReal.ofReal (d ξ) := by gcongr
      _ = _ := by rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_mul (sq_nonneg _)]; ac_rfl
  calc
    _ = ∑' n : ℕ, ∫⁻ ξ, (ball 0 ((2:ℝ)^n))ᶜ.indicator
        (fun ξ => ENNReal.ofReal ((4:ℝ)^n)*ENNReal.ofReal (d ξ)) ξ := by
      apply tsum_congr
      intro n
      rw [highDensity_lintegral,lintegral_indicator measurableSet_ball.compl,
        lintegral_const_mul'' _ (hm.restrict)]
    _ = ∫⁻ ξ, ∑' n : ℕ, (ball 0 ((2:ℝ)^n))ᶜ.indicator
        (fun ξ => ENNReal.ofReal ((4:ℝ)^n)*ENNReal.ofReal (d ξ)) ξ := by
      symm
      apply lintegral_tsum
      intro n
      exact (hm.const_mul _).indicator measurableSet_ball.compl
    _ ≤ ∫⁻ ξ, ENNReal.ofReal (4/3:ℝ) * ENNReal.ofReal (‖ξ‖^2*d ξ) :=
      lintegral_mono hpoint
    _ = _ := by
      have hm' : AEMeasurable (fun ξ : Space => ENNReal.ofReal (‖ξ‖^2*d ξ)) volume :=
        ((continuous_norm.pow 2).aestronglyMeasurable.mul
          (familyDensity_integrable _).aestronglyMeasurable).aemeasurable.ennreal_ofReal
      exact lintegral_const_mul'' _ hm'

theorem finite_lieb_thirring_lintegral {f : ι → Lp ℂ 2 (volume : Measure Space)}
    (hf : BesselFamily f) :
    (∫⁻ x, ENNReal.ofReal (familyDensity f x ^(5/3:ℝ))) ≤
      16*ENNReal.ofReal (∑ j, ‖f j‖^2) + ENNReal.ofReal (1024/3:ℝ) *
        ∫⁻ ξ, ENNReal.ofReal (‖ξ‖^2 * familyDensity (fun j => 𝓕 (f j)) ξ) := by
  have hm : AEMeasurable (fun x => ENNReal.ofReal (familyDensity f x)) volume :=
    (familyDensity_integrable f).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hH (n : ℕ) : AEMeasurable
      (fun x => ENNReal.ofReal ((4:ℝ)^n* highDensity f n x)) volume :=
    ((highDensity_integrable f n).const_mul _).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hT : AEMeasurable (fun x => ∑' n : ℕ, ENNReal.ofReal ((4:ℝ)^n*highDensity f n x)) volume :=
    AEMeasurable.tsum hH
  calc
    _ ≤ ∫⁻ x, 16*ENNReal.ofReal (familyDensity f x) +
        256*(∑' n : ℕ, ENNReal.ofReal ((4:ℝ)^n*highDensity f n x)) :=
      lintegral_mono (familyDensity_pointwise hf)
    _ = 16*ENNReal.ofReal (∑ j, ‖f j‖^2) +
        256*(∑' n : ℕ, ENNReal.ofReal ((4:ℝ)^n)*∫⁻ x, ENNReal.ofReal (highDensity f n x)) := by
      rw [lintegral_add_left' (hm.const_mul _), lintegral_const_mul'' _ hm,
        density_mass, lintegral_const_mul'' _ hT, lintegral_tsum hH]
      congr 2
      apply tsum_congr
      intro n
      simp_rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (4:ℝ)^n)]
      exact lintegral_const_mul'' _
        (highDensity_integrable f n).aestronglyMeasurable.aemeasurable.ennreal_ofReal
    _ ≤ 16*ENNReal.ofReal (∑ j, ‖f j‖^2) +
        256*(ENNReal.ofReal (4/3:ℝ)*∫⁻ ξ,
          ENNReal.ofReal (‖ξ‖^2*familyDensity (fun j => 𝓕 (f j)) ξ)) := by
      gcongr
      exact dyadic_kinetic_bound f
    _ = _ := by
      rw [← mul_assoc]
      congr 2
      calc
        _ = ENNReal.ofReal ((256:ℝ)*(4/3)) := by
          rw [ENNReal.ofReal_mul (by norm_num)]
          norm_num
        _ = _ := by norm_num
end CoulombLT

end

end OAI
