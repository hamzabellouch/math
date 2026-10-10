import Mathlib
import OAI.Analysis.CoulombRadii.Packets.TailMoment
import OAI.Analysis.CoulombRadii.RandomFields.RecordedStatistic
import OAI.Analysis.CoulombRadii.FieldAnalysis.RawRMS

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace Coulomb

lemma radialTailKernel_measurable (r : ℝ) : Measurable (radialTailKernel r) := by
  unfold radialTailKernel
  exact Measurable.ite (measurableSet_le measurable_const continuous_norm.measurable)
    continuous_norm.measurable.inv measurable_const

lemma radialTailStatistic_nonneg {n : ℕ} (r : ℝ) (x : Configuration n) :
    0 ≤ arrayStatistic (radialTailKernel r) x :=
  Finset.sum_nonneg (fun _ _ => radialTailKernel_nonneg _ _)

lemma radialTailStatistic_bound {n : ℕ} {r : ℝ} (hr : 0<r) (x : Configuration n) :
    |arrayStatistic (radialTailKernel r) x| ≤ (n:ℝ)/r := by
  rw [abs_of_nonneg (radialTailStatistic_nonneg _ _)]
  calc
    _ ≤ ∑ _i : Fin n, r⁻¹ := Finset.sum_le_sum (fun i _ => radialTailKernel_le hr _)
    _ = _ := by simp [div_eq_mul_inv]

lemma radialTailStatistic_step {n : ℕ} {r : ℝ} (hr : 0<r) (x : Configuration n) :
    arrayStatistic (radialTailKernel r) x ≤
      r⁻¹*localCount {z : Space | (1/2:ℝ)*r < ‖z‖ ∧ ‖z‖ < 4*r} x+
      arrayStatistic (radialTailKernel (2*r)) x := by
  have H := Finset.sum_le_sum (s:=Finset.univ) (fun (i : Fin n) _ => radialTailKernel_step hr (position x i))
  simpa only [Finset.sum_add_distrib,←Finset.mul_sum,arrayStatistic,localCount] using H

lemma radialTailRMS_step {n : ℕ} (ψ : H1Vector n) {r : ℝ} (hr : 0<r) :
    rawRMS ψ (arrayStatistic (radialTailKernel r)) ≤
      Real.sqrt (localCountSecondMoment ψ {z : Space | (1/2:ℝ)*r < ‖z‖ ∧ ‖z‖ < 4*r})/r+
      rawRMS ψ (arrayStatistic (radialTailKernel (2*r))) := by
  let A : Set Space := {z | (1/2:ℝ)*r < ‖z‖ ∧ ‖z‖ < 4*r}
  have hA : MeasurableSet A := (isOpen_lt continuous_const continuous_norm).measurableSet.inter
    (isOpen_lt continuous_norm continuous_const).measurableSet
  have hb (x : Configuration n) : |r⁻¹*localCount A x| ≤ r⁻¹*(n:ℝ) := by
    rw [abs_mul,abs_of_nonneg (inv_nonneg.mpr hr.le),abs_of_nonneg (localCount_nonneg _ _)]
    exact mul_le_mul_of_nonneg_left (localCount_le _ _) (inv_nonneg.mpr hr.le)
  have ht := radialTailStatistic_bound (n:=n) (show 0<2*r by positivity)
  have hsum (x : Configuration n) : |r⁻¹*localCount A x+arrayStatistic (radialTailKernel (2*r)) x| ≤
      r⁻¹*(n:ℝ)+(n:ℝ)/(2*r) := (abs_add_le _ _).trans (add_le_add (hb x) (ht x))
  have hm1 : Measurable (fun x : Configuration n => r⁻¹*localCount A x) := measurable_const.mul (localCount_measurable hA)
  have hm2 := arrayStatistic_measurable (n:=n) (radialTailKernel_measurable (2*r))
  calc
    _ ≤ rawRMS ψ (fun x => r⁻¹*localCount A x+arrayStatistic (radialTailKernel (2*r)) x) :=
      rawRMS_mono ψ _ _ (arrayStatistic_measurable (radialTailKernel_measurable r)) (hm1.add hm2)
        (radialTailStatistic_bound hr) hsum (radialTailStatistic_nonneg _) (radialTailStatistic_step hr)
    _ ≤ rawRMS ψ (fun x => r⁻¹*localCount A x)+rawRMS ψ (arrayStatistic (radialTailKernel (2*r))) :=
      rawRMS_add ψ _ _ hm1 hm2 hb ht
    _ = _ := by
      rw [rawRMS_const_mul ψ _ (inv_nonneg.mpr hr.le)]
      change r⁻¹ * Real.sqrt (localCountSecondMoment ψ A) + _ = _
      dsimp [A]
      ring

lemma radialTailRMS_cap {n : ℕ} (ψ : H1Vector n) (hm : mass ψ=1) {r : ℝ} (hr : 0<r) :
    rawRMS ψ (arrayStatistic (radialTailKernel r)) ≤ (n:ℝ)/r := by
  calc
    _ ≤ rawRMS ψ (fun _ => (n:ℝ)/r) := rawRMS_mono ψ _ _
      (arrayStatistic_measurable (radialTailKernel_measurable r)) measurable_const
      (radialTailStatistic_bound hr) (fun _ => le_rfl)
      (radialTailStatistic_nonneg _) (fun x => (le_abs_self _).trans (radialTailStatistic_bound hr x))
    _ = _ := rawRMS_const ψ hm (by positivity)

theorem atomic_radial_tail_second_moment : ∃ C : ℝ, 0 ≤ C ∧
    ∀ {J n : ℕ} (S : Nuclei J), (∀ i, S.position i=0) →
    ∀ (ψ : H1Vector n), Antisymmetric ψ → mass ψ=1 →
    ∀ {E δ : ℝ}, (E:EReal) ≤ unrestrictedFormBottom S → form S ψ ≤ E+δ → 0 ≤ δ →
    ∀ {h : ℝ}, 0<h → rawRMS ψ (arrayStatistic (radialTailKernel h)) ≤ C*screenMass δ h/h := by
  obtain ⟨C,hC,H⟩ := atomic_annular_second_moment (α:=(1/2:ℝ)) (β:=4) (by norm_num) (by norm_num)
  refine ⟨4*Real.sqrt C,by positivity,?_⟩
  intro J n S hatom ψ hψ hm E δ hE hstate hδ h hh
  have hmean {r : ℝ} (hr : 0<r) :
      Real.sqrt (localCountSecondMoment ψ {z : Space | (1/2:ℝ)*r < ‖z‖ ∧ ‖z‖ < 4*r}) ≤
        Real.sqrt C*screenMass δ r := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨mul_nonneg (Real.sqrt_nonneg _) (screenMass_pos _ _).le,?_⟩
    rw [mul_pow,Real.sq_sqrt hC]
    exact H S hatom ψ hψ hm hE hstate hδ hr
  let K : ℝ := Real.sqrt C*screenMass δ h/h
  have hK : 0 ≤ K := by exact div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (screenMass_pos _ _).le) hh.le
  have hstep (j : ℕ) : rawRMS ψ (arrayStatistic (radialTailKernel ((2:ℝ)^j*h))) ≤ K*(3/4:ℝ)^j+
      rawRMS ψ (arrayStatistic (radialTailKernel ((2:ℝ)^(j+1)*h))) := by
    have hr : 0 < (2:ℝ)^j*h := by positivity
    have H1 := div_le_div_of_nonneg_right (hmean hr) hr.le
    have H2 := mul_le_mul_of_nonneg_left (screenMass_dyadic_bound hδ hh j) (Real.sqrt_nonneg C)
    have H3 : Real.sqrt (localCountSecondMoment ψ {z : Space | (1/2:ℝ)*((2:ℝ)^j*h) < ‖z‖ ∧ ‖z‖ < 4*((2:ℝ)^j*h)})/((2:ℝ)^j*h) ≤ K*(3/4:ℝ)^j := by
      calc
        _ ≤ Real.sqrt C*screenMass δ ((2:ℝ)^j*h)/((2:ℝ)^j*h) := H1
        _ ≤ K*(3/4:ℝ)^j := by simpa only [K,mul_div_assoc,mul_assoc] using H2
    have He : 2*((2:ℝ)^j*h)=(2:ℝ)^(j+1)*h := by rw [pow_succ]; ring
    exact (radialTailRMS_step ψ hr).trans (by rw [He]; exact add_le_add H3 le_rfl)
  have hfinite (N : ℕ) : rawRMS ψ (arrayStatistic (radialTailKernel h)) ≤
      K*(∑ j∈Finset.range N, (3/4:ℝ)^j)+rawRMS ψ (arrayStatistic (radialTailKernel ((2:ℝ)^N*h))) := by
    induction N with
    | zero => simp
    | succ N ih =>
      have HS := add_le_add (le_refl (K*∑ j∈Finset.range N, (3/4:ℝ)^j)) (hstep N)
      refine ih.trans (HS.trans_eq ?_)
      rw [Finset.sum_range_succ]
      ring
  have hbound (N : ℕ) : rawRMS ψ (arrayStatistic (radialTailKernel h)) ≤ 4*K+((n:ℝ)/h)*(1/2:ℝ)^N := by
    have hs : (∑ j∈Finset.range N, (3/4:ℝ)^j) ≤ 4 := by
      have HH := geom_sum_mul_neg (3/4:ℝ) N
      nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 3/4) N]
    have ht := radialTailRMS_cap ψ hm (show 0 < (2:ℝ)^N*h by positivity)
    have he : (n:ℝ)/((2:ℝ)^N*h)=((n:ℝ)/h)*(1/2:ℝ)^N := by
      rw [div_pow,one_pow]
      field_simp
    exact (hfinite N).trans (by rw [←he]; nlinarith [mul_le_mul_of_nonneg_left hs hK])
  have hlim : Tendsto (fun N : ℕ => 4*K+(n:ℝ)/h*(1/2:ℝ)^N) atTop (𝓝 (4*K)) := by
    convert tendsto_const_nhds.add (tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1))) using 1
    simp
  have Hfinal := ge_of_tendsto' hlim hbound
  dsimp [K] at Hfinal
  exact Hfinal.trans_eq (by ring)

end Coulomb
end

end

end OAI
