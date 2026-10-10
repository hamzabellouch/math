import Mathlib
import OAI.Analysis.CoulombRadii.Propagation.UniformScreening
import OAI.Analysis.CoulombRadii.Packets.TailMoment

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
noncomputable section
namespace Coulomb

theorem atomic_radial_tail_uniform : ∃ C : ℝ, 0 ≤ C ∧
    ∀ {J n : ℕ} (S : Nuclei J), (∀ i, S.position i=0) →
    ∀ (ψ : H1Vector n), Antisymmetric ψ → mass ψ=1 →
    ∀ {E δ : ℝ}, (E:EReal) ≤ unrestrictedFormBottom S → form S ψ ≤ E+δ → 0 ≤ δ →
    ∀ {h : ℝ}, 0 < h → radialTailPotential ψ h ≤ C*screenMass δ h/h := by
  obtain ⟨C,hC,H⟩ := atomic_annular_second_moment (α:=(1/2:ℝ)) (β:=4) (by norm_num) (by norm_num)
  refine ⟨4*Real.sqrt C,by positivity,?_⟩
  intro J n S hatom ψ hψ hm E δ hE hstate hδ h hh
  have hmean {r : ℝ} (hr : 0 < r) :
      expectedPopulation ψ {z : Space | (1/2:ℝ)*r < ‖z‖ ∧ ‖z‖ < 4*r} ≤ Real.sqrt C*screenMass δ r := by
    have hA : MeasurableSet {z : Space | (1/2:ℝ)*r < ‖z‖ ∧ ‖z‖ < 4*r} :=
      (isOpen_lt continuous_const continuous_norm).measurableSet.inter (isOpen_lt continuous_norm continuous_const).measurableSet
    have hs := (expectedPopulation_sq_le ψ hA hm).trans (H S hatom ψ hψ hm hE hstate hδ hr)
    rw [←Real.sq_sqrt hC,←mul_pow] at hs
    exact (sq_le_sq₀ (expectedPopulation_nonneg _ _) (mul_nonneg (Real.sqrt_nonneg _) (screenMass_pos _ _).le)).mp hs
  let K : ℝ := Real.sqrt C*screenMass δ h/h
  have hK : 0 ≤ K := by exact div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (screenMass_pos _ _).le) hh.le
  have hstep (j : ℕ) : radialTailPotential ψ ((2:ℝ)^j*h) ≤ K*(3/4:ℝ)^j+
      radialTailPotential ψ ((2:ℝ)^(j+1)*h) := by
    have hr : 0 < (2:ℝ)^j*h := by positivity
    have H1 := div_le_div_of_nonneg_right (hmean hr) hr.le
    have H2 := mul_le_mul_of_nonneg_left (screenMass_dyadic_bound hδ hh j) (Real.sqrt_nonneg C)
    have H3 : expectedPopulation ψ {z : Space | (1/2:ℝ)*((2:ℝ)^j*h) < ‖z‖ ∧ ‖z‖ < 4*((2:ℝ)^j*h)}/((2:ℝ)^j*h) ≤ K*(3/4:ℝ)^j := by
      calc
        _ ≤ Real.sqrt C*screenMass δ ((2:ℝ)^j*h)/((2:ℝ)^j*h) := H1
        _ ≤ K*(3/4:ℝ)^j := by simpa only [K,mul_div_assoc,mul_assoc] using H2
    have He : 2*((2:ℝ)^j*h)=(2:ℝ)^(j+1)*h := by rw [pow_succ]; ring
    exact (radialTailPotential_step ψ hr).trans (by rw [He]; exact add_le_add H3 le_rfl)
  have hfinite (N : ℕ) : radialTailPotential ψ h ≤
      K*(∑ j∈Finset.range N, (3/4:ℝ)^j)+radialTailPotential ψ ((2:ℝ)^N*h) := by
    induction N with
    | zero => simp
    | succ N ih =>
      have HS := add_le_add (le_refl (K*∑ j∈Finset.range N, (3/4:ℝ)^j)) (hstep N)
      refine ih.trans (HS.trans_eq ?_)
      rw [Finset.sum_range_succ]
      ring
  have hbound (N : ℕ) : radialTailPotential ψ h ≤ 4*K+((n:ℝ)/h)*(1/2:ℝ)^N := by
    have hs : (∑ j∈Finset.range N, (3/4:ℝ)^j) ≤ 4 := by
      have HH := geom_sum_mul_neg (3/4:ℝ) N
      nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 3/4) N]
    have ht := radialTailPotential_cap ψ (show 0 < (2:ℝ)^N*h by positivity)
    rw [hm,mul_one] at ht
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

def atomicTailConstant : ℝ := Classical.choose atomic_radial_tail_uniform
lemma atomicTailConstant_nonneg : 0 ≤ atomicTailConstant :=
  (Classical.choose_spec atomic_radial_tail_uniform).1

theorem atomic_radial_tail_bound {J n : ℕ} (S : Nuclei J)
    (hatom : ∀ i, S.position i=0) (ψ : H1Vector n) (hψ : Antisymmetric ψ) (hm : mass ψ=1)
    {E δ : ℝ} (hE : (E:EReal) ≤ unrestrictedFormBottom S) (hstate : form S ψ ≤ E+δ)
    (hδ : 0 ≤ δ) {h : ℝ} (hh : 0 < h) :
    radialTailPotential ψ h ≤ atomicTailConstant*screenMass δ h/h :=
  (Classical.choose_spec atomic_radial_tail_uniform).2 S hatom ψ hψ hm hE hstate hδ hh

end Coulomb
end

end
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
noncomputable section
namespace Coulomb

def atomicInnerField {J n : ℕ} (S : Nuclei J) (ψ : H1Vector n) (h : ℝ) (y : Space) : ℝ :=
  attraction S y-restrictedCorePotential ψ (Metric.ball 0 h) y

lemma far_radial_kernel_bound {y z : Space} (hy : y≠0)
    (hfar : 40*atomicCellScale y ≤ ‖z-y‖) (hz : z≠0) :
    coulombKernel (z-y) ≤ 2501*coulombKernel z := by
  have hy0 := atomicCellScale_pos hy
  have hd : 0 < ‖z-y‖ := lt_of_lt_of_le (by positivity : 0 < 40*atomicCellScale y) hfar
  have hz0 := norm_pos_iff.mpr hz
  have hn := norm_add_le (z-y) y
  rw [sub_add_cancel] at hn
  dsimp only [atomicCellScale] at hfar
  have H : (1:ℝ)/‖z-y‖ ≤ 2501/‖z‖ :=
    (div_le_div_iff₀ hd hz0).mpr (by nlinarith)
  simpa only [div_eq_mul_inv,one_mul,coulombKernel] using H

lemma restrictedCore_far_le_inner_tail {n : ℕ} (ψ : H1Vector n)
    {h : ℝ} (hh : 0 < h) {y : Space} (hy : y≠0) :
    restrictedCorePotential ψ {z | 40*atomicCellScale y ≤ ‖z-y‖} y ≤
      restrictedCorePotential ψ (Metric.ball 0 h) y+2501*radialTailPotential ψ h := by
  let A : Set Space := {z | 40*atomicCellScale y ≤ ‖z-y‖}
  have hA : MeasurableSet A := (isClosed_le continuous_const (by fun_prop)).measurableSet
  have hk (z : Space) : (if z∈A then coulombKernel (z-y) else 0) ≤
      (if z∈Metric.ball 0 h then coulombKernel (z-y) else 0)+2501*radialTailKernel h z := by
    have htail := radialTailKernel_nonneg h z
    by_cases hf : z∈A
    · by_cases hi : z∈Metric.ball 0 h
      · simp only [ite_eq_left hf,ite_eq_left hi]; linarith
      · have hz : h ≤ ‖z‖ := by simpa only [Metric.mem_ball,dist_zero_right,not_lt] using hi
        have hz0 : z≠0 := norm_pos_iff.mp (hh.trans_le hz)
        simp only [ite_eq_left hf,ite_eq_right hi,zero_add,radialTailKernel,ite_eq_left hz]
        exact far_radial_kernel_bound hy hf hz0
    · simp only [ite_eq_right hf]
      exact add_nonneg (by split_ifs <;> first | exact inv_nonneg.mpr (norm_nonneg _) | exact le_rfl) (by positivity)
  rw [radialTailPotential_eq]
  change (∑ s : Spins n, ∑ i : Fin n, ∫ x, if position x i∈A then coulombKernel (position x i-y)*‖ψ.value s x‖^2 else 0) ≤ _
  calc
    _ ≤ ∑ s : Spins n, ∑ i : Fin n, ∫ x,
        (if position x i∈Metric.ball 0 h then coulombKernel (position x i-y)*‖ψ.value s x‖^2 else 0)+
        2501*(radialTailKernel h (position x i)*‖ψ.value s x‖^2) := by
      apply Finset.sum_le_sum; intro s hs
      apply Finset.sum_le_sum; intro i hi
      have hiR : Integrable (fun x =>
          (if position x i∈Metric.ball 0 h then coulombKernel (position x i-y)*‖ψ.value s x‖^2 else 0)+
          2501*(radialTailKernel h (position x i)*‖ψ.value s x‖^2)) := by
        exact (restrictedCore_integrable ψ measurableSet_ball s i y).add
          ((radialTailKernel_integrable ψ h s i).const_mul 2501)
      apply integral_mono (restrictedCore_integrable ψ hA s i y) hiR
      intro x
      have H := mul_le_mul_of_nonneg_right (hk (position x i)) (sq_nonneg ‖ψ.value s x‖)
      simpa only [add_mul,ite_mul,zero_mul,mul_assoc] using H
    _ = _ := by
      simp_rw [integral_add (restrictedCore_integrable ψ measurableSet_ball _ _ y)
        ((radialTailKernel_integrable ψ h _ _).const_mul 2501), integral_const_mul]
      simp only [Finset.sum_add_distrib,←Finset.mul_sum,restrictedCorePotential]

theorem atomic_inner_field_bound {J n : ℕ} (S : Nuclei J)
    (hatom : ∀ i, S.position i=0) (ψ : H1Vector n) (hψ : Antisymmetric ψ) (hm : mass ψ=1)
    {E δ : ℝ} (hE : (E:EReal) ≤ unrestrictedFormBottom S) (hstate : form S ψ ≤ E+δ)
    (hδ : 0 ≤ δ) {h : ℝ} (hh : 0 < h) {y : Space} (hy : y≠0) :
    atomicInnerField S ψ h y ≤
      2*atomicBudgetRecursionC^2*screenFieldUnit δ atomicCountConstant (atomicCellScale y)+
      2501*atomicTailConstant*screenMass δ h/h := by
  have Hb := restrictedCore_far_le_inner_tail ψ hh hy
  have Hr := atomic_expected_raw_field_bound S hatom ψ hψ hm hE hstate hδ hy
  have Ht := atomic_radial_tail_bound S hatom ψ hψ hm hE hstate hδ hh
  dsimp only [atomicInnerField]
  have HM := le_max_left (attraction S y-restrictedCorePotential ψ {z | 40*atomicCellScale y ≤ ‖z-y‖} y) 0
  have Ht' := mul_le_mul_of_nonneg_left Ht (show (0:ℝ) ≤ 2501 by norm_num)
  have he : 2501*(atomicTailConstant*screenMass δ h/h)=2501*atomicTailConstant*screenMass δ h/h := by ring
  rw [he] at Ht'
  linarith

end Coulomb
end

end
end

end OAI
