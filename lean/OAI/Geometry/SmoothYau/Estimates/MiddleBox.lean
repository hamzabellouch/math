import Mathlib

namespace OAI

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory BoxIntegral
open scoped Topology
namespace YauCounterexamples

def middleBox (I : Box (Fin 3)) : Box (Fin 3) where
  lower i := (3*I.lower i+I.upper i)/4
  upper i := (I.lower i+3*I.upper i)/4
  lower_lt_upper i := by linarith [I.lower_lt_upper i]

lemma middleBox_Icc_subset (I : Box (Fin 3)) : Box.Icc (middleBox I) ⊆ Box.Ioo I := by
  intro x hx i _
  have hlo := hx.1 i
  have hup := hx.2 i
  change (3*I.lower i+I.upper i)/4 ≤ x i at hlo
  change x i ≤ (I.lower i+3*I.upper i)/4 at hup
  constructor <;> linarith [I.lower_lt_upper i]

lemma middleBox_volume (I : Box (Fin 3)) :
    (volume (Box.Icc (middleBox I))).toReal = (volume (Box.Ioo I)).toReal/8 := by
  rw [←measure_congr (middleBox I).coe_ae_eq_Icc,
    ←measure_congr (I.coe_ae_eq_Icc.trans I.Ioo_ae_eq_Icc.symm)]
  simp only [Box.volume_apply']
  simp only [middleBox]
  rw [Fin.prod_univ_three,Fin.prod_univ_three]
  ring

lemma middleBox_shift_mem (I : Box (Fin 3)) {d : ℝ} (hd : 0 ≤ d)
    (hsmall : ∀ i, d < (I.upper i-I.lower i)/4)
    {x : Fin 3 → ℝ} (hx : x ∈ Box.Icc (middleBox I)) (j : Fin 3) :
    x+Pi.single j d ∈ Box.Ioo I := by
  intro i _
  have hxi := middleBox_Icc_subset I hx i trivial
  have hu := hx.2 i
  change x i ≤ (I.lower i+3*I.upper i)/4 at hu
  by_cases hij : i=j
  · subst i
    simp only [Pi.add_apply,Pi.single_eq_same]
    constructor <;> linarith [hsmall j,hxi.1]
  · simpa only [Pi.add_apply,Pi.single_eq_of_ne hij,add_zero] using hxi

lemma middleBox_eventually_shift_mem (I : Box (Fin 3)) {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ) :
    ∀ᶠ n : ℝ in atTop, ∀ x ∈ Box.Icc (middleBox I), ∀ j : Fin 3,
      x+Pi.single j (ε/(n*ℓ)) ∈ Box.Ioo I := by
  have hd : Tendsto (fun n : ℝ => ε/(n*ℓ)) atTop (𝓝 0) := by
    have ht := (tendsto_const_nhds (x := ε)).mul (tendsto_inv_atTop_zero.mul_const (ℓ⁻¹))
    simpa only [mul_zero,zero_mul,div_eq_mul_inv,mul_inv_rev,mul_comm (ℓ⁻¹)] using ht
  have he : ∀ᶠ n : ℝ in atTop, ∀ j : Fin 3, ε/(n*ℓ) < (I.upper j-I.lower j)/4 := by
    rw [Filter.eventually_all]
    intro j
    exact (tendsto_order.mp hd).2 _ (by linarith [I.lower_lt_upper j])
  filter_upwards [he,eventually_ge_atTop (1:ℝ)] with n hn hn1
  intro x hx j
  exact middleBox_shift_mem I (div_nonneg hε.le (mul_nonneg (by linarith) hℓ.le)) hn hx j

end YauCounterexamples
end

end OAI
