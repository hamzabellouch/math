import OAI.Probability.BenjaminiSchramm.SusceptibilityUpper
import OAI.Probability.UnimodularPercolation.Kernel.RussoRows

namespace OAI

open MeasureTheory Filter
open scoped Topology ENNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def realSusceptibility (G : BondGraph V E) (x : V) (t : ℝ) : ℝ :=
  ∑' y, realTwoPoint G x y t

@[simp] theorem realSusceptibility_coe (G : BondGraph V E) (x : V) (p : unitInterval) :
    realSusceptibility G x (p : ℝ) = susceptibility G p x := by
  simp only [realSusceptibility,realTwoPoint_coe,susceptibility]

theorem summable_russoSlope [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x : V) :
    Summable (fun y => russoSlope G x y (p : ℝ)) := by
  exact (summable_russoMajorant G hloc hqt p hp x).of_nonneg_of_le
    (fun y => russoSlope_nonneg G x y p p.2.2)
    (fun y => russoSlope_le_majorant G hloc hqt p p hp le_rfl x y)

theorem hasDerivAt_realSusceptibility [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp0 : 0 < (p : ℝ)) (hp : p < pc G) (x : V) :
    HasDerivAt (realSusceptibility G x) (∑' y, russoSlope G x y (p : ℝ)) p := by
  obtain ⟨b,hpb,hb⟩ := exists_between hp
  apply hasDerivAt_tsum_of_isPreconnected (summable_russoMajorant G hloc hqt b hb x)
    isOpen_Ioo isPreconnected_Ioo
    (fun y t ht => hasDerivAt_realTwoPoint_slope G hloc hqt t
      ⟨ht.1,lt_trans ht.2 hb⟩ x y)
    (fun y t ht => ?_) (show (p : ℝ) ∈ Set.Ioo 0 (b : ℝ) from ⟨hp0,hpb⟩)
    (by simpa only [realTwoPoint_coe] using summable_twoPoint_subcritical G hloc hqt p hp x)
    ⟨hp0,hpb⟩
  let q : unitInterval := ⟨t,ht.1.le,ht.2.le.trans b.2.2⟩
  rw [Real.norm_eq_abs,abs_of_nonneg (russoSlope_nonneg G x y t q.2.2)]
  exact russoSlope_le_majorant G hloc hqt b q hb ht.2.le x y

theorem susceptibility_derivative_upper [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (d : ℕ) (hd : ∀ z, degree G z ≤ d) (p : unitInterval)
    (hp0 : 0 < (p : ℝ)) (hp : p < pc G) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ z, susceptibility G p z ≤ C) (x : V) :
    deriv (realSusceptibility G x) p ≤ (d : ℝ) * C ^ 2 / (1 - p) := by
  rw [(hasDerivAt_realSusceptibility G hloc hqt p hp0 hp x).deriv]
  have hmajor := (summable_russoSlope G hloc hqt p hp x).tsum_le_tsum
    (fun y => russoSlope_le_majorant G hloc hqt p p hp le_rfl x y)
    (summable_russoMajorant G hloc hqt p hp x)
  have hCenn (z : V) : (∑' y, law p {ω | Conn G ω z y}) ≤ ENNReal.ofReal C := by
    rw [←ennreal_susceptibility G hloc hqt p hp z]
    exact ENNReal.ofReal_le_ofReal (hC z)
  have hdiag := russoDiagram_row_bound G hloc d hd p (ENNReal.ofReal C) hCenn x
  have htop : (d : ℝ≥0∞) * ENNReal.ofReal C ^ 2 ≠ ⊤ := by finiteness
  have hreal := ENNReal.toReal_mono htop hdiag
  rw [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal hC0] at hreal
  apply hmajor.trans
  simp only [russoMajorant,tsum_div_const]
  rw [←ENNReal.tsum_toReal_eq (russoDiagram_ne_top G hloc hqt p hp x)]
  exact div_le_div_of_nonneg_right hreal
    (sub_nonneg.mpr p.2.2)

theorem hasDerivAt_realRootSusceptibility [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (p : unitInterval) (hp0 : 0 < (p : ℝ)) (hp : p < pc G) :
    HasDerivAt (realRootSusceptibility G root weight)
      (∑ i, weight i * (∑' y, russoSlope G (root i) y (p : ℝ))) p := by
  have he : realRootSusceptibility G root weight =
      fun t => ∑ i, weight i * realSusceptibility G (root i) t := by
    funext t
    simp only [realRootSusceptibility,rootSusceptibility,susceptibility,
      realSusceptibility,realTwoPoint]
  rw [he]
  exact HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    (hasDerivAt_realSusceptibility G hloc hqt p hp0 hp (root i)).const_mul (weight i))

theorem rootSusceptibility_derivative_upper [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (d : ℕ) (hd : ∀ z, degree G z ≤ d) (c : ℝ) (hc : 0 ≤ c)
    (p : unitInterval) (hp0 : 0 < (p : ℝ)) (hp : p < pc G)
    (hC : ∀ z, susceptibility G p z ≤ c * rootSusceptibility G root weight p) :
    deriv (realRootSusceptibility G root weight) p ≤
      (d : ℝ) * (c * rootSusceptibility G root weight p) ^ 2 / (1 - p) := by
  rw [(hasDerivAt_realRootSusceptibility G hloc hqt root weight p hp0 hp).deriv]
  have hrow (i : ι) : (∑' y, russoSlope G (root i) y (p : ℝ)) ≤
      (d : ℝ) * (c * rootSusceptibility G root weight p) ^ 2 / (1 - p) := by
    have hh := susceptibility_derivative_upper G hloc hqt d hd p hp0 hp
      (c * rootSusceptibility G root weight p)
      (mul_nonneg hc (rootSusceptibility_nonneg G root weight hw p)) hC (root i)
    rwa [(hasDerivAt_realSusceptibility G hloc hqt p hp0 hp (root i)).deriv] at hh
  calc
    _ ≤ ∑ i, weight i *
        ((d : ℝ) * (c * rootSusceptibility G root weight p) ^ 2 / (1 - p)) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hrow i) (hw i))
    _ = _ := by rw [←Finset.sum_mul,hw1,one_mul]

end Percolation.BenjaminiSchramm

end OAI
