import OAI.Dynamics.StandardMap.WeightedCompact

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology CompactlySupported Classical
namespace StandardMapEntropy
noncomputable def slowCapOpen : Set DistanceArray :=
  {d | 3/10000 < min (arrayShortfall 0 (dyadicInt 1) d) (arrayShortfall (dyadicInt 1) (dyadicInt 2) d)}
lemma isOpen_slowCapOpen : IsOpen slowCapOpen :=
  isOpen_lt continuous_const ((continuous_arrayShortfall _ _).min (continuous_arrayShortfall _ _))
lemma capG_zero_slowOpen {α:ℝ} {d:DistanceArray} (hd:d∈slowCapOpen) : capG α d=0 := by
  have h1 : 3/10000 < arrayShortfall 0 (dyadicInt 1) d := hd.trans_le (min_le_left _ _)
  have h2 : 3/10000 < arrayShortfall (dyadicInt 1) (dyadicInt 2) d := hd.trans_le (min_le_right _ _)
  have hj:=arrayJ_nonneg 0 (dyadicInt 2) (by norm_num) d
  simp only [arrayJ,dyadicMid_zero_two] at hj
  have h3 : 3/10000 ≤ arrayShortfall 0 (dyadicInt 2) d := by linarith
  simp only [capG,entropyCap_one h1.le,entropyCap_one h2.le,entropyCap_one h3]
  norm_num
lemma affine_shortfall (w:Icc (0:ℝ) 1) (s t:DyadicTime) (hst:(s:ℝ)<(t:ℝ)) :
    arrayShortfall s t (affineArray w)=1-w.val := by
  change 1-w.val*|(t:ℝ)-(s:ℝ)|/((t:ℝ)-(s:ℝ))=1-w.val
  rw [abs_of_pos (sub_pos.mpr hst),mul_div_cancel_right₀ _ (sub_ne_zero.mpr hst.ne')]
lemma affine_mem_slowOpen (w:Icc (0:ℝ) 1) (hw:w.val≤999/1000) : affineArray w∈slowCapOpen := by
  change (3/10000:ℝ) < min _ _
  rw [affine_shortfall _ _ _ (by norm_num),affine_shortfall _ _ _ (by norm_num),min_self]
  linarith
namespace CompactWeightLimit
variable {ι:Type*} {l:Filter ι} [l.NeBot] {μ:ι→Measure DistanceArray} {f:DistanceArray→ℝ}
variable (Q:CompactWeightLimit l μ f)
lemma open_null {U:Set DistanceArray} (hU:IsOpen U)
    (hconv:∀g:C_c(DistanceArray,ℝ),(∀d,0≤g d) → (∀d∉U,g d=0) →
      Tendsto (fun i => ∫d,g d*f d ∂μ i) l (𝓝 0)) : Q.law U=0 := by
  have:=Q.regular
  apply open_null_of_integral_zero Q.law hU
  intro g h0 hz
  exact tendsto_nhds_unique (Q.converges g.toContinuousMap) (hconv g h0 hz)
lemma slow_null {α:ℝ} (h0:∀d,0≤f d) (hb:∀d,f d≤|capG α d|) : Q.law slowCapOpen=0 := by
  apply Q.open_null isOpen_slowCapOpen
  intro g hg hz
  have he:∀d,g d*f d=0 := by
    intro d
    by_cases hd:d∈slowCapOpen
    · have hf:f d=0 := le_antisymm (by simpa [capG_zero_slowOpen hd] using hb d) (h0 d)
      rw [hf,mul_zero]
    · rw [hz d hd,zero_mul]
  simp only [he,integral_zero]
  exact tendsto_const_nhds
end CompactWeightLimit
end StandardMapEntropy

end OAI
