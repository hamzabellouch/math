import Mathlib
import OAI.Combinatorics.UniformKServer.OffsetSuffix
import OAI.Combinatorics.UniformKServer.UniformSlope
import OAI.Combinatorics.UniformKServer.OffsetParameters

namespace OAI

noncomputable section
                                     
section

/-! Uniform absolute squared-log cost for the exact rational-search/dyadic
suffix, with arbitrary repeated starts and arbitrary finite activation delay.
The literal bit-machine implementation is deliberately not asserted here. -/
namespace UniformKServer.OffsetInstance

theorem history_diameter {n k : ℕ} (d : RationalMetric n) (s : Configuration n k)
    (h : History n k) (D : ℝ) (hd : ∀x y,(d.distance x y : ℝ) ≤ D) :
    costAlong d s h ≤ h.length*D := by
  induction h generalizing s with
  | nil => simp [costAlong]
  | cons x h ih =>
    simp only [costAlong,List.length_cons,Nat.cast_add,Nat.cast_one]
    have hh := ih (serve s x.1 x.2)
    have hx := hd (s x.2) x.1
    linarith

open EffectiveLP ComputedInstance
variable (mult : ℕ) (hm : PartitionTree.absoluteRate ≤ (mult : ℝ))
variable {n k : ℕ} [NeZero k]

def slope (k : ℕ) : ℚ := OffsetLP.slope mult k

include hm in
omit [NeZero k] in
theorem rate_bound (hk : 2 ≤ k) :
    PartitionTree.absoluteRate*(Real.log (k+1))^2 ≤ (slope mult k : ℝ) :=
  (OffsetLP.slope_bounds mult k (by omega) hm).1

def restart (hn : 2 ≤ n) (hk : 2 ≤ k) (hkn : k ≤ n) (d : RationalMetric n) : ℕ :=
  OffsetParameters.restart hn hk d (canonical hkn) (slope mult k) (rate_bound mult hm hk)

def cap (hn : 2 ≤ n) (hk : 2 ≤ k) (hkn : k ≤ n) (d : RationalMetric n) : ℕ :=
  OffsetParameters.cap (k:=k) hn d (restart mult hm hn hk hkn d)

include hm in
theorem valid (hk : 2 ≤ k) (hkn : k ≤ n) (d : RationalMetric n) (H : ℕ) :
    OffsetLP.Valid d (canonical hkn) (slope mult k)
      (OffsetTable.flow (H:=H) d (canonical hkn) (slope mult k))
      (OffsetTable.offset d (canonical hkn) (slope mult k) H) := by
  obtain ⟨_,_,h⟩ := OffsetTable.computed_uniform d (canonical hkn) hk (slope mult k)
    (rate_bound mult hm hk)
  exact (h H).1

theorem restart_pos (hn : 2 ≤ n) (hk : 2 ≤ k) (hkn : k ≤ n) (d : RationalMetric n) :
    0 < restart mult hm hn hk hkn d :=
  (OffsetParameters.restart_spec hn hk d (canonical hkn) (slope mult k) (rate_bound mult hm hk)).1

noncomputable def expected (hn : 2 ≤ n) (hk : 2 ≤ k) (hkn : k ≤ n)
    (d : RationalMetric n) (s : Configuration n k) (w : List (Fin n)) : ℝ :=
  OffsetSuffix.expected d (canonical hkn) (slope mult k) (cap mult hm hn hk hkn d)
    (valid mult hm hk hkn d _) s
    (EpochPartition.epochs k (restart mult hm hn hk hkn d) (restart_pos mult hm hn hk hkn d) w)

def endpoint (hn : 2 ≤ n) (hk : 2 ≤ k) (hkn : k ≤ n) (d : RationalMetric n) : ℚ :=
  (2*slope mult k+1)*k*diameter hn d+
    2*OffsetTable.offset d (canonical hkn) (slope mult k) (horizon k (cap mult hm hn hk hkn d))+
      2*diameter hn d

theorem endpoint_nonneg (hn : 2 ≤ n) (hk : 2 ≤ k) (hkn : k ≤ n) (d : RationalMetric n) :
    0 ≤ endpoint mult hm hn hk hkn d := by
  have hs := OffsetLP.slope_nonneg mult k
  have hE := (valid mult hm hk hkn d (horizon k (cap mult hm hn hk hkn d))).1
  have hD : 0 ≤ diameter hn d := by exact_mod_cast (ComputedInstance.parameters hn (NeZero.pos k) d).1
  unfold endpoint slope
  positivity

theorem suffix_bound (hn : 2 ≤ n) (hk : 2 ≤ k) (hkn : k ≤ n) (d : RationalMetric n)
    (pre w : List (Fin n)) (original actual : Configuration n k) :
    expected mult hm hn hk hkn d actual w ≤
      (4*(slope mult k : ℝ)+4)*offlineCost d original (pre++w)+
        (endpoint mult hm hn hk hkn d : ℝ) := by
  obtain ⟨hD,hδ,hdiam,hsep,-⟩ := ComputedInstance.parameters hn (NeZero.pos k) d
  have hspec := OffsetParameters.restart_spec hn hk d (canonical hkn) (slope mult k) (rate_bound mult hm hk)
  have hh := OffsetSuffix.suffix hk d (canonical hkn) (slope mult k)
    (cap mult hm hn hk hkn d) (restart mult hm hn hk hkn d)
    (valid mult hm hk hkn d _) (OffsetLP.slope_nonneg mult k) (restart_pos mult hm hn hk hkn d)
    (diameter hn d : ℝ) (separation hn d : ℝ) hD hδ.le hdiam hsep
    (OffsetParameters.cap_bound hn d (restart mult hm hn hk hkn d))
    (OffsetParameters.overhead_bound hn hk d (canonical hkn) (slope mult k)
      (OffsetLP.slope_nonneg mult k) (restart mult hm hn hk hkn d) hspec) pre w original actual
  simpa only [expected,endpoint,Rat.cast_add,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_natCast,Rat.cast_one] using hh

noncomputable def coefficient : ℝ := 4*(mult : ℝ)*(2/Real.log 2)^2+4/(Real.log 2)^2

theorem coefficient_positive : 0 < coefficient mult := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold coefficient
  positivity

include hm in
omit [NeZero k] in
theorem coefficient_bound (hk : 2 ≤ k) :
    4*(slope mult k : ℝ)+4 ≤ coefficient mult*(Real.log (k+1))^2 := by
  obtain ⟨_,hs⟩ := OffsetLP.slope_bounds mult k (by omega) hm
  have hlog : Real.log 2 ≤ Real.log (k+1) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (show 2 ≤ k+1 by omega))
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsq : (Real.log 2)^2 ≤ (Real.log (k+1))^2 := by nlinarith
  have hb := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 4/(Real.log 2)^2 by positivity)
  have he : 4/(Real.log 2)^2*(Real.log 2)^2=4 := by field_simp [ne_of_gt hl]
  rw [he] at hb
  unfold coefficient slope
  nlinarith only [hs,hb]

noncomputable def delayedCost (hn : 2 ≤ n) (hk : 2 ≤ k) (hkn : k ≤ n)
    (d : RationalMetric n) (s : Configuration n k) (delay : ℕ) (w : List (Fin n)) : ℝ :=
  let gp := prefixTrace (w.take delay)
  costAlong d s gp+expected mult hm hn hk hkn d (finish s gp) (w.drop delay)

theorem delayed_bound (hn : 2 ≤ n) (hk : 2 ≤ k) (hkn : k ≤ n)
    (d : RationalMetric n) (s : Configuration n k) (delay : ℕ) :
    ∃ B : ℝ,0 ≤ B ∧ ∀w : List (Fin n),
      delayedCost mult hm hn hk hkn d s delay w ≤
        coefficient mult*(Real.log (k+1))^2*offlineCost d s w+B := by
  let B : ℝ := (delay:ℝ)*(diameter hn d : ℝ)+(endpoint mult hm hn hk hkn d : ℝ)
  have hD := (ComputedInstance.parameters hn (NeZero.pos k) d).1
  have hE : 0 ≤ (endpoint mult hm hn hk hkn d : ℝ) := by exact_mod_cast endpoint_nonneg mult hm hn hk hkn d
  refine ⟨B,by dsimp [B];positivity,?_⟩
  intro w
  have he := suffix_bound mult hm hn hk hkn d (w.take delay) (w.drop delay) s
    (finish s (prefixTrace (w.take delay)))
  rw [List.take_append_drop] at he
  have hp : costAlong d s (prefixTrace (w.take delay)) ≤ (delay:ℝ)*(diameter hn d : ℝ) := by
    have hb := history_diameter d s (prefixTrace (w.take delay)) (diameter hn d : ℝ)
      (ComputedInstance.parameters hn (NeZero.pos k) d).2.2.1
    have hl : (prefixTrace (k:=k) (w.take delay)).length ≤ delay := by simp [prefixTrace,List.length_take]
    exact hb.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hl) hD)
  have ho : 0 ≤ offlineCost d s w := by
    rw [OfflineDynamic.offline_eq_optRat]
    exact_mod_cast EffectiveLP.opt_nonneg d s w
  have hc := mul_le_mul_of_nonneg_right (coefficient_bound mult hm hk) ho
  change costAlong d s (prefixTrace (w.take delay))+_ ≤ _
  dsimp [B]
  linarith

end UniformKServer.OffsetInstance

end


end

end OAI
