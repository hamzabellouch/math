import Mathlib
import OAI.Combinatorics.UniformKServer.EpochGeometry
import OAI.Combinatorics.UniformKServer.SideParameters

namespace OAI

                                      
section

/-! Parameters on the actual positive held-size domain of one vector epoch.
These are the geometric hypotheses of the logarithmic proportion minimizer. -/
noncomputable section
namespace UniformKServer.EpochParameters
open Finset
open scoped Classical
variable {ι : Type*} [Fintype ι]

def active (a : ι → ℝ) : Finset ι := by
  classical
  exact univ.filter fun i => 0 < a i

theorem mem_active {a : ι → ℝ} {i : ι} : i ∈ active a ↔ 0 < a i := by
  classical
  simp [active]

theorem active_sum {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) :
    (∑ i : active a, a i) = EpochGeometry.total a := by
  classical
  rw [sum_coe_sort]
  unfold active EpochGeometry.total
  rw [sum_filter]
  apply sum_congr rfl
  intro i _
  split_ifs with h
  · rfl
  · exact le_antisymm (ha i) (not_lt.mp h)

theorem exp_height {A a : ℝ} (hA : 0 < A) (ha : 0 < a) :
    Real.exp (-SideParameters.height A a) = Real.exp (-1)*(a/A) := by
  unfold SideParameters.height
  rw [neg_add,Real.exp_add]
  rw [Real.exp_neg (Real.log (A/a)),Real.exp_log (div_pos hA ha)]
  congr 1
  field_simp

theorem exp_height_le {A a : ℝ} (hA : 0 < A) (ha : 0 < a) :
    Real.exp (-SideParameters.height A a) ≤ a/A := by
  rw [exp_height hA ha]
  exact mul_le_of_le_one_left (div_nonneg ha.le hA.le)
    (Real.exp_le_one_iff.mpr (by norm_num))

theorem regular_height {s : EpochGeometry.State ι} {a : ι → ℝ}
    (hs : EpochGeometry.valid a s) {i : ι} (ha : 0 < a i)
    (hi : EpochGeometry.dominant s ≠ some i) :
    1 ≤ SideParameters.height (EpochGeometry.total s.base) (a i) := by
  have ht := EpochGeometry.total_nonneg hs.1
  have h := EpochGeometry.regular_size hs hi
  exact SideParameters.height_ge_one ha (by linarith)

theorem active_total_pos {s : EpochGeometry.State ι} {a : ι → ℝ}
    (hs : EpochGeometry.valid a s) {i : ι} (ha : 0 < a i) :
    0 < EpochGeometry.total s.base := by
  have hd := EpochGeometry.coordinate_difference s.base a i
  have hb : s.base i ≤ EpochGeometry.total s.base :=
    single_le_sum (fun j _ => hs.1 j) (mem_univ i)
  have hp := le_abs_self (a i-s.base i)
  linarith [hs.2.2.1,hs.2.2.2]

theorem regular_exponential_sum {s : EpochGeometry.State ι} {a : ι → ℝ}
    (hs : EpochGeometry.valid a s) (ha : ∀ i, 0 ≤ a i)
    (hA : 0 < EpochGeometry.total s.base) :
    (∑ i : active a, Real.exp (-SideParameters.height (EpochGeometry.total s.base) (a i))) ≤ 2 := by
  calc
    _ ≤ ∑ i : active a, a i/EpochGeometry.total s.base :=
      sum_le_sum fun i _ => exp_height_le hA (mem_active.mp i.property)
    _ = EpochGeometry.total a/EpochGeometry.total s.base := by rw [←sum_div,active_sum ha]
    _ ≤ 2 := (div_le_iff₀ hA).mpr (by linarith [(EpochGeometry.total_comparison hs).2])

theorem side_nonneg {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (o : ι) :
    0 ≤ EpochGeometry.side o a := by
  classical
  unfold EpochGeometry.side
  exact sum_nonneg fun i _ => by split_ifs <;> first | exact ha i | norm_num

theorem side_coordinate {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) {o i : ι} (hi : i ≠ o) :
    a i ≤ EpochGeometry.side o a := by
  classical
  have h := single_le_sum (s:=univ) (f:=fun j => if j=o then 0 else a j)
    (fun j _ => by split_ifs <;> first | exact ha j | norm_num) (mem_univ i)
  simpa [EpochGeometry.side,hi] using h

def sideReference (a : ι → ℝ) (o : ι) (U : ℝ) : Prop :=
  0 ≤ U ∧ U/(1001/1000) ≤ EpochGeometry.side o a ∧
    EpochGeometry.side o a ≤ (1001/1000)*U

theorem marked_u_upper {s : EpochGeometry.State ι} {a : ι → ℝ} {o : ι} {U : ℝ}
    (hs : EpochGeometry.valid a s) (ho : EpochGeometry.dominant s=some o)
    (hU : sideReference a o U) : U/EpochGeometry.total s.base < 1/4 := by
  have hA := (EpochGeometry.dominant_spec ho).1
  have hd := (EpochGeometry.dominant_size hs ho).2
  have hU' := (div_le_iff₀ (by norm_num : (0:ℝ)<1001/1000)).mp hU.2.1
  apply (div_lt_iff₀ hA).mpr
  linarith

/-- The logarithmic side weight controls the approaching-simplex-vertex height.
The estimate keeps the factor independent of the number of inactive children. -/
theorem marked_height_lower {A ai U : ℝ} (hA : 0 < A) (hai : 0 < ai)
    (haiU : ai ≤ (1001/1000)*U) (hu : U/A ≤ 1) (hU : 0 < U) :
    (1/2)*(1+Real.log (1/(U/A))) ≤ SideParameters.height A ai := by
  have hua : 0 < U/A := div_pos hU hA
  have hlogu := Real.log_nonneg ((one_le_div hua).mpr hu)
  have hratio : A/((1001/1000)*U) ≤ A/ai :=
    div_le_div_of_nonneg_left hA.le hai haiU
  have hlog := Real.log_le_log (div_pos hA (by positivity : (0:ℝ)<(1001/1000)*U)) hratio
  rw [Real.log_div hA.ne' (by positivity : (1001/1000)*U ≠ (0:ℝ)),
    Real.log_mul (by norm_num : (1001/1000:ℝ) ≠ 0) hU.ne'] at hlog
  have he : Real.log (1/(U/A)) = Real.log A-Real.log U := by
    rw [one_div_div,Real.log_div hA.ne' hU.ne']
  rw [he] at hlogu ⊢
  have hc := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<1001/1000)
  unfold SideParameters.height
  linarith

theorem side_exp_sum {s : EpochGeometry.State ι} {a : ι → ℝ} {o : ι} {U : ℝ}
    (ha : ∀ i, 0 ≤ a i) (hA : 0 < EpochGeometry.total s.base)
    (hU : sideReference a o U) :
    (∑ i : {i : active a // (i : ι) ≠ o},
      Real.exp (-SideParameters.height (EpochGeometry.total s.base) (a i.1))) ≤
        2*(U/EpochGeometry.total s.base) := by
  classical
  have hsum : (∑ i : {i : active a // (i : ι) ≠ o}, a i.1) = EpochGeometry.side o a := by
    rw [←Finset.sum_subtype (univ.filter fun i : active a => (i:ι) ≠ o)
      (by simp) (fun i => a i),sum_filter]
    rw [sum_coe_sort (active a) (fun i : ι => if i ≠ o then a i else 0)]
    unfold active EpochGeometry.side
    rw [sum_filter]
    apply sum_congr rfl
    intro i _
    by_cases hi : i=o
    · simp [hi]
    · by_cases hp : 0 < a i
      · simp [hi,hp]
      · have hz : a i=0 := le_antisymm (not_lt.mp hp) (ha i)
        simp [hz,hi]
  calc
    _ ≤ ∑ i : {i : active a // (i : ι) ≠ o}, a i.1/EpochGeometry.total s.base :=
      sum_le_sum fun i _ => exp_height_le hA (mem_active.mp i.1.property)
    _ = EpochGeometry.side o a/EpochGeometry.total s.base := by rw [←sum_div,hsum]
    _ ≤ 2*(U/EpochGeometry.total s.base) := by
      apply (div_le_iff₀ hA).mpr
      have he : 2*(U/EpochGeometry.total s.base)*EpochGeometry.total s.base=2*U := by field_simp
      rw [he]
      linarith [hU.2.2,hU.1]

end UniformKServer.EpochParameters

end


end

end OAI
