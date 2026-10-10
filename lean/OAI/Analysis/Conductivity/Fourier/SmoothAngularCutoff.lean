import Mathlib
import OAI.Analysis.Conductivity.Branching.PhysicalAttachedAssembly

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory

def periodCutoff (T x : ℝ) : ℝ := smoothTransition (x/T+1)-smoothTransition (x/T)

lemma periodCutoff_smooth (T : ℝ) : ContDiff ℝ (↑(⊤:ℕ∞)) (periodCutoff T) :=
  (smoothTransition.contDiff.comp ((contDiff_id.div_const T).add contDiff_const)).sub
    (smoothTransition.contDiff.comp (contDiff_id.div_const T))

lemma periodCutoff_nonneg (T x : ℝ) : 0≤periodCutoff T x :=
  sub_nonneg.mpr (smoothTransition.monotone (by linarith))

lemma periodCutoff_zero_left {T : ℝ} (hT : 0<T) {x : ℝ} (hx : x≤-T) :
    periodCutoff T x=0 := by
  have hh : x/T≤-1 := (div_le_iff₀ hT).mpr (by linarith)
  rw [periodCutoff,smoothTransition.zero_of_nonpos (by linarith),
    smoothTransition.zero_of_nonpos (by linarith),sub_self]

lemma periodCutoff_zero_right {T : ℝ} (hT : 0<T) {x : ℝ} (hx : T≤x) :
    periodCutoff T x=0 := by
  have hh : 1≤x/T := (le_div_iff₀ hT).mpr (by linarith)
  rw [periodCutoff,smoothTransition.one_of_one_le (by linarith),
    smoothTransition.one_of_one_le hh,sub_self]

lemma periodCutoff_support {T : ℝ} (hT : 0<T) : tsupport (periodCutoff T)⊆Icc (-T) T := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  constructor
  · by_contra h
    exact hx (periodCutoff_zero_left hT (le_of_not_ge h))
  · by_contra h
    exact hx (periodCutoff_zero_right hT (le_of_not_ge h))

lemma periodCutoff_compact {T : ℝ} (hT : 0<T) : HasCompactSupport (periodCutoff T) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (periodCutoff_support hT)

lemma periodCutoff_partition {T : ℝ} (hT : 0<T) {x : ℝ} (hx : x∈Icc 0 T) :
    periodCutoff T x+periodCutoff T (x-T)=1 := by
  have hz : 0≤x/T := div_nonneg hx.1 hT.le
  have h1 : x/T≤1 := (div_le_one hT).mpr hx.2
  have he : (x-T)/T+1=x/T := by field_simp; ring
  rw [periodCutoff,periodCutoff,he,
    smoothTransition.one_of_one_le (by linarith),
    smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx.2) hT.le)]
  ring

lemma periodCutoff_support_translate {T : ℝ} (hT : 0<T) {x : ℝ} (hx : x∈Icc 0 T)
    {n : ℤ} (hn : periodCutoff T (x+T*n)≠0) : n=-1 ∨ n=0 := by
  by_contra h
  have hh : n≤-2 ∨ 1≤n := by omega
  rcases hh with hh | hh
  · have hc : (n:ℝ)≤-2 := by exact_mod_cast hh
    exact hn (periodCutoff_zero_left hT (by nlinarith [hx.1,hx.2,mul_le_mul_of_nonneg_left hc hT.le]))
  · have hc : (1:ℝ)≤(n:ℝ) := by exact_mod_cast hh
    exact hn (periodCutoff_zero_right hT (by nlinarith [hx.1,hx.2,mul_le_mul_of_nonneg_left hc hT.le]))

lemma periodCutoff_finsum_core {T : ℝ} (hT : 0<T) {x : ℝ} (hx : x∈Icc 0 T) :
    (∑ᶠ n : ℤ,periodCutoff T (x+T*n))=1 := by
  classical
  rw [finsum_eq_sum_of_support_subset _ (s:={-1,0}) (by
    intro n hn
    simpa only [Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton] using
      periodCutoff_support_translate hT hx hn)]
  simp only [Finset.sum_insert (by norm_num : (-1:ℤ)∉({0}:Finset ℤ)),Finset.sum_singleton,
    Int.cast_neg,Int.cast_one,Int.cast_zero,mul_neg_one,mul_zero,add_zero]
  simpa only [sub_eq_add_neg,add_comm] using periodCutoff_partition hT hx

lemma periodCutoff_finsum {T : ℝ} (hT : 0<T) (x : ℝ) :
    (∑ᶠ n : ℤ,periodCutoff T (x+T*n))=1 := by
  let m : ℤ := ⌊x/T⌋
  let y := x-T*m
  have hy : y∈Icc 0 T := by
    have ha := Int.floor_le (x/T)
    have hb := Int.lt_floor_add_one (x/T)
    constructor
    · dsimp [y,m]
      have hh := (le_div_iff₀ hT).mp ha
      nlinarith
    · dsimp [y,m]
      have hh := (div_lt_iff₀ hT).mp hb
      nlinarith
  have he := finsum_comp_equiv (Equiv.addRight m)
    (f:=fun n : ℤ => periodCutoff T (y+T*n))
  have hf : (fun n : ℤ => periodCutoff T (y+T*((n+m:ℤ):ℝ)))=
      (fun n : ℤ => periodCutoff T (x+T*n)) := by
    funext n
    congr 1
    simp only [y,Int.cast_add]
    ring
  change (∑ᶠ n : ℤ,periodCutoff T (y+T*((n+m:ℤ):ℝ)))=_ at he
  rw [hf,periodCutoff_finsum_core hT hy] at he
  exact he

theorem periodCutoff_integral {T : ℝ} (hT : 0<T) {g : ℝ → ℝ}
    (hg : Continuous g) (hp : Function.Periodic g T) :
    (∫ x,periodCutoff T x*g x)=∫ x in (0:ℝ)..T,g x := by
  let f := fun x => periodCutoff T x*g x
  have hf : Continuous f := (periodCutoff_smooth T).continuous.mul hg
  have hs : Function.support f⊆Ioc (-T) T := by
    intro x hx
    constructor
    · by_contra h
      exact hx (by simp [f,periodCutoff_zero_left hT (le_of_not_gt h)])
    · by_contra h
      exact hx (by simp [f,periodCutoff_zero_right hT (le_of_not_ge h)])
  rw [←intervalIntegral.integral_eq_integral_of_support_subset hs,
    ←intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable (-T) 0) (hf.intervalIntegrable 0 T)]
  have he : (∫ x in -T..(0:ℝ),f x)=∫ x in (0:ℝ)..T,f (x-T) := by
    rw [intervalIntegral.integral_comp_sub_right]
    simp
  rw [he]
  have hi : IntervalIntegrable (fun x => f (x-T)) volume 0 T :=
    (hf.comp (continuous_id.sub continuous_const)).intervalIntegrable 0 T
  rw [←intervalIntegral.integral_add hi (hf.intervalIntegrable 0 T)]
  apply intervalIntegral.integral_congr
  intro x hx
  have hx' : x∈Icc 0 T := by simpa only [uIcc_of_le hT.le] using hx
  have hgp : g (x-T)=g x := by simpa using hp.sub_eq x
  dsimp [f]
  rw [hgp,←add_mul]
  rw [add_comm (periodCutoff T (x-T)),periodCutoff_partition hT hx',one_mul]

end ScalarConductivity

end
end

end OAI
