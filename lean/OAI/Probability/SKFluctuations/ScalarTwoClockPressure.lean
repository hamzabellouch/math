import Mathlib
import OAI.Probability.SKFluctuations.MarkedPairExpectation

namespace OAI

/-! Scalar Two Clock Pressure. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

noncomputable def scalarTwoClockPressure (T a q r : ℝ) : ℝ :=
  zeroContinuation (Measure.pi fun _ : Fin 1 => gaussianReal 0 (Real.toNNReal (T*q)))
    (clockContinuation a (clockContinuation 1 scalarTerminal.F (T-T*r)) (T*r-T*q)) 0

 def twoCutBoundary (u v w : ℝ) (i : ℕ) : ℝ := if i = 0 then u else if i = 1 then v else w

 theorem twoCutBoundary_monotone {u v w : ℝ} (huv : u ≤ v) (hvw : v ≤ w) :
    Monotone (twoCutBoundary u v w) := by
  intro i j hij
  dsimp only [twoCutBoundary]
  split_ifs <;> first | exact le_rfl | exact huv | exact hvw | exact huv.trans hvw | omega

 theorem scalarTwoClockPressure_eq {T a : ℝ} (ha : 0 < a) (q r : ℝ) :
    scalarTwoClockPressure T a q r =
      scalarTerminal.rootBoundarySchedule [⟨a,ha⟩,⟨1,by norm_num⟩] 0 (twoCutBoundary (T*q) (T*r) T) 0 := by
  simp [scalarTwoClockPressure,HeatJet.rootBoundarySchedule,HeatJet.boundarySchedule,
    twoCutBoundary,HeatJet.evolve]

 theorem scalarTwoClockPressure_bound {T a q r q' r' : ℝ} (hT : 0 ≤ T) (ha : a ∈ Ioc (0:ℝ) 1)
    (hq : q ∈ Icc (0:ℝ) 1) (hr : r ∈ Icc (0:ℝ) 1) (hqr : q ≤ r)
    (hq' : q' ∈ Icc (0:ℝ) 1) (hr' : r' ∈ Icc (0:ℝ) 1) (hqr' : q' ≤ r') :
    |scalarTwoClockPressure T a q r-scalarTwoClockPressure T a q' r'| ≤
      (1/2:ℝ)*max |T*q-T*q'| |T*r-T*r'| := by
  let as : List PositiveMass := [⟨a,ha.1⟩,⟨1,by norm_num⟩]
  let M := max |T*q-T*q'| |T*r-T*r'|
  have hm : 0 ≤ M := (abs_nonneg _).trans (le_max_left _ _)
  have hqmon := twoCutBoundary_monotone (mul_le_mul_of_nonneg_left hqr hT)
    (show T*r ≤ T by nlinarith [hr.2])
  have hrmon := twoCutBoundary_monotone (mul_le_mul_of_nonneg_left hqr' hT)
    (show T*r' ≤ T by nlinarith [hr'.2])
  have hh := scalarTerminal.rootCumulativeClock_uniform (fun _ => 1) scalarTerminal_G_bound as
    hqmon hrmon (by simpa [twoCutBoundary] using mul_nonneg hT hq.1)
    (by simpa [twoCutBoundary] using mul_nonneg hT hq'.1)
    (by rfl) hm (by simp [as,ha.2])
    (by
      intro b hb
      simp only [as,List.mem_cons,List.not_mem_nil,or_false] at hb
      rcases hb with rfl|rfl
      · exact ha.2
      · exact le_rfl)
    (by
      intro i _
      dsimp only [twoCutBoundary]
      split_ifs
      · exact le_max_left _ _
      · exact le_max_right _ _
      · simpa only [sub_self,abs_zero] using hm) 0
  rw [← scalarTwoClockPressure_eq ha.1,← scalarTwoClockPressure_eq ha.1] at hh
  simpa [M] using hh

 theorem scalarTwoClockPressure_tendsto_below {T a q r : ℝ} (hT : 0 ≤ T) (ha : a ∈ Ioc (0:ℝ) 1)
    (hq : q ∈ Icc (0:ℝ) 1) (hr : r ∈ Icc (0:ℝ) 1) (hqr : q ≤ r) :
    Tendsto (fun j => scalarTwoClockPressure T a (scalarDyadicBelow q j) (scalarDyadicBelow r j))
      atTop (𝓝 (scalarTwoClockPressure T a q r)) := by
  have hqj (j : ℕ) : scalarDyadicBelow q j ∈ Icc (0:ℝ) 1 :=
    ⟨scalarDyadicBelow_nonneg q j,(scalarDyadicBelow_le hq.1 j).trans hq.2⟩
  have hrj (j : ℕ) : scalarDyadicBelow r j ∈ Icc (0:ℝ) 1 :=
    ⟨scalarDyadicBelow_nonneg r j,(scalarDyadicBelow_le hr.1 j).trans hr.2⟩
  have hqrj (j : ℕ) : scalarDyadicBelow q j ≤ scalarDyadicBelow r j := by
    apply div_le_div_of_nonneg_right _ (by positivity : (0:ℝ) ≤ 2^j)
    exact_mod_cast Nat.floor_mono (mul_le_mul_of_nonneg_right hqr (by positivity : (0:ℝ) ≤ 2^j))
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ => dist_nonneg)
    (fun j => by simpa only [Real.dist_eq] using scalarTwoClockPressure_bound hT ha (hqj j) (hrj j) (hqrj j) hq hr hqr)
  have hp := ((scalarDyadicBelow_tendsto hq.1).const_mul T).sub_const (T*q)
  have hs := ((scalarDyadicBelow_tendsto hr.1).const_mul T).sub_const (T*r)
  simpa only [sub_self,abs_zero,max_self,mul_zero] using (hp.abs.max hs.abs).const_mul (1/2:ℝ)

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 

theorem HeatJet.grid_two_dyadic_cuts {n : ℕ} (J : HeatJet n) (α : PositiveMassProfile)
    {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (l : ℝ) (t : ℝ≥0)
    (ht : 0 < (t:ℝ)) (j k m r : ℕ) (hkm : k ≤ m) (hm : m ≤ 2^j)
    (hs : ∀ s ∈ Ico l (l+t), α.mass s =
      if s < l+(t:ℝ)*k/2^j then a else if s < l+(t:ℝ)*m/2^j then b else c) :
    (J.schedule (α.grid l t (j+r))).F = clockContinuation a
      (clockContinuation b (clockContinuation c J.F ((t:ℝ)-(t:ℝ)*m/2^j))
        ((t:ℝ)*m/2^j-(t:ℝ)*k/2^j)) ((t:ℝ)*k/2^j) := by
  induction j generalizing J l t k m with
  | zero =>
    have hmm : m = 0 ∨ m = 1 := Nat.le_one_iff_eq_zero_or_eq_one.mp (by simpa using hm)
    rcases hmm with rfl | rfl
    · have : k = 0 := Nat.eq_zero_of_le_zero hkm
      subst k
      simp only [Nat.cast_zero,mul_zero,zero_div,sub_zero,Nat.zero_add]
      rw [show clockContinuation b (clockContinuation c J.F t) 0 = clockContinuation c J.F t from
        funext (clockContinuation_zero hb.ne'),
        show clockContinuation a (clockContinuation c J.F t) 0 = clockContinuation c J.F t from
        funext (clockContinuation_zero ha.ne')]
      apply J.grid_constant α hc l t ht r
      intro s h
      simpa only [pow_zero,Nat.cast_zero,mul_zero,zero_div,add_zero,ite_eq_right (not_lt.mpr h.1)] using hs s h
    · have hk : k = 0 ∨ k = 1 := Nat.le_one_iff_eq_zero_or_eq_one.mp hkm
      rcases hk with rfl | rfl
      · simp only [Nat.cast_zero,Nat.cast_one,mul_zero,mul_one,pow_zero,div_one,sub_self,sub_zero,Nat.zero_add]
        rw [show clockContinuation c J.F 0 = J.F from funext (clockContinuation_zero hc.ne'),
          show clockContinuation a (clockContinuation b J.F t) 0 = clockContinuation b J.F t from
          funext (clockContinuation_zero ha.ne')]
        apply J.grid_constant α hb l t ht r
        intro s h
        simpa only [pow_zero,Nat.cast_zero,Nat.cast_one,mul_zero,mul_one,zero_div,div_one,add_zero,
          ite_eq_right (not_lt.mpr h.1),ite_eq_left h.2] using hs s h
      · simp only [Nat.cast_one,mul_one,pow_zero,div_one,sub_self,Nat.zero_add]
        rw [show clockContinuation c J.F 0 = J.F from funext (clockContinuation_zero hc.ne'),
          show clockContinuation b J.F 0 = J.F from funext (clockContinuation_zero hb.ne')]
        apply J.grid_constant α ha l t ht r
        intro s h
        simpa only [pow_zero,Nat.cast_one,mul_one,div_one,ite_eq_left h.2] using hs s h
  | succ j ih =>
    have hp : (0:ℝ) < 2^j := by positivity
    have hh : 0 < ((t/2:ℝ≥0):ℝ) := by simpa using half_pos ht
    have he (u : ℕ) : (((t/2:ℝ≥0):ℝ)*(u:ℝ)/2^j) = (t:ℝ)*u/2^(j+1) := by
      simp only [NNReal.coe_div,NNReal.coe_ofNat,pow_succ]
      ring
    have hshift (u : ℕ) (hu : 2^j ≤ u) :
        (t:ℝ)/2+((t/2:ℝ≥0):ℝ)*((u-2^j:ℕ):ℝ)/2^j = (t:ℝ)*u/2^(j+1) := by
      rw [Nat.cast_sub hu,Nat.cast_pow,Nat.cast_ofNat]
      simp only [NNReal.coe_div,NNReal.coe_ofNat,pow_succ]
      field_simp
      ring
    have hlow (u : ℕ) (hu : u ≤ 2^j) : (t:ℝ)*u/2^(j+1) ≤ (t:ℝ)/2 := by
      rw [pow_succ]
      apply (div_le_iff₀ (mul_pos hp (by norm_num))).2
      have hhR : (u:ℝ) ≤ 2^j := by exact_mod_cast hu
      nlinarith [mul_le_mul_of_nonneg_left hhR ht.le]
    have hhigh (u : ℕ) (hu : 2^j ≤ u) : (t:ℝ)/2 ≤ (t:ℝ)*u/2^(j+1) := by
      rw [← hshift u hu]
      have : 0 ≤ ((t/2:ℝ≥0):ℝ)*((u-2^j:ℕ):ℝ)/2^j := by positivity
      linarith
    have hlsub : Ico l (l+(t/2:ℝ≥0)) ⊆ Ico l (l+t) := by
      intro s h
      simp only [NNReal.coe_div,NNReal.coe_ofNat] at h
      exact ⟨h.1,by linarith [h.2]⟩
    have hrsub : Ico (l+(t:ℝ)/2) (l+(t:ℝ)/2+(t/2:ℝ≥0)) ⊆ Ico l (l+t) := by
      intro s h
      simp only [NNReal.coe_div,NNReal.coe_ofNat] at h
      constructor <;> linarith [h.1,h.2]
    by_cases hml : m ≤ 2^j
    · have hkl := hkm.trans hml
      have hl : ∀ s ∈ Ico l (l+(t/2:ℝ≥0)), α.mass s =
          if s < l+((t/2:ℝ≥0):ℝ)*k/2^j then a else
          if s < l+((t/2:ℝ≥0):ℝ)*m/2^j then b else c := by
        intro s h
        rw [he,he]
        exact hs s (hlsub h)
      have hr : ∀ s ∈ Ico (l+(t:ℝ)/2) (l+(t:ℝ)/2+(t/2:ℝ≥0)), α.mass s = c := by
        intro s h
        rw [hs s (hrsub h),ite_eq_right,ite_eq_right]
        · linarith [h.1,hlow m hml]
        · linarith [h.1,hlow k hkl]
      rw [Nat.succ_add,PositiveMassProfile.grid,J.schedule_append]
      rw [ih _ l (t/2) hh k m hkm hml hl,J.grid_constant α hc (l+(t:ℝ)/2) (t/2) hh (j+r) hr,he,he]
      have hmerge : clockContinuation c (clockContinuation c J.F ((t/2:ℝ≥0):ℝ))
          (((t/2:ℝ≥0):ℝ)-(t:ℝ)*m/2^(j+1)) = clockContinuation c J.F ((t:ℝ)-(t:ℝ)*m/2^(j+1)) := by
        funext x
        rw [clockContinuation_add J.lipschitz hc.ne'
          (by simpa only [NNReal.coe_div,NNReal.coe_ofNat] using sub_nonneg.mpr (hlow m hml)) (by positivity)]
        congr 1
        simp only [NNReal.coe_div,NNReal.coe_ofNat]
        ring
      rw [hmerge]
    · have hmlo : 2^j ≤ m := (lt_of_not_ge hml).le
      have hmr : m-2^j ≤ 2^j := by rw [pow_succ] at hm; omega
      by_cases hkl : k ≤ 2^j
      · have hl : ∀ s ∈ Ico l (l+(t/2:ℝ≥0)), α.mass s =
            if s < l+((t/2:ℝ≥0):ℝ)*k/2^j then a else b := by
          intro s h
          rw [he,hs s (hlsub h)]
          have hm' : s < l+(t:ℝ)*m/2^(j+1) := by
            simp only [NNReal.coe_div,NNReal.coe_ofNat] at h
            linarith [h.2,hhigh m hmlo]
          rw [ite_eq_left hm']
        have hr : ∀ s ∈ Ico (l+(t:ℝ)/2) (l+(t:ℝ)/2+(t/2:ℝ≥0)), α.mass s =
            if s < l+(t:ℝ)/2+((t/2:ℝ≥0):ℝ)*((m-2^j:ℕ):ℝ)/2^j then b else c := by
          intro s h
          rw [add_assoc l,hshift m hmlo,hs s (hrsub h),ite_eq_right]
          linarith [h.1,hlow k hkl]
        rw [Nat.succ_add,PositiveMassProfile.grid,J.schedule_append]
        rw [(J.schedule (α.grid (l+(t:ℝ)/2) (t/2) (j+r))).grid_dyadic_cut α ha hb l (t/2) hh j k r hkl hl,
          J.grid_dyadic_cut α hb hc (l+(t:ℝ)/2) (t/2) hh j (m-2^j) r hmr hr,he k]
        have hlast : ((t/2:ℝ≥0):ℝ)-((t/2:ℝ≥0):ℝ)*((m-2^j:ℕ):ℝ)/2^j =
            (t:ℝ)-(t:ℝ)*m/2^(j+1) := by
          have hm' := hshift m hmlo
          simp only [NNReal.coe_div,NNReal.coe_ofNat] at hm' ⊢
          linarith
        rw [hlast]
        have hcL : LipschitzWith J.C (clockContinuation c J.F ((t:ℝ)-(t:ℝ)*m/2^(j+1))) :=
          (J.evolve hc ((t:ℝ)-(t:ℝ)*m/2^(j+1))).lipschitz
        have hmerge : clockContinuation b
            (clockContinuation b (clockContinuation c J.F ((t:ℝ)-(t:ℝ)*m/2^(j+1)))
              (((t/2:ℝ≥0):ℝ)*((m-2^j:ℕ):ℝ)/2^j))
            (((t/2:ℝ≥0):ℝ)-(t:ℝ)*k/2^(j+1)) =
            clockContinuation b (clockContinuation c J.F ((t:ℝ)-(t:ℝ)*m/2^(j+1)))
              ((t:ℝ)*m/2^(j+1)-(t:ℝ)*k/2^(j+1)) := by
          funext y
          rw [clockContinuation_add hcL hb.ne'
            (by simpa only [NNReal.coe_div,NNReal.coe_ofNat] using sub_nonneg.mpr (hlow k hkl))
            (by positivity)]
          congr 1
          have hm' := hshift m hmlo
          simp only [NNReal.coe_div,NNReal.coe_ofNat] at hm' ⊢
          linarith
        rw [hmerge]
      · have hklo : 2^j ≤ k := (lt_of_not_ge hkl).le
        have hkr : k-2^j ≤ m-2^j := Nat.sub_le_sub_right hkm _
        have hl : ∀ s ∈ Ico l (l+(t/2:ℝ≥0)), α.mass s = a := by
          intro s h
          rw [hs s (hlsub h),ite_eq_left]
          simp only [NNReal.coe_div,NNReal.coe_ofNat] at h
          linarith [h.2,hhigh k hklo]
        have hr : ∀ s ∈ Ico (l+(t:ℝ)/2) (l+(t:ℝ)/2+(t/2:ℝ≥0)), α.mass s =
            if s < l+(t:ℝ)/2+((t/2:ℝ≥0):ℝ)*((k-2^j:ℕ):ℝ)/2^j then a else
            if s < l+(t:ℝ)/2+((t/2:ℝ≥0):ℝ)*((m-2^j:ℕ):ℝ)/2^j then b else c := by
          intro s h
          rw [add_assoc l,hshift k hklo,add_assoc l,hshift m hmlo]
          exact hs s (hrsub h)
        rw [Nat.succ_add,PositiveMassProfile.grid,J.schedule_append]
        rw [(J.schedule (α.grid (l+(t:ℝ)/2) (t/2) (j+r))).grid_constant α ha l (t/2) hh (j+r) hl,
          ih _ (l+(t:ℝ)/2) (t/2) hh (k-2^j) (m-2^j) hkr hmr hr]
        have hlast : ((t/2:ℝ≥0):ℝ)-((t/2:ℝ≥0):ℝ)*((m-2^j:ℕ):ℝ)/2^j =
            (t:ℝ)-(t:ℝ)*m/2^(j+1) := by
          have hm' := hshift m hmlo
          simp only [NNReal.coe_div,NNReal.coe_ofNat] at hm' ⊢
          linarith
        have hmiddle : ((t/2:ℝ≥0):ℝ)*((m-2^j:ℕ):ℝ)/2^j-((t/2:ℝ≥0):ℝ)*((k-2^j:ℕ):ℝ)/2^j =
            (t:ℝ)*m/2^(j+1)-(t:ℝ)*k/2^(j+1) := by
          linarith [hshift m hmlo,hshift k hklo]
        rw [hlast,hmiddle]
        have hL : LipschitzWith J.C (clockContinuation b (clockContinuation c J.F ((t:ℝ)-(t:ℝ)*m/2^(j+1)))
            ((t:ℝ)*m/2^(j+1)-(t:ℝ)*k/2^(j+1))) :=
          ((J.evolve hc ((t:ℝ)-(t:ℝ)*m/2^(j+1))).evolve hb
          ((t:ℝ)*m/2^(j+1)-(t:ℝ)*k/2^(j+1))).lipschitz
        funext x
        rw [clockContinuation_add hL ha.ne' (by positivity) (by positivity)]
        congr 1
        have hk' := hshift k hklo
        simpa only [NNReal.coe_div,NNReal.coe_ofNat] using hk'

 theorem HeatJet.profileValue_two_dyadic_cuts {n : ℕ} (J : HeatJet n) (α : PositiveMassProfile)
    {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (l : ℝ) (t : ℝ≥0)
    (ht : 0 < (t:ℝ)) (j k m : ℕ) (hkm : k ≤ m) (hm : m ≤ 2^j)
    (hs : ∀ s ∈ Ico l (l+t), α.mass s =
      if s < l+(t:ℝ)*k/2^j then a else if s < l+(t:ℝ)*m/2^j then b else c)
    (x : Fin (n+1) → ℝ) :
    J.profileValue α l t x = clockContinuation a
      (clockContinuation b (clockContinuation c J.F ((t:ℝ)-(t:ℝ)*m/2^j))
        ((t:ℝ)*m/2^j-(t:ℝ)*k/2^j)) ((t:ℝ)*k/2^j) x := by
  have hh := (J.grid_tendsto α l t x).comp (tendsto_add_atTop_nat j)
  apply tendsto_nhds_unique hh
  have he : (fun r : ℕ => (J.schedule (α.grid l t (r+j))).F x) = (fun _ : ℕ => clockContinuation a
      (clockContinuation b (clockContinuation c J.F ((t:ℝ)-(t:ℝ)*m/2^j))
        ((t:ℝ)*m/2^j-(t:ℝ)*k/2^j)) ((t:ℝ)*k/2^j) x) := by
    funext r
    rw [Nat.add_comm,J.grid_two_dyadic_cuts α ha hb hc l t ht j k m r hkm hm hs]
  change Tendsto (fun r : ℕ => (J.schedule (α.grid l t (r+j))).F x) _ _
  rw [he]
  exact tendsto_const_nhds

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 theorem HeatJet.nonnegativeProfileValue_two_dyadic_cuts {n : ℕ} (J : HeatJet n)
    (α : NonnegativeMassProfile) {b c : ℝ} (hb : 0 < b) (hc : 0 < c) (l : ℝ) (t : ℝ≥0)
    (ht : 0 < (t:ℝ)) (j k m : ℕ) (hkm : k ≤ m) (hm : m ≤ 2^j)
    (hs : ∀ s ∈ Ico l (l+t), α.mass s =
      if s < l+(t:ℝ)*k/2^j then 0 else if s < l+(t:ℝ)*m/2^j then b else c)
    (x : Fin (n+1) → ℝ) :
    J.nonnegativeProfileValue α l t x = zeroContinuation
      (Measure.pi fun _ : Fin (n+1) => gaussianReal 0 (Real.toNNReal ((t:ℝ)*k/2^j)))
      (clockContinuation b (clockContinuation c J.F ((t:ℝ)-(t:ℝ)*m/2^j))
        ((t:ℝ)*m/2^j-(t:ℝ)*k/2^j)) x := by
  let u := (t:ℝ)*k/2^j
  let v := (t:ℝ)*m/2^j-(t:ℝ)*k/2^j
  let w := (t:ℝ)-(t:ℝ)*m/2^j
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hv : 0 ≤ v := by
    apply sub_nonneg.mpr
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by exact_mod_cast hkm) ht.le) (by positivity)
  have hw : 0 ≤ w := by
    apply sub_nonneg.mpr
    apply (div_le_iff₀ (by positivity : (0:ℝ) < 2^j)).2
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hm) ht.le
  let e : ℕ → ℝ := fun i => (1/2:ℝ)^i
  have he (i : ℕ) : 0 < e i := by dsimp [e]; positivity
  have hp : Tendsto e atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hp' : Tendsto e atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr ⟨hp,Eventually.of_forall he⟩
  let F := clockContinuation b (clockContinuation c J.F w) v
  have hF : LipschitzWith J.C F := ((J.evolve hc w).evolve hb v).lipschitz
  have hl := (shiftedContinuation_tendsto_zero_mass hF
    (exponentialIncrement_gaussian (fun _ : Fin (n+1) => Real.toNNReal u)) x).comp hp'
  change Tendsto (fun i => clockContinuation (e i) F u x) atTop _ at hl
  have hval (i : ℕ) : J.profileValue (α.positiveApprox i) l t x =
      clockContinuation (e i) (clockContinuation (b+e i) (clockContinuation (c+e i) J.F w) v) u x := by
    apply J.profileValue_two_dyadic_cuts (α.positiveApprox i) (he i) (add_pos hb (he i)) (add_pos hc (he i))
      l t ht j k m hkm hm
    intro s h
    dsimp only [NonnegativeMassProfile.positiveApprox]
    rw [hs s h]
    split_ifs <;> simp only [zero_add,e]
  choose D _ hD using fun i => (J.smoothG i).bound
  have htail (i : ℕ) (y : Fin (n+1) → ℝ) :
      |clockContinuation (b+e i) (clockContinuation (c+e i) J.F w) v y-F y| ≤
        (∑ i, (D i)^2)/2*(e i*(v+w)) := by
    let cs : List CoupledHeatClock :=
      [⟨b+e i,b,add_pos hb (he i),hb,Real.toNNReal v⟩,
       ⟨c+e i,c,add_pos hc (he i),hc,Real.toNNReal w⟩]
    have hh := J.schedule_mass_comparison D hD cs y
    simpa only [cs,List.map_cons,List.map_nil,CoupledHeatClock.left,CoupledHeatClock.right,
      HeatJet.schedule,HeatJet.evolve,Real.coe_toNNReal _ hv,Real.coe_toNNReal _ hw,
      CoupledHeatClock.cost,List.sum_cons,List.sum_nil,add_sub_cancel_left,abs_of_pos (he i),add_zero,mul_add,F] using hh
  have hd (i : ℕ) : dist (clockContinuation (e i) F u x) (J.profileValue (α.positiveApprox i) l t x) ≤
      (∑ i, (D i)^2)/2*(e i*(v+w)) := by
    rw [hval,Real.dist_eq,abs_sub_comm]
    exact clockContinuation_abs_sub_le
      ((J.evolve (add_pos hc (he i)) w).evolve (add_pos hb (he i)) v).lipschitz hF (he i)
      (htail i) u x
  have hd0 : Tendsto (fun i => dist (clockContinuation (e i) F u x)
      (J.profileValue (α.positiveApprox i) l t x)) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => dist_nonneg) hd
    simpa only [zero_mul,mul_zero] using (hp.mul_const (v+w)).const_mul ((∑ i, (D i)^2)/2)
  exact tendsto_nhds_unique (J.regularized_tendsto α l t x) (hl.congr_dist hd0)

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 theorem scalarParisiValue_twoAtom_dyadic {T a : ℝ} (hT : 0 < T) (ha : a ∈ Ioc (0:ℝ) 1)
    (j k m : ℕ) (hkm : k ≤ m) (hm : m ≤ 2^j) :
    scalarParisiValue hT (twoAtomMassProfile ((k:ℝ)/2^j) ((m:ℝ)/2^j) ⟨ha.1.le,ha.2⟩) =
      scalarTwoClockPressure T a ((k:ℝ)/2^j) ((m:ℝ)/2^j)-
        T/4*(a*(1-((k:ℝ)/2^j)^2)+(1-a)*(1-((m:ℝ)/2^j)^2))-T/4 := by
  change 0 < a ∧ a ≤ 1 at ha
  have hq : (k:ℝ)/2^j ∈ Icc (0:ℝ) 1 :=
    ⟨by positivity,(div_le_one (by positivity : (0:ℝ) < 2^j)).2 (by exact_mod_cast hkm.trans hm)⟩
  have hr : (m:ℝ)/2^j ∈ Icc (0:ℝ) 1 :=
    ⟨by positivity,(div_le_one (by positivity : (0:ℝ) < 2^j)).2 (by exact_mod_cast hm)⟩
  have hqr : (k:ℝ)/2^j ≤ (m:ℝ)/2^j :=
    div_le_div_of_nonneg_right (by exact_mod_cast hkm) (by positivity)
  have hs : ∀ s ∈ Ico (0:ℝ) (0+(⟨T,hT.le⟩:ℝ≥0)),
      (rescaledMassProfile (twoAtomMassProfile ((k:ℝ)/2^j) ((m:ℝ)/2^j) ⟨ha.1.le,ha.2⟩) hT).mass s =
        if s < 0+((⟨T,hT.le⟩:ℝ≥0):ℝ)*k/2^j then 0 else
        if s < 0+((⟨T,hT.le⟩:ℝ≥0):ℝ)*m/2^j then a else 1 := by
    intro s _
    change (twoAtomMassProfile ((k:ℝ)/2^j) ((m:ℝ)/2^j) ⟨ha.1.le,ha.2⟩).val (s/T) = _
    erw [twoAtomMassProfile_apply _ hqr]
    have he (x : ℝ) : s/T < x/2^j ↔ s < T*x/2^j := by
      rw [div_lt_iff₀ hT]
      ring_nf
    simp only [he,zero_add]
  have hp := scalarTerminal.nonnegativeProfileValue_two_dyadic_cuts
    (rescaledMassProfile (twoAtomMassProfile ((k:ℝ)/2^j) ((m:ℝ)/2^j) ⟨ha.1.le,ha.2⟩) hT)
    ha.1 (by norm_num : (0:ℝ) < 1) 0 ⟨T,hT.le⟩ hT j k m hkm hm hs 0
  unfold scalarParisiValue
  erw [hp,scalarPenalty_twoAtom hq hr]
  change zeroContinuation (Measure.pi fun _ : Fin 1 => gaussianReal 0 (Real.toNNReal (T*k/2^j)))
    (clockContinuation a (clockContinuation 1 scalarTerminal.F (T-T*m/2^j)) (T*m/2^j-T*k/2^j)) 0 -
    T/2*((a*(1-((k:ℝ)/2^j)^2)+(1-a)*(1-((m:ℝ)/2^j)^2))/2)-T/4 = _
  simp only [scalarTwoClockPressure,mul_div_assoc]
  ring

 theorem scalarParisiValue_twoAtom {T a q r : ℝ} (hT : 0 < T) (ha : a ∈ Ioc (0:ℝ) 1)
    (hq : q ∈ Icc (0:ℝ) 1) (hr : r ∈ Icc (0:ℝ) 1) (hqr : q ≤ r) :
    scalarParisiValue hT (twoAtomMassProfile q r ⟨ha.1.le,ha.2⟩) =
      scalarTwoClockPressure T a q r-T/4*(a*(1-q^2)+(1-a)*(1-r^2))-T/4 := by
  change 0 < a ∧ a ≤ 1 at ha
  have hp := (scalarParisiValue_continuous hT).continuousAt.tendsto.comp
    (twoAtomMassProfile_tendsto_below ⟨ha.1.le,ha.2⟩ (scalarDyadicBelow_tendsto hq.1)
      (scalarDyadicBelow_tendsto hr.1) (Eventually.of_forall (scalarDyadicBelow_le hq.1))
      (Eventually.of_forall (scalarDyadicBelow_le hr.1)))
  apply tendsto_nhds_unique hp
  have he (j : ℕ) : scalarParisiValue hT
      (twoAtomMassProfile (scalarDyadicBelow q j) (scalarDyadicBelow r j) ⟨ha.1.le,ha.2⟩) =
      scalarTwoClockPressure T a (scalarDyadicBelow q j) (scalarDyadicBelow r j)-
        T/4*(a*(1-(scalarDyadicBelow q j)^2)+(1-a)*(1-(scalarDyadicBelow r j)^2))-T/4 := by
    exact scalarParisiValue_twoAtom_dyadic hT ha j _ _
      (Nat.floor_mono (mul_le_mul_of_nonneg_right hqr (by positivity : (0:ℝ) ≤ 2^j)))
      (scalarDyadicBelow_numerator hr.2 j)
  have hl := ((scalarTwoClockPressure_tendsto_below hT.le ha hq hr hqr).sub
    (((((scalarDyadicBelow_tendsto hq.1).pow 2).const_sub 1).const_mul a).add
      ((((scalarDyadicBelow_tendsto hr.1).pow 2).const_sub 1).const_mul (1-a)) |>.const_mul (T/4))).sub_const (T/4)
  exact hl.congr (fun j => (he j).symm)

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι : Type*} [Fintype ι]

 theorem clockRoot_add {A : (ι → ℝ) → ℝ} (hA : BddSmooth 0 A)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (x : ι → ℝ) :
    clockRoot (clockRoot A t) s x = clockRoot A (s+t) x := by
  have hh := clockTest_add (LipschitzWith.const (0:ℝ)) hA (m := 1) one_ne_zero hs ht x
  simp only [clockContinuation_zero_potential] at hh
  have he : clockTest 1 (fun _ : ι → ℝ => 0) A t = clockRoot A t := funext (clockTest_zero_potential A 1 t)
  simpa only [he,clockTest_zero_potential] using hh

 theorem clockRoot_smooth {A : (ι → ℝ) → ℝ} {k : ℕ} (hA : BddSmooth k A) (t : ℝ) :
    BddSmooth k (clockRoot A t) := by
  have he : clockTest 1 (fun _ : ι → ℝ => 0) A t = clockRoot A t := funext (clockTest_zero_potential A 1 t)
  rw [← he]
  apply clockTest_bddSmooth _ hA
  refine ⟨⟨0,LipschitzWith.const _⟩, fun v => ⟨fun _ => 0,BddSmooth.const k 0,?_⟩⟩
  exact fun x s => hasDerivAt_const s 0

 theorem clockRoot_square_le {A : (ι → ℝ) → ℝ} (hA : BddSmooth 0 A)
    (t : ℝ) (x : ι → ℝ) : (clockRoot A t x)^2 ≤ clockRoot (fun y => (A y)^2) t x := by
  have hi : Integrable (fun _ : ι → ℝ => Real.exp (1*(0:ℝ)))
      (Measure.pi fun _ : ι => gaussianReal 0 (Real.toNNReal t)) := by simp
  have hh := shiftedMean_square_sub_nonneg (F := fun _ : ι → ℝ => 0)
    (ν := Measure.pi fun _ : ι => gaussianReal 0 (Real.toNNReal t))
    (m := 1) continuous_const hA (x := x) hi
  change 0 ≤ clockTest 1 (fun _ => 0) (fun y => (A y)^2) t x-
    (clockTest 1 (fun _ => 0) A t x)^2 at hh
  simpa only [clockTest_zero_potential,sub_nonneg] using hh

 theorem clockRoot_mono {A B : (ι → ℝ) → ℝ} (hA : BddSmooth 0 A) (hB : BddSmooth 0 B)
    (h : ∀ x, A x ≤ B x) (t : ℝ) (x : ι → ℝ) : clockRoot A t x ≤ clockRoot B t x := by
  have hh := shiftedMean_mono (F := fun _ : ι → ℝ => 0) (m := 1) hA hB h
    (ν := Measure.pi fun _ : ι => gaussianReal 0 (Real.toNNReal t)) (x := x)
    (by simp : Integrable (fun z : ι → ℝ => Real.exp (1*(0:ℝ))) _)
  change clockTest 1 (fun _ => 0) A t x ≤ clockTest 1 (fun _ => 0) B t x at hh
  simpa only [clockTest_zero_potential] using hh

 theorem clockRoot_sum {κ : Type*} [Fintype κ] {A : κ → (ι → ℝ) → ℝ}
    (hA : ∀ i, BddSmooth 0 (A i)) (t : ℝ) (x : ι → ℝ) :
    clockRoot (fun y => ∑ i, A i y) t x = ∑ i, clockRoot (A i) t x := by
  have hh := clockTest_sum (LipschitzWith.const (0:ℝ)) hA 1 t x
  simpa only [clockTest_zero_potential] using hh

 theorem clockRoot_zero_time (A : (ι → ℝ) → ℝ) (x : ι → ℝ) : clockRoot A 0 x = A x := by
  rw [← clockTest_zero_potential A 1 0,clockTest_zero]

 theorem HeatJet.rootFilledEnergy_le {n : ℕ} (J : HeatJet n) {T t : ℝ}
    (ht : t ∈ Icc 0 T) (x : Fin (n+1) → ℝ) :
    J.rootFilledEnergy T t x ≤ clockRoot (fun y => ∑ i, (J.A₁ i y)^2) T x := by
  have hs := sub_nonneg.mpr ht.2
  have hsq (i : Fin (n+1)) : BddSmooth 0 (fun y => (J.A₁ i y)^2) := by
    simpa only [pow_two] using (J.smoothA₁ i).mul (J.smoothA₁ i)
  have hroot (i : Fin (n+1)) : BddSmooth 0 (fun y => (clockRoot (J.A₁ i) (T-t) y)^2) := by
    have HH := clockRoot_smooth (J.smoothA₁ i) (T-t)
    simpa only [pow_two] using HH.mul HH
  unfold HeatJet.rootFilledEnergy
  rw [clockRoot_sum hroot,clockRoot_sum hsq]
  apply Finset.sum_le_sum
  intro i _
  calc
    clockRoot (fun y => (clockRoot (J.A₁ i) (T-t) y)^2) t x ≤
        clockRoot (clockRoot (fun y => (J.A₁ i y)^2) (T-t)) t x :=
      clockRoot_mono (hroot i) (clockRoot_smooth (hsq i) _) (clockRoot_square_le (J.smoothA₁ i) _) _ _
    _ = clockRoot (fun y => (J.A₁ i y)^2) T x := by
      rw [clockRoot_add (hsq i) ht.1 hs,add_sub_cancel]

 theorem HeatJet.gaussian_poincare {n : ℕ} (J : HeatJet n) {T : ℝ} (hT : 0 ≤ T)
    (x : Fin (n+1) → ℝ) :
    clockRoot (fun y => (J.A y)^2) T x-(clockRoot J.A T x)^2 ≤
      T*clockRoot (fun y => ∑ i, (J.A₁ i y)^2) T x := by
  rw [J.root_variance_eq_integral_energy hT x]
  have hc : Continuous (fun t => J.rootFilledEnergy T t x) := by
    simpa only [J.erased_filledEnergy] using J.erasePotential.continuous_filledEnergy (m := 1) zero_lt_one T x
  calc
    _ ≤ ∫ t in (0:ℝ)..T, clockRoot (fun y => ∑ i, (J.A₁ i y)^2) T x :=
      intervalIntegral.integral_mono_on hT (hc.intervalIntegrable 0 T) (intervalIntegrable_const)
        (fun t ht => J.rootFilledEnergy_le ht x)
    _ = _ := by simp

 

 theorem HeatJet.gaussian_poincare_strict {n : ℕ} (J : HeatJet n) {T : ℝ} (hT : 0 < T)
    (x : Fin (n+1) → ℝ)
    (hv : (∑ i, (clockRoot (J.A₁ i) T x)^2) < clockRoot (fun y => ∑ i, (J.A₁ i y)^2) T x) :
    clockRoot (fun y => (J.A y)^2) T x-(clockRoot J.A T x)^2 <
      T*clockRoot (fun y => ∑ i, (J.A₁ i y)^2) T x := by
  rw [J.root_variance_eq_integral_energy hT.le x]
  have hc : Continuous (fun t => J.rootFilledEnergy T t x) := by
    simpa only [J.erased_filledEnergy] using J.erasePotential.continuous_filledEnergy (m := 1) zero_lt_one T x
  calc
    _ < ∫ t in (0:ℝ)..T, clockRoot (fun y => ∑ i, (J.A₁ i y)^2) T x := by
      apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hT hc.continuousOn continuousOn_const
      · exact fun t ht => J.rootFilledEnergy_le ⟨ht.1.le,ht.2⟩ x
      · refine ⟨0,⟨le_rfl,hT.le⟩,?_⟩
        simpa only [HeatJet.rootFilledEnergy,clockRoot_zero_time,sub_zero] using hv
    _ = _ := by simp

end SKFluctuations.Hierarchy

namespace SKFluctuations.Scalar
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal

 

 theorem variance_gaussian_pos {A : ℝ → ℝ} (hA : Hierarchy.BddSmooth 0 A)
    (hne : ∃ x y, A x ≠ A y) {v : ℝ≥0} (hv : v ≠ 0) :
    0 < (∫ z, (A z)^2 ∂gaussianReal 0 v)-(∫ z, A z ∂gaussianReal 0 v)^2 := by
  obtain ⟨C,_,hC⟩ := hA.bound
  have hm : MemLp A 2 (gaussianReal 0 v) := MemLp.of_bound hA.continuous.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hC z)
  have heq := variance_eq_sub hm
  simp only [Pi.pow_apply] at heq
  rw [← heq]
  apply lt_of_le_of_ne (variance_nonneg A (gaussianReal 0 v))
  intro h
  have hae := ae_eq_integral_of_variance_eq_zero hm h.symm
  have he := MeasureTheory.Measure.eq_of_ae_eq ((gaussianReal_absolutelyContinuous' 0 hv).ae_le hae)
    hA.continuous continuous_const
  obtain ⟨x,y,hxy⟩ := hne
  exact hxy ((congrFun he x).trans (congrFun he y).symm)

 theorem curvature_nonconstant : ∃ x y, curvature x ≠ curvature y := by
  refine ⟨0,1,?_⟩
  have ht : Real.tanh (1:ℝ) ≠ 0 := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_ne_zero (Real.sinh_ne_zero.mpr one_ne_zero) (Real.cosh_pos _).ne'
  simp only [curvature,Real.tanh_zero,zero_pow (by decide : 2 ≠ 0),sub_zero]
  nlinarith [sq_pos_of_ne_zero ht]

 theorem curvature_bddSmooth : Hierarchy.BddSmooth 0 curvature :=
  ⟨curvature_continuous,1,by norm_num,fun z => by
    simpa only [abs_of_nonneg (curvature_bounds z).1] using (curvature_bounds z).2⟩

 theorem gaussian_tanh_mean_zero (t : ℝ≥0) : ∫ z, Real.tanh z ∂gaussianReal 0 t = 0 := by
  have hh := integral_map_of_stronglyMeasurable (μ := gaussianReal 0 t)
    measurable_neg tanh_continuous.stronglyMeasurable
  rw [gaussianReal_map_neg,neg_zero] at hh
  simp only [Real.tanh_neg,integral_neg] at hh
  linarith

end SKFluctuations.Scalar

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 theorem scalarTanh_bddSmooth : BddSmooth 0 (fun x : Fin 1 → ℝ => Real.tanh (x 0)) :=
  ⟨Scalar.tanh_continuous.comp (continuous_apply 0),1,by norm_num,
    fun x => (Real.abs_tanh_lt_one _).le⟩

 theorem scalarCurvature_bddSmooth : BddSmooth 0 (fun x : Fin 1 → ℝ => Scalar.curvature (x 0)) :=
  ⟨Scalar.curvature_continuous.comp (continuous_apply 0),1,by norm_num,
    fun x => by simpa only [abs_of_nonneg (Scalar.curvature_bounds _).1] using (Scalar.curvature_bounds (x 0)).2⟩

 theorem scalarThird_bddSmooth : BddSmooth 0 (fun x : Fin 1 → ℝ => Scalar.third (x 0)) := by
  refine ⟨Scalar.third_continuous.comp (continuous_apply 0),2,by norm_num,?_⟩
  intro x
  simp only [Scalar.third,abs_mul,abs_neg,abs_of_nonneg (Scalar.curvature_bounds _).1]
  norm_num only
  nlinarith [(mul_le_mul (Real.abs_tanh_lt_one (x 0)).le (Scalar.curvature_bounds (x 0)).2
    (Scalar.curvature_bounds (x 0)).1 (by norm_num : (0:ℝ) ≤ 1))]

 theorem scalarTanh_derivative (x v : Fin 1 → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.tanh ((x+s • v) 0))
      (∑ i : Fin 1, v i*Scalar.curvature ((x+t • v) 0)) t := by
  have hd := (Scalar.tanh_derivative (x 0+t*v 0)).comp t
    (((hasDerivAt_id t).mul_const (v 0)).const_add (x 0))
  simpa only [Fin.sum_univ_one,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
    Function.comp_def,id_eq,one_mul,mul_comm] using hd

 theorem scalarCurvature_derivative (i : Fin 1) (x : Fin 1 → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Scalar.curvature ((x+s • (Pi.single i (1:ℝ) : Fin 1 → ℝ)) 0))
      (Scalar.third ((x+t • (Pi.single i (1:ℝ) : Fin 1 → ℝ)) 0)) t := by
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  have hd := (Scalar.curvature_derivative (x 0+t)).comp t ((hasDerivAt_id t).const_add (x 0))
  simpa only [Pi.add_apply,Pi.smul_apply,Pi.single_eq_same,smul_eq_mul,mul_one,Function.comp_def,id_eq] using hd

 

noncomputable def scalarMeanJet : HeatJet 0 where
  F := fun _ => 0
  A := fun x => Real.tanh (x 0)
  G := fun _ _ => 0
  H := fun _ _ => 0
  A₁ := fun _ x => Scalar.curvature (x 0)
  A₂ := fun _ x => Scalar.third (x 0)
  C := 0
  lipschitz := LipschitzWith.const _
  smoothA := scalarTanh_bddSmooth
  smoothG _ := BddSmooth.const 0 0
  smoothH _ := BddSmooth.const 0 0
  smoothA₁ _ := scalarCurvature_bddSmooth
  smoothA₂ _ := scalarThird_bddSmooth
  derivF x v t := by simpa using hasDerivAt_const t (0:ℝ)
  derivG i x t := hasDerivAt_const t 0
  derivA := scalarTanh_derivative
  derivA₁ := scalarCurvature_derivative

 theorem scalarMeanJet_strict {t : ℝ} (ht : 0 < t) :
    (∫ z, (Real.tanh z)^2 ∂gaussianReal 0 (Real.toNNReal t)) <
      t*(∫ z, (Scalar.curvature z)^2 ∂gaussianReal 0 (Real.toNNReal t)) := by
  have hv := Scalar.variance_gaussian_pos Scalar.curvature_bddSmooth Scalar.curvature_nonconstant
    (v := Real.toNNReal t) (by exact ne_of_gt (Real.toNNReal_pos.mpr ht))
  have he (f : ℝ → ℝ) (hf : Continuous f) : clockRoot (fun x : Fin 1 → ℝ => f (x 0)) t 0 =
      ∫ z, f z ∂gaussianReal 0 (Real.toNNReal t) := by
    change (∫ z : Fin 1 → ℝ, f ((0+z) 0) ∂Measure.pi fun _ : Fin 1 => gaussianReal 0 (Real.toNNReal t)) = _
    simpa only [zero_add] using integral_gaussian_eval (0:Fin 1) (Real.toNNReal t) hf
  have hcurv := he (fun z => Scalar.curvature z) Scalar.curvature_continuous
  have hcurv2 := he (fun z => (Scalar.curvature z)^2) (Scalar.curvature_continuous.pow 2)
  have htanh := he (fun z => Real.tanh z) Scalar.tanh_continuous
  have htanh2 := he (fun z => (Real.tanh z)^2) (Scalar.tanh_continuous.pow 2)
  have hder : (∑ i : Fin 1, (clockRoot (scalarMeanJet.A₁ i) t 0)^2) <
      clockRoot (fun y => ∑ i : Fin 1, (scalarMeanJet.A₁ i y)^2) t 0 := by
    change (∑ i : Fin 1, (clockRoot (fun x : Fin 1 → ℝ => Scalar.curvature (x 0)) t 0)^2) <
      clockRoot (fun y : Fin 1 → ℝ => ∑ i : Fin 1, (Scalar.curvature (y 0))^2) t 0
    simpa only [Fin.sum_univ_one,hcurv,hcurv2] using sub_pos.mp hv
  have hh := scalarMeanJet.gaussian_poincare_strict ht 0 hder
  change clockRoot (fun y : Fin 1 → ℝ => (Real.tanh (y 0))^2) t 0-
    (clockRoot (fun y : Fin 1 → ℝ => Real.tanh (y 0)) t 0)^2 <
    t*clockRoot (fun y : Fin 1 → ℝ => ∑ i : Fin 1, (Scalar.curvature (y 0))^2) t 0 at hh
  simpa only [Fin.sum_univ_one,htanh2,htanh,hcurv2,
    Scalar.gaussian_tanh_mean_zero,zero_pow (by decide : 2 ≠ 0),sub_zero] using hh

end SKFluctuations.Hierarchy

namespace SKFluctuations.Scalar
open MeasureTheory ProbabilityTheory
open scoped NNReal

 

theorem rs_replicon_strict {T q : ℝ} (hT : 0 < T) (hq : 0 < q)
    (hfix : q = ∫ z, (Real.tanh z)^2 ∂gaussianReal 0 (Real.toNNReal (T*q))) :
    1 < T*(∫ z, (curvature z)^2 ∂gaussianReal 0 (Real.toNNReal (T*q))) := by
  have hh := Hierarchy.scalarMeanJet_strict (mul_pos hT hq)
  rw [← hfix] at hh
  nlinarith

end SKFluctuations.Scalar

end

end OAI
