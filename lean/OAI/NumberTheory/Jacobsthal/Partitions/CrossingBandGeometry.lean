import Mathlib.Algebra.Order.Group.MinMax
import OAI.NumberTheory.Jacobsthal.Estimates.SourceCandidateFreezing
import OAI.NumberTheory.Jacobsthal.Probability.ArrivalKernelGeometry

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.LogarithmicBinScale


noncomputable def binCount (w z xi : ℝ) : ℕ := ⌈Real.log (z/w)/Real.log (1+xi)⌉₊
noncomputable def logWidth (w z xi : ℝ) : ℝ := Real.log (z/w)/(binCount w z xi:ℝ)
noncomputable def effectiveWidth (w z xi : ℝ) : ℝ := Real.exp (logWidth w z xi)-1

theorem span_log_pos {w z : ℝ} (hw : 0 < w) (hwz : w < z) : 0 < Real.log (z/w) := by
  apply Real.log_pos
  exact (lt_div_iff₀ hw).mpr (by simpa only [one_mul] using hwz)

theorem binCount_pos {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi) :
    0 < binCount w z xi :=
  Nat.ceil_pos.mpr (div_pos (span_log_pos hw hwz) (Real.log_pos (by linarith)))

theorem logWidth_pos {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi) :
    0 < logWidth w z xi :=
  div_pos (span_log_pos hw hwz) (by exact_mod_cast binCount_pos hw hwz hxi)

theorem count_mul_logWidth {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi) :
    (binCount w z xi:ℝ)*logWidth w z xi = Real.log (z/w) := by
  have hn : (binCount w z xi:ℝ) ≠ 0 := by exact_mod_cast (binCount_pos hw hwz hxi).ne'
  unfold logWidth
  field_simp [hn]

theorem logWidth_le {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi) :
    logWidth w z xi ≤ Real.log (1+xi) := by
  have hlog : 0 < Real.log (1+xi) := Real.log_pos (by linarith)
  have hc := Nat.le_ceil (Real.log (z/w)/Real.log (1+xi))
  have hm := (div_le_iff₀ hlog).mp hc
  change Real.log (z/w) ≤ (binCount w z xi:ℝ)*Real.log (1+xi) at hm
  apply (div_le_iff₀ (by exact_mod_cast binCount_pos hw hwz hxi : (0:ℝ) < binCount w z xi)).mpr
  exact (by nlinarith : Real.log (z/w) ≤ Real.log (1+xi)*(binCount w z xi:ℝ))

theorem logWidth_ge_half {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi)
    (hspan : Real.log (1+xi) ≤ Real.log (z/w)) :
    Real.log (1+xi)/2 ≤ logWidth w z xi := by
  have hlog : 0 < Real.log (1+xi) := Real.log_pos (by linarith)
  have hc := Nat.ceil_lt_add_one (div_pos (span_log_pos hw hwz) hlog).le
  have hm := mul_lt_mul_of_pos_right hc hlog
  have he : (Real.log (z/w)/Real.log (1+xi)+1)*Real.log (1+xi) =
      Real.log (z/w)+Real.log (1+xi) := by field_simp [hlog.ne']
  rw [he] at hm
  apply (le_div_iff₀ (by exact_mod_cast binCount_pos hw hwz hxi : (0:ℝ) < binCount w z xi)).mpr
  change _ ≤ Real.log (z/w)
  change (binCount w z xi:ℝ)*Real.log (1+xi) < _ at hm
  nlinarith

theorem effectiveWidth_pos {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi) :
    0 < effectiveWidth w z xi := by
  exact sub_pos.mpr (Real.one_lt_exp_iff.mpr (logWidth_pos hw hwz hxi))

theorem effectiveWidth_le {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi) :
    effectiveWidth w z xi ≤ xi := by
  have he := Real.exp_le_exp.mpr (logWidth_le hw hwz hxi)
  rw [Real.exp_log (by linarith : 0 < 1+xi)] at he
  exact sub_le_iff_le_add.mpr (by linarith)

theorem effectiveWidth_ge_quarter {w z xi : ℝ} (hw : 0 < w) (hwz : w < z)
    (hxi : 0 < xi) (hxi1 : xi ≤ 1) (hspan : Real.log (1+xi) ≤ Real.log (z/w)) :
    xi/4 ≤ effectiveWidth w z xi := by
  have hpos : 0 < 1+xi := by linarith
  have hl := Real.one_sub_inv_le_log_of_pos hpos
  have he : 1-(1+xi)⁻¹ = xi/(1+xi) := by field_simp [hpos.ne']; ring
  rw [he] at hl
  have hf : xi/2 ≤ xi/(1+xi) := div_le_div_of_nonneg_left hxi.le hpos (by linarith)
  have hwide := logWidth_ge_half hw hwz hxi hspan
  have hexp := Real.add_one_le_exp (logWidth w z xi)
  unfold effectiveWidth
  linarith

end NumberTheoryLean.LogarithmicBinScale



namespace NumberTheoryLean.LogarithmicBinEndpoints

open LogarithmicBinScale PrimeBinRepresentatives ErdosInversePrimeBin

noncomputable def endpoint (w z xi : ℝ) (k : ℕ) : ℝ := w*Real.exp ((k:ℝ)*logWidth w z xi)
noncomputable def lower (w z xi : ℝ) (i : Fin (binCount w z xi)) : ℝ := endpoint w z xi i.1
noncomputable def width (w z xi : ℝ) (_i : Fin (binCount w z xi)) : ℝ := effectiveWidth w z xi
noncomputable def upper (w z xi : ℝ) (i : Fin (binCount w z xi)) : ℝ :=
  (1+width w z xi i)*lower w z xi i

theorem endpoint_zero (w z xi : ℝ) : endpoint w z xi 0 = w := by simp [endpoint]

theorem upper_endpoint (w z xi : ℝ) (i : Fin (binCount w z xi)) :
    upper w z xi i = endpoint w z xi (i.1+1) := by
  simp only [upper,width,lower,effectiveWidth,endpoint,Nat.cast_add,Nat.cast_one,add_mul,one_mul,Real.exp_add]
  ring

theorem endpoint_count {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi) :
    endpoint w z xi (binCount w z xi) = z := by
  rw [endpoint,count_mul_logWidth hw hwz hxi,Real.exp_log (div_pos (hw.trans hwz) hw)]
  field_simp [hw.ne']

theorem endpoint_pos {w z xi : ℝ} (hw : 0 < w) (k : ℕ) : 0 < endpoint w z xi k := by
  exact mul_pos hw (Real.exp_pos _)

theorem endpoint_mono {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi)
    {k m : ℕ} (hkm : k ≤ m) : endpoint w z xi k ≤ endpoint w z xi m := by
  have hc : (k:ℝ) ≤ m := by exact_mod_cast hkm
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hc (logWidth_pos hw hwz hxi).le)) hw.le

theorem bin_source_bounds {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi)
    (i : Fin (binCount w z xi)) : w ≤ lower w z xi i ∧ lower w z xi i < upper w z xi i ∧
      upper w z xi i ≤ z := by
  have hlow : w ≤ lower w z xi i := by
    have h := endpoint_mono hw hwz hxi (Nat.zero_le i.1)
    simpa only [endpoint_zero,lower] using h
  have hstrict : lower w z xi i < upper w z xi i := by
    have hp : 0 < lower w z xi i := endpoint_pos hw _
    have he : 0 < width w z xi i := effectiveWidth_pos hw hwz hxi
    unfold upper
    nlinarith
  refine ⟨hlow,hstrict,?_⟩
  rw [upper_endpoint]
  exact (endpoint_mono hw hwz hxi (Nat.succ_le_of_lt i.isLt)).trans_eq (endpoint_count hw hwz hxi)

theorem bins_separated {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi)
    (i j : Fin (binCount w z xi)) (hij : i ≠ j) :
    upper w z xi i ≤ lower w z xi j ∨ upper w z xi j ≤ lower w z xi i := by
  have hne : i.1 ≠ j.1 := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · apply Or.inl
    rw [upper_endpoint]
    exact endpoint_mono hw hwz hxi (by omega)
  · apply Or.inr
    rw [upper_endpoint]
    exact endpoint_mono hw hwz hxi (by omega)

theorem last_bin_endpoint {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi)
    (i : Fin (binCount w z xi)) (hi : i.1+1 = binCount w z xi) : upper w z xi i = z := by
  rw [upper_endpoint,hi,endpoint_count hw hwz hxi]

theorem bin_prime_in_source {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi)
    (i : Fin (binCount w z xi)) {p : ℕ} (hp : p ∈ primeBin (lower w z xi i) (width w z xi i)) :
    p.Prime ∧ w < (p:ℝ) ∧ (p:ℝ) ≤ z := by
  have hb := (mem_primeBin (endpoint_pos hw i.1).le (effectiveWidth_pos hw hwz hxi).le p).mp hp
  have hs := bin_source_bounds hw hwz hxi i
  exact ⟨hb.1,hs.1.trans_lt hb.2.1,hb.2.2.trans hs.2.2⟩

end NumberTheoryLean.LogarithmicBinEndpoints



namespace NumberTheoryLean.LogarithmicBinLabels

open LogarithmicBinScale LogarithmicBinEndpoints ErdosInversePrimeBin

noncomputable def coordinate (w z xi : ℝ) (p : ℕ) : ℝ := Real.log ((p:ℝ)/w)/logWidth w z xi

noncomputable def index (w z xi : ℝ) (p : ℕ) : ℕ :=
  min (binCount w z xi-1) (⌈coordinate w z xi p⌉₊-1)

theorem coordinate_bounds {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi)
    {p : ℕ} (hp : w < (p:ℝ) ∧ (p:ℝ) ≤ z) :
    0 < coordinate w z xi p ∧ coordinate w z xi p ≤ (binCount w z xi:ℝ) := by
  have hlog : 0 < Real.log ((p:ℝ)/w) := by
    apply Real.log_pos
    exact (lt_div_iff₀ hw).mpr (by simpa only [one_mul] using hp.1)
  have hd := logWidth_pos hw hwz hxi
  refine ⟨div_pos hlog hd,?_⟩
  apply (div_le_iff₀ hd).mpr
  rw [count_mul_logWidth hw hwz hxi]
  exact Real.log_le_log (div_pos (hw.trans hp.1) hw) (div_le_div_of_nonneg_right hp.2 hw.le)

theorem index_lt {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi) (p : ℕ) :
    index w z xi p < binCount w z xi := by
  have hn := binCount_pos hw hwz hxi
  have hm : index w z xi p ≤ binCount w z xi-1 := min_le_left _ _
  omega

noncomputable def label {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi)
    (p : ℕ) : Fin (binCount w z xi) := ⟨index w z xi p,index_lt hw hwz hxi p⟩

theorem index_eq_ceiling {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi)
    {p : ℕ} (hp : w < (p:ℝ) ∧ (p:ℝ) ≤ z) : index w z xi p = ⌈coordinate w z xi p⌉₊-1 := by
  have hc : ⌈coordinate w z xi p⌉₊ ≤ binCount w z xi := Nat.ceil_le.mpr (coordinate_bounds hw hwz hxi hp).2
  exact min_eq_right (by omega)

theorem label_coordinate_bounds {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi)
    {p : ℕ} (hp : w < (p:ℝ) ∧ (p:ℝ) ≤ z) :
    ((label hw hwz hxi p).1:ℝ) < coordinate w z xi p ∧
      coordinate w z xi p ≤ ((label hw hwz hxi p).1:ℝ)+1 := by
  have hc := coordinate_bounds hw hwz hxi hp
  have hpos : 0 < ⌈coordinate w z xi p⌉₊ := Nat.ceil_pos.mpr hc.1
  have hlow := Nat.ceil_lt_add_one hc.1.le
  have hhigh := Nat.le_ceil (coordinate w z xi p)
  have he : ((label hw hwz hxi p).1:ℝ) = (⌈coordinate w z xi p⌉₊:ℝ)-1 := by
    change (index w z xi p:ℝ) = _
    rw [index_eq_ceiling hw hwz hxi hp,Nat.cast_sub (by omega : 1 ≤ ⌈coordinate w z xi p⌉₊)]
    norm_num
  rw [he]
  constructor <;> linarith

theorem label_value_bounds {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi)
    {p : ℕ} (hp : w < (p:ℝ) ∧ (p:ℝ) ≤ z) :
    lower w z xi (label hw hwz hxi p) < (p:ℝ) ∧
      (p:ℝ) ≤ upper w z xi (label hw hwz hxi p) := by
  have hb := label_coordinate_bounds hw hwz hxi hp
  have hd := logWidth_pos hw hwz hxi
  have hpw : 0 < (p:ℝ)/w := div_pos (hw.trans hp.1) hw
  have he : coordinate w z xi p*logWidth w z xi = Real.log ((p:ℝ)/w) := by
    unfold coordinate
    field_simp [hd.ne']
  have hlo := mul_lt_mul_of_pos_right hb.1 hd
  have hhi := mul_le_mul_of_nonneg_right hb.2 hd.le
  rw [he] at hlo hhi
  have hExpLo := Real.exp_lt_exp.mpr hlo
  have hExpHi := Real.exp_le_exp.mpr hhi
  rw [Real.exp_log hpw] at hExpLo hExpHi
  constructor
  · have h := (lt_div_iff₀ hw).mp hExpLo
    simpa only [lower,endpoint,mul_comm] using h
  · rw [upper_endpoint]
    have h := (div_le_iff₀ hw).mp hExpHi
    simpa only [endpoint,Nat.cast_add,Nat.cast_one,mul_comm] using h

theorem label_prime_membership {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi)
    {p : ℕ} (hprime : p.Prime) (hp : w < (p:ℝ) ∧ (p:ℝ) ≤ z) :
    p ∈ primeBin (lower w z xi (label hw hwz hxi p)) (width w z xi (label hw hwz hxi p)) := by
  apply (mem_primeBin (endpoint_pos hw _).le (effectiveWidth_pos hw hwz hxi).le p).mpr
  exact ⟨hprime,(label_value_bounds hw hwz hxi hp).1,(label_value_bounds hw hwz hxi hp).2⟩

end NumberTheoryLean.LogarithmicBinLabels



namespace NumberTheoryLean.LogarithmicBinPartition

open _root_.Set _root_.Finset
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels ErdosInversePrimeBin

noncomputable def sourcePrimeSet (w z : ℝ) : Finset ℕ := Nat.primesLE ⌊z⌋₊ \ Nat.primesLE ⌊w⌋₊

theorem mem_sourcePrimeSet {w z : ℝ} (hw : 0 < w) (hwz : w < z) (p : ℕ) :
    p ∈ sourcePrimeSet w z ↔ p.Prime ∧ w < (p:ℝ) ∧ (p:ℝ) ≤ z := by
  constructor
  · intro hp
    obtain ⟨hup,hnot⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hbound,hprime⟩ := Nat.mem_primesLE.mp hup
    refine ⟨hprime,?_,(Nat.le_floor_iff (hw.trans hwz).le).mp hbound⟩
    by_contra! hlo
    exact hnot (Nat.mem_primesLE.mpr ⟨(Nat.le_floor_iff hw.le).mpr hlo,hprime⟩)
  · rintro ⟨hprime,hlo,hhi⟩
    apply Finset.mem_sdiff.mpr
    refine ⟨Nat.mem_primesLE.mpr ⟨(Nat.le_floor_iff (hw.trans hwz).le).mpr hhi,hprime⟩,?_⟩
    intro hp
    exact (not_le_of_gt hlo) ((Nat.le_floor_iff hw.le).mp (Nat.mem_primesLE.mp hp).1)

theorem bin_mem_iff_label {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi)
    (i : Fin (binCount w z xi)) (p : ℕ) :
    p ∈ primeBin (lower w z xi i) (width w z xi i) ↔
      p.Prime ∧ w < (p:ℝ) ∧ (p:ℝ) ≤ z ∧ label hw hwz hxi p = i := by
  constructor
  · intro hp
    have hs := bin_prime_in_source hw hwz hxi i hp
    have hI := (mem_primeBin (endpoint_pos hw _).le (effectiveWidth_pos hw hwz hxi).le p).mp hp
    have hL := label_value_bounds hw hwz hxi hs.2
    refine ⟨hs.1,hs.2.1,hs.2.2,?_⟩
    by_contra hne
    have hsep := bins_separated hw hwz hxi i (label hw hwz hxi p) (Ne.symm hne)
    have huI : (p:ℝ) ≤ upper w z xi i := hI.2.2
    have hlI : lower w z xi i < (p:ℝ) := hI.2.1
    rcases hsep with hsep | hsep <;> linarith [hlI,hL.1,hL.2]
  · rintro ⟨hprime,hlo,hhi,heq⟩
    rw [← heq]
    exact label_prime_membership hw hwz hxi hprime ⟨hlo,hhi⟩

theorem bins_pairwise_disjoint {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi)
    (i j : Fin (binCount w z xi)) (hij : i ≠ j) :
    Disjoint (primeBin (lower w z xi i) (width w z xi i))
      (primeBin (lower w z xi j) (width w z xi j)) := by
  apply Finset.disjoint_left.mpr
  intro p hi hj
  have hpi := (bin_mem_iff_label hw hwz hxi i p).mp hi
  have hpj := (bin_mem_iff_label hw hwz hxi j p).mp hj
  exact hij (hpi.2.2.2.symm.trans hpj.2.2.2)

theorem union_bins_eq_source {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi) :
    (Finset.univ : Finset (Fin (binCount w z xi))).biUnion
      (fun i => primeBin (lower w z xi i) (width w z xi i)) = sourcePrimeSet w z := by
  ext p
  constructor
  · intro hp
    obtain ⟨i,_hi,hp⟩ := Finset.mem_biUnion.mp hp
    exact (mem_sourcePrimeSet hw hwz p).mpr (bin_prime_in_source hw hwz hxi i hp)
  · intro hp
    have hs := (mem_sourcePrimeSet hw hwz p).mp hp
    exact Finset.mem_biUnion.mpr ⟨label hw hwz hxi p,Finset.mem_univ _,
      label_prime_membership hw hwz hxi hs.1 hs.2⟩

theorem source_sum_over_bins {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi)
    (F : ℕ → ℝ) :
    (∑ p ∈ sourcePrimeSet w z,F p) =
      ∑ i : Fin (binCount w z xi),∑ p ∈ primeBin (lower w z xi i) (width w z xi i),F p := by
  rw [← union_bins_eq_source hw hwz hxi]
  exact Finset.sum_biUnion (fun i _ j _ hij => bins_pairwise_disjoint hw hwz hxi i j hij)

end NumberTheoryLean.LogarithmicBinPartition



namespace NumberTheoryLean.NearbyParentGeometry

open FinitePathGeometry OccupationBoundaries

theorem minRatio_stability (i : Side) (s t : ℝ) :
    |minRatio i s-minRatio i t| ≤ |s-t| := by
  cases i with
  | even => simp [minRatio]
  | odd =>
    simpa only [minRatio, sub_sub_sub_cancel_right, sub_self, abs_zero,
      max_eq_right (abs_nonneg (s-t))] using abs_max_sub_max_le_max (2:ℝ) (s-1) 2 (t-1)

theorem log_stability {m x y : ℝ} (hm : 0 < m) (hx : m ≤ x) (hy : m ≤ y) :
    |Real.log x-Real.log y| ≤ |x-y|/m := by
  wlog hxy : y ≤ x generalizing x y
  · simpa only [abs_sub_comm] using this hy hx (le_of_not_ge hxy)
  have hx0 := hm.trans_le hx
  have hy0 := hm.trans_le hy
  rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hy0 hxy)), abs_of_nonneg (sub_nonneg.mpr hxy)]
  have h := Real.log_le_sub_one_of_pos (div_pos hx0 hy0)
  rw [Real.log_div hx0.ne' hy0.ne'] at h
  calc
    Real.log x-Real.log y ≤ (x-y)/y := by
      convert h using 1
      field_simp
    _ ≤ (x-y)/m := div_le_div_of_nonneg_left (sub_nonneg.mpr hxy) hm hy

theorem cost_stability {s t : ℝ} (hs : (1/2:ℝ) ≤ s) (ht : (1/2:ℝ) ≤ t) :
    |cost s-cost t| ≤ 4*|s-t| := by
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  have h1 := log_stability (m:=1/2) (by norm_num) hs ht
  have h2 := log_stability (m:=1/2) (x:=s+1) (y:=t+1) (by norm_num) (by linarith) (by linarith)
  have heq : cost s-cost t = (Real.log (s+1)-Real.log (t+1))-(Real.log s-Real.log t) := by
    linarith [cost_add_log hs0, cost_add_log ht0]
  rw [heq]
  calc
    _ ≤ |Real.log (s+1)-Real.log (t+1)|+|Real.log s-Real.log t| := abs_sub _ _
    _ ≤ 4*|s-t| := by
      simp only [add_sub_add_right_eq_sub] at h2
      linarith

theorem clipped_relative_stability {A x y c : ℝ} (hA : 0 ≤ A) (hc : 1 ≤ c)
    (hxy : x ≤ c*y) (hyx : y ≤ c*x) :
    |min A x-min A y| ≤ A*(c-1) := by
  have hnonneg : 0 ≤ A*(c-1) := mul_nonneg hA (by linarith)
  simp only [min_def]
  split_ifs <;> apply abs_le.mpr <;> constructor <;> nlinarith

theorem log_gap_relative {r q d : ℝ} (hr : 0 < r) (hq : 0 < q)
    (hd : |Real.log r-Real.log q| ≤ d) : r ≤ Real.exp d*q ∧ q ≤ Real.exp d*r := by
  have h1 := Real.exp_le_exp.mpr (abs_le.mp hd).2
  have h2 := Real.exp_le_exp.mpr (show Real.log q-Real.log r ≤ d by linarith [(abs_le.mp hd).1])
  rw [Real.exp_sub,Real.exp_log hr,Real.exp_log hq] at h1
  rw [Real.exp_sub,Real.exp_log hq,Real.exp_log hr] at h2
  exact ⟨(div_le_iff₀ hq).mp h1,(div_le_iff₀ hr).mp h2⟩

theorem arrival_endpoint_stability {r q ell S d : ℝ} (hr : 0 < r) (hq : 0 < q)
    (hell : 0 < ell) (hS : 0 ≤ S+1) (hd : |Real.log r-Real.log q| ≤ d) :
    |min S (r/ell-1)-min S (q/ell-1)| ≤ (S+1)*(Real.exp d-1) := by
  have hrel := log_gap_relative hr hq hd
  have hd0 : 0 ≤ d := (abs_nonneg _).trans hd
  have he : 1 ≤ Real.exp d := Real.one_le_exp_iff.mpr hd0
  have h1 : r/ell ≤ Real.exp d*(q/ell) := by
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hrel.1 hell.le
  have h2 : q/ell ≤ Real.exp d*(r/ell) := by
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hrel.2 hell.le
  have h := clipped_relative_stability hS he h1 h2
  have hu (x:ℝ) : min S (x-1) = min (S+1) x-1 := by
    rw [← min_sub_sub_right]
    simp
  simpa only [hu,sub_sub_sub_cancel_right] using h

theorem log_gap_step {r q s t d e : ℝ} (hr : 0 < r) (hq : 0 < q)
    (hs : (1/2:ℝ) ≤ s) (ht : (1/2:ℝ) ≤ t)
    (hd : |Real.log r-Real.log q| ≤ d) (he : |s-t| ≤ e) :
    |Real.log (nextGap r s)-Real.log (nextGap q t)| ≤ d+4*e := by
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  rw [nextGap_eq_cost hs0,nextGap_eq_cost ht0,Real.log_mul hr.ne' (Real.exp_pos _).ne',
    Real.log_mul hq.ne' (Real.exp_pos _).ne',Real.log_exp,Real.log_exp]
  have ha := abs_sub (Real.log r-Real.log q) (cost s-cost t)
  have hc := cost_stability hs ht
  have heq : Real.log r + -cost s-(Real.log q + -cost t) =
      (Real.log r-Real.log q)-(cost s-cost t) := by ring
  rw [heq]
  linarith

end NumberTheoryLean.NearbyParentGeometry



namespace NumberTheoryLean.LogarithmicBinMaps

open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open SourceStopPredicate PrimeBinRepresentatives RepresentativeAdmission PrimeHistories
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem source_list_boxed {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi)
    (ps : List ℕ) (hp : ∀ p ∈ ps,p ∈ sourcePrimeSet w z) :
    boxed (lower w z xi) (width w z xi) (label hw hwz hxi) ps := by
  intro p hps
  have hs := (mem_sourcePrimeSet hw hwz p).mp (hp p hps)
  exact label_prime_membership hw hwz hxi hs.1 hs.2

theorem source_representative_error {w z xi : ℝ} (hw : 1 < w) (hwz : w < z) (hxi : 0 < xi)
    {p : ℕ} (hp : p ∈ sourcePrimeSet w z) :
    0 ≤ representative w (lower w z xi) (width w z xi) (label (by linarith : 0 < w) hwz hxi) p-primeExponent w p ∧
      representative w (lower w z xi) (width w z xi) (label (by linarith : 0 < w) hwz hxi) p-primeExponent w p ≤ xi/Real.log w := by
  have hw0 : 0 < w := by linarith
  have hs := (mem_sourcePrimeSet hw0 hwz p).mp hp
  have hbin := label_prime_membership hw0 hwz hxi hs.1 hs.2
  have he := representative_error hw (endpoint_pos hw0 _) (effectiveWidth_pos hw0 hwz hxi).le hbin
  refine ⟨he.1,he.2.trans ?_⟩
  exact div_le_div_of_nonneg_right (effectiveWidth_le hw0 hwz hxi) (Real.log_pos hw).le

theorem source_prefix_movement {w z xi B Clen : ℝ} (hw : 1 < w) (hwz : w < z) (hxi : 0 < xi)
    (hC : 0 ≤ Clen) (hcomp : Real.log B ≤ 2*Real.log w) (v : Node) (ps : List ℕ)
    (hp : ∀ p ∈ ps,p ∈ sourcePrimeSet w z) (hlen : (ps.length:ℝ) ≤ Clen*Real.log B) :
    0 ≤ (terminal w v ps).gap-representativeGap
      (representative w (lower w z xi) (width w z xi) (label (by linarith : 0 < w) hwz hxi)) v.gap ps ∧
    (terminal w v ps).gap-representativeGap
      (representative w (lower w z xi) (width w z xi) (label (by linarith : 0 < w) hwz hxi)) v.gap ps ≤ 2*Clen*xi := by
  exact source_movement_bound hw hC hxi.le hcomp _ v ps hlen
    (fun p hps => source_representative_error hw hwz hxi (hp p hps))

theorem common_width_bounds {w z xi : ℝ} (hw : 0 < w) (hwz : w < z)
    (hxi : 0 < xi) (hxi1 : xi ≤ 1) (hspan : (1+xi)*w ≤ z) :
    0 < effectiveWidth w z xi ∧ xi/4 ≤ effectiveWidth w z xi ∧ effectiveWidth w z xi ≤ xi ∧
      ∀ i : Fin (binCount w z xi),width w z xi i = effectiveWidth w z xi := by
  have hl : Real.log (1+xi) ≤ Real.log (z/w) :=
    Real.log_le_log (by linarith : 0 < 1+xi) ((le_div_iff₀ hw).mpr hspan)
  exact ⟨effectiveWidth_pos hw hwz hxi,effectiveWidth_ge_quarter hw hwz hxi hxi1 hl,
    effectiveWidth_le hw hwz hxi,fun _ => rfl⟩

theorem endpoint_exponent {w z xi : ℝ} (hw : 1 < w) (k : ℕ) :
    Real.log (endpoint w z xi k)/Real.log w = 1+(k:ℝ)*(logWidth w z xi/Real.log w) := by
  have hw0 : 0 < w := by linarith
  rw [endpoint,Real.log_mul hw0.ne' (Real.exp_pos _).ne',Real.log_exp]
  field_simp [(Real.log_pos hw).ne']

theorem representative_exponent {w z xi : ℝ} (hw : 1 < w) (i : Fin (binCount w z xi)) :
    rightExponent w (lower w z xi i) (width w z xi i) =
      1+((i.1:ℝ)+1)*(logWidth w z xi/Real.log w) := by
  change Real.log (upper w z xi i)/Real.log w = _
  rw [upper_endpoint,endpoint_exponent hw]
  simp only [Nat.cast_add,Nat.cast_one]

end NumberTheoryLean.LogarithmicBinMaps



namespace NumberTheoryLean.IsolatedBinGeometry
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition LogarithmicBinMaps
open PrimeBinRepresentatives SourceStopPredicate
open ErdosPrimeInputs.HarmonicPrimeMeasure

noncomputable def isolatedBin (w top xi B alpha beta : ℝ) (b : Fin (binCount w top xi)) : Prop :=
  alpha*B ≤ leftExponent w (lower w top xi b) ∧ rightExponent w (lower w top xi b) (width w top xi b) ≤ beta*B

theorem source_left_error {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    {p : ℕ} (hp : p ∈ sourcePrimeSet w top) :
    0 ≤ primeExponent w p-leftExponent w (lower w top xi (label (zero_lt_one.trans hw) htop hxi p)) ∧
      primeExponent w p-leftExponent w (lower w top xi (label (zero_lt_one.trans hw) htop hxi p)) ≤ xi/Real.log w := by
  have hp' := (mem_sourcePrimeSet (zero_lt_one.trans hw) htop p).mp hp
  have hbin := label_prime_membership (zero_lt_one.trans hw) htop hxi hp'.1 hp'.2
  have hh := bin_exponent_bounds hw (endpoint_pos (zero_lt_one.trans hw) _) (effectiveWidth_pos (zero_lt_one.trans hw) htop hxi).le hbin
  have hwid := bin_exponent_width (w:=w)
    (R:=lower w top xi (label (zero_lt_one.trans hw) htop hxi p))
    (xi:=width w top xi (label (zero_lt_one.trans hw) htop hxi p))
    (endpoint_pos (zero_lt_one.trans hw) _) (effectiveWidth_pos (zero_lt_one.trans hw) htop hxi).le
  have heff := effectiveWidth_pos (zero_lt_one.trans hw) htop hxi
  have hlog : Real.log (1+effectiveWidth w top xi) ≤ xi := by
    have he := Real.log_le_sub_one_of_pos (by positivity : 0 < 1+effectiveWidth w top xi)
    linarith [effectiveWidth_le (zero_lt_one.trans hw) htop hxi]
  refine ⟨sub_nonneg.mpr hh.1.le,?_⟩
  have hb := div_le_div_of_nonneg_right hlog (Real.log_pos hw).le
  simp only [width,lower] at hwid ⊢
  linarith [hh.2]

theorem whole_bin_of_exponent_band {w top xi B alpha beta : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    {p : ℕ} (hp : p ∈ sourcePrimeSet w top)
    (hlo : alpha*B+xi/Real.log w ≤ primeExponent w p)
    (hhi : primeExponent w p+xi/Real.log w ≤ beta*B) :
    isolatedBin w top xi B alpha beta (label (zero_lt_one.trans hw) htop hxi p) := by
  have hl := (source_left_error hw htop hxi hp).2
  have hu := (source_representative_error hw htop hxi hp).2
  change rightExponent w (lower w top xi _) (width w top xi _)-primeExponent w p ≤ _ at hu
  exact ⟨by linarith,by linarith⟩

theorem isolated_bin_search {w top xi B alpha beta : ℝ} {b : Fin (binCount w top xi)}
    (hb : isolatedBin w top xi B alpha beta b) (hscale : w^((1/4:ℝ)) ≤ alpha*B) :
    ActualSourceTags.searchBin w (lower w top xi b) := hscale.trans hb.1
end NumberTheoryLean.IsolatedBinGeometry



namespace NumberTheoryLean.RepeatedBinGeometry
open _root_.Set FinitePathGeometry SourceStopPredicate
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition LogarithmicBinMaps
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem equal_label_exponent_distance {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    {p q : ℕ} (hp : p ∈ sourcePrimeSet w top) (hq : q ∈ sourcePrimeSet w top)
    (hl : label (zero_lt_one.trans hw) htop hxi p=label (zero_lt_one.trans hw) htop hxi q) :
    |primeExponent w p-primeExponent w q| ≤ xi/Real.log w := by
  have hpe := source_representative_error hw htop hxi hp
  have hqe := source_representative_error hw htop hxi hq
  have he : representative w (lower w top xi) (width w top xi) (label (zero_lt_one.trans hw) htop hxi) p=
      representative w (lower w top xi) (width w top xi) (label (zero_lt_one.trans hw) htop hxi) q := by
    unfold representative
    rw [hl]
  rw [he] at hpe
  exact abs_le.mpr ⟨by linarith [hpe.1,hpe.2,hqe.1,hqe.2],by linarith [hpe.1,hpe.2,hqe.1,hqe.2]⟩

theorem adjacent_ratio_slack {r x x' h : ℝ} (hr : 0 < r) (hx : 0 < x)
    (hxx : x ≤ x') (hwidth : x'-x ≤ h) :
    0 ≤ (r/x-1)-(r/x'-1) ∧ (r/x-1)-(r/x'-1) ≤ (r/x')*h/x := by
  have hx' : 0 < x' := hx.trans_le hxx
  have he : (r/x-1)-(r/x'-1)=(r/x')*(x'-x)/x := by
    field_simp [hx.ne',hx'.ne']
    ring
  rw [he]
  exact ⟨div_nonneg (mul_nonneg (div_pos hr hx').le (sub_nonneg.mpr hxx)) hx.le,
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hwidth (div_pos hr hx').le) hx.le⟩

theorem matched_repeat_interval (i : Side) {s t s' t' H mesh : ℝ}
    (hs : |s-s'| ≤ mesh) (ht : |t-t'| ≤ mesh)
    (hslack : t-(s-1) ≤ H) (hsupport : minRatio i s' ≤ t') :
    t' ∈ Icc (minRatio i s') (minRatio i s'+H+2*mesh) := by
  refine ⟨hsupport,?_⟩
  have hmin := minRatio_ge_sub_one i s'
  linarith [(abs_le.mp hs).2,(abs_le.mp ht).1]
end NumberTheoryLean.RepeatedBinGeometry



namespace NumberTheoryLean.BinReplacementOrder
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open ErdosInversePrimeBin

theorem prime_order_replacement {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi)
    (p p' q : ℕ) (hp : p ∈ sourcePrimeSet w z) (hp' : p' ∈ sourcePrimeSet w z)
    (hq : q ∈ sourcePrimeSet w z) (he : label hw hwz hxi p' = label hw hwz hxi p)
    (hne : label hw hwz hxi q ≠ label hw hwz hxi p) :
    (p < q ↔ p' < q) ∧ (q < p ↔ q < p') := by
  have bp := label_value_bounds hw hwz hxi ((mem_sourcePrimeSet hw hwz p).mp hp).2
  have bp' := label_value_bounds hw hwz hxi ((mem_sourcePrimeSet hw hwz p').mp hp').2
  have bq := label_value_bounds hw hwz hxi ((mem_sourcePrimeSet hw hwz q).mp hq).2
  rw [he] at bp'
  have hs := bins_separated hw hwz hxi (label hw hwz hxi p) (label hw hwz hxi q) hne.symm
  rcases hs with hs | hs
  · have h1 : p < q := by exact_mod_cast (show (p:ℝ)<q by linarith)
    have h2 : p' < q := by exact_mod_cast (show (p':ℝ)<q by linarith)
    exact ⟨iff_of_true h1 h2,iff_of_false (Nat.not_lt_of_ge h1.le) (Nat.not_lt_of_ge h2.le)⟩
  · have h1 : q < p := by exact_mod_cast (show (q:ℝ)<p by linarith)
    have h2 : q < p' := by exact_mod_cast (show (q:ℝ)<p' by linarith)
    exact ⟨iff_of_false (Nat.not_lt_of_ge h1.le) (Nat.not_lt_of_ge h2.le),iff_of_true h1 h2⟩

theorem unique_label_other {n : ℕ} (label : ℕ → Fin n) (pre tail : List ℕ) (p : ℕ)
    (hc : ((pre++p::tail).map label).count (label p) = 1) :
    ∀ q ∈ pre++tail,label q ≠ label p := by
  have h0 : ((pre++tail).map label).count (label p) = 0 := by
    simp only [List.map_append,List.map_cons,List.count_append,List.count_cons_self] at hc ⊢
    omega
  intro q hq he
  have hm : label p ∈ (pre++tail).map label := List.mem_map.mpr ⟨q,hq,he⟩
  have hh := List.count_pos_iff.mpr hm
  omega

theorem decreasing_replacement {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi)
    (pre tail : List ℕ) (p p' : ℕ)
    (hall : ∀ q ∈ pre++p::tail,q ∈ sourcePrimeSet w z)
    (hp' : p' ∈ sourcePrimeSet w z)
    (he : label hw hwz hxi p' = label hw hwz hxi p)
    (hc : ((pre++p::tail).map (label hw hwz hxi)).count (label hw hwz hxi p) = 1) :
    (pre++p::tail).Pairwise (· > ·) ↔ (pre++p'::tail).Pairwise (· > ·) := by
  have hp := hall p (by simp)
  have hother := unique_label_other (label hw hwz hxi) pre tail p hc
  have hqall (q : ℕ) (hq : q ∈ pre++tail) : q ∈ sourcePrimeSet w z := by
    apply hall q
    simp only [List.mem_append,List.mem_cons] at hq ⊢
    tauto
  have horder (q : ℕ) (hq : q ∈ pre++tail) :=
    prime_order_replacement hw hwz hxi p p' q hp hp' (hqall q hq) he (hother q hq)
  simp only [List.pairwise_append,List.pairwise_cons]
  constructor
  · rintro ⟨hpre,htail,hcross⟩
    refine ⟨hpre,⟨?_,htail.2⟩,?_⟩
    · intro q hq
      exact (horder q (by simp [hq])).2.mp (htail.1 q hq)
    · intro q hq r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact (horder q (by simp [hq])).1.mp (hcross q hq p (by simp))
      · exact hcross q hq r (by simp [hr])
  · rintro ⟨hpre,htail,hcross⟩
    refine ⟨hpre,⟨?_,htail.2⟩,?_⟩
    · intro q hq
      exact (horder q (by simp [hq])).2.mpr (htail.1 q hq)
    · intro q hq r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact (horder q (by simp [hq])).1.mpr (hcross q hq p' (by simp))
      · exact hcross q hq r (by simp [hr])

theorem replacement_no_collision {n : ℕ} (label : ℕ → Fin n) (pre tail : List ℕ) (p p' : ℕ)
    (hc : ((pre++p::tail).map label).count (label p) = 1) (he : label p' = label p) :
    p' ∉ pre++tail := by
  intro hp'
  exact unique_label_other label pre tail p hc p' hp' he
end NumberTheoryLean.BinReplacementOrder



namespace NumberTheoryLean.CrossingBandGeometry
open _root_.Set FinitePathGeometry FinitePathMeasures ArrivalKernelGeometry
open RegeneratingInverseBands

noncomputable def crossingLower (H : ℝ) : ℝ := (3/10)*H
noncomputable def crossingUpper (H : ℝ) : ℝ := (11/10)*H
noncomputable def crossingWidth : ℝ := Real.log ((11:ℝ)/3)
noncomputable def crossingCenter (v H : ℝ) : ℝ := v-Real.log (crossingUpper H)

theorem matched_gap_crossing {H r q d : ℝ} (_hH : 0 < H) (hr : 0 < r) (hq : 0 < q)
    (hlo : H/3 < r) (hhi : r ≤ H) (hd : |Real.log r-Real.log q| ≤ d)
    (he : Real.exp d ≤ 11/10) : q ∈ Icc (crossingLower H) (crossingUpper H) := by
  have h := NearbyParentGeometry.log_gap_relative hr hq hd
  have hl : r ≤ (11/10:ℝ)*q := h.1.trans (mul_le_mul_of_nonneg_right he hq.le)
  have hu : q ≤ (11/10:ℝ)*r := h.2.trans (mul_le_mul_of_nonneg_right he hr.le)
  exact ⟨by dsimp [crossingLower]; nlinarith,by dsimp [crossingUpper]; nlinarith⟩

theorem crossing_width_positive : 0 < crossingWidth := Real.log_pos (by norm_num)

theorem crossing_cost_band {H : ℝ} (hH : 0 < H) (v : ℝ) (z : CostState)
    (hz : gapValue v z ∈ Icc (crossingLower H) (crossingUpper H)) :
    z.2 ∈ Icc (crossingCenter v H) (crossingCenter v H+crossingWidth) := by
  have hlo : 0 < crossingLower H := by unfold crossingLower; positivity
  have hhi : 0 < crossingUpper H := by unfold crossingUpper; positivity
  have hl := Real.log_le_log hlo hz.1
  have hu := Real.log_le_log (Real.exp_pos (v-z.2)) hz.2
  change Real.log (crossingLower H) ≤ Real.log (Real.exp (v-z.2)) at hl
  change Real.log (Real.exp (v-z.2)) ≤ Real.log (crossingUpper H) at hu
  rw [Real.log_exp] at hl hu
  have hwidth : Real.log (crossingUpper H)-Real.log (crossingLower H)=crossingWidth := by
    unfold crossingWidth
    rw [← Real.log_div hhi.ne' hlo.ne']
    congr 1
    dsimp [crossingUpper,crossingLower]
    field_simp [hH.ne']
  constructor <;> dsimp [crossingCenter] <;> linarith
end NumberTheoryLean.CrossingBandGeometry


end Erdos970

end OAI
