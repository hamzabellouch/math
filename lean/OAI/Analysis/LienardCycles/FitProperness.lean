import OAI.Analysis.LienardCycles.AngleBounds

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter Metric
open Set Filter
open scoped Topology ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open scoped Topology

open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace QuinticLienard.QuadraticFit
open QuadraticCoordinates ReferenceCharacteristic RealAnalysis

noncomputable def seqA (r M : ℝ) (n : ℕ) (s : ℝ) : ℝ := A ((label ((((n:ℝ)+1),r),M),(n:ℝ)+1),s)
noncomputable def seqE (r M : ℝ) (n : ℕ) (s : ℝ) : ℝ := E ((label ((((n:ℝ)+1),r),M),(n:ℝ)+1),s)
noncomputable def seqJ (r M : ℝ) (n : ℕ) (s : ℝ) : ℝ := J ((label ((((n:ℝ)+1),r),M),(n:ℝ)+1),s)
noncomputable def seqL (r M : ℝ) (n : ℕ) (s : ℝ) : ℝ := L ((label ((((n:ℝ)+1),r),M),(n:ℝ)+1),s)
noncomputable def seqθ (r M : ℝ) (n : ℕ) (s : ℝ) : ℝ := angle (seqA r M n s)
noncomputable def seqg (r M : ℝ) (n : ℕ) (s : ℝ) : ℝ := s*(1-(seqA r M n s)^2)

lemma seqA_abs {r M s : ℝ} (n : ℕ) (hs : 0 < s) : |seqA r M n s|<1 := A_abs_lt hs
lemma seqA_mono {r M s : ℝ} (hr : 0 < r) (hM : |M|<1) (hs : 0 < s) (hsr : s < r) :
    Monotone (fun n => seqA r M n s) := by
  intro n m hnm
  exact (conditionalA_strictMono hr hM hs hsr).monotone (by exact_mod_cast Nat.add_le_add_right hnm 1)
lemma seqE_mono {r M s : ℝ} (hr : 0 < r) (hM : |M|<1) (hs : 0 < s) (hsr : s < r) :
    Monotone (fun n => seqE r M n s) := by
  intro n m hnm
  exact (conditionalE_strictMono hr hM hs hsr).monotone (by exact_mod_cast Nat.add_le_add_right hnm 1)
lemma seqθ_lower {r M s : ℝ} (hr : 0 < r) (hM : |M|<1) (hs : 0 < s) (hsr : s < r) (n : ℕ) :
    seqθ r M 0 s ≤ seqθ r M n s :=
  angle_strictMono.monotoneOn (abs_lt.mp (seqA_abs 0 hs)) (abs_lt.mp (seqA_abs n hs))
    (seqA_mono hr hM hs hsr (Nat.zero_le n))
lemma seqE_continuousOn (r M : ℝ) (n : ℕ) : ContinuousOn (seqE r M n) (Ioi 0) := E_continuousOn _ _
lemma seqJ_continuousOn (r M : ℝ) (n : ℕ) : ContinuousOn (seqJ r M n) (Ioi 0) := J_continuousOn _ _
lemma seqA_continuousOn (r M : ℝ) (n : ℕ) : ContinuousOn (seqA r M n) (Ioi 0) := by
  intro s hs
  exact (A_deriv (z := label ((((n:ℝ)+1),r),M)) (k := (n:ℝ)+1) hs).continuousAt.continuousWithinAt
lemma seqg_continuousOn (r M : ℝ) (n : ℕ) : ContinuousOn (seqg r M n) (Ioi 0) :=
  continuousOn_id.mul (continuousOn_const.sub ((seqA_continuousOn r M n).pow 2))
lemma seqg_pos {r M s : ℝ} (n : ℕ) (hs : 0 < s) : 0 < seqg r M n s :=
  mul_pos hs (A_gap_pos hs)
lemma seqE_integrable {r M a b : ℝ} (n : ℕ) (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (seqE r M n) volume a b :=
  ((seqE_continuousOn r M n).mono (fun _ hs => ha.trans_le hs.1)).intervalIntegrable_of_Icc hab
lemma seqJ_integrable {r M a b : ℝ} (n : ℕ) (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (seqJ r M n) volume a b :=
  ((seqJ_continuousOn r M n).mono (fun _ hs => ha.trans_le hs.1)).intervalIntegrable_of_Icc hab
lemma seqE_integral_bounds {r M C a b : ℝ} (hr : 0 < r) (hM : |M|<1)
    (hC : ∀ n, seqL r M n r ≤ C) (ha : 0 < a) (hab : a ≤ b) (hbr : b ≤ r) (n : ℕ) :
    (∫ s in a..b, seqE r M 0 s) ≤ (∫ s in a..b, seqE r M n s) ∧
    (∫ s in a..b, seqE r M n s) ≤ (∫ s in a..b, seqE r M 0 s)+C-seqL r M 0 r := by
  have h := integral_E_difference_bound (k₁ := ((0:ℕ):ℝ)+1) (k₂ := (n:ℝ)+1) hr hM
    (by simp only [Nat.cast_zero]; linarith [Nat.cast_nonneg (α := ℝ) n]) ha hab hbr
  change 0 ≤ (∫ s in a..b, seqE r M n s-seqE r M 0 s) ∧
    (∫ s in a..b, seqE r M n s-seqE r M 0 s) ≤ seqL r M n r-seqL r M 0 r at h
  rw [intervalIntegral.integral_sub (seqE_integrable n ha hab) (seqE_integrable 0 ha hab)] at h
  constructor <;> linarith [h.1,h.2,hC n]

lemma seqθ_ae_bdd {r M C a b : ℝ} (hr : 0 < r) (hM : |M|<1)
    (hC : ∀ n, seqL r M n r ≤ C) (ha : 0 < a) (hab : a ≤ b) (hbr : b < r) :
    ∀ᵐ s ∂volume.restrict (Ioc a b), BddAbove (range (fun n => seqθ r M n s)) := by
  have hmem : ∀ᵐ s ∂volume.restrict (Ioc a b), s ∈ Ioc a b := ae_restrict_mem measurableSet_Ioc
  have hbd := ae_bddAbove_of_integral_bounded
    (μ := volume.restrict (Ioc a b)) (f := fun n s => seqE r M n s-seqE r M 0 s)
    (C := C-seqL r M 0 r)
    (fun n => ((seqE_integrable n ha hab).sub (seqE_integrable 0 ha hab)).1)
    (hmem.mono (fun s hs n => sub_nonneg.mpr (seqE_mono hr hM (ha.trans hs.1) (hs.2.trans_lt hbr) (Nat.zero_le n))))
    (hmem.mono (fun s hs n m hnm => sub_le_sub_right (seqE_mono hr hM (ha.trans hs.1) (hs.2.trans_lt hbr) hnm) _))
    (by intro n; rw [←intervalIntegral.integral_of_le hab,intervalIntegral.integral_sub
        (seqE_integrable n ha hab) (seqE_integrable 0 ha hab)]
        have h := (seqE_integral_bounds hr hM hC ha hab hbr.le n).2
        linarith)
  filter_upwards [hbd,hmem] with s hs hsm
  have hrates : BddAbove (range (fun n => 2*seqA r M n s/(s*(1-(seqA r M n s)^2)))) := by
    obtain ⟨B,hB⟩ := hs
    refine ⟨B+seqE r M 0 s,?_⟩
    rintro y ⟨n,rfl⟩
    have h := hB (mem_range_self n)
    change 2*seqA r M n s/(s*(1-(seqA r M n s)^2))-seqE r M 0 s ≤ B at h
    linarith
  exact bddAbove_angle_of_rate (ha.trans hsm.1) (fun n => seqA_abs n (ha.trans hsm.1))
    (seqA_mono hr hM (ha.trans hsm.1) (hsm.2.trans_lt hbr)) hrates

lemma seqg_uniform_integral_pos {r M C a b : ℝ} (hr : 0 < r) (hM : |M|<1)
    (hC : ∀ n, seqL r M n r ≤ C) (ha : 0 < a) (hab : a < b) (hbr : b < r) :
    ∃ ε > 0, ∀ n, ε ≤ ∫ s in a..b, seqg r M n s := by
  let q : ℝ → ℝ := fun s => 1/(s*(1+seqA r M 0 s))
  have hq : ContinuousOn q (Icc a b) := by
    apply continuousOn_const.div
      (continuousOn_id.mul (continuousOn_const.add ((seqA_continuousOn r M 0).mono (fun _ hs => ha.trans_le hs.1))))
    intro s hs
    apply ne_of_gt (mul_pos (ha.trans_le hs.1) _)
    change 0 < 1+seqA r M 0 s
    linarith [(abs_lt.mp (seqA_abs (r := r) (M := M) 0 (ha.trans_le hs.1))).1]
  apply uniform_integral_pos_of_reciprocal hab
    (fun n => (seqg_continuousOn r M n).mono (fun _ hs => ha.trans_le hs.1))
    (fun n s hs => seqg_pos n (ha.trans_le hs.1))
    (B := ((∫ s in a..b, seqE r M 0 s)+C-seqL r M 0 r)/2+(∫ s in a..b, q s))
  intro n
  have h₁ := seqE_integrable (r := r) (M := M) n ha hab.le
  have h₂ : IntervalIntegrable q volume a b := hq.intervalIntegrable_of_Icc hab.le
  have hg : IntervalIntegrable (fun s => 1/seqg r M n s) volume a b :=
    (continuousOn_const.div ((seqg_continuousOn r M n).mono (fun _ hs => ha.trans_le hs.1))
      (fun s hs => ne_of_gt (seqg_pos n (ha.trans_le hs.1)))).intervalIntegrable_of_Icc hab.le
  have hpoint (s : ℝ) (hs : s ∈ Icc a b) : 1/seqg r M n s ≤ seqE r M n s/2+q s := by
    have hs0 := ha.trans_le hs.1
    have hin : 0 < 1+seqA r M n s := by linarith [(abs_lt.mp (seqA_abs (r := r) (M := M) n hs0)).1]
    have hi0 : 0 < 1+seqA r M 0 s := by linarith [(abs_lt.mp (seqA_abs (r := r) (M := M) 0 hs0)).1]
    have hgap : 0 < 1-(seqA r M n s)^2 := A_gap_pos hs0
    have hid : 1/seqg r M n s=seqE r M n s/2+1/(s*(1+seqA r M n s)) := by
      change 1/(s*(1-(seqA r M n s)^2))= (2*seqA r M n s/(s*(1-(seqA r M n s)^2)))/2+1/(s*(1+seqA r M n s))
      field_simp [ne_of_gt hs0,ne_of_gt hin,ne_of_gt hgap]
      ring
    rw [hid]
    have hinv : 1/(s*(1+seqA r M n s)) ≤ 1/(s*(1+seqA r M 0 s)) := one_div_le_one_div_of_le (mul_pos hs0 hi0)
      (mul_le_mul_of_nonneg_left (by linarith [seqA_mono hr hM hs0 (hs.2.trans_lt hbr) (Nat.zero_le n)]) hs0.le)
    dsimp only [q]
    linarith
  have hle := intervalIntegral.integral_mono_on hab.le hg ((h₁.div_const 2).add h₂) hpoint
  rw [intervalIntegral.integral_add (h₁.div_const 2) h₂,intervalIntegral.integral_div] at hle
  linarith [(seqE_integral_bounds hr hM hC ha hab.le hbr.le n).2]

lemma seqJ_drop {r M a b : ℝ} (n : ℕ) (ha : 0 < a) (hab : a ≤ b) :
    seqJ r M n a-seqJ r M n b=((n:ℝ)+1)*(∫ s in a..b, seqg r M n s) := by
  have hg : IntervalIntegrable (seqg r M n) volume a b :=
    ((seqg_continuousOn r M n).mono (fun _ hs => ha.trans_le hs.1)).intervalIntegrable_of_Icc hab
  have hd (s : ℝ) (hs : s ∈ uIcc a b) : HasDerivAt (seqJ r M n) (-((n:ℝ)+1)*seqg r M n s) s := by
    have h := J_deriv (z := label ((((n:ℝ)+1),r),M)) (k := (n:ℝ)+1) (ha.trans_le (((uIcc_of_le hab) ▸ hs).1))
    convert! h using 1
    dsimp only [seqg,seqA]
    ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hg.const_mul (-((n:ℝ)+1)))
  rw [intervalIntegral.integral_const_mul] at he
  linarith

theorem seqL_not_bddAbove {r M : ℝ} (hr : 0 < r) (hM : |M|<1) :
    ¬ BddAbove (range (fun n => seqL r M n r)) := by
  rintro ⟨C,hC⟩
  have hCn (n : ℕ) : seqL r M n r ≤ C := hC (mem_range_self n)
  have hgood := seqθ_ae_bdd hr hM hCn (show 0<r/4 by positivity)
    (show r/4 ≤ 3*r/4 by linarith) (show 3*r/4<r by linarith)
  obtain ⟨b,hb,hθb⟩ := exists_mem_Ioo_of_ae (a := r/3) (b := 5*r/12)
    (by linarith) (by intro s hs; constructor <;> linarith [hs.1,hs.2]) hgood
  obtain ⟨c,hc,hθc⟩ := exists_mem_Ioo_of_ae (a := 7*r/12) (b := 2*r/3)
    (by linarith) (by intro s hs; constructor <;> linarith [hs.1,hs.2]) hgood
  obtain ⟨Bθb,hBθb⟩ := hθb
  obtain ⟨Bθc,hBθc⟩ := hθc
  let a := r/4
  let d := 3*r/4
  have ha : 0<a := by dsimp [a]; positivity
  have hab : a<b := by dsimp [a]; linarith [hb.1]
  have hbc : b<c := by linarith [hb.2,hc.1]
  have hcd : c<d := by dsimp [d]; linarith [hc.2]
  have hdr : d<r := by dsimp [d]; linarith
  let U := Bθb-seqθ r M 0 a+(∫ s in a..b, seqE r M 0 s)+C-seqL r M 0 r
  let V := seqθ r M 0 d-Bθc+(∫ s in c..d, seqE r M 0 s)
  have hupper (n : ℕ) : seqJ r M n b ≤ U/(b-a) := by
    have he : (∫ s in a..b, seqJ r M n s)=seqθ r M n b-seqθ r M n a+(∫ s in a..b, seqE r M n s) := integral_J ha hab.le
    have hI := intervalIntegral.integral_mono_on hab.le intervalIntegrable_const
      (seqJ_integrable n ha hab.le) (fun s hs =>
        (J_strictAnti (z := label ((((n:ℝ)+1),r),M)) (by positivity : (0:ℝ)<(n:ℝ)+1)).antitoneOn
          (ha.trans_le hs.1) (ha.trans hab) hs.2)
    rw [intervalIntegral.integral_const] at hI
    simp only [smul_eq_mul] at hI
    change (b-a)*seqJ r M n b ≤ (∫ s in a..b, seqJ r M n s) at hI
    apply (le_div_iff₀ (sub_pos.mpr hab)).mpr
    have hLow := seqθ_lower hr hM ha (hab.trans (hbc.trans (hcd.trans hdr))) n
    have hHigh := hBθb (mem_range_self n)
    have hEB := (seqE_integral_bounds hr hM hCn ha hab.le (hbc.trans (hcd.trans hdr)).le n).2
    dsimp only [U]
    nlinarith
  have hlower (n : ℕ) : V/(d-c) ≤ seqJ r M n c := by
    have hc0 := ha.trans (hab.trans hbc)
    have he : (∫ s in c..d, seqJ r M n s)=seqθ r M n d-seqθ r M n c+(∫ s in c..d, seqE r M n s) := integral_J hc0 hcd.le
    have hI := intervalIntegral.integral_mono_on hcd.le (seqJ_integrable n hc0 hcd.le)
      intervalIntegrable_const (fun s hs =>
        (J_strictAnti (z := label ((((n:ℝ)+1),r),M)) (by positivity : (0:ℝ)<(n:ℝ)+1)).antitoneOn
          hc0 (hc0.trans_le hs.1) hs.1)
    rw [intervalIntegral.integral_const] at hI
    simp only [smul_eq_mul] at hI
    change (∫ s in c..d, seqJ r M n s) ≤ (d-c)*seqJ r M n c at hI
    apply (div_le_iff₀ (sub_pos.mpr hcd)).mpr
    have hLow := seqθ_lower hr hM (hc0.trans hcd) hdr n
    have hHigh := hBθc (mem_range_self n)
    have hEB := (seqE_integral_bounds hr hM hCn hc0 hcd.le hdr.le n).1
    dsimp only [V]
    nlinarith
  obtain ⟨ε,hε,hbound⟩ := seqg_uniform_integral_pos hr hM hCn (ha.trans hab) hbc (hcd.trans hdr)
  obtain ⟨n,hn⟩ := exists_nat_gt ((U/(b-a)-V/(d-c))/ε)
  have hmul := mul_le_mul_of_nonneg_left (hbound n) (show (0:ℝ) ≤ (n:ℝ)+1 by positivity)
  rw [←seqJ_drop n (ha.trans hab) hbc.le] at hmul
  have hn' := (div_lt_iff₀ hε).mp hn
  nlinarith [hupper n,hlower n]
end QuinticLienard.QuadraticFit

end OAI
