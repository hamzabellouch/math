import OAI.InformationTheory.SoftChannel.RateWindow

namespace OAI

section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace LeanBlast.CourtadeKumar
open SoftChannel204

def pairH (c d : ℝ) : ℝ := (entropy (c+d)+entropy (c-d))/2
def thinX (c l : ℝ) : ℝ := 1-l*(1-c)
def thinI (c d l : ℝ) : ℝ := entropy (thinX c l)-l*pairH c d
def thinJ (c d l : ℝ) : ℝ := pairH (thinX c l) (l*d)-l*pairH c d

lemma thinX_mem {c l : ℝ} (hc : c ∈ Ioo (-1) 1) (hl : l ∈ Ioc (0:ℝ) 1) :
    thinX c l ∈ Ioo (-1) 1 := by
  dsimp [thinX]
  constructor
  · have := mul_le_mul_of_nonneg_right hl.2 (show 0 ≤ 1-c by linarith [hc.2])
    nlinarith [hc.1]
  · nlinarith [mul_pos hl.1 (show 0 < 1-c by linarith [hc.2])]

lemma thinX_add (c d l : ℝ) : thinX c l+l*d=thinX (c+d) l := by unfold thinX; ring
lemma thinX_sub (c d l : ℝ) : thinX c l-l*d=thinX (c-d) l := by unfold thinX; ring

lemma entropy_thinX {a l : ℝ} (ha : a ∈ Icc (-1) 1) (hl : l ∈ Icc (0:ℝ) 1) :
    l*entropy a ≤ entropy (thinX a l) := by
  have h := entropy_common_output ha hl
  convert! h using 1
  congr 1
  unfold thinX
  ring

lemma entropy_thinX_strict {a l : ℝ} (ha : a ∈ Ioo (-1) 1) (hl : l ∈ Ioo (0:ℝ) 1) :
    l*entropy a < entropy (thinX a l) := by
  have hap : (1+a)/2 ∈ Icc (0:ℝ) 1 := by constructor <;> linarith [ha.1,ha.2]
  have h := Real.strictConcave_binEntropy.2 (by norm_num : (1:ℝ) ∈ Icc 0 1) hap
    (by linarith [ha.2] : (1:ℝ) ≠ (1+a)/2) (by linarith [hl.2] : 0 < 1-l) hl.1
    (by ring : 1-l+l=1)
  rw [entropy_eq_binEntropy,entropy_eq_binEntropy]
  simp only [smul_eq_mul,Real.binEntropy_one,mul_zero,zero_add,mul_one] at h
  convert! h using 1
  congr 1
  unfold thinX
  ring

lemma thinJ_nonneg {c d l : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) (hcd : c+d < 1)
    (hl : l ∈ Ioc (0:ℝ) 1) : 0 ≤ thinJ c d l := by
  have hh : |c|+|d| < 1 := by rw [abs_of_nonneg hc,abs_of_nonneg hd]; exact hcd
  have ha := pair_add_mem_Ioo c d hh
  have hb := pair_sub_mem_Ioo c d hh
  have h₁ := entropy_thinX ⟨ha.1.le,ha.2.le⟩ ⟨hl.1.le,hl.2⟩
  have h₂ := entropy_thinX ⟨hb.1.le,hb.2.le⟩ ⟨hl.1.le,hl.2⟩
  dsimp [thinJ,pairH]
  rw [thinX_add,thinX_sub]
  linarith

lemma thinJ_pos {c d l : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) (hcd : c+d < 1)
    (hl : l ∈ Ioo (0:ℝ) 1) : 0 < thinJ c d l := by
  have hh : |c|+|d| < 1 := by rw [abs_of_nonneg hc,abs_of_nonneg hd]; exact hcd
  have h₁ := entropy_thinX_strict (pair_add_mem_Ioo c d hh) hl
  have h₂ := entropy_thinX_strict (pair_sub_mem_Ioo c d hh) hl
  dsimp [thinJ,pairH]
  rw [thinX_add,thinX_sub]
  linarith

lemma thinning_domain {c d l : ℝ} (hc : 0 ≤ c) (hd : 0 < d) (hcd : c+d < 1)
    (hl : l ∈ Ioc (0:ℝ) 1) :
    0 ≤ thinX c l ∧ 0 < l*d ∧ thinX c l+l*d < 1 ∧ 0 < l*pairH c d := by
  have hc1 : c < 1 := by linarith
  have hh : |c|+|d| < 1 := by rw [abs_of_nonneg hc,abs_of_pos hd]; exact hcd
  refine ⟨?_,mul_pos hl.1 hd,?_,mul_pos hl.1 (pair_entropyAverage_pos c d hh)⟩
  · dsimp [thinX]
    have := mul_le_mul_of_nonneg_right hl.2 (show 0 ≤ 1-c by linarith)
    nlinarith
  · rw [thinX_add]
    exact (thinX_mem (pair_add_mem_Ioo c d hh) hl).2

lemma thinJ_le_thinI {c d l : ℝ} (hc : 0 ≤ c) (hd : 0 < d) (hcd : c+d < 1)
    (hl : l ∈ Ioc (0:ℝ) 1) : thinJ c d l ≤ thinI c d l := by
  obtain ⟨hx,hy,hxy,_⟩ := thinning_domain hc hd hcd hl
  have hh : |thinX c l|+|l*d| < 1 := by rw [abs_of_nonneg hx,abs_of_pos hy]; exact hxy
  have h := pairEntropyGap_nonneg (thinX c l) (l*d) hh
  dsimp [thinJ,thinI,pairH]
  unfold pairEntropyGap at h
  linarith

lemma thinI_lt_ell {c d l : ℝ} (hc : 0 ≤ c) (hd : 0 < d) (hcd : c+d < 1)
    (hl : l ∈ Ioc (0:ℝ) 1) : thinI c d l < ell := by
  have hpos := (thinning_domain hc hd hcd hl).2.2.2
  have h := entropy_le_ell (thinX c l)
  dsimp [thinI]
  linarith

lemma thinning_entropy_floor {c d l : ℝ} (hc : 0 ≤ c) (hd : 0 < d) (hcd : c+d < 1)
    (hl : l ∈ Ioc (0:ℝ) 1) :
    (1-thinX c l)*entropy (l*d/(1-thinX c l)) ≤ l*pairH c d := by
  have hc0 : 1-c ≠ 0 := by linarith
  have h := mul_le_mul_of_nonneg_left (pair_entropy_floor hc hd.le hcd) hl.1.le
  have he : l*d/(1-thinX c l) = d/(1-c) := by
    rw [show 1-thinX c l=l*(1-c) by dsimp [thinX]; ring]
    field_simp [hl.1.ne',hc0]
  rw [he]
  dsimp [thinX,pairH] at *
  nlinarith

lemma thinning_path_window {c d l : ℝ} (hc : 0 ≤ c) (hd : 0 < d) (hcd : c+d < 1)
    (hl : l ∈ Ioc (0:ℝ) 1) :
    (∫ h in (ell-thinI c d l)..(ell-thinJ c d l),
      clipKernel (Real.log (1+thinX c l)) h) ≤
      -(3/2:ℝ)*Real.log (1-(l*d)^2/(1+thinX c l)^2) := by
  obtain ⟨hx,hy,hxy,_⟩ := thinning_domain hc hd hcd hl
  have H := thinning_window hx hy hxy (thinning_entropy_floor hc hd hcd hl)
    (show l*pairH c d ≤ (entropy (thinX c l+l*d)+entropy (thinX c l-l*d))/2 by
      have := thinJ_nonneg hc hd.le hcd hl
      dsimp [thinJ,pairH] at this ⊢
      linarith)
  convert! H using 1; congr 1 <;> simp only [thinI,thinJ,entropy,pairH] <;> ring

lemma entropy_euler {x : ℝ} (hx : x ∈ Ioo (-1) 1) :
    entropy x-(1-x)*Real.artanh x = ell-Real.log (1+x) := by
  rw [Real.artanh_eq_half_log ⟨hx.1.le,hx.2.le⟩,
    Real.log_div (by linarith [hx.1] : 1+x ≠ 0) (by linarith [hx.2] : 1-x ≠ 0)]
  unfold entropy psi
  ring

lemma log_pair_defect {x d : ℝ} (hx : 0 ≤ x) (hd : 0 < d) (hxd : x+d < 1) :
    (Real.log (1+(x+d))+Real.log (1+(x-d)))/2 =
      Real.log (1+x)+(1/2:ℝ)*Real.log (1-d^2/(1+x)^2) := by
  have hp : 0 < 1+x := by linarith
  have hpm : 0 < 1+(x-d) := by linarith
  have hpp : 0 < 1+(x+d) := by linarith
  have hr : 1-d^2/(1+x)^2 = ((1+(x+d))*(1+(x-d)))/(1+x)^2 := by field_simp; ring
  rw [hr,Real.log_div (mul_ne_zero hpp.ne' hpm.ne') (pow_ne_zero _ hp.ne'),
    Real.log_mul hpp.ne' hpm.ne',Real.log_pow]
  ring

lemma thinning_defect_nonneg {x d : ℝ} (hx : 0 ≤ x) (hd : 0 < d) (hxd : x+d < 1) :
    0 ≤ -(1/2:ℝ)*Real.log (1-d^2/(1+x)^2) := by
  have hr : 0 < 1-d^2/(1+x)^2 := by
    have hp : 0 < (1+x)^2 := sq_pos_of_pos (by linarith)
    have hs : d^2 < (1+x)^2 := by
      nlinarith [mul_pos (show 0 < 1+x-d by linarith) (show 0 < 1+x+d by linarith)]
    linarith [(div_lt_one hp).mpr hs]
  have hle : 1-d^2/(1+x)^2 ≤ 1 := sub_le_self _ (div_nonneg (sq_nonneg _) (sq_nonneg _))
  have hlog := Real.log_nonpos hr.le hle
  linarith

def thinIDeriv (c d l : ℝ) : ℝ := (1-c)*Real.artanh (thinX c l)-pairH c d
def thinJDeriv (c d l : ℝ) : ℝ :=
  ((1-(c+d))*Real.artanh (thinX (c+d) l)+(1-(c-d))*Real.artanh (thinX (c-d) l))/2-pairH c d

def thinA (c l : ℝ) : ℝ := ell-Real.log (1+thinX c l)
def thinK (c d l : ℝ) : ℝ := -(1/2:ℝ)*Real.log (1-(l*d)^2/(1+thinX c l)^2)

lemma hasDerivAt_thinX (c l : ℝ) : HasDerivAt (thinX c) (-(1-c)) l := by
  convert! (((hasDerivAt_id l).mul_const (1-c)).const_sub 1) using 1; simp

lemma hasDerivAt_entropy_thinX {c l : ℝ} (hc : c ∈ Ioo (-1) 1) (hl : l ∈ Ioc (0:ℝ) 1) :
    HasDerivAt (fun z => entropy (thinX c z)) ((1-c)*Real.artanh (thinX c l)) l := by
  convert! (hasDerivAt_entropy (thinX_mem hc hl)).comp l (hasDerivAt_thinX c l) using 1; ring

lemma hasDerivAt_thinI {c d l : ℝ} (hc : 0 ≤ c) (hd : 0 < d) (hcd : c+d < 1)
    (hl : l ∈ Ioc (0:ℝ) 1) : HasDerivAt (thinI c d) (thinIDeriv c d l) l := by
  convert!
    (hasDerivAt_entropy_thinX (show c ∈ Ioo (-1) 1 from ⟨by linarith,by linarith⟩) hl).sub
      ((hasDerivAt_id l).mul_const (pairH c d)) using 1; simp [thinIDeriv]

lemma hasDerivAt_thinJ {c d l : ℝ} (hc : 0 ≤ c) (hd : 0 < d) (hcd : c+d < 1)
    (hl : l ∈ Ioc (0:ℝ) 1) : HasDerivAt (thinJ c d) (thinJDeriv c d l) l := by
  have hh : |c|+|d| < 1 := by rw [abs_of_nonneg hc,abs_of_pos hd]; exact hcd
  have h := (((hasDerivAt_entropy_thinX (pair_add_mem_Ioo c d hh) hl).add
    (hasDerivAt_entropy_thinX (pair_sub_mem_Ioo c d hh) hl)).div_const 2).sub
    ((hasDerivAt_id l).mul_const (pairH c d))
  convert! h using 1
  · ext z
    simp [thinJ,pairH,thinX_add,thinX_sub]
  · simp [thinJDeriv]

lemma thinI_euler {c d l : ℝ} (hc : 0 ≤ c) (hd : 0 < d) (hcd : c+d < 1)
    (hl : l ∈ Ioc (0:ℝ) 1) : l*thinIDeriv c d l = thinI c d l-thinA c l := by
  have hx := thinX_mem (show c ∈ Ioo (-1) 1 by constructor <;> linarith) hl
  have h := entropy_euler hx
  dsimp [thinIDeriv,thinI,thinA,thinX] at *
  nlinarith

lemma thinJ_euler {c d l : ℝ} (hc : 0 ≤ c) (hd : 0 < d) (hcd : c+d < 1)
    (hl : l ∈ Ioc (0:ℝ) 1) : l*thinJDeriv c d l = thinJ c d l-thinA c l-thinK c d l := by
  have hh : |c|+|d| < 1 := by rw [abs_of_nonneg hc,abs_of_pos hd]; exact hcd
  have h₁ := entropy_euler (thinX_mem (pair_add_mem_Ioo c d hh) hl)
  have h₂ := entropy_euler (thinX_mem (pair_sub_mem_Ioo c d hh) hl)
  obtain ⟨hx,hy,hxy,_⟩ := thinning_domain hc hd hcd hl
  have hlog := log_pair_defect hx hy hxy
  rw [thinX_add,thinX_sub] at hlog
  dsimp [thinJDeriv,thinJ,thinA,thinK,pairH]
  rw [thinX_add,thinX_sub]
  simp only [thinX] at h₁ h₂ hlog ⊢
  nlinarith

lemma continuous_thinI (c d : ℝ) : Continuous (thinI c d) := by
  unfold thinI thinX
  exact (continuous_entropy.comp (continuous_const.sub (continuous_id.mul continuous_const))).sub
    (continuous_id.mul continuous_const)

lemma continuous_thinJ (c d : ℝ) : Continuous (thinJ c d) := by
  unfold thinJ pairH thinX
  have he := continuous_entropy
  fun_prop

def normalizedDemand (c d l : ℝ) : ℝ := (r (thinI c d l)-r (thinJ c d l))/l

def normalizedDemandDeriv (c d l : ℝ) : ℝ :=
  ((rDeriv (thinI c d l)*thinIDeriv c d l-rDeriv (thinJ c d l)*thinJDeriv c d l)*l-
    (r (thinI c d l)-r (thinJ c d l)))/l^2

lemma hasDerivAt_normalizedDemand {c d l : ℝ} (hc : 0 ≤ c) (hd : 0 < d) (hcd : c+d < 1)
    (hl : l ∈ Ioo (0:ℝ) 1) : HasDerivAt (normalizedDemand c d) (normalizedDemandDeriv c d l) l := by
  have hl' : l ∈ Ioc (0:ℝ) 1 := ⟨hl.1,hl.2.le⟩
  have hj := thinJ_pos hc hd.le hcd hl
  have hjI := thinJ_le_thinI hc hd hcd hl'
  have hI := thinI_lt_ell hc hd hcd hl'
  have h := (((hasDerivAt_r ⟨hj.trans_le hjI,hI⟩).comp l (hasDerivAt_thinI hc hd hcd hl')).sub
    ((hasDerivAt_r ⟨hj,hjI.trans_lt hI⟩).comp l (hasDerivAt_thinJ hc hd hcd hl'))).div
    (hasDerivAt_id l) hl.1.ne'
  convert! h using 1; dsimp [normalizedDemand,normalizedDemandDeriv]; ring

lemma normalizedDemandDeriv_nonneg {c d l : ℝ} (hc : 0 ≤ c) (hd : 0 < d) (hcd : c+d < 1)
    (hl : l ∈ Ioo (0:ℝ) 1) : 0 ≤ normalizedDemandDeriv c d l := by
  have hl' : l ∈ Ioc (0:ℝ) 1 := ⟨hl.1,hl.2.le⟩
  obtain ⟨hx,hy,hxy,_⟩ := thinning_domain hc hd hcd hl'
  have hk : 0 ≤ thinK c d l := thinning_defect_nonneg hx hy hxy
  have hw : (∫ h in (ell-thinI c d l)..(ell-thinJ c d l),
      clipKernel (Real.log (1+thinX c l)) h) ≤ 3*thinK c d l := by
    convert! thinning_path_window hc hd hcd hl' using 1; unfold thinK; ring
  have H := rate_window_euler (thinJ_pos hc hd.le hcd hl) (thinJ_le_thinI hc hd hcd hl')
    (thinI_lt_ell hc hd hcd hl') hk hw
  have hI := thinI_euler hc hd hcd hl'
  have hJ := thinJ_euler hc hd hcd hl'
  change 0 ≤ ((thinI c d l-thinA c l)*rDeriv (thinI c d l)-r (thinI c d l))-
    ((thinJ c d l-thinA c l)*rDeriv (thinJ c d l)-r (thinJ c d l))+
    rDeriv (thinJ c d l)*thinK c d l at H
  unfold normalizedDemandDeriv
  apply div_nonneg _ (sq_nonneg l)
  nlinarith [congrArg (fun z => z*rDeriv (thinI c d l)) hI,
    congrArg (fun z => z*rDeriv (thinJ c d l)) hJ]

lemma common_output_payment {c d l : ℝ} (hc : 0 ≤ c) (hd : 0 < d) (hcd : c+d < 1)
    (hl : l ∈ Ioc (0:ℝ) 1) :
    r (thinI c d l)-r (thinJ c d l) ≤ l*r (pairEntropyGap c d) := by
  have hdom (z : ℝ) (hz : z ∈ Icc l 1) : z ∈ Ioc (0:ℝ) 1 := ⟨hl.1.trans_le hz.1,hz.2⟩
  have hci : ContinuousOn (fun z => r (thinI c d z)) (Icc l 1) := by
    apply continuousOn_r.comp (continuous_thinI c d).continuousOn
    intro z hz
    have h := hdom z hz
    exact ⟨(thinJ_nonneg hc hd.le hcd h).trans (thinJ_le_thinI hc hd hcd h),thinI_lt_ell hc hd hcd h⟩
  have hcj : ContinuousOn (fun z => r (thinJ c d z)) (Icc l 1) := by
    apply continuousOn_r.comp (continuous_thinJ c d).continuousOn
    intro z hz
    have h := hdom z hz
    exact ⟨thinJ_nonneg hc hd.le hcd h,(thinJ_le_thinI hc hd hcd h).trans_lt (thinI_lt_ell hc hd hcd h)⟩
  have hmono : MonotoneOn (normalizedDemand c d) (Icc l 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := normalizedDemandDeriv c d) (convex_Icc l 1)
    · exact (hci.sub hcj).div continuousOn_id (fun z hz => (hdom z hz).1.ne')
    · intro z hz
      have hz' : z ∈ Ioo (0:ℝ) 1 := by rw [interior_Icc] at hz; exact ⟨hl.1.trans hz.1,hz.2⟩
      exact (hasDerivAt_normalizedDemand hc hd hcd hz').hasDerivWithinAt
    · intro z hz
      have hz' : z ∈ Ioo (0:ℝ) 1 := by rw [interior_Icc] at hz; exact ⟨hl.1.trans hz.1,hz.2⟩
      exact normalizedDemandDeriv_nonneg hc hd hcd hz'
  have H := hmono ⟨le_rfl,hl.2⟩ ⟨hl.2,le_rfl⟩ hl.2
  have hI : thinI c d 1 = pairEntropyGap c d := by simp [thinI,thinX,pairH,pairEntropyGap]
  have hJ : thinJ c d 1 = 0 := by simp [thinJ,thinX]
  unfold normalizedDemand at H
  rw [hI,hJ,r_zero,sub_zero,div_one] at H
  exact (div_le_iff₀ hl.1).mp H |>.trans_eq (by ring)

end LeanBlast.CourtadeKumar
end
end

end OAI
