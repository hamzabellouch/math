import OAI.Geometry.PlaneColoring.Expansion

namespace OAI

noncomputable section
open Set Filter Topology
namespace EuclideanFiveColor
def binaryQ (d t : ℝ) : ℝ := 1-2*d*Real.cos t+d^2
def binaryR (d t : ℝ) : ℝ := 2*Real.sqrt (binaryQ d t)*Real.sqrt (1-binaryQ d t/4)
def binaryB (d t : ℝ) : ℝ := (Real.cos t-d)/binaryQ d t+Real.sin t/binaryR d t
def binaryM (d t : ℝ) : ℝ := Real.sin t/binaryQ d t+(d-Real.cos t)/binaryR d t
def binaryCircleMap (d t : ℝ) : ℝ :=
  t+Real.pi/3+Real.arctan (d*Real.sin t/(1-d*Real.cos t))-Real.arccos (Real.sqrt (binaryQ d t)/2)
lemma binaryQ_range {d : ℝ} (hd : |d| < 1/2) (t : ℝ) :
    0 < binaryQ d t ∧ binaryQ d t < 4 ∧ 0 < 1-d*Real.cos t := by
  have hdc : |d*Real.cos t| ≤ |d| := by
    simpa only [abs_mul,mul_one] using mul_le_mul_of_nonneg_left (Real.abs_cos_le_one t) (abs_nonneg d)
  have hdc' := abs_le.mp hdc
  have hd' := abs_lt.mp hd
  dsimp [binaryQ]
  constructor
  · nlinarith [sq_nonneg d]
  constructor
  · nlinarith [sq_abs d,abs_nonneg d]
  · linarith
lemma binaryR_pos {d : ℝ} (hd : |d| < 1/2) (t : ℝ) : 0 < binaryR d t := by
  have h := binaryQ_range hd t
  unfold binaryR
  exact mul_pos (mul_pos (by norm_num) (Real.sqrt_pos.mpr h.1)) (Real.sqrt_pos.mpr (by linarith [h.2.1]))
lemma binary_arctan_identity (d t : ℝ) :
    (1-d*Real.cos t)^2+(d*Real.sin t)^2=binaryQ d t := by
  have h := Real.sin_sq_add_cos_sq t
  dsimp [binaryQ]
  nlinarith [sq_nonneg d]
lemma binary_arctan_recip {d : ℝ} (hd : |d| < 1/2) (t : ℝ) :
    1/(1+(d*Real.sin t/(1-d*Real.cos t))^2)/(1-d*Real.cos t)^2=1/binaryQ d t := by
  have hq := binaryQ_range hd t
  have hi := binary_arctan_identity d t
  field_simp [hq.1.ne',hq.2.2.ne']
  simp only [mul_pow] at hi
  rw [hi,div_self hq.1.ne']
lemma binaryCircleMap_hasDeriv_t {d : ℝ} (hd : |d| < 1/2) (t : ℝ) :
    HasDerivAt (binaryCircleMap d) (1+d*binaryB d t) t := by
  have hq := binaryQ_range hd t
  have hsq := Real.sq_sqrt hq.1.le
  have hs : 0 < Real.sqrt (binaryQ d t) := Real.sqrt_pos.mpr hq.1
  have hc : Real.sqrt (binaryQ d t)/2 ≠ -1 := by linarith
  have hc' : Real.sqrt (binaryQ d t)/2 ≠ 1 := by intro h; nlinarith [hq.2.1]
  have hqd : HasDerivAt (binaryQ d) (2*d*Real.sin t) t := by
    convert (((Real.hasDerivAt_cos t).const_mul (2*d)).const_sub 1).add_const (d^2) using 1 <;>
      first | rfl | ring
  have hat := (((Real.hasDerivAt_sin t).const_mul d).div
    (((Real.hasDerivAt_cos t).const_mul d).const_sub 1) hq.2.2.ne').arctan
  have hac := (Real.hasDerivAt_arccos hc hc').comp t ((hqd.sqrt hq.1.ne').div_const 2)
  have hh := (((hasDerivAt_id t).add_const (Real.pi/3)).add hat).sub hac
  change HasDerivAt (binaryCircleMap d) _ t at hh
  convert hh using 1
  dsimp [binaryB,binaryR]
  have hss : 1-(Real.sqrt (binaryQ d t)/2)^2=1-binaryQ d t/4 := by nlinarith [hsq]
  rw [hss]
  have hrec := binary_arctan_recip hd t
  have hnum : d*Real.cos t*(1-d*Real.cos t)-d*Real.sin t*-(d*-Real.sin t)=
      d*(Real.cos t-d) := by linear_combination -d^2*(Real.sin_sq_add_cos_sq t)
  rw [hnum]
  have hrearr : 1/(1+(d*Real.sin t/(1-d*Real.cos t))^2)*
      (d*(Real.cos t-d)/(1-d*Real.cos t)^2) = d*(Real.cos t-d)/binaryQ d t := by
    calc
      _ = (1/(1+(d*Real.sin t/(1-d*Real.cos t))^2)/(1-d*Real.cos t)^2)*(d*(Real.cos t-d)) := by ring
      _ = d*(Real.cos t-d)/binaryQ d t := by rw [hrec]; ring
  rw [hrearr]
  ring
lemma binaryCircleMap_hasDeriv_d {d : ℝ} (hd : |d| < 1/2) (t : ℝ) :
    HasDerivAt (fun s => binaryCircleMap s t) (binaryM d t) d := by
  have hq := binaryQ_range hd t
  have hsq := Real.sq_sqrt hq.1.le
  have hs : 0 < Real.sqrt (binaryQ d t) := Real.sqrt_pos.mpr hq.1
  have hc : Real.sqrt (binaryQ d t)/2 ≠ -1 := by linarith
  have hc' : Real.sqrt (binaryQ d t)/2 ≠ 1 := by intro h; nlinarith [hq.2.1]
  have hqd : HasDerivAt (fun s => binaryQ s t) (2*(d-Real.cos t)) d := by
    convert (((hasDerivAt_id d).mul_const (2*Real.cos t)).const_sub 1).add ((hasDerivAt_id d).pow 2) using 1 <;>
      first | rfl | (funext s; dsimp only [binaryQ,Pi.add_apply,Pi.pow_apply,id_eq]; ring) |
        (try dsimp only [id_eq]; ring)
  have hat := (((hasDerivAt_id d).mul_const (Real.sin t)).div
    (((hasDerivAt_id d).mul_const (Real.cos t)).const_sub 1) hq.2.2.ne').arctan
  have hac := (Real.hasDerivAt_arccos hc hc').comp d ((hqd.sqrt hq.1.ne').div_const 2)
  have hh := (hat.const_add (t+Real.pi/3)).sub hac
  change HasDerivAt (fun s => binaryCircleMap s t) _ d at hh
  convert hh using 1
  dsimp [binaryM,binaryR]
  have hss : 1-(Real.sqrt (binaryQ d t)/2)^2=1-binaryQ d t/4 := by nlinarith [hsq]
  rw [hss]
  have hrec := binary_arctan_recip hd t
  simp only [one_mul]
  have hnum : Real.sin t*(1-d*Real.cos t)-d*Real.sin t*-(Real.cos t)=Real.sin t := by ring
  rw [hnum]
  have hrearr : 1/(1+(d*Real.sin t/(1-d*Real.cos t))^2)*
      (Real.sin t/(1-d*Real.cos t)^2) = Real.sin t/binaryQ d t := by
    calc
      _ = (1/(1+(d*Real.sin t/(1-d*Real.cos t))^2)/(1-d*Real.cos t)^2)*Real.sin t := by ring
      _ = Real.sin t/binaryQ d t := by rw [hrec]; ring
  rw [hrearr]
  ring
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology
namespace EuclideanFiveColor
lemma periodic_reduce_to_period {P : ℝ} (hP : 0 < P) (t : ℝ) :
    ∃ u ∈ Icc 0 P, ∃ n : ℤ, t=u+(n : ℝ)*P := by
  refine ⟨Int.fract (t/P)*P,?_,⌊t/P⌋,?_⟩
  · exact ⟨(Int.fract_div_mul_self_mem_Ico P t hP).1,(Int.fract_div_mul_self_mem_Ico P t hP).2.le⟩
  · simpa only [zsmul_eq_mul] using (Int.fract_div_mul_self_add_zsmul_eq P t hP.ne').symm
lemma compact_periodic_uniform {g : ℝ → ℝ → ℝ} {a P : ℝ} (ha : 0 < a) (hP : 0 < P)
    (hg : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2) (Icc (-a) a ×ˢ Icc 0 P))
    (hper : ∀ d, Function.Periodic (g d) P) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, δ ≤ a ∧ ∀ d, |d| < δ → ∀ t, |g d t-g 0 t| < ε := by
  have hu := (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hg
  obtain ⟨δ,hδ,hδg⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  refine ⟨min a δ,lt_min ha hδ,min_le_left _ _,?_⟩
  intro d hd t
  obtain ⟨u,hu,n,rfl⟩ := periodic_reduce_to_period hP t
  have hper' : ∀ d, g d (u+(n : ℝ)*P)=g d u := fun d => by
    simpa only [zsmul_eq_mul] using (hper d).int_mul n u
  rw [hper' d,hper' 0]
  have hda := abs_lt.mp (lt_of_lt_of_le hd (min_le_left _ _))
  have hh := hδg (d,u) ⟨⟨hda.1.le,hda.2.le⟩,hu⟩ (0,u) ⟨⟨by linarith,ha.le⟩,hu⟩
  rw [Prod.dist_eq,dist_self,dist_zero_right,max_eq_left (norm_nonneg d)] at hh
  exact hh (lt_of_lt_of_le hd (min_le_right _ _))
lemma compact_periodic_bounded {g : ℝ → ℝ → ℝ} {a P : ℝ} (_ha : 0 ≤ a) (hP : 0 < P)
    (hg : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2) (Icc (-a) a ×ˢ Icc 0 P))
    (hper : ∀ d, |d| ≤ a → Function.Periodic (g d) P) :
    ∃ C > 0, ∀ d, |d| ≤ a → ∀ t, |g d t| ≤ C := by
  obtain ⟨C,hC⟩ := ((isCompact_Icc.prod isCompact_Icc).image_of_continuousOn hg).isBounded |>.exists_pos_norm_le
  refine ⟨C,hC.1,?_⟩
  intro d hd t
  obtain ⟨u,hu,n,rfl⟩ := periodic_reduce_to_period hP t
  have he : g d (u+(n : ℝ)*P)=g d u := by
    simpa only [zsmul_eq_mul] using (hper d hd).int_mul n u
  rw [he]
  exact hC.2 _ ⟨(d,u),⟨abs_le.mp hd,hu⟩,rfl⟩
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology
namespace EuclideanFiveColor
lemma binaryQ_contDiff : ContDiff ℝ 2 (fun p : ℝ × ℝ => binaryQ p.1 p.2) := by
  unfold binaryQ
  fun_prop
lemma binaryB_contDiffAt {p : ℝ × ℝ} (hp : |p.1| < 1/2) :
    ContDiffAt ℝ 2 (fun q : ℝ × ℝ => binaryB q.1 q.2) p := by
  have hq := binaryQ_range hp p.2
  have hr := binaryR_pos hp p.2
  have hs := Real.sqrt_pos.mpr hq.1
  have hs' : 0 < 1-binaryQ p.1 p.2/4 := by linarith [hq.2.1]
  have hQ := binaryQ_contDiff.contDiffAt (x := p)
  have hR : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => binaryR q.1 q.2) p := by
    unfold binaryR
    fun_prop (disch := first | exact hq.1.ne' | exact hs'.ne')
  unfold binaryB
  exact ((contDiffAt_snd.cos.sub contDiffAt_fst).div hQ hq.1.ne').add
    (contDiffAt_snd.sin.div hR hr.ne')
lemma binaryM_contDiffAt {p : ℝ × ℝ} (hp : |p.1| < 1/2) :
    ContDiffAt ℝ 2 (fun q : ℝ × ℝ => binaryM q.1 q.2) p := by
  have hq := binaryQ_range hp p.2
  have hr := binaryR_pos hp p.2
  have hs := Real.sqrt_pos.mpr hq.1
  have hs' : 0 < 1-binaryQ p.1 p.2/4 := by linarith [hq.2.1]
  have hQ := binaryQ_contDiff.contDiffAt (x := p)
  have hR : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => binaryR q.1 q.2) p := by
    unfold binaryR
    fun_prop (disch := first | exact hq.1.ne' | exact hs'.ne')
  unfold binaryM
  exact (contDiffAt_snd.sin.div hQ hq.1.ne').add
    ((contDiffAt_fst.sub contDiffAt_snd.cos).div hR hr.ne')
lemma binaryB_periodic (d : ℝ) : Function.Periodic (binaryB d) (2*Real.pi) := by
  intro t
  simp only [binaryB,binaryQ,binaryR,Real.cos_add_two_pi,Real.sin_add_two_pi]
lemma binaryM_periodic (d : ℝ) : Function.Periodic (binaryM d) (2*Real.pi) := by
  intro t
  simp only [binaryM,binaryQ,binaryR,Real.cos_add_two_pi,Real.sin_add_two_pi]
def binaryE (d t : ℝ) : ℝ := fderiv ℝ (fun q : ℝ × ℝ => binaryB q.1 q.2) (d,t) (0,1)
lemma binaryE_continuousAt {p : ℝ × ℝ} (hp : |p.1| < 1/2) :
    ContinuousAt (fun q : ℝ × ℝ => binaryE q.1 q.2) p := by
  exact ((binaryB_contDiffAt hp).continuousAt_fderiv (by norm_num)).clm_apply continuousAt_const
lemma binaryB_hasDeriv_t {d : ℝ} (hd : |d| < 1/2) (t : ℝ) :
    HasDerivAt (binaryB d) (binaryE d t) t := by
  have h := (binaryB_contDiffAt (p := (d,t)) hd).differentiableAt (by norm_num)
  convert h.hasFDerivAt.comp t ((hasFDerivAt_const d t).prodMk (hasFDerivAt_id t)) |>.hasDerivAt using 1 <;> rfl
lemma binaryE_periodic (d : ℝ) (hd : |d| < 1/2) : Function.Periodic (binaryE d) (2*Real.pi) := by
  intro t
  have h := (binaryB_hasDeriv_t hd (t+2*Real.pi)).comp t ((hasDerivAt_id t).add_const (2*Real.pi))
  simp only [mul_one] at h
  have he : (fun s => binaryB d (s+2*Real.pi))=binaryB d := funext (binaryB_periodic d)
  change HasDerivAt (fun s => binaryB d (s+2*Real.pi)) _ t at h
  rw [he] at h
  exact h.unique (binaryB_hasDeriv_t hd t)
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology
namespace EuclideanFiveColor
lemma binary_uniform_controls {ε : ℝ} (hε : 0 < ε) :
    ∃ δ C : ℝ, 0 < δ ∧ δ ≤ 1/4 ∧ 0 < C ∧
    (∀ d, |d| < δ → ∀ t, |binaryB d t-binaryB 0 t| < ε ∧
       |binaryM d t-binaryM 0 t| < ε) ∧
    (∀ d, |d| ≤ δ → ∀ t, |binaryB d t| ≤ C ∧ |binaryM d t| ≤ C ∧ |binaryE d t| ≤ C) := by
  have hB : ContinuousOn (fun p : ℝ × ℝ => binaryB p.1 p.2)
      (Icc (-(1/4)) (1/4) ×ˢ Icc 0 (2*Real.pi)) := by
    intro p hp
    exact (binaryB_contDiffAt (by rw [abs_lt]; constructor <;> linarith [hp.1.1,hp.1.2])).continuousAt.continuousWithinAt
  have hM : ContinuousOn (fun p : ℝ × ℝ => binaryM p.1 p.2)
      (Icc (-(1/4)) (1/4) ×ˢ Icc 0 (2*Real.pi)) := by
    intro p hp
    exact (binaryM_contDiffAt (by rw [abs_lt]; constructor <;> linarith [hp.1.1,hp.1.2])).continuousAt.continuousWithinAt
  have hE : ContinuousOn (fun p : ℝ × ℝ => binaryE p.1 p.2)
      (Icc (-(1/4)) (1/4) ×ˢ Icc 0 (2*Real.pi)) := by
    intro p hp
    exact (binaryE_continuousAt (by rw [abs_lt]; constructor <;> linarith [hp.1.1,hp.1.2])).continuousWithinAt
  have hP : 0 < 2*Real.pi := by positivity
  obtain ⟨δB,hδB,hδBa,hδBg⟩ := compact_periodic_uniform (by norm_num : (0:ℝ)<1/4) hP hB binaryB_periodic hε
  obtain ⟨δM,hδM,hδMa,hδMg⟩ := compact_periodic_uniform (by norm_num : (0:ℝ)<1/4) hP hM binaryM_periodic hε
  obtain ⟨CB,hCB,hCBg⟩ := compact_periodic_bounded (by norm_num : (0:ℝ)≤1/4) hP hB (fun d _ => binaryB_periodic d)
  obtain ⟨CM,hCM,hCMg⟩ := compact_periodic_bounded (by norm_num : (0:ℝ)≤1/4) hP hM (fun d _ => binaryM_periodic d)
  obtain ⟨CE,hCE,hCEg⟩ := compact_periodic_bounded (by norm_num : (0:ℝ)≤1/4) hP hE
    (fun d hd => binaryE_periodic d (by linarith))
  refine ⟨min δB δM,CB+CM+CE,lt_min hδB hδM,(min_le_left _ _).trans hδBa,by positivity,?_,?_⟩
  · intro d hd t
    exact ⟨hδBg d (hd.trans_le (min_le_left _ _)) t,hδMg d (hd.trans_le (min_le_right _ _)) t⟩
  · intro d hd t
    have hda := hd.trans ((min_le_left δB δM).trans hδBa)
    exact ⟨(hCBg d hda t).trans (by linarith),(hCMg d hda t).trans (by linarith),(hCEg d hda t).trans (by linarith)⟩
lemma binaryCircleMap_zero (t : ℝ) : binaryCircleMap 0 t=t := by
  have h : Real.arccos (1/2) = Real.pi/3 := by
    rw [← Real.cos_pi_div_three,Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])]
  simp only [binaryCircleMap,binaryQ,mul_zero,zero_mul,sub_zero,zero_pow (by norm_num : (2:ℕ)≠0),add_zero,Real.sqrt_one,one_div,zero_div,Real.arctan_zero]
  rw [← one_div,h]
  ring
lemma binaryCircleMap_displacement {d δ C : ℝ} (hd : 0 ≤ d) (hδ : δ < 1/2) (hdδ : d ≤ δ)
    (hM : ∀ s, |s| ≤ δ → ∀ t, |binaryM s t| ≤ C) (t : ℝ) :
    |binaryCircleMap d t-t| ≤ C*d := by
  have hh : ∀ s ∈ Icc 0 d, HasDerivWithinAt (fun s => binaryCircleMap s t) (binaryM s t) (Icc 0 d) s := by
    intro s hs
    exact (binaryCircleMap_hasDeriv_d (lt_of_le_of_lt (by rw [abs_of_nonneg hs.1]; exact hs.2.trans hdδ) hδ) t).hasDerivWithinAt
  have h := (convex_Icc (0:ℝ) d).norm_image_sub_le_of_norm_hasDerivWithin_le hh
    (fun s hs => hM s (by rw [abs_of_nonneg hs.1]; exact hs.2.trans hdδ) t) (left_mem_Icc.mpr hd) (right_mem_Icc.mpr hd)
  simpa only [binaryCircleMap_zero,Real.norm_eq_abs,sub_zero,abs_of_nonneg hd] using h
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology
namespace EuclideanFiveColor
lemma binaryR_zero (t : ℝ) : binaryR 0 t=Real.sqrt 3 := by
  simp only [binaryR,binaryQ,mul_zero,zero_mul,sub_zero,zero_pow (by norm_num : (2:ℕ)≠0),add_zero,Real.sqrt_one,mul_one]
  have h : (1:ℝ)-1/4=3/(2^2) := by norm_num
  rw [h,Real.sqrt_div (by norm_num),Real.sqrt_sq (by norm_num)]
  ring
lemma binaryB_zero (t : ℝ) : binaryB 0 t=Real.cos t+Real.sin t/Real.sqrt 3 := by
  simp [binaryB,binaryQ,binaryR_zero]
lemma binaryM_zero (t : ℝ) : binaryM 0 t=Real.sin t-Real.cos t/Real.sqrt 3 := by
  simp [binaryM,binaryQ,binaryR_zero,sub_eq_add_neg,neg_div]
lemma binaryB_zero_shift (t : ℝ) : binaryB 0 (t+Real.pi/3)=Real.cos t-Real.sin t/Real.sqrt 3 := by
  rw [binaryB_zero,Real.cos_add,Real.sin_add,Real.cos_pi_div_three,Real.sin_pi_div_three]
  have hr : Real.sqrt 3 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤3)
  field_simp
  linear_combination -Real.sin t*hs
lemma binaryM_zero_shift (t : ℝ) : binaryM 0 (t+Real.pi/3)=Real.sin t+Real.cos t/Real.sqrt 3 := by
  rw [binaryM_zero,Real.cos_add,Real.sin_add,Real.cos_pi_div_three,Real.sin_pi_div_three]
  have hr : Real.sqrt 3 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤3)
  field_simp
  linear_combination Real.cos t*hs
lemma trig_two_large {c s : ℝ} (hcs : c^2+s^2=1) :
    1/4 ≤ |c+s/Real.sqrt 3| ∨ 1/4 ≤ |c-s/Real.sqrt 3| := by
  by_contra h
  push Not at h
  have h1 := abs_lt.mp h.1
  have h2 := abs_lt.mp h.2
  have hc : |c| < 1/4 := by rw [abs_lt]; constructor <;> linarith
  have hq : |s/Real.sqrt 3| < 1/4 := by rw [abs_lt]; constructor <;> linarith
  have hr : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hr2 : Real.sqrt 3 < 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤3)]
  rw [abs_div,abs_of_pos hr,div_lt_iff₀ hr] at hq
  have hs : |s| < 1/2 := by linarith
  have hc2 : c^2 < (1/4 : ℝ)^2 := by nlinarith [sq_abs c,abs_nonneg c]
  have hs2 : s^2 < (1/2 : ℝ)^2 := by nlinarith [sq_abs s,abs_nonneg s]
  nlinarith
lemma sign_shift_large {g : ℝ → ℝ} (hg : ∀ t, g (t+Real.pi) = -g t)
    {t r : ℝ} (hr : r ≤ |g t|) : r ≤ g t ∨ r ≤ g (t+Real.pi) := by
  rw [hg]
  rcases le_total 0 (g t) with h|h
  · exact Or.inl (by simpa only [abs_of_nonneg h] using hr)
  · exact Or.inr (by simpa only [abs_of_nonpos h] using hr)
lemma binaryB_zero_large (t : ℝ) : ∃ n : ℕ, 1/4 ≤ binaryB 0 (t+(n : ℝ)*(Real.pi/3)) := by
  have hg : ∀ u, binaryB 0 (u+Real.pi) = -binaryB 0 u := by
    intro u
    simp only [binaryB_zero,Real.cos_add_pi,Real.sin_add_pi]
    ring
  have hh := trig_two_large (Real.cos_sq_add_sin_sq t)
  rw [← binaryB_zero,← binaryB_zero_shift] at hh
  rcases hh with h|h
  · rcases sign_shift_large hg h with h|h
    · exact ⟨0,by simpa using h⟩
    · refine ⟨3,?_⟩
      convert h using 2; norm_num; ring
  · rcases sign_shift_large hg h with h|h
    · exact ⟨1,by simpa using h⟩
    · refine ⟨4,?_⟩
      convert h using 2; norm_num; ring
lemma binaryM_zero_large (t : ℝ) : ∃ n : ℕ, 1/4 ≤ binaryM 0 (t+(n : ℝ)*(Real.pi/3)) := by
  have hg : ∀ u, binaryM 0 (u+Real.pi) = -binaryM 0 u := by
    intro u
    simp only [binaryM_zero,Real.cos_add_pi,Real.sin_add_pi]
    ring
  have hh := trig_two_large (Real.sin_sq_add_cos_sq t)
  rw [← binaryM_zero_shift,← binaryM_zero] at hh
  rcases hh with h|h
  · rcases sign_shift_large hg h with h|h
    · exact ⟨1,by simpa using h⟩
    · refine ⟨4,?_⟩
      convert h using 2; norm_num; ring
  · rcases sign_shift_large hg h with h|h
    · exact ⟨0,by simpa using h⟩
    · refine ⟨3,?_⟩
      convert h using 2; norm_num; ring
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal
namespace EuclideanFiveColor
lemma expansion_alternation_false {ι : Type*} {F D : ι → ℝ → ℝ}
    {K : ℝ≥0} {e U L P B κ : ℝ} {A : Set ℝ}
    (hd : ∀ j x, HasDerivAt (F j) (D j x) x)
    (hp : ∀ j x, (1/2 : ℝ) ≤ D j x) (hup : ∀ j x, D j x ≤ U)
    (hK : ∀ j, LipschitzWith K (D j)) (hlarge : ∀ x, ∃ j, 1+e ≤ D j x)
    (hadvance : ∀ x, ∃ j, x+e ≤ F j x) (hdispl : ∀ j x, F j x ≤ x+B)
    (he : 0 < e) (hKL : (K : ℝ)*L ≤ e) (hU : 0 < U) (hL : 0 < L) (hP : 0 < P)
    (hB : B ≤ L/2) (hκ : 0 < κ)
    (hinv : ∀ j, ∀ᵐ x : ℝ ∂volume, x ∈ A ↔ F j x ∈ A)
    (hA : MeasurableSet A)
    (hper : ∀ (n : ℤ) x, x+(n : ℝ)*P ∈ A ↔ x ∈ A)
    (halt : ∀ᵐ x : ℝ ∂volume, x+κ ∈ A ↔ x ∉ A) : False := by
  have hpos : volume A ≠ 0 := by
    intro hz
    have ha : ∀ᵐ x : ℝ ∂volume, x ∉ A := by
      rw [ae_iff]
      convert hz using 2
      ext x
      simp only [mem_ofPred_eq,not_not]
    have hf : ∀ᵐ x : ℝ ∂volume, False := by
      filter_upwards [ha,(measurePreserving_add_right volume κ).quasiMeasurePreserving.ae ha,halt] with x hx hx' hh
      exact hx' (hh.mpr hx)
    exact hf.exists.choose_spec
  obtain ⟨a,b,hlen,hnull⟩ := expansion_conull_interval hd hp hup hK hlarge he hKL hU hL hP hinv hA hpos hper
  have hLip : ∀ j, LipschitzWith (Real.toNNReal U) (F j) := by
    intro j
    apply lipschitzWith_of_nnnorm_deriv_le (fun x => (hd j x).differentiableAt)
    intro x
    rw [(hd j x).deriv]
    apply NNReal.coe_le_coe.mp
    rw [Real.coe_toNNReal _ hU.le,coe_nnnorm,Real.norm_eq_abs,
      abs_of_nonneg (le_trans (by norm_num) (hp j x))]
    exact hup j x
  have hmono : ∀ j, Monotone (F j) := by
    intro j
    apply StrictMono.monotone
    apply strictMono_of_deriv_pos
    intro x
    rw [(hd j x).deriv]
    exact lt_of_lt_of_le (by norm_num) (hp j x)
  obtain ⟨n,hn⟩ := exists_nat_gt ((κ-(b-a))/e)
  have hnn : κ < b+(n : ℝ)*e-a := by
    have := (div_lt_iff₀ he).mp hn
    linarith
  obtain ⟨b',hb',hnull'⟩ := conull_extend_intervals hLip hmono hadvance hdispl he
    (by linarith) (hB.trans_eq hlen.symm) hinv hnull n
  exact conull_interval_alternation_false hκ (by linarith) hnull' halt
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
namespace EuclideanFiveColor
def binaryConjugate (d : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  binaryCircleMap d (t+(n : ℝ)*(Real.pi/3))-(n : ℝ)*(Real.pi/3)
lemma binaryConjugate_hasDeriv {d : ℝ} (hd : |d|<1/2) (n : ℕ) (t : ℝ) :
    HasDerivAt (binaryConjugate d n) (1+d*binaryB d (t+(n : ℝ)*(Real.pi/3))) t := by
  convert ((binaryCircleMap_hasDeriv_t hd (t+(n : ℝ)*(Real.pi/3))).comp t
    ((hasDerivAt_id t).add_const ((n : ℝ)*(Real.pi/3)))).sub_const ((n : ℝ)*(Real.pi/3)) using 1 <;> first | rfl | simp
lemma binaryCircleMap_advance {d δ : ℝ} (hd : 0 < d) (hδ : δ ≤ 1/4) (hdδ : d < δ)
    (hM : ∀ s, |s| < δ → ∀ t, |binaryM s t-binaryM 0 t| < 1/8)
    {t : ℝ} (ht : 1/4 ≤ binaryM 0 t) : t+d/8 ≤ binaryCircleMap d t := by
  have hh : ∀ s ∈ Icc 0 d, HasDerivAt (fun s => binaryCircleMap s t) (binaryM s t) s := by
    intro s hs
    exact binaryCircleMap_hasDeriv_d (by rw [abs_of_nonneg hs.1]; linarith [hs.2]) t
  obtain ⟨s,hs,he⟩ := exists_hasDerivAt_eq_slope (fun s => binaryCircleMap s t) (fun s => binaryM s t) hd
    (fun s hs => (hh s hs).continuousAt.continuousWithinAt) (fun s hs => hh s ⟨hs.1.le,hs.2.le⟩)
  have hms := (abs_lt.mp (hM s (by rw [abs_of_pos hs.1]; exact hs.2.trans hdδ) t)).1
  rw [binaryCircleMap_zero,sub_zero] at he
  have hl : 1/8 ≤ (binaryCircleMap d t-t)/d := by rw [← he]; linarith
  have := (le_div_iff₀ hd).mp hl
  linarith
lemma binary_dynamics_controls : ∃ δ > 0, ∀ d, 0 < d → d < δ →
    ∃ C L : ℝ, 0 < C ∧ 0 < L ∧ C*d ≤ L/2 ∧
    (∀ (n : ℕ) t, (1/2 : ℝ) ≤ 1+d*binaryB d (t+(n : ℝ)*(Real.pi/3))) ∧
    (∀ (n : ℕ) t, 1+d*binaryB d (t+(n : ℝ)*(Real.pi/3)) ≤ 2) ∧
    (∀ n : ℕ, LipschitzWith (Real.toNNReal (d*C)) (fun t => 1+d*binaryB d (t+(n : ℝ)*(Real.pi/3)))) ∧
    (∀ t, ∃ n : ℕ, 1+d/8 ≤ 1+d*binaryB d (t+(n : ℝ)*(Real.pi/3))) ∧
    (∀ t, ∃ n : ℕ, t+d/8 ≤ binaryConjugate d n t) ∧
    (∀ (n : ℕ) t, binaryConjugate d n t ≤ t+C*d) ∧ d*C*L ≤ d/8 ∧ d < 1/2 := by
  obtain ⟨δ,C,hδ,hδa,hC,hclose,hbound⟩ := binary_uniform_controls (by norm_num : (0:ℝ)<1/8)
  let L := 1/(8*C)
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨min δ (min (1/(2*C)) (L/(2*C))),lt_min hδ (lt_min (by positivity) (by positivity)),?_⟩
  intro d hd hds
  have hdδ : d < δ := (lt_min_iff.mp hds).1
  have hda : d < 1/2 := by linarith
  have hdC : d*C < 1/2 := by
    have := (lt_div_iff₀ (by positivity : 0 < 2*C)).mp ((lt_min_iff.mp (lt_min_iff.mp hds).2).1)
    nlinarith
  have hdL : C*d ≤ L/2 := by
    have := (lt_div_iff₀ (by positivity : 0 < 2*C)).mp ((lt_min_iff.mp (lt_min_iff.mp hds).2).2)
    nlinarith
  have hbd := hbound d (by rw [abs_of_pos hd]; exact hdδ.le)
  have hdd : |d|<1/2 := by rwa [abs_of_pos hd]
  refine ⟨C,L,hC,hL,hdL,?_,?_,?_,?_,?_,?_,?_,hda⟩
  · intro n t
    have h := (abs_le.mp (hbd (t+(n : ℝ)*(Real.pi/3))).1).1
    nlinarith
  · intro n t
    have h := (abs_le.mp (hbd (t+(n : ℝ)*(Real.pi/3))).1).2
    nlinarith
  · intro n
    have hder : ∀ t, HasDerivAt (fun t => 1+d*binaryB d (t+(n : ℝ)*(Real.pi/3)))
        (d*binaryE d (t+(n : ℝ)*(Real.pi/3))) t := by
      intro t
      convert (((binaryB_hasDeriv_t hdd (t+(n : ℝ)*(Real.pi/3))).comp t
        ((hasDerivAt_id t).add_const ((n : ℝ)*(Real.pi/3)))).const_mul d).const_add 1 using 1 <;> first | rfl | simp
    apply lipschitzWith_of_nnnorm_deriv_le (fun t => (hder t).differentiableAt)
    intro t
    rw [(hder t).deriv]
    apply NNReal.coe_le_coe.mp
    rw [Real.coe_toNNReal _ (by positivity),coe_nnnorm,norm_mul,Real.norm_eq_abs,abs_of_pos hd,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hbd _).2.2 hd.le
  · intro t
    obtain ⟨n,hn⟩ := binaryB_zero_large t
    refine ⟨n,?_⟩
    have hh := (abs_lt.mp (hclose d (by rwa [abs_of_pos hd]) (t+(n : ℝ)*(Real.pi/3))).1).1
    nlinarith
  · intro t
    obtain ⟨n,hn⟩ := binaryM_zero_large t
    refine ⟨n,?_⟩
    have hh := binaryCircleMap_advance hd hδa hdδ (fun s hs u => (hclose s hs u).2) hn
    dsimp only [binaryConjugate]
    linarith
  · intro n t
    have hh := binaryCircleMap_displacement hd.le (lt_of_le_of_lt hδa (by norm_num)) hdδ.le
      (fun s hs u => (hbound s hs u).2.1) (t+(n : ℝ)*(Real.pi/3))
    dsimp only [binaryConjugate]
    linarith [(abs_le.mp hh).2]
  · dsimp [L]
    field_simp
    norm_num
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma binaryConjugate_step (d : ℝ) (n : ℕ) (x : ℝ) :
    binaryConjugate d n (x+Real.pi/3)=binaryConjugate d (n+1) x+Real.pi/3 := by
  unfold binaryConjugate
  push_cast
  have h : x+Real.pi/3+(n : ℝ)*(Real.pi/3)=x+((n : ℝ)+1)*(Real.pi/3) := by ring
  rw [h]
  ring
lemma binary_conjugates_invariant {d : ℝ} {A : Set ℝ}
    (hq : ∀ n : ℕ, Measure.QuasiMeasurePreserving (binaryConjugate d n) volume volume)
    (hF : ∀ᵐ x : ℝ ∂volume, x ∈ A ↔ binaryCircleMap d x ∈ A)
    (halt : ∀ᵐ x : ℝ ∂volume, x+Real.pi/3 ∈ A ↔ x ∉ A) :
    ∀ n : ℕ, ∀ᵐ x : ℝ ∂volume, x ∈ A ↔ binaryConjugate d n x ∈ A := by
  intro n
  induction n with
  | zero => simpa only [binaryConjugate,Nat.cast_zero,zero_mul,add_zero,sub_zero] using hF
  | succ n ih =>
    have hshift := (measurePreserving_add_right volume (Real.pi/3)).quasiMeasurePreserving.ae ih
    filter_upwards [hshift,halt,(hq (n+1)).ae halt] with x hx ha hb
    rw [binaryConjugate_step] at hx
    exact not_iff_not.mp (ha.symm.trans (hx.trans hb))
lemma binary_alternating_invariant_false : ∃ δ > 0, ∀ d, 0 < d → d < δ →
    ∀ A : Set ℝ, MeasurableSet A →
    (∀ (n : ℤ) x, x+(n : ℝ)*(2*Real.pi) ∈ A ↔ x ∈ A) →
    (∀ᵐ x : ℝ ∂volume, x+Real.pi/3 ∈ A ↔ x ∉ A) →
    (∀ᵐ x : ℝ ∂volume, x ∈ A ↔ binaryCircleMap d x ∈ A) → False := by
  obtain ⟨δ,hδ,hctrl⟩ := binary_dynamics_controls
  refine ⟨δ,hδ,?_⟩
  intro d hd hdδ A hA hper halt hF
  obtain ⟨C,L,hC,hL,hB,hlo,hhi,hLip,hlarge,hadvance,hdispl,hKL,hda⟩ := hctrl d hd hdδ
  have hdd : |d|<1/2 := by rwa [abs_of_pos hd]
  have hder := fun n t => binaryConjugate_hasDeriv hdd n t
  have hinv := binary_conjugates_invariant (fun n => deriv_lower_qmp (hder n) (hlo n)) hF halt
  exact expansion_alternation_false hder hlo hhi hLip hlarge hadvance hdispl (by positivity)
    (by simpa only [Real.coe_toNNReal _ (mul_pos hd hC).le] using hKL) (by norm_num) hL
    (by positivity : 0<2*Real.pi) hB (by positivity : 0<Real.pi/3) hinv hA hper halt
end EuclideanFiveColor
end

end OAI
