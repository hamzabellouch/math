import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.DimensionDrop.ConnectingTraces

namespace OAI

noncomputable section



namespace JiangSuConstruction
open Filter
open scoped Topology CStarAlgebra ComplexOrder

local instance positiveStagePNeZero (n : ℕ) : NeZero (stagePair n).p := ⟨(stagePair n).p_pos.ne'⟩
local instance positiveStageQNeZero (n : ℕ) : NeZero (stagePair n).q := ⟨(stagePair n).q_pos.ne'⟩

lemma spectralTransfer_re {p q : ℕ} (m : Multiplicities p q)
    (z : C(Interval,ℂ)) (t : Interval) :
    (spectralTransfer m z t).re = ((m.k*m.l:ℕ):ℝ)⁻¹ *
      ((m.lower:ℝ)*(z (lowerEigenvalue t)).re+
       (m.upper:ℝ)*(z (upperEigenvalue t)).re+(m.residual:ℝ)*(z t).re) := by
  simp [spectralTransfer,Complex.mul_re,Complex.inv_re,Complex.normSq_natCast]

lemma spectralTransfer_re_lower_bound {p q : ℕ} (m : Multiplicities p q)
    (z : C(Interval,ℂ)) {b : ℝ} (hz : ∀ t,b≤(z t).re) :
    ∀ t,b≤(spectralTransfer m z t).re := by
  intro t
  rw [spectralTransfer_re]
  have hN : (0:ℝ)<((m.k*m.l:ℕ):ℝ) := by exact_mod_cast Nat.mul_pos m.k_pos m.l_pos
  have htot : (m.lower:ℝ)+m.upper+m.residual=((m.k*m.l:ℕ):ℝ) := by exact_mod_cast m.total
  rw [le_inv_mul_iff₀ hN]
  calc
    _ = (m.lower:ℝ)*b+(m.upper:ℝ)*b+(m.residual:ℝ)*b := by rw [←htot]; ring
    _ ≤ _ := by gcongr <;> exact hz _

lemma spectralTransfer_re_lower {p q : ℕ} (m : Multiplicities p q)
    (z : C(Interval,ℂ)) (hz : ∀ t,0≤(z t).re) (t : Interval) :
    (1/8:ℝ)*(z (lowerEigenvalue t)).re≤(spectralTransfer m z t).re := by
  rw [spectralTransfer_re]
  have hN : (0:ℝ)<((m.k*m.l:ℕ):ℝ) := by exact_mod_cast Nat.mul_pos m.k_pos m.l_pos
  have hlo : ((m.k*m.l:ℕ):ℝ)≤8*(m.lower:ℝ) := by exact_mod_cast m.lower_mass
  rw [le_inv_mul_iff₀ hN]
  have hb := mul_le_mul_of_nonneg_right hlo (hz (lowerEigenvalue t))
  have hu := mul_nonneg (Nat.cast_nonneg m.upper (α := ℝ)) (hz (upperEigenvalue t))
  have hr := mul_nonneg (Nat.cast_nonneg m.residual (α := ℝ)) (hz t)
  nlinarith

lemma spectralTransfer_re_upper {p q : ℕ} (m : Multiplicities p q)
    (z : C(Interval,ℂ)) (hz : ∀ t,0≤(z t).re) (t : Interval) :
    (1/8:ℝ)*(z (upperEigenvalue t)).re≤(spectralTransfer m z t).re := by
  rw [spectralTransfer_re]
  have hN : (0:ℝ)<((m.k*m.l:ℕ):ℝ) := by exact_mod_cast Nat.mul_pos m.k_pos m.l_pos
  have hup : ((m.k*m.l:ℕ):ℝ)≤8*(m.upper:ℝ) := by exact_mod_cast m.upper_mass
  rw [le_inv_mul_iff₀ hN]
  have hb := mul_le_mul_of_nonneg_right hup (hz (upperEigenvalue t))
  have hl := mul_nonneg (Nat.cast_nonneg m.lower (α := ℝ)) (hz (lowerEigenvalue t))
  have hr := mul_nonneg (Nat.cast_nonneg m.residual (α := ℝ)) (hz t)
  nlinarith

lemma scalarIterates_re_lower_bound (n : ℕ) (z : C(Interval,ℂ)) {b : ℝ}
    (hz : ∀ t,b≤(z t).re) (k : ℕ) : ∀ t,b≤(scalarIterates n z k t).re := by
  induction k with
  | zero => exact hz
  | succ k ih => exact spectralTransfer_re_lower_bound _ _ ih

lemma scalarIterates_shift (n k : ℕ) (z : C(Interval,ℂ)) :
    scalarIterates n z (k+1)=scalarIterates (n+1)
      (spectralTransfer (canonicalMultiplicities (stagePair n).p_pos (stagePair n).q_pos) z) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change spectralTransfer (canonicalMultiplicities (stagePair (n+(k+1))).p_pos
      (stagePair (n+(k+1))).q_pos) (scalarIterates n z (k+1)) =
      spectralTransfer (canonicalMultiplicities (stagePair ((n+1)+k)).p_pos
        (stagePair ((n+1)+k)).q_pos)
        (scalarIterates (n+1) (spectralTransfer
          (canonicalMultiplicities (stagePair n).p_pos (stagePair n).q_pos) z) k)
    rw [ih]
    exact congrArg (fun j : ℕ => spectralTransfer
      (canonicalMultiplicities (stagePair j).p_pos (stagePair j).q_pos)
      (scalarIterates (n+1) (spectralTransfer
        (canonicalMultiplicities (stagePair n).p_pos (stagePair n).q_pos) z) k))
      (show n+(k+1)=(n+1)+k by omega)

lemma scalarIterates_re_net (k : ℕ) : ∀ n (z : C(Interval,ℂ))
    (_ : ∀ t,0≤(z t).re) (x t : Interval),
    ∃ s : Interval, |s.val-x.val|≤(1/2:ℝ)^k ∧
      (1/8:ℝ)^k*(z s).re≤(scalarIterates n z k t).re := by
  induction k with
  | zero =>
    intro n z hz x t
    refine ⟨t,?_,by simp [scalarIterates]⟩
    simp only [pow_zero,abs_le]
    constructor <;> linarith [t.property.1,t.property.2,x.property.1,x.property.2]
  | succ k ih =>
    intro n z hz x t
    let w := spectralTransfer (canonicalMultiplicities (stagePair n).p_pos (stagePair n).q_pos) z
    have hw : ∀ t,0≤(w t).re := spectralTransfer_re_lower_bound _ _ hz
    rw [scalarIterates_shift]
    by_cases hx : x.val≤1/2
    · let y : Interval := ⟨2*x.val,by constructor <;> linarith [x.property.1]⟩
      obtain ⟨s,hs,hb⟩ := ih (n+1) w hw y t
      refine ⟨lowerEigenvalue s,?_,?_⟩
      · change |s.val/2-x.val|≤(1/2:ℝ)^(k+1)
        calc
          |s.val/2-x.val|=|s.val-y.val|/2 := by
            change |s.val/2-x.val|=|s.val-2*x.val|/2
            rw [←abs_of_pos (by norm_num : (0:ℝ)<2),←abs_div]
            congr 1
            ring
          _ ≤ (1/2:ℝ)^k/2 := div_le_div_of_nonneg_right hs (by norm_num)
          _ = (1/2:ℝ)^(k+1) := by rw [pow_succ]; ring
      · have hl := spectralTransfer_re_lower
          (canonicalMultiplicities (stagePair n).p_pos (stagePair n).q_pos) z hz s
        calc
          _ = (1/8:ℝ)^k*((1/8:ℝ)*(z (lowerEigenvalue s)).re) := by rw [pow_succ]; ring
          _ ≤ (1/8:ℝ)^k*(w s).re := mul_le_mul_of_nonneg_left hl (by positivity)
          _ ≤ _ := hb
    · let y : Interval := ⟨2*x.val-1,by constructor <;> linarith [x.property.2]⟩
      obtain ⟨s,hs,hb⟩ := ih (n+1) w hw y t
      refine ⟨upperEigenvalue s,?_,?_⟩
      · change |(s.val+1)/2-x.val|≤(1/2:ℝ)^(k+1)
        calc
          |(s.val+1)/2-x.val|=|s.val-y.val|/2 := by
            change |(s.val+1)/2-x.val|=|s.val-(2*x.val-1)|/2
            rw [←abs_of_pos (by norm_num : (0:ℝ)<2),←abs_div]
            congr 1
            ring
          _ ≤ (1/2:ℝ)^k/2 := div_le_div_of_nonneg_right hs (by norm_num)
          _ = (1/2:ℝ)^(k+1) := by rw [pow_succ]; ring
      · have hl := spectralTransfer_re_upper
          (canonicalMultiplicities (stagePair n).p_pos (stagePair n).q_pos) z hz s
        calc
          _ = (1/8:ℝ)^k*((1/8:ℝ)*(z (upperEigenvalue s)).re) := by rw [pow_succ]; ring
          _ ≤ (1/8:ℝ)^k*(w s).re := mul_le_mul_of_nonneg_left hl (by positivity)
          _ ≤ _ := hb

lemma scalarIterates_add (n k l : ℕ) (z : C(Interval,ℂ)) :
    scalarIterates n z (k+l)=scalarIterates (n+k) (scalarIterates n z k) l := by
  induction l with
  | zero => rfl
  | succ l ih =>
    change spectralTransfer (canonicalMultiplicities (stagePair (n+(k+l))).p_pos
      (stagePair (n+(k+l))).q_pos) (scalarIterates n z (k+l)) =
      spectralTransfer (canonicalMultiplicities (stagePair ((n+k)+l)).p_pos
        (stagePair ((n+k)+l)).q_pos) (scalarIterates (n+k) (scalarIterates n z k) l)
    rw [ih]
    exact congrArg (fun j : ℕ => spectralTransfer
      (canonicalMultiplicities (stagePair j).p_pos (stagePair j).q_pos)
      (scalarIterates (n+k) (scalarIterates n z k) l))
      (show n+(k+l)=(n+k)+l by omega)

theorem scalarIterates_eventually_positive (n : ℕ) (z : C(Interval,ℂ))
    (hz : ∀ t,0≤(z t).re) (x : Interval) (hx : 0<(z x).re) :
    ∃ (b : ℝ) (k : ℕ),0<b ∧ ∀ l, k≤l → ∀ t,b≤(scalarIterates n z l t).re := by
  have hu := CompactSpace.uniformContinuous_of_continuous z.continuous
  obtain ⟨δ,hδ,hzδ⟩ := Metric.uniformContinuous_iff.mp hu ((z x).re/2) (half_pos hx)
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1/2:ℝ)<1)
  obtain ⟨k,hk⟩ := (hp.eventually (gt_mem_nhds hδ)).exists
  let b : ℝ := (1/8:ℝ)^k*((z x).re/2)
  have hb : 0<b := by dsimp [b]; positivity
  have hkall (t : Interval) : b≤(scalarIterates n z k t).re := by
    obtain ⟨s,hs,hb'⟩ := scalarIterates_re_net k n z hz x t
    have hd : dist s x<δ := hs.trans_lt hk
    have hn := hzδ hd
    rw [dist_eq_norm] at hn
    have hr := Complex.re_le_norm (z x-z s)
    rw [Complex.sub_re,norm_sub_rev] at hr
    have hsval : (z x).re/2≤(z s).re := by linarith
    exact (mul_le_mul_of_nonneg_left hsval (by positivity : 0≤(1/8:ℝ)^k)).trans hb'
  refine ⟨b,k,hb,?_⟩
  intro l hl t
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hl
  rw [scalarIterates_add]
  exact scalarIterates_re_lower_bound (n+k) _ hkall j t

theorem scalarIterates_eventually_oscillation (n : ℕ) (z : C(Interval,ℂ))
    {ε : ℝ} (hε : 0<ε) :
    ∃ k : ℕ,∀ l, k≤l → ∀ s t,
      ‖scalarIterates n z l s-scalarIterates n z l t‖<ε := by
  obtain ⟨L,hL,hz⟩ := continuous_affine_modulus z (half_pos hε)
  have ht : Tendsto (fun k : ℕ => (7/8:ℝ)^k*L) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤7/8)
      (by norm_num : (7/8:ℝ)<1)).mul_const L
  obtain ⟨k,hk⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds (half_pos hε)))
  refine ⟨k,fun l hl s t => ?_⟩
  have hb := scalarIterates_affine_modulus n z hL hz l s t
  have hc : ((7/8:ℝ)^l*L)*dist s t≤(7/8:ℝ)^l*L :=
    mul_le_of_le_one_right (mul_nonneg (pow_nonneg (by norm_num) _) hL) (interval_dist_le_one s t)
  have hkl := hk l hl
  linarith

end JiangSuConstruction

end

end OAI
