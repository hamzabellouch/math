import Mathlib
import OAI.Probability.LogConcave.Numerics.OrdinaryDerivativeWeight

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.Quadrature
open Set MeasureTheory
open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

lemma twoends_continuousOn {a b : ℝ} (ha : 0<a) (hab : a≤b) (hb : b<1) :
    ContinuousOn (fun t : ℝ => t⁻¹*(1-t)⁻¹) (uIcc a b) := by
  rw [uIcc_of_le hab]
  exact (continuousOn_id.inv₀ (fun _ ht => ne_of_gt (ha.trans_le ht.1))).mul
    ((continuousOn_const.sub continuousOn_id).inv₀ (fun t ht => by change 1-t≠0; linarith [ht.2]))

lemma twoends_integral {a b : ℝ} (ha : 0<a) (hab : a≤b) (hb : b<1) :
    (∫t in a..b,t⁻¹*(1-t)⁻¹)=
      Real.log b-Real.log (1-b)-(Real.log a-Real.log (1-a)) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f:=fun t => Real.log t-Real.log (1-t))
  · intro t ht
    rw [uIcc_of_le hab] at ht
    have ht0 : t≠0 := ne_of_gt (ha.trans_le ht.1)
    have ht1 : 1-t≠0 := by linarith [ht.2]
    have hd : HasDerivAt (fun t : ℝ => Real.log t-Real.log (1-t))
        (t⁻¹-(-1/(1-t))) t := by
      convert! (Real.hasDerivAt_log ht0).sub
        (((hasDerivAt_id t).const_sub 1).log ht1) using 1
    convert! hd using 1; field_simp [ht0,ht1]; ring
  · exact (twoends_continuousOn ha hab hb).intervalIntegrable

lemma twoends_integral_upper {a T h : ℝ} (ha : 0<a) (haT : a≤T) (hT : T<1)
    (hh : 0<h) (hla : h/4≤a) :
    (∫t in a..T,t⁻¹*(1-t)⁻¹)≤logMeshLength T+|Real.log h|+Real.log 4 := by
  rw [twoends_integral ha haT hT]
  have hT0 : 0<T := ha.trans_le haT
  have h1a : 0<1-a := by linarith
  have hlogT : Real.log T≤0 := Real.log_nonpos hT0.le hT.le
  have hloga : Real.log (1-a)≤0 := Real.log_nonpos h1a.le (by linarith)
  have hl := Real.log_le_log (by positivity : 0<h/4) hla
  rw [Real.log_div (ne_of_gt hh) (by norm_num)] at hl
  have hh' : -Real.log h≤|Real.log h| := neg_le_abs _
  dsimp only [logMeshLength]
  linarith

lemma ordinaryDerivativeWeight_bound (u : I → ℝ) (D : ℝ) (hD : 0≤D)
    (hDu : ∀t∈Icc (0:ℝ) 1,∑i,|basisDerivative u i t|≤D)
    {a b h : ℝ} (ha : 0<a) (hab : a<b) (hb : b<1) (hh : 0<h)
    (hl : h/4*(1-a)≤b-a) (i : I) :
    |ordinaryDerivativeWeight u a b i|≤
      (4*D/h)*(∫t in a..b,t⁻¹*(1-t)⁻¹) := by
  have hc := ordinaryDerivativeWeight_integrand_continuousOn u a b i ha hab.le
  have hk := twoends_continuousOn ha hab.le hb
  have hnorm := intervalIntegral.norm_integral_le_integral_norm (f:=fun t =>
    (b-a)⁻¹*t⁻¹*basisDerivative u i ((t-a)/(b-a))) (μ:=volume) hab.le
  change |ordinaryDerivativeWeight u a b i|≤_ at hnorm
  apply hnorm.trans
  rw [←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on hab.le hc.norm.intervalIntegrable
    (continuousOn_const.mul hk).intervalIntegrable
  intro t ht
  have ht0 : 0<t := ha.trans_le ht.1
  have ht1 : 0<1-t := by linarith [ht.2]
  have hba : 0<b-a := sub_pos.mpr hab
  have hur : (t-a)/(b-a)∈Icc (0:ℝ) 1 :=
    ⟨div_nonneg (sub_nonneg.mpr ht.1) hba.le,
      (div_le_one hba).mpr (by linarith [ht.2])⟩
  have hu : |basisDerivative u i ((t-a)/(b-a))|≤D :=
    (Finset.single_le_sum (fun j _ => abs_nonneg (basisDerivative u j ((t-a)/(b-a))))
      (Finset.mem_univ i)).trans (hDu _ hur)
  have hinv : (b-a)⁻¹≤4/h*(1-t)⁻¹ := by
    rw [←one_div,div_le_iff₀ hba]
    have hl' : h*(1-t)≤4*(b-a) := by nlinarith [mul_nonneg hh.le (sub_nonneg.mpr ht.1)]
    have he : 1≤(4*(b-a))/(h*(1-t)) := (one_le_div (mul_pos hh ht1)).mpr hl'
    simpa only [div_eq_mul_inv,mul_inv_rev,mul_comm,mul_left_comm,mul_assoc] using he
  change |(b-a)⁻¹*t⁻¹*basisDerivative u i ((t-a)/(b-a))|≤
    (4*D/h)*(t⁻¹*(1-t)⁻¹)
  simp only [abs_mul,abs_of_nonneg (inv_nonneg.mpr hba.le),
    abs_of_nonneg (inv_nonneg.mpr ht0.le)]
  calc
    _ ≤ (b-a)⁻¹*t⁻¹*D := mul_le_mul_of_nonneg_left hu (by positivity)
    _ ≤ (4/h*(1-t)⁻¹)*t⁻¹*D := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hinv (by positivity)) hD
    _ = _ := by ring
end LogConcaveSampling.Quadrature

end

end

section

noncomputable section
namespace LogConcaveSampling.Quadrature
open Set MeasureTheory
open scoped BigOperators

lemma sum_fin_skip_first_integral {N : ℕ} (hN : 0<N) (a : ℕ → ℝ) (f : ℝ → ℝ)
    (hi : ∀k,1≤k → k<N → IntervalIntegrable f volume (a k) (a (k+1))) :
    (∑i : Fin N,if i.val=0 then 0 else ∫t in a i.val..a (i.val+1),f t)=
      ∫t in a 1..a N,f t := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hN)
  rw [Fin.sum_univ_eq_sum_range (fun j => if j=0 then 0 else ∫t in a j..a (j+1),f t),Finset.sum_range_succ']
  simp only [Nat.add_one_ne_zero,ite_false,ite_true,zero_add,add_zero]
  exact intervalIntegral.sum_integral_adjacent_intervals (a:=fun j => a (j+1))
    (fun j hj => hi (j+1) (by omega) (by omega))

lemma sum_fin_first {N : ℕ} (hN : 0<N) (C : ℝ) :
    (∑i : Fin N,if i.val=0 then C else 0)=C := by
  have he (i : Fin N) : (i.val=0)↔i=⟨0,hN⟩ := by
    constructor
    · intro hh; exact Fin.ext hh
    · intro hh; exact congrArg Fin.val hh
  simp_rw [he]
  simp
end LogConcaveSampling.Quadrature

namespace LogConcaveSampling
open Set MeasureTheory Quadrature
open scoped Classical BigOperators

theorem terminalQuadratureWeight_sum {T h : ℝ} (hT0 : 0<T) (hT1 : T<1)
    (hh : 0<h) (hs : h≤Real.log 2) (hL : h≤logMeshLength T)
    (n : ℕ) (D : ℝ) (hD : 0≤D)
    (hDu : ∀t∈Icc (0:ℝ) 1,∑i,|basisDerivative (probabilityNodes (n+1)) i t|≤D) :
    (∑s,|terminalQuadratureWeight T h n s|)≤
      4/h*((∑i,|zeroHermiteWeight (probabilityNodes (n+1)) 0 i|)+
        (n+2)*D*(logMeshLength T+|Real.log h|+Real.log 4)) := by
  let H := ∑i,|zeroHermiteWeight (probabilityNodes (n+1)) 0 i|
  let K := fun t : ℝ => t⁻¹*(1-t)⁻¹
  have hH : 0≤H := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hc (c : Fin (logMeshCount T h)) :
      (∑i,|terminalQuadratureWeight T h n (c,i)|)≤
        (if c.val=0 then 4*H/h else 0)+
        ((n+2:ℕ):ℝ)*(4*D/h)*(if c.val=0 then 0 else
          ∫t in logMeshNode T h c.val..logMeshNode T h (c.val+1),K t) := by
    by_cases hc0 : c.val=0
    · simp only [terminalQuadratureWeight,hc0,ite_true,mul_zero,add_zero,
        abs_div,abs_of_nonneg (probabilityCellLength_pos hT0 hT1 hh c).le,←Finset.sum_div]
      have hb := logMeshFirst_lower hT0 hT1 hh hL hs
      have he : h/4≤probabilityCellLength T h c := by
        simpa only [probabilityCellLength,hc0,logMeshNode_zero,zero_add,sub_zero] using hb
      apply (div_le_iff₀ (probabilityCellLength_pos hT0 hT1 hh c)).mpr
      apply (le_of_eq (by field_simp [ne_of_gt hh] : H=(4*H/h)*(h/4))).trans
      exact mul_le_mul_of_nonneg_left he (by positivity)
    · simp only [terminalQuadratureWeight,hc0,ite_false,zero_add]
      have ha := logMeshNode_pos hT0 hT1 hh (Nat.pos_of_ne_zero hc0)
      have hb := (logMeshNode_mem hT0 hT1 hh (Nat.succ_le_of_lt c.2)).2.trans_lt hT1
      have hab := logMeshNode_strictMono hT0 hT1 hh (Nat.lt_succ_self c.val)
      have he := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) =>
        ordinaryDerivativeWeight_bound (probabilityNodes (n+1)) D hD hDu ha hab hb hh
          (logMeshCell_lower hT0 hT1 hh hL hs c.val) i)
      simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
        Nat.cast_add,Nat.cast_one,mul_assoc,K,Nat.cast_ofNat,add_assoc,show (1:ℝ)+1=2 by norm_num] using he
  rw [Fintype.sum_prod_type]
  apply (Finset.sum_le_sum (fun c _ => hc c)).trans
  rw [Finset.sum_add_distrib,sum_fin_first (logMeshCount_pos hT0 hT1 hh),←Finset.mul_sum]
  rw [sum_fin_skip_first_integral (logMeshCount_pos hT0 hT1 hh)]
  · rw [logMeshNode_last hT0 hT1 hh]
    have hi := twoends_integral_upper (logMeshNode_pos hT0 hT1 hh (by norm_num : 0<1))
      (logMeshNode_mem hT0 hT1 hh (logMeshCount_pos hT0 hT1 hh)).2 hT1 hh
      (logMeshFirst_lower hT0 hT1 hh hL hs)
    have he := mul_le_mul_of_nonneg_left hi (by positivity : 0≤((n+2:ℕ):ℝ)*(4*D/h))
    change 4*H/h+((n+2:ℕ):ℝ)*(4*D/h)*(∫t in logMeshNode T h 1..T,K t)≤_
    calc
      _ ≤ 4*H/h+((n+2:ℕ):ℝ)*(4*D/h)*(logMeshLength T+|Real.log h|+Real.log 4) := add_le_add le_rfl he
      _ = _ := by dsimp only [H]; push_cast; ring
  · intro j hj hjN
    exact (twoends_continuousOn (logMeshNode_pos hT0 hT1 hh (by omega))
      (logMeshNode_strictMono hT0 hT1 hh (Nat.lt_succ_self j)).le
      ((logMeshNode_mem hT0 hT1 hh (by omega)).2.trans_lt hT1)).intervalIntegrable
end LogConcaveSampling

end

end

end OAI
