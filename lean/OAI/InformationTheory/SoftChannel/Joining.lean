import OAI.InformationTheory.SoftChannel.SoftReserve

namespace OAI

section

noncomputable section
open Set Filter
open scoped Topology
namespace LeanBlast.CourtadeKumar

lemma joiningCost_pair (c d : ℝ) : joiningCost (c+d) (c-d) = pairDissipation c d := by
  unfold joiningCost pairDissipation
  ring

lemma joiningCost_symm (a b : ℝ) : joiningCost a b = joiningCost b a := by
  unfold joiningCost; ring

lemma onecorner_payment {m d k : ℝ} (_hm : 0 ≤ m) (hd : 0 < d) (hmd : m+d<1)
    (hk : k ∈ Icc (1-m) 1) :
    wallDemand m d (onecornerEntropy m d k) ≤ k*joiningCost (onecornerX m d k) (onecornerY m d k) := by
  have hk0 : 0 < k := by linarith [hk.1]
  let c := 1-(1-m)/k
  let v := d/k
  have hc : 0 ≤ c := by dsimp [c]; exact sub_nonneg.mpr ((div_le_one hk0).mpr hk.1)
  have hv : 0 < v := div_pos hd hk0
  have hcv : c+v<1 := by
    dsimp [c,v]
    rw [show 1-(1-m)/k+d/k=1-(1-m-d)/k by ring]
    exact sub_lt_self _ (div_pos (by linarith : 0<1-m-d) hk0)
  have hx : c+v=onecornerX m d k := by dsimp [c,v,onecornerX]; ring
  have hy : c-v=onecornerY m d k := by dsimp [c,v,onecornerY]; ring
  have hthin : thinX c k=m := by dsimp [thinX,c]; field_simp; ring
  have hkv : k*v=d := by dsimp [v]; field_simp
  have he : k*pairH c v=onecornerEntropy m d k := by dsimp [pairH,onecornerEntropy]; rw [hx,hy]; ring
  have h := common_output_payment hc hv hcv ⟨hk0,hk.2⟩
  have hcap := mul_le_mul_of_nonneg_left
    (r_pairEntropyGap_le_pairDissipation c v (wall_domain hc hv.le hcv)) hk0.le
  have hI : thinI c v k=entropy m-onecornerEntropy m d k := by dsimp [thinI]; rw [hthin,he]
  have hJ : thinJ c v k=pairH m d-onecornerEntropy m d k := by dsimp [thinJ]; rw [hthin,he,hkv]
  rw [hI,hJ] at h
  rw [← joiningCost_pair,hx,hy] at hcap
  exact h.trans hcap

lemma high_value_joining {n : ℕ} (A B : Cube n → ℝ) (hA : IsInterior A) (hB : IsInterior B)
    {m d : ℝ} (hm : 0 ≤ m) (hd : 0 < d) (hmd : m+d<1)
    (ha : cubeAverage A=m+d) (hb : cubeAverage B=m-d)
    (he : (1-m)*entropy (d/(1-m)) ≤ (entropyAverage A+entropyAverage B)/2)
    (hphys : (entropyAverage A+entropyAverage B)/2 ≤ pairH m d) :
    wallDemand m d ((entropyAverage A+entropyAverage B)/2) ≤
      cubeAverage (fun x => joiningCost (A x) (B x)) := by
  obtain ⟨k,hk,hke⟩ := exists_onecorner_entropy hm hd hmd he hphys
  exact (hke ▸ onecorner_payment hm hd hmd hk).trans
    (onecorner_cost_lower A B hA hB hm hd hmd hk ha hb hke.symm)

lemma reflected_payment {m r k : ℝ} (hm : 0 < m) (hr : r ∈ Ioo 0 1)
    (hk : 0 < k) (hkm : k ≤ 1-m) (hI : entropy m-k*entropy r ≤ softCutoff) :
    wallDemand m (k*r) (k*entropy r) ≤ k*joiningCost r (-r) := by
  have hk1 : k < 1 := by linarith
  have hw : 0 ≤ 1-k := by linarith
  have hd : 0 < k*r := mul_pos hk hr.1
  have hwd : (1-k)+k*r<1 := by nlinarith [mul_pos hk (sub_pos.mpr hr.2)]
  have he : 0 < k*entropy r := mul_pos hk (entropy_pos ⟨by linarith [hr.1],hr.2⟩)
  have hX : thinX 0 k=1-k := by simp [thinX]
  have hH : pairH 0 r=entropy r := by simp [pairH,entropy_neg]
  have hj := thinJ_pos (by norm_num : (0:ℝ) ≤ 0) hr.1.le (by linarith [hr.2] : 0+r<1) ⟨hk,hk1⟩
  have hje : k*entropy r < pairH (1-k) (k*r) := by
    dsimp [thinJ] at hj
    rw [hX,hH] at hj
    linarith
  have hwall := wall_comparison hm.le (by linarith : m ≤ 1-k) hd.le hwd he hje hI
  have hpay := common_output_payment (by norm_num : (0:ℝ) ≤ 0) hr.1 (by linarith [hr.2] : 0+r<1) ⟨hk,hk1.le⟩
  have hI' : thinI 0 r k=entropy (1-k)-k*entropy r := by dsimp [thinI]; rw [hX,hH]
  have hJ' : thinJ 0 r k=pairH (1-k) (k*r)-k*entropy r := by dsimp [thinJ]; rw [hX,hH]
  rw [hI',hJ'] at hpay
  have hcap := mul_le_mul_of_nonneg_left (r_pairEntropyGap_le_pairDissipation 0 r
    (by simpa only [abs_zero,zero_add,abs_of_pos hr.1] using hr.2)) hk.le
  have hcost : pairDissipation 0 r=joiningCost r (-r) := by
    simpa using (joiningCost_pair 0 r).symm
  rw [hcost] at hcap
  exact hwall.trans (hpay.trans hcap)

lemma low_information_joining {n : ℕ} (A B : Cube n → ℝ) (hA : IsInterior A) (hB : IsInterior B)
    {m d : ℝ} (hm : 0 < m) (hd : 0 < d) (hmd : m+d<1)
    (ha : cubeAverage A=m+d) (hb : cubeAverage B=m-d)
    (hphys : (entropyAverage A+entropyAverage B)/2 ≤ pairH m d)
    (hI : entropy m-(entropyAverage A+entropyAverage B)/2 ≤ softCutoff) :
    wallDemand m d ((entropyAverage A+entropyAverage B)/2) ≤
      cubeAverage (fun x => joiningCost (A x) (B x)) := by
  by_cases he : (1-m)*entropy (d/(1-m)) ≤ (entropyAverage A+entropyAverage B)/2
  · exact high_value_joining A B hA hB hm.le hd hmd ha hb he hphys
  · have hep : 0 < (entropyAverage A+entropyAverage B)/2 := by
      linarith [hA.entropyAverage_pos,hB.entropyAverage_pos]
    obtain ⟨r,hr,hre⟩ := exists_reflected_entropy hm.le hd hmd hep (le_of_not_ge he)
    have hm1 : 0 < 1-m := by linarith
    have hr0 : 0 < r := (div_pos hd hm1).trans_le hr.1
    let k := d/r
    have hk : 0 < k := div_pos hd hr0
    have hkr : k*r=d := by dsimp [k]; field_simp
    have hkm : k ≤ 1-m := by
      apply (div_le_iff₀ hr0).mpr
      have h := (div_le_iff₀ hm1).mp hr.1
      nlinarith
    have heq : k*entropy r=(entropyAverage A+entropyAverage B)/2 := hre
    have hpay := reflected_payment hm ⟨hr0,hr.2⟩ hk hkm (by rwa [heq])
    rw [hkr,heq] at hpay
    have hcost := reflected_cost_lower A B hA hB ⟨hr0,hr.2⟩
      (show cubeAverage A-cubeAverage B=2*k*r by rw [ha,hb]; nlinarith [hkr]) heq.symm
    exact hpay.trans hcost

end LeanBlast.CourtadeKumar
end
end

end OAI
