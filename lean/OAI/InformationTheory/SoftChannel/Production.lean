import OAI.InformationTheory.BooleanNoise.Attainment
import OAI.InformationTheory.BooleanNoise.CubeVariance
import OAI.InformationTheory.SoftChannel.Joining

namespace OAI

section

noncomputable section
open Set Filter
open scoped BigOperators Topology
namespace LeanBlast.CourtadeKumar

lemma IsInterior.neg_soft {n : ℕ} {g : Cube n → ℝ} (hg : IsInterior g) :
    IsInterior (fun x => -g x) := by
  intro x
  constructor <;> linarith [(hg x).1,(hg x).2]

lemma dissipation_neg_soft {n : ℕ} (g : Cube n → ℝ) (hg : IsInterior g) :
    dissipation (fun x => -g x)=dissipation g := by
  unfold dissipation cubeDerivative
  congr 1
  funext i
  congr 1
  funext x
  dsimp only
  rw [artanh_neg_interior (hg x)]
  ring

lemma IsInterior.information_lt_entropy {n : ℕ} {g : Cube n → ℝ} (hg : IsInterior g) :
    informationDeficit g < entropy (CourtadeKumar.cubeAverage g) := by
  unfold informationDeficit
  linarith [hg.entropyAverage_pos]

lemma IsInterior.information_mem {n : ℕ} {g : Cube n → ℝ} (hg : IsInterior g) :
    informationDeficit g ∈ Ico 0 ell :=
  ⟨informationDeficit_nonneg hg,hg.information_lt_entropy.trans_le (entropy_le_ell _)⟩

lemma r_pooled_child_information {n : ℕ} (A B : Cube n → ℝ)
    (hA : IsInterior A) (hB : IsInterior B) :
    r ((informationDeficit A+informationDeficit B)/2) ≤
      (r (informationDeficit A)+r (informationDeficit B))/2 := by
  have h := convexOn_r.2 hA.information_mem hB.information_mem
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  simpa only [smul_eq_mul, ← add_div, one_div_mul_eq_div] using h

lemma ordered_positive_joining {n : ℕ} (A B : Cube n → ℝ)
    (hA : IsInterior A) (hB : IsInterior B) (horder : cubeAverage B ≤ cubeAverage A)
    (hm : 0 < (cubeAverage A+cubeAverage B)/2)
    (hI : entropy ((cubeAverage A+cubeAverage B)/2)-(entropyAverage A+entropyAverage B)/2 ≤ softCutoff) :
    r (entropy ((cubeAverage A+cubeAverage B)/2)-(entropyAverage A+entropyAverage B)/2) ≤
      (r (informationDeficit A)+r (informationDeficit B))/2+
        cubeAverage (fun x => joiningCost (A x) (B x)) := by
  let m := (cubeAverage A+cubeAverage B)/2
  let d := (cubeAverage A-cubeAverage B)/2
  let e := (entropyAverage A+entropyAverage B)/2
  have hd : 0 ≤ d := by dsimp [d]; linarith
  have ha : cubeAverage A=m+d := by dsimp [m,d]; ring
  have hb : cubeAverage B=m-d := by dsimp [m,d]; ring
  have herr : entropy m-e = entropy ((cubeAverage A+cubeAverage B)/2)-(entropyAverage A+entropyAverage B)/2 := rfl
  have hj : pairH m d-e=(informationDeficit A+informationDeficit B)/2 := by
    dsimp [pairH,informationDeficit,e]; rw [← ha,← hb]; ring
  have hp : e ≤ pairH m d := by
    have h1 := informationDeficit_nonneg hA
    have h2 := informationDeficit_nonneg hB
    nlinarith [hj]
  have hc : wallDemand m d e ≤ cubeAverage (fun x => joiningCost (A x) (B x)) := by
    rcases hd.eq_or_lt with hd | hd
    · have hd0 : d=0 := hd.symm
      simp only [wallDemand,hd0,pairH,add_zero,sub_zero,add_self_div_two,sub_self]
      exact cubeAverage_nonneg (fun x => joiningCost_nonneg (hA x) (hB x))
    · exact low_information_joining A B hA hB hm hd
        (by rw [← ha]; exact hA.cubeAverage.2) ha hb hp hI
  have hpool := r_pooled_child_information A B hA hB
  dsimp [wallDemand] at hc
  rw [hj] at hc
  linarith

lemma positive_joining {n : ℕ} (A B : Cube n → ℝ)
    (hA : IsInterior A) (hB : IsInterior B)
    (hm : 0 < (cubeAverage A+cubeAverage B)/2)
    (hI : entropy ((cubeAverage A+cubeAverage B)/2)-(entropyAverage A+entropyAverage B)/2 ≤ softCutoff) :
    r (entropy ((cubeAverage A+cubeAverage B)/2)-(entropyAverage A+entropyAverage B)/2) ≤
      (r (informationDeficit A)+r (informationDeficit B))/2+
        cubeAverage (fun x => joiningCost (A x) (B x)) := by
  rcases le_total (cubeAverage B) (cubeAverage A) with hab | hab
  · exact ordered_positive_joining A B hA hB hab hm hI
  · have h := ordered_positive_joining B A hB hA hab
      (by simpa only [add_comm] using hm) (by simpa only [add_comm] using hI)
    simpa only [add_comm, joiningCost_symm] using h

lemma all_soft_meanReserve {n : ℕ} (g : Cube n → ℝ) (hg : IsInterior g) :
    meanReserve (cubeAverage g) (informationDeficit g) ≤ dissipation g := by
  have h := all_soft_reserve g hg
  convert! h using 1
  simp only [meanReserve,meanVariance,informationDeficit]
  ring_nf

theorem all_soft_sharp_production {n : ℕ} (g : Cube n → ℝ) (hg : IsInterior g) :
    r (informationDeficit g) ≤ dissipation g := by
  induction n with
  | zero => simp only [informationDeficit_dim_zero,dissipation_dim_zero,r_zero]; exact le_rfl
  | succ n ih =>
    have positive (G : Cube (n+1) → ℝ) (hG : IsInterior G) (hm : 0 < cubeAverage G) :
        r (informationDeficit G) ≤ dissipation G := by
      by_cases hI : softCutoff ≤ informationDeficit G
      · exact (high_information_reserve (abs_lt.mpr hG.cubeAverage) hI hG.information_lt_entropy).trans
          (all_soft_meanReserve G hG)
      · have hj := positive_joining (restrict G true) (restrict G false)
          (hG.restrict true) (hG.restrict false)
          (by rwa [← cubeAverage_split])
          (by rw [← cubeAverage_split, ← entropyAverage_split]; exact (le_of_not_ge hI))
        have hc : (fun x => joiningCost (restrict G true x) (restrict G false x))=
            (fun x => pairDissipation (pairMean G x) (pairHalfDifference G x)) := by
          funext x
          rw [← pairMean_add_halfDifference G x,← pairMean_sub_halfDifference G x,joiningCost_pair]
        rw [← cubeAverage_split, ← entropyAverage_split,hc] at hj
        have ht := ih (restrict G true) (hG.restrict true)
        have hf := ih (restrict G false) (hG.restrict false)
        rw [dissipation_split]
        change r (entropy (cubeAverage G)-entropyAverage G) ≤ _
        linarith
    rcases lt_trichotomy 0 (cubeAverage g) with hm | hm | hm
    · exact positive g hg hm
    · have h := all_soft_meanReserve g hg
      rw [← hm,meanReserve_zero_mean hg.information_mem] at h
      exact h
    · have h := positive (fun x => -g x) hg.neg_soft (by rw [cubeAverage_neg]; linarith)
      rwa [informationDeficit_neg,dissipation_neg_soft g hg] at h

theorem all_soft_max_production {n : ℕ} (g : Cube n → ℝ) (hg : IsInterior g) :
    max (meanReserve (cubeAverage g) (informationDeficit g)) (r (informationDeficit g)) ≤ dissipation g :=
  max_le (all_soft_meanReserve g hg) (all_soft_sharp_production g hg)

end LeanBlast.CourtadeKumar
end
end

end OAI
