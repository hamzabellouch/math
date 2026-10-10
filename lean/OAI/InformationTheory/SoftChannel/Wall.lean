import OAI.InformationTheory.SoftChannel.RateSlope

namespace OAI

section

noncomputable section
open Set Filter
open scoped Topology
namespace LeanBlast.CourtadeKumar

def wallA (m d : ℝ) : ℝ := (Real.artanh (m+d)+Real.artanh (m-d))/2
def wallC (m d : ℝ) : ℝ := (Real.artanh (m+d)-Real.artanh (m-d))/2
def wallADeriv (m d : ℝ) : ℝ := (1/(1-(m+d)^2)-1/(1-(m-d)^2))/2

def entropySlopeAux (u : ℝ) : ℝ := 1/(1-u^2)-Real.artanh u^2

lemma artanh_neg_interior {u : ℝ} (hu : u ∈ Ioo (-1) 1) : Real.artanh (-u) = -Real.artanh u := by
  rw [artanh_eq_log_sub (show -u ∈ Ioo (-1) 1 by constructor <;> linarith [hu.1,hu.2]),
    artanh_eq_log_sub hu]
  simp only [← sub_eq_add_neg,sub_neg_eq_add]
  ring

lemma entropySlopeAux_neg {u : ℝ} (hu : u ∈ Ioo (-1) 1) : entropySlopeAux (-u) = entropySlopeAux u := by
  simp [entropySlopeAux,artanh_neg_interior hu]

lemma hasDerivAt_entropySlopeAux {u : ℝ} (hu : u ∈ Ioo (-1) 1) :
    HasDerivAt entropySlopeAux (2*(u-(1-u^2)*Real.artanh u)/(1-u^2)^2) u := by
  have hd : 1-u^2 ≠ 0 := by nlinarith [hu.1,hu.2]
  have h := ((hasDerivAt_const u (1:ℝ)).div (((hasDerivAt_id u).pow 2).const_sub 1) hd).sub
    ((hasDerivAt_artanh hu).pow 2)
  convert! h using 1; dsimp [entropySlopeAux]; field_simp; ring

lemma monotoneOn_entropySlopeAux : MonotoneOn entropySlopeAux (Ico 0 1) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg
    (f' := fun u => 2*(u-(1-u^2)*Real.artanh u)/(1-u^2)^2) (convex_Ico _ _)
  · intro u hu
    exact (hasDerivAt_entropySlopeAux ⟨by linarith [hu.1],hu.2⟩).continuousAt.continuousWithinAt
  · intro u hu
    simp only [interior_Ico,mem_Ioo] at hu
    exact (hasDerivAt_entropySlopeAux ⟨by linarith [hu.1],hu.2⟩).hasDerivWithinAt
  · intro u hu
    simp only [interior_Ico,mem_Ioo] at hu
    exact div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr (one_sub_sq_mul_artanh_le_self ⟨hu.1.le,hu.2⟩))) (sq_nonneg _)

lemma wall_domain {m d : ℝ} (hm : 0 ≤ m) (hd : 0 ≤ d) (hmd : m+d < 1) : |m|+|d|<1 := by
  rwa [abs_of_nonneg hm,abs_of_nonneg hd]

lemma wallA_nonneg {m d : ℝ} (hm : 0 ≤ m) (hd : 0 ≤ d) (hmd : m+d < 1) : 0 ≤ wallA m d := by
  have hh := wall_domain hm hd hmd
  have hp := pair_add_mem_Ioo m d hh
  have hn := pair_sub_mem_Ioo m d hh
  have h := Real.strictMonoOn_artanh.monotoneOn
    (show -(m-d) ∈ Ioo (-1) 1 by constructor <;> linarith [hn.1,hn.2]) hp (by linarith : -(m-d) ≤ m+d)
  rw [artanh_neg_interior hn] at h
  unfold wallA; linarith

lemma wallC_nonneg {m d : ℝ} (hm : 0 ≤ m) (hd : 0 ≤ d) (hmd : m+d < 1) : 0 ≤ wallC m d := by
  have hh := wall_domain hm hd hmd
  have h := Real.strictMonoOn_artanh.monotoneOn (pair_sub_mem_Ioo m d hh) (pair_add_mem_Ioo m d hh)
    (by linarith : m-d ≤ m+d)
  unfold wallC; linarith

lemma wallADeriv_lower {m d : ℝ} (hm : 0 ≤ m) (hd : 0 ≤ d) (hmd : m+d < 1) :
    2*wallA m d*wallC m d ≤ wallADeriv m d := by
  have hh := wall_domain hm hd hmd
  have hn := pair_sub_mem_Ioo m d hh
  have h := monotoneOn_entropySlopeAux
    (show |m-d| ∈ Ico 0 1 by exact ⟨abs_nonneg _,by rw [abs_lt]; exact hn⟩)
    (show m+d ∈ Ico 0 1 by exact ⟨by linarith,hmd⟩)
    (show |m-d| ≤ m+d by rw [abs_le]; constructor <;> linarith)
  have he : entropySlopeAux |m-d| = entropySlopeAux (m-d) := by
    rcases le_total 0 (m-d) with hpos | hneg
    · rw [abs_of_nonneg hpos]
    · rw [abs_of_nonpos hneg,entropySlopeAux_neg hn]
  rw [he] at h
  dsimp [entropySlopeAux,wallA,wallC,wallADeriv] at *
  nlinarith

lemma hasDerivAt_wallA_d {m d : ℝ} (hh : |m|+|d|<1) :
    HasDerivAt (wallA m) (wallADeriv m d) d := by
  have h := (((hasDerivAt_artanh (pair_add_mem_Ioo m d hh)).comp d
    ((hasDerivAt_id d).const_add m)).add ((hasDerivAt_artanh (pair_sub_mem_Ioo m d hh)).comp d
    ((hasDerivAt_id d).const_sub m))).div_const 2
  convert! h using 1; dsimp [wallA,wallADeriv]; ring

lemma hasDerivAt_pairH_d {m d : ℝ} (hh : |m|+|d|<1) :
    HasDerivAt (pairH m) (-wallC m d) d := by
  have h := (hasDerivAt_pairEntropyGap m d hh).const_sub (entropy m)
  convert! h using 1
  ext t; dsimp [pairH,pairEntropyGap]; ring

lemma hasDerivAt_pairH_m {m d : ℝ} (hh : |m|+|d|<1) :
    HasDerivAt (fun x => pairH x d) (-wallA m d) m := by
  have h := (((hasDerivAt_entropy (pair_add_mem_Ioo m d hh)).comp m
    ((hasDerivAt_id m).add_const d)).add ((hasDerivAt_entropy (pair_sub_mem_Ioo m d hh)).comp m
    ((hasDerivAt_id m).sub_const d))).div_const 2
  convert! h using 1; dsimp [pairH,wallA]; ring

lemma pairH_antitone_d {m d : ℝ} (hm : 0 ≤ m) (_hd : 0 ≤ d) (hmd : m+d<1) :
    AntitoneOn (pairH m) (Icc 0 d) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun t => -wallC m t) (convex_Icc _ _)
  · intro t ht
    exact (hasDerivAt_pairH_d (wall_domain hm ht.1 (by linarith [ht.2]))).continuousAt.continuousWithinAt
  · intro t ht
    simp only [interior_Icc,mem_Ioo] at ht
    exact (hasDerivAt_pairH_d (wall_domain hm ht.1.le (by linarith [ht.2]))).hasDerivWithinAt
  · intro t ht
    simp only [interior_Icc,mem_Ioo] at ht
    exact neg_nonpos.mpr (wallC_nonneg hm ht.1.le (by linarith [ht.2]))

lemma pairH_le_entropy {m d : ℝ} (hm : 0 ≤ m) (hd : 0 ≤ d) (hmd : m+d<1) :
    pairH m d ≤ entropy m := by
  have h := pairEntropyGap_nonneg m d (wall_domain hm hd hmd)
  dsimp [pairEntropyGap,pairH] at *
  linarith

lemma rate_entropy_slope {m d e : ℝ} (hm : 0 ≤ m) (hd : 0 ≤ d) (hmd : m+d<1)
    (he : 0 < e) (hj : e < pairH m d) (hI : entropy m-e ≤ softCutoff) :
    rDeriv (entropy m-e)*Real.artanh m ≤ rDeriv (pairH m d-e)*wallA m d := by
  have hdom (t : ℝ) (ht : t ∈ Icc 0 d) : |m|+|t|<1 :=
    wall_domain hm ht.1 (by linarith [ht.2])
  have hjdom (t : ℝ) (ht : t ∈ Icc 0 d) : pairH m t-e ∈ Ioo 0 ell := by
    have ha := pairH_antitone_d hm hd hmd ht ⟨hd,le_rfl⟩ ht.2
    have hb := pairH_le_entropy hm ht.1 (by linarith [ht.2])
    constructor <;> linarith [entropy_le_ell m]
  have hjcut (t : ℝ) (ht : t ∈ Icc 0 d) : pairH m t-e ≤ softCutoff := by
    linarith [pairH_le_entropy hm ht.1 (by linarith [ht.2])]
  let f := fun t => rDeriv (pairH m t-e)*wallA m t
  let f' := fun t => -rSecondDeriv (pairH m t-e)*wallC m t*wallA m t+
      rDeriv (pairH m t-e)*wallADeriv m t
  have hf (t : ℝ) (ht : t ∈ Icc 0 d) : HasDerivAt f (f' t) t := by
    have h := (((hasDerivAt_rDeriv (hjdom t ht)).comp t
      ((hasDerivAt_pairH_d (hdom t ht)).sub_const e)).mul (hasDerivAt_wallA_d (hdom t ht)))
    convert! h using 1; dsimp [f,f']; ring
  have hf' (t : ℝ) (ht : t ∈ Icc 0 d) : 0 ≤ f' t := by
    have hs := r_slope_bound ⟨(hjdom t ht).1.le,hjcut t ht⟩
    have ha := wallA_nonneg hm ht.1 (by linarith [ht.2])
    have hc := wallC_nonneg hm ht.1 (by linarith [ht.2])
    have hb := wallADeriv_lower hm ht.1 (by linarith [ht.2])
    have hr := rDeriv_ge_two (hjdom t ht).1.le (hjdom t ht).2
    have h1 := mul_le_mul_of_nonneg_right hs.le (mul_nonneg hc ha)
    have h2 := mul_le_mul_of_nonneg_left hb (show 0 ≤ rDeriv (pairH m t-e) by linarith)
    dsimp [f']; nlinarith
  have hmono : MonotoneOn f (Icc 0 d) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := f') (convex_Icc _ _)
    · intro t ht; exact (hf t ht).continuousAt.continuousWithinAt
    · intro t ht; exact (hf t (interior_subset ht)).hasDerivWithinAt
    · intro t ht; exact hf' t (interior_subset ht)
  have h := hmono ⟨le_rfl,hd⟩ ⟨hd,le_rfl⟩ hd
  simpa [f,pairH,wallA] using h

def wallDemand (m d e : ℝ) : ℝ := r (entropy m-e)-r (pairH m d-e)
def wallDemandDeriv (m d e : ℝ) : ℝ :=
  -rDeriv (entropy m-e)*Real.artanh m+rDeriv (pairH m d-e)*wallA m d

lemma hasDerivAt_wallDemand {m d e : ℝ} (hm : 0 ≤ m) (hd : 0 ≤ d) (hmd : m+d<1)
    (he : 0 < e) (hj : e < pairH m d) :
    HasDerivAt (fun x => wallDemand x d e) (wallDemandDeriv m d e) m := by
  have hp := pairH_le_entropy hm hd hmd
  have hI : entropy m-e ∈ Ioo 0 ell := by constructor <;> linarith [entropy_le_ell m]
  have hJ : pairH m d-e ∈ Ioo 0 ell := by constructor <;> linarith [entropy_le_ell m]
  have hh := wall_domain hm hd hmd
  have h := (((hasDerivAt_r hI).comp m
    ((hasDerivAt_entropy (pair_mean_mem_Ioo m d hh)).sub_const e)).sub
    ((hasDerivAt_r hJ).comp m ((hasDerivAt_pairH_m hh).sub_const e)))
  convert! h using 1; dsimp [wallDemand,wallDemandDeriv]; ring

lemma pairH_antitone_m {m d : ℝ} (_hm : 0 ≤ m) (hd : 0 ≤ d) (hmd : m+d<1) :
    AntitoneOn (fun x => pairH x d) (Icc 0 m) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun t => -wallA t d) (convex_Icc _ _)
  · intro t ht
    exact (hasDerivAt_pairH_m (wall_domain ht.1 hd (by linarith [ht.2]))).continuousAt.continuousWithinAt
  · intro t ht
    simp only [interior_Icc,mem_Ioo] at ht
    exact (hasDerivAt_pairH_m (wall_domain ht.1.le hd (by linarith [ht.2]))).hasDerivWithinAt
  · intro t ht
    simp only [interior_Icc,mem_Ioo] at ht
    exact neg_nonpos.mpr (wallA_nonneg ht.1.le hd (by linarith [ht.2]))

lemma wall_comparison {m w d e : ℝ} (hm : 0 ≤ m) (hmw : m ≤ w) (hd : 0 ≤ d) (hwd : w+d<1)
    (he : 0 < e) (hj : e < pairH w d) (hI : entropy m-e ≤ softCutoff) :
    wallDemand m d e ≤ wallDemand w d e := by
  have hdom (t : ℝ) (ht : t ∈ Icc m w) : 0 ≤ t ∧ t+d<1 ∧ e < pairH t d := by
    have h := pairH_antitone_m (hm.trans hmw) hd hwd ⟨hm.trans ht.1,ht.2⟩ ⟨hm.trans hmw,le_rfl⟩ ht.2
    exact ⟨hm.trans ht.1,by linarith [ht.2],hj.trans_le h⟩
  have hcut (t : ℝ) (ht : t ∈ Icc m w) : entropy t-e ≤ softCutoff := by
    have h := strictMonoOn_psi.monotoneOn (show m ∈ Icc 0 1 by constructor; exact hm; linarith)
      (show t ∈ Icc 0 1 by constructor; exact hm.trans ht.1; linarith [ht.2]) ht.1
    dsimp [entropy] at *; linarith
  have hmono : MonotoneOn (fun x => wallDemand x d e) (Icc m w) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun t => wallDemandDeriv t d e) (convex_Icc _ _)
    · intro t ht
      obtain ⟨ht0,htd,htj⟩ := hdom t ht
      exact (hasDerivAt_wallDemand ht0 hd htd he htj).continuousAt.continuousWithinAt
    · intro t ht
      obtain ⟨ht0,htd,htj⟩ := hdom t (interior_subset ht)
      exact (hasDerivAt_wallDemand ht0 hd htd he htj).hasDerivWithinAt
    · intro t ht
      obtain ⟨ht0,htd,htj⟩ := hdom t (interior_subset ht)
      have h := rate_entropy_slope ht0 hd htd he htj (hcut t (interior_subset ht))
      unfold wallDemandDeriv; linarith
  exact hmono ⟨le_rfl,hmw⟩ ⟨hmw,le_rfl⟩ hmw

end LeanBlast.CourtadeKumar
end
end

end OAI
