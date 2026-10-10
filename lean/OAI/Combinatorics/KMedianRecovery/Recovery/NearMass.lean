import Mathlib

namespace OAI

namespace MetricKMedianRecovery.NearClients
variable {V : Type*}

lemma sublevel_card [DecidableEq V] (C : Finset V) (f : V → ℝ) (hf : ∀ p ∈ C, 0 ≤ f p)
    (mean a : ℝ) (hmean : ∑ p ∈ C, f p = mean * C.card) (ha : 0 < a) :
    (1-1/a) * (C.card : ℝ) ≤ ((C.filter (fun p => f p ≤ a*mean)).card : ℝ) := by
  classical
  let N := C.filter (fun p => f p ≤ a*mean)
  by_cases hm : mean = 0
  · have hzero : ∀ p ∈ C, f p = 0 := by
      have hs : ∑ p ∈ C, f p = 0 := by simpa only [hm, zero_mul] using hmean
      exact (Finset.sum_eq_zero_iff_of_nonneg hf).mp hs
    have hN : N = C := by
      apply Finset.filter_eq_self.mpr
      intro p hp
      simp [hzero p hp, hm]
    change (1-1/a)*(C.card : ℝ) ≤ (N.card : ℝ)
    rw [hN]
    nlinarith [mul_nonneg (one_div_pos.mpr ha).le (Nat.cast_nonneg (α := ℝ) C.card)]
  · by_cases hn : C.Nonempty
    · have hc : (0 : ℝ) < C.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hn)
      have hmn : 0 < mean := by
        have hs : 0 ≤ mean * C.card := hmean ▸ Finset.sum_nonneg hf
        exact lt_of_le_of_ne (nonneg_of_mul_nonneg_left hs hc) (Ne.symm hm)
      have hh : (a*mean) * ((C \ N).card : ℝ) ≤ ∑ p ∈ C \ N, f p := by
        calc
          _ = ∑ _p ∈ C \ N, a*mean := by simp [mul_comm]
          _ ≤ _ := Finset.sum_le_sum (fun p hp => by
            have hnp := (Finset.mem_sdiff.mp hp).2
            have hpC := (Finset.mem_sdiff.mp hp).1
            exact (lt_of_not_ge (fun h => hnp (Finset.mem_filter.mpr ⟨hpC,h⟩))).le)
      have hs : (∑ p ∈ C \ N, f p) ≤ mean * C.card := by
        rw [← hmean]
        exact Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun p hp _ => hf p hp)
      have hcard := Finset.card_sdiff_add_card_eq_card (show N ⊆ C from Finset.filter_subset _ _)
      have hcard' : ((C \ N).card : ℝ) + (N.card : ℝ) = C.card := by exact_mod_cast hcard
      change (1-1/a)*(C.card : ℝ) ≤ (N.card : ℝ)
      have hmc : a*((C \ N).card : ℝ) ≤ C.card := by
        nlinarith [hh.trans hs]
      apply (mul_le_mul_iff_right₀ ha).mp
      field_simp
      nlinarith
    · simp only [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.card_empty, Nat.cast_zero, mul_zero,
        Finset.filter_empty, le_refl]

lemma exists_le_average [DecidableEq V] (C : Finset V) (hC : C.Nonempty) (f : V → ℝ) :
    ∃ p ∈ C, f p ≤ (∑ q ∈ C, f q)/(C.card : ℝ) := by
  obtain ⟨p,hp,hmin⟩ := Finset.exists_min_image C f hC
  refine ⟨p,hp,?_⟩
  apply (le_div_iff₀ (Nat.cast_pos.mpr (Finset.card_pos.mpr hC))).mpr
  calc
    _ = ∑ _q ∈ C, f p := by simp [mul_comm]
    _ ≤ _ := Finset.sum_le_sum (fun q hq => hmin q hq)

noncomputable def nearMass [PseudoMetricSpace V] (C : Finset V)
    (o : V) (mean a : ℝ) (H : V → ℝ) : ℝ := by
  classical
  exact ∑ p ∈ C.filter (fun p => dist p o ≤ a*mean), H p

lemma nearMass_nonneg [PseudoMetricSpace V] (C : Finset V)
    (o : V) (mean a : ℝ) (H : V → ℝ) (hH : ∀ p ∈ C, 0 ≤ H p) :
    0 ≤ nearMass C o mean a H := by
  classical
  exact Finset.sum_nonneg (fun p hp => hH p (Finset.mem_filter.mp hp).1)

variable [PseudoMetricSpace V]

lemma center_bound [DecidableEq V] (C : Finset V) (hC : C.Nonempty) (o : V)
    (mean a b : ℝ) (H : V → ℝ) (hmean : ∑ p ∈ C, dist p o = mean*C.card)
    (hb : 1 < b) (hba : b ≤ a) (hH : ∀ p ∈ C, 0 ≤ H p)
    (htri : ∀ p ∈ C, H o ≤ dist p o + H p) :
    H o ≤ b*mean + nearMass C o mean a H / ((1-1/b)*(C.card : ℝ)) := by
  classical
  have hc : (0 : ℝ) < C.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hC)
  have hm : 0 ≤ mean := by
    have hh : 0 ≤ mean*C.card := hmean ▸ Finset.sum_nonneg (fun _ _ => dist_nonneg)
    exact nonneg_of_mul_nonneg_left hh hc
  let N := C.filter (fun p => dist p o ≤ b*mean)
  have hb0 : 0 < 1-1/b := by
    have hh := (div_lt_one (by linarith : 0 < b)).mpr hb
    linarith
  have hpop : (1-1/b)*(C.card : ℝ) ≤ N.card :=
    sublevel_card C (fun p => dist p o) (fun _ _ => dist_nonneg) mean b hmean (by linarith)
  have hN : N.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp ((mul_pos hb0 hc).trans_le hpop))
  obtain ⟨p,hp,hw⟩ := exists_le_average N hN H
  have hsub : N ⊆ C.filter (fun p => dist p o ≤ a*mean) := by
    intro q hq
    have hq' := Finset.mem_filter.mp hq
    exact Finset.mem_filter.mpr ⟨hq'.1,hq'.2.trans (mul_le_mul_of_nonneg_right hba hm)⟩
  have hsum : (∑ q ∈ N, H q) ≤ nearMass C o mean a H :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q hq _ => hH q (Finset.mem_filter.mp hq).1)
  have hand : (∑ q ∈ N, H q)/(N.card : ℝ) ≤
      nearMass C o mean a H / ((1-1/b)*(C.card : ℝ)) := by
    apply (div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _)).trans
    exact div_le_div_of_nonneg_left (nearMass_nonneg C o mean a H hH) (mul_pos hb0 hc) hpop
  have hp' := Finset.mem_filter.mp hp
  exact (htri p hp'.1).trans (add_le_add hp'.2 (hw.trans hand))

lemma main_center_bound [DecidableEq V] (C : Finset V) (hC : C.Nonempty) (o : V)
    (mean : ℝ) (H : V → ℝ) (hmean : ∑ p ∈ C, dist p o = mean*C.card)
    (hH : ∀ p ∈ C, 0 ≤ H p) (htri : ∀ p ∈ C, H o ≤ dist p o + H p) :
    H o ≤ (51/50 : ℝ)*mean + 60*nearMass C o mean (6/5) H/(C.card : ℝ) := by
  have hh := center_bound C hC o mean (6/5) (51/50) H hmean (by norm_num) (by norm_num) hH htri
  norm_num at hh
  have hT := nearMass_nonneg C o mean (6/5) H hH
  have hc : (0 : ℝ) < C.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hC)
  have he : nearMass C o mean (6/5) H / ((1/51 : ℝ)*C.card) =
      51*nearMass C o mean (6/5) H/(C.card : ℝ) := by field_simp
  rw [he] at hh
  apply hh.trans
  exact add_le_add_right (div_le_div_of_nonneg_right (by nlinarith : 51*nearMass C o mean (6/5) H ≤ 60*nearMass C o mean (6/5) H) hc.le) _

lemma main_far_bound [DecidableEq V] (C : Finset V) (hC : C.Nonempty) (o p : V)
    (mean : ℝ) (H : V → ℝ) (hmean : ∑ q ∈ C, dist q o = mean*C.card)
    (hH : ∀ q ∈ C, 0 ≤ H q) (htri : ∀ q ∈ C, H o ≤ dist q o + H q)
    (hp : H p ≤ dist p o + H o) (hfar : (6/5 : ℝ)*mean < dist p o) :
    H p ≤ (37/20 : ℝ)*dist p o + 60*nearMass C o mean (6/5) H/(C.card : ℝ) := by
  have hh := main_center_bound C hC o mean H hmean hH htri
  linarith

lemma main_weight_algebra (P Pg PA PB T W : ℝ) (hP : 0 ≤ P)
    (hg : 0 ≤ Pg) (_hA : 0 ≤ PA) (hB : 0 ≤ PB) (hs : Pg+PA+PB=P)
    (hW : W ≤ Pg+(1/100 : ℝ)*P+(17/5+6/5*(1/1000000))*PA+
      (26/5*(1/1000000))*P+(37/20)*PB+61*T) :
    W ≤ (171/50 : ℝ)*P+61*T := by
  linarith

noncomputable def progressConstant (kappa : ℝ) : ℝ := kappa/(2*(171/50+61*kappa))

lemma progressConstant_pos (kappa : ℝ) (hk : 0 < kappa) : 0 < progressConstant kappa := by
  unfold progressConstant
  positivity

lemma ball_progress (P T W kappa : ℝ) (_hP : 0 < P) (hk : 0 < kappa)
    (hW : 0 < W) (hT : kappa*P < T) (hbound : W ≤ (171/50 : ℝ)*P+61*T) :
    progressConstant kappa ≤ T/(2*W) := by
  unfold progressConstant
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith

lemma removal_progress (P T I W kappa : ℝ) (_hP : 0 < P) (hk : 0 < kappa)
    (hW : 0 < W) (hT : T ≤ kappa*P) (hI : kappa*P < I)
    (hbound : W ≤ (171/50 : ℝ)*P+61*T) :
    progressConstant kappa ≤ I/(2*W) := by
  unfold progressConstant
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith

end MetricKMedianRecovery.NearClients

end OAI
