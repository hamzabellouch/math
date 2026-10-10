import OAI.MathematicalPhysics.CriticalSK.GOESpectrum

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

open scoped ENNReal NNReal

open scoped BigOperators NNReal

open scoped BigOperators

open scoped BigOperators InnerProductSpace

open Module

open Matrix Polynomial

open scoped BigOperators Topology

open Filter

namespace CriticalSK


open scoped Topology

def edgeLength (n : ℕ) : ℕ := 2^(Nat.clog 8 (n+1))

def naturalEdgeScale (n : ℕ) (L : ℝ) : ℝ := L/(edgeLength n : ℝ)^2

def formConstant : ℝ := 41472*Real.sqrt (512*(48*Real.exp 1+4))

lemma edgeLength_pos (n : ℕ) : 0 < edgeLength n := by unfold edgeLength; positivity

lemma edgeLength_cast_pos (n : ℕ) : (0:ℝ) < edgeLength n := by exact_mod_cast edgeLength_pos n

lemma edgeLength_cube (n : ℕ) : (n+1:ℝ) ≤ (edgeLength n:ℝ)^3 ∧
    (edgeLength n:ℝ)^3 ≤ 8*(n+1:ℝ) := by
  simpa only [edgeLength,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one] using
    dyadic_cube_scale (n+1) (Nat.succ_pos n)

lemma naturalEdgeScale_pos (n : ℕ) {L : ℝ} (hL : 0 < L) : 0 < naturalEdgeScale n L := by
  exact div_pos hL (sq_pos_of_pos (edgeLength_cast_pos n))

lemma naturalEdgeScale_base (n : ℕ) {L : ℝ} (hL : 1 ≤ L) :
    scaleEnergy (Nat.clog 8 (n+1)) 0 ≤ naturalEdgeScale n L := by
  simp only [scaleEnergy,scaleRoot,pow_zero,one_div,naturalEdgeScale,edgeLength,Nat.cast_pow,Nat.cast_ofNat]
  rw [inv_pow,← one_div]
  exact div_le_div_of_nonneg_right hL (by positivity)

lemma formConstant_pos : 0 < formConstant := by unfold formConstant; positivity

lemma formA_edgeLength (n : ℕ) {h : ℝ} (hh : 0 ≤ h) :
    formA n h ≤ formConstant*(h+1)*(edgeLength n:ℝ)^(-5/4:ℝ) := by
  let D : ℝ := edgeLength n
  have hD : 0 < D := edgeLength_cast_pos n
  have hN : (0:ℝ) < n+1 := by positivity
  have hroot : Real.sqrt (32*(entryVariance n:ℝ)) ≤
      Real.sqrt (512*(48*Real.exp 1+4))*D^(-3/2:ℝ) := by
    have hfrac : 32*(entryVariance n:ℝ) ≤ (512*(48*Real.exp 1+4))/D^3 := by
      change 32*(2*(48*Real.exp 1+4)/(n+1)) ≤ _
      apply (le_div_iff₀ (pow_pos hD 3)).mpr
      calc
        _ = (64*(48*Real.exp 1+4))*D^3/(n+1) := by ring
        _ ≤ (64*(48*Real.exp 1+4))*(8*(n+1))/(n+1) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (edgeLength_cube n).2 (by positivity)) hN.le
        _ = 512*(48*Real.exp 1+4) := by field_simp; ring
    calc
      _ ≤ Real.sqrt ((512*(48*Real.exp 1+4))/D^3) := Real.sqrt_le_sqrt hfrac
      _ = _ := by
        rw [Real.sqrt_div (by positivity)]
        have hd : Real.sqrt (D^3) = D^(3/2:ℝ) := by
          rw [Real.sqrt_eq_rpow,← Real.rpow_natCast,← Real.rpow_mul hD.le]
          norm_num
        rw [hd,div_eq_mul_inv,← Real.rpow_neg hD.le]
        congr 2; norm_num
  calc
    _ = 41472*Real.sqrt (32*(entryVariance n:ℝ))*(h+1)*D^(1/4:ℝ) := by
      simp only [formA,D,edgeLength,Nat.cast_pow,Nat.cast_ofNat]
    _ ≤ 41472*(Real.sqrt (512*(48*Real.exp 1+4))*D^(-3/2:ℝ))*(h+1)*D^(1/4:ℝ) := by
      gcongr
    _ = formConstant*(h+1)*D^(-5/4:ℝ) := by
      rw [formConstant,show (-5/4:ℝ)=(-3/2:ℝ)+(1/4:ℝ) by norm_num,Real.rpow_add hD]
      ring

lemma formA_natural_scale (n : ℕ) {h L : ℝ} (hh : 0 ≤ h) (hL : 0 < L) :
    formA n h*(naturalEdgeScale n L)^(-5/8:ℝ) ≤ formConstant*(h+1)*L^(-5/8:ℝ) := by
  have hD := edgeLength_cast_pos n
  calc
    _ ≤ (formConstant*(h+1)*(edgeLength n:ℝ)^(-5/4:ℝ))*(naturalEdgeScale n L)^(-5/8:ℝ) := by
      exact mul_le_mul_of_nonneg_right (formA_edgeLength n hh)
        (Real.rpow_nonneg (naturalEdgeScale_pos n hL).le _)
    _ = _ := by
      rw [naturalEdgeScale,Real.div_rpow hL.le (sq_nonneg _),← Real.rpow_natCast,
        ← Real.rpow_mul hD.le]
      norm_num
      field_simp [Real.rpow_ne_zero hD.le hD.ne']

lemma orderedJacobiGaps_top_bound {n m : ℕ} (hm : 0 < m) (hfit : 12*m ≤ n)
    (i : Fin (n+1)) (hi : i.val < 3) :
    orderedJacobiGaps n i ≤ 4/(m:ℝ)^2+2*(12*m+1:ℝ)/(n+1) := by
  have hh := pathOperator_eigenvalue_lower hm (r := 3) (by omega) i hi
  unfold orderedJacobiGaps
  norm_num only [Nat.cast_ofNat] at hh
  rw [show (4:ℝ)*m*3 = 12*m by ring] at hh
  linarith

lemma edgeLength_tendsto : Tendsto (fun n : ℕ => (edgeLength n:ℝ)) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  have hn : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  filter_upwards [hn.eventually_ge_atTop ((max b 0)^3)] with n hn'
  by_contra! hb
  have hp := pow_lt_pow_left₀ (hb.trans_le (le_max_left b 0))
    (edgeLength_cast_pos n).le (by norm_num : 3 ≠ 0)
  linarith [(edgeLength_cube n).1]

lemma edgeLength_sq_div_bound (n : ℕ) :
    (edgeLength n:ℝ)^2/(n+1) ≤ 8/(edgeLength n:ℝ) := by
  have hD := edgeLength_cast_pos n
  have hN : (0:ℝ) < n+1 := by positivity
  rw [div_le_div_iff₀ hN hD]
  nlinarith [(edgeLength_cube n).2]

lemma edgeLength_sq_div_tendsto :
    Tendsto (fun n : ℕ => (edgeLength n:ℝ)^2/(n+1)) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => by positivity) edgeLength_sq_div_bound
  exact edgeLength_tendsto.const_div_atTop 8

lemma edgeLength_div_sqrt_tendsto :
    Tendsto (fun n : ℕ => (edgeLength n:ℝ)/Real.sqrt (n+1)) atTop (𝓝 0) := by
  have hh := edgeLength_sq_div_tendsto.sqrt
  simpa only [Real.sqrt_div (sq_nonneg _),Real.sqrt_sq (edgeLength_cast_pos _).le,Real.sqrt_zero] using hh

lemma naturalEdgeScale_tendsto (L : ℝ) :
    Tendsto (fun n => naturalEdgeScale n L) atTop (𝓝 0) := by
  exact ((tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp edgeLength_tendsto).const_div_atTop L

lemma formB_natural_scale_tendsto (L : ℝ) :
    Tendsto (fun n => formB n / naturalEdgeScale n L) atTop (𝓝 0) := by
  have hh := (edgeLength_sq_div_tendsto.const_mul 8).div_const L
  simpa only [mul_zero,zero_div] using hh.congr (fun n => by
    dsimp only [formB,naturalEdgeScale]
    ring_nf; simp only [inv_inv]; ring)

lemma formC_natural_scale_tendsto {L : ℝ} (hL : 0 < L) :
    Tendsto (fun n => formC n / Real.sqrt (naturalEdgeScale n L)) atTop (𝓝 0) := by
  have hh := (edgeLength_div_sqrt_tendsto.const_mul 16).div_const (Real.sqrt L)
  simpa only [mul_zero,zero_div] using hh.congr (fun n => by
    dsimp only [formC,naturalEdgeScale]
    rw [Real.sqrt_div hL.le,Real.sqrt_sq (edgeLength_cast_pos n).le]
    simp only [div_eq_mul_inv,_root_.mul_inv_rev,inv_inv]; ring)

lemma naturalEdgeScale_space (n : ℕ) {L : ℝ} (hL : 0 < L) :
    L*Real.sqrt L/8 ≤ (n+1:ℝ)*naturalEdgeScale n L*Real.sqrt (naturalEdgeScale n L) ∧
    (n+1:ℝ)*naturalEdgeScale n L*Real.sqrt (naturalEdgeScale n L) ≤ L*Real.sqrt L := by
  have hD := edgeLength_cast_pos n
  have he : (n+1:ℝ)*naturalEdgeScale n L*Real.sqrt (naturalEdgeScale n L) =
      (L*Real.sqrt L)*((n+1:ℝ)/(edgeLength n:ℝ)^3) := by
    rw [naturalEdgeScale,Real.sqrt_div hL.le,Real.sqrt_sq hD.le]
    ring
  have hfrac : (1/8:ℝ) ≤ (n+1:ℝ)/(edgeLength n:ℝ)^3 := by
    rw [le_div_iff₀ (pow_pos hD 3)]
    linarith [(edgeLength_cube n).2]
  have hfrac' : (n+1:ℝ)/(edgeLength n:ℝ)^3 ≤ 1 := by
    rw [div_le_one (pow_pos hD 3)]
    exact (edgeLength_cube n).1
  rw [he]
  constructor
  · simpa only [div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_left hfrac (by positivity : 0 ≤ L*Real.sqrt L)
  · simpa using mul_le_mul_of_nonneg_left hfrac' (by positivity : 0 ≤ L*Real.sqrt L)

lemma formB_tendsto : Tendsto formB atTop (𝓝 0) := by
  exact (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1:ℝ)))).const_div_atTop 8

lemma formC_tendsto : Tendsto formC atTop (𝓝 0) := by
  exact (Real.tendsto_sqrt_atTop.comp
    (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1:ℝ))))).const_div_atTop 16

lemma formA_tendsto {h : ℝ} (hh : 0 ≤ h) : Tendsto (fun n => formA n h) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => formA_nonneg n hh) (fun n => formA_edgeLength n hh)
  have ht := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 5/4)).comp edgeLength_tendsto
  simpa only [mul_zero,neg_div,Function.comp_def] using ht.const_mul (formConstant*(h+1))

lemma edgeLength_tents_eventually : ∀ᶠ n : ℕ in atTop, 12*edgeLength n ≤ n := by
  have ht := edgeLength_sq_div_tendsto.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/24))
  filter_upwards [ht,eventually_ge_atTop 1] with n hn hn1
  have hD1 : (1:ℝ) ≤ edgeLength n := by exact_mod_cast edgeLength_pos n
  have hN : (0:ℝ) < n+1 := by positivity
  have h' := (div_lt_iff₀ hN).mp hn
  have hn1' : (1:ℝ) ≤ n := by exact_mod_cast hn1
  have hr : (12:ℝ)*edgeLength n ≤ n := by nlinarith
  exact_mod_cast hr

lemma orderedJacobiGaps_natural_top {n : ℕ} (hfit : 12*edgeLength n ≤ n)
    (i : Fin (n+1)) (hi : i.val < 3) :
    orderedJacobiGaps n i ≤ 212/(edgeLength n:ℝ)^2 := by
  have hD := edgeLength_cast_pos n
  have hD1 : (1:ℝ) ≤ edgeLength n := by exact_mod_cast edgeLength_pos n
  have hN : (0:ℝ) < n+1 := by positivity
  apply (orderedJacobiGaps_top_bound (edgeLength_pos n) hfit i hi).trans
  have hcube := (edgeLength_cube n).2
  have hmain : 2*(12*(edgeLength n:ℝ)+1)*(edgeLength n:ℝ)^2 ≤ 208*(n+1) := by
    nlinarith [mul_nonneg (sq_nonneg (edgeLength n:ℝ)) (sub_nonneg.mpr hD1)]
  apply (le_div_iff₀ (sq_pos_of_pos hD)).mpr
  have hx := (div_le_iff₀ hN).mpr hmain
  calc
    _ = 4+2*(12*(edgeLength n:ℝ)+1)*(edgeLength n:ℝ)^2/(n+1) := by field_simp
    _ ≤ _ := by linarith



lemma orderedJacobiGaps_le_four (n : ℕ) (i : Fin (n+1)) : orderedJacobiGaps n i ≤ 4 := by
  let h := pathOperator_symmetric n
  let x := h.eigenvectorBasis (by simp) i
  have hx : ‖x‖=1 := (h.eigenvectorBasis (by simp)).norm_eq_one i
  have hh := pathEnergy_le_four_mass n (extendPath n x)
  rw [extendPath_mass,hx] at hh
  have he := pathOperator_energy n x
  have heig : inner ℝ x (pathOperator n x) = h.eigenvalues (by simp) i := by
    dsimp only [x]
    rw [h.apply_eigenvectorBasis,inner_smul_right,real_inner_self_eq_norm_sq]
    simp only [(h.eigenvectorBasis (by simp)).norm_eq_one i,one_pow,mul_one,RCLike.ofReal_real_eq_id,id_eq]
  rw [heig,hx] at he
  unfold orderedJacobiGaps
  linarith

lemma spectralGood_resolvent (n : ℕ) {lam : Fin (n+1) → ℝ} {h s₀ s : ℝ}
    (hh : 0 ≤ h) (hs₀ : 0 < s₀) (hs : s₀ ≤ s)
    (hsmall : formA n h*s₀^(-5/8:ℝ)+formB n/s₀+formC n ≤ 1/2)
    (hspace : 2 ≤ (n+1:ℝ)*s₀*Real.sqrt s₀)
    (hlam : lam ∈ spectralGood n h s₀) :
    (∀ i, 0 < 2+s-lam i) ∧
    (∑ i, (2+s-lam i)⁻¹^2)/(n+1) ≤ 16/Real.sqrt s ∧
    |(∑ i, (2+s-lam i)⁻¹)/(n+1)-semicircleResolvent s| ≤
      416*formA n h*s^(-1/8:ℝ)+8*formB n/Real.sqrt s+2*formC n+2/((n+1:ℝ)*s) := by
  have hn : (0:ℝ) < n+1 := by positivity
  have hspos : 0 < s := hs₀.trans_le hs
  have hA := formA_nonneg n hh
  have hB := formB_nonneg n
  have hC := formC_nonneg n
  have hsc (t : ℝ) (hst : s ≤ t) : 2 ≤ (n+1:ℝ)*t*Real.sqrt t := by
    have htpos : 0 < t := hspos.trans_le hst
    exact hspace.trans (mul_le_mul (mul_le_mul_of_nonneg_left (hs.trans hst) hn.le)
      (Real.sqrt_le_sqrt (hs.trans hst)) (Real.sqrt_nonneg _) (by positivity))
  have hc := resolvent_trace_transfer (orderedJacobiGaps n) (lam)
    (orderedJacobiGaps_nonneg n) hA hB hC hs₀ hs
    hlam hsmall
    (fun t hst => (orderedJacobi_trace n (hspos.trans_le hst) (hsc t hst)).1)
  have hd := orderedJacobi_trace n hspos (hsc s le_rfl)
  refine ⟨hc.1,?_,?_⟩
  · apply (div_le_iff₀ hn).mpr
    convert hc.2.1 using 1
    all_goals first | rfl | ring
  · have hdif : |(∑ i, (2+s-lam i)⁻¹)/(n+1)-
        (∑ i, (s+orderedJacobiGaps n i)⁻¹)/(n+1)| ≤
        416*formA n h*s^(-1/8:ℝ)+8*formB n/Real.sqrt s+2*formC n := by
      rw [← sub_div,abs_div,abs_of_pos hn]
      apply (div_le_iff₀ hn).mpr
      calc
        _ ≤ _ := hc.2.2
        _ ≤ 104*formA n h*(4*(n+1))*s^(-1/8:ℝ)+2*formB n*(4*(n+1)/Real.sqrt s)+2*formC n*(n+1) := by gcongr; exact hd.2.2
        _ = _ := by ring
    exact (abs_sub_le _ _ _).trans (add_le_add hdif hd.2.1)

def traceCost (n : ℕ) (h s : ℝ) : ℝ :=
  416*formA n h*s^(-5/8:ℝ)+8*formB n/s+2*formC n/Real.sqrt s+
    2/((n+1:ℝ)*s*Real.sqrt s)

lemma traceCost_nonneg (n : ℕ) {h s : ℝ} (hh : 0 ≤ h) (hs : 0 < s) : 0 ≤ traceCost n h s := by
  have := formA_nonneg n hh
  have := formB_nonneg n
  have := formC_nonneg n
  unfold traceCost; positivity

lemma traceCost_antitone (n : ℕ) {h s t : ℝ} (hh : 0 ≤ h) (hs : 0 < s) (hst : s ≤ t) :
    traceCost n h t ≤ traceCost n h s := by
  have ht : 0 < t := hs.trans_le hst
  have hA := formA_nonneg n hh
  have hB := formB_nonneg n
  have hC := formC_nonneg n
  have hr := Real.sqrt_le_sqrt hst
  have hsp := Real.sqrt_pos.mpr hs
  unfold traceCost
  apply add_le_add
  · apply add_le_add
    · apply add_le_add
      · exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hs hst (by norm_num)) (by positivity)
      · exact div_le_div_of_nonneg_left (by positivity) hs hst
    · exact div_le_div_of_nonneg_left (by positivity) hsp hr
  · apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hst (by positivity)) hr hsp.le (by positivity)

lemma traceError_eq_cost (n : ℕ) (h : ℝ) {s : ℝ} (hs : 0 < s) :
    416*formA n h*s^(-1/8:ℝ)+8*formB n/Real.sqrt s+2*formC n+2/((n+1:ℝ)*s) =
      traceCost n h s * Real.sqrt s := by
  have hp : s^(-1/8:ℝ) = s^(-5/8:ℝ)*Real.sqrt s := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_add hs]
    norm_num
  have hsqrt := Real.sqrt_pos.mpr hs
  have hN : (0:ℝ) < n+1 := by positivity
  rw [hp,traceCost]
  field_simp
  linear_combination -(8*formB n*(n+1))*(Real.sq_sqrt hs.le)

lemma spectralGood_relative_trace (n : ℕ) {lam : Fin (n+1) → ℝ} {h s₀ s η : ℝ}
    (hh : 0 ≤ h) (hs₀ : 0 < s₀) (hs : s₀ ≤ s)
    (hsmall : formA n h*s₀^(-5/8:ℝ)+formB n/s₀+formC n ≤ 1/2)
    (hspace : 2 ≤ (n+1:ℝ)*s₀*Real.sqrt s₀)
    (hlam : lam ∈ spectralGood n h s₀) (hcost : traceCost n h s₀ ≤ η) :
    |(∑ i, (2+s-lam i)⁻¹)/(n+1)-semicircleResolvent s| ≤ η*Real.sqrt s := by
  have ht := spectralGood_resolvent n hh hs₀ hs hsmall hspace hlam
  apply ht.2.2.trans
  rw [traceError_eq_cost n h (hs₀.trans_le hs)]
  exact mul_le_mul_of_nonneg_right ((traceCost_antitone n hh hs₀ hs).trans hcost) (Real.sqrt_nonneg _)

lemma traceCost_small (n : ℕ) {h s η : ℝ} (hh : 0 ≤ h) (hs : 0 < s) (hs1 : s ≤ 1)
    (hcost : traceCost n h s ≤ η) :
    formA n h*s^(-5/8:ℝ)+formB n/s+formC n ≤ η := by
  have hA := formA_nonneg n hh
  have hB := formB_nonneg n
  have hC := formC_nonneg n
  have hp : 0 ≤ formA n h*s^(-5/8:ℝ) := by positivity
  have hq : 0 ≤ formB n/s := by positivity
  have hroot : Real.sqrt s ≤ 1 := by simpa using Real.sqrt_le_sqrt hs1
  have hcle : formC n ≤ 2*formC n/Real.sqrt s := by
    rw [le_div_iff₀ (Real.sqrt_pos.mpr hs)]
    nlinarith [mul_le_mul_of_nonneg_left hroot hC]
  have htail : 0 ≤ 2/((n+1:ℝ)*s*Real.sqrt s) := by positivity
  unfold traceCost at hcost
  have h8 : 8*formB n/s = 8*(formB n/s) := by ring
  rw [h8] at hcost
  nlinarith

open scoped Topology

def edgeFixedCost (h L : ℝ) : ℝ :=
  416*formConstant*(h+1)*L^(-5/8:ℝ)+16/(L*Real.sqrt L)

lemma edgeFixedCost_tendsto (h : ℝ) : Tendsto (edgeFixedCost h) atTop (𝓝 0) := by
  have hA := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 5/8)).const_mul
    (416*formConstant*(h+1))
  have hB := (tendsto_id.atTop_mul_atTop₀ Real.tendsto_sqrt_atTop).const_div_atTop (16:ℝ)
  have ht : Tendsto (fun L => edgeFixedCost h L) atTop (𝓝 0) := by
    simpa only [edgeFixedCost,neg_div,mul_zero,zero_add,id_eq] using hA.add hB
  exact ht

lemma traceCost_natural_le (n : ℕ) {h L : ℝ} (hh : 0 ≤ h) (hL : 0 < L) :
    traceCost n h (naturalEdgeScale n L) ≤ edgeFixedCost h L+
      8*(formB n/naturalEdgeScale n L)+2*(formC n/Real.sqrt (naturalEdgeScale n L)) := by
  have hspace := (naturalEdgeScale_space n hL).1
  have hbot : 0 < L*Real.sqrt L/8 := by positivity
  have htail := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 2) hbot hspace
  have hA := mul_le_mul_of_nonneg_left (formA_natural_scale n hh hL) (by norm_num : (0:ℝ) ≤ 416)
  rw [show 2/(L*Real.sqrt L/8) = 16/(L*Real.sqrt L) by ring] at htail
  unfold traceCost edgeFixedCost
  ring_nf at hA htail ⊢
  linarith

lemma traceCost_natural_eventually {h L η : ℝ} (hh : 0 ≤ h) (hL : 0 < L)
    (hcost : edgeFixedCost h L < η) :
    ∀ᶠ n : ℕ in atTop, traceCost n h (naturalEdgeScale n L) ≤ η := by
  have ht := ((formB_natural_scale_tendsto L).const_mul 8).add
    ((formC_natural_scale_tendsto hL).const_mul 2)
  have ht' : Tendsto (fun n => 8*(formB n/naturalEdgeScale n L)+
      2*(formC n/Real.sqrt (naturalEdgeScale n L))) atTop (𝓝 0) := by simpa using ht
  filter_upwards [ht'.eventually (gt_mem_nhds (sub_pos.mpr hcost))] with n hn
  linarith [traceCost_natural_le n hh hL]

lemma exists_natural_edge_parameters {h η B : ℝ} (hh : 0 ≤ h) (hη : 0 < η) :
    ∃ L : ℝ, max 1696 B ≤ L ∧ 0 < L ∧
      (∀ᶠ n : ℕ in atTop, traceCost n h (naturalEdgeScale n L) ≤ η) := by
  obtain ⟨L,hL,hcost⟩ := ((eventually_ge_atTop (max 1696 B)).and
    ((edgeFixedCost_tendsto h).eventually (gt_mem_nhds hη))).exists
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1696) ((le_max_left _ _).trans hL)
  exact ⟨L,hL,hLp,traceCost_natural_eventually hh hLp hcost⟩

lemma spectralGood_relative_error (n : ℕ) {lam : Fin (n+1) → ℝ} {h s η : ℝ}
    (hh : 0 ≤ h) (hs : 0 < s) (hs1 : s ≤ 1) (hcost : traceCost n h s ≤ η)
    (hlam : lam ∈ spectralGood n h s) (i : Fin (n+1)) :
    |lam i-(2-orderedJacobiGaps n i)| ≤ η*(s+orderedJacobiGaps n i) := by
  have he := edgeError_relative (formA_nonneg n hh) (formB_nonneg n) (formC_nonneg n)
    hs le_rfl (orderedJacobiGaps_nonneg n i)
  exact (hlam i).trans (he.trans (mul_le_mul_of_nonneg_right (traceCost_small n hh hs hs1 hcost)
    (by linarith [orderedJacobiGaps_nonneg n i])))

lemma spectralGood_bounded (n : ℕ) {lam : Fin (n+1) → ℝ} {h s η : ℝ}
    (hh : 0 ≤ h) (hs : 0 < s) (hs1 : s ≤ 1) (hη : η ≤ 1/5)
    (hcost : traceCost n h s ≤ η) (hlam : lam ∈ spectralGood n h s) :
    ∀ i, |lam i| ≤ 3 := by
  have hη0 := (traceCost_nonneg n hh hs).trans hcost
  intro i
  have he := spectralGood_relative_error n hh hs hs1 hcost hlam i
  have h0 := orderedJacobiGaps_nonneg n i
  have h4 := orderedJacobiGaps_le_four n i
  have hE : η*(s+orderedJacobiGaps n i) ≤ 1 := by nlinarith
  have h := abs_le.mp (he.trans hE)
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma spectralGood_top_upper (n : ℕ) {lam : Fin (n+1) → ℝ} {h s η : ℝ}
    (hh : 0 ≤ h) (hs : 0 < s) (hs1 : s ≤ 1) (hη : η ≤ 1)
    (hcost : traceCost n h s ≤ η) (hlam : lam ∈ spectralGood n h s) :
    ∀ i, lam i ≤ 2+η*s := by
  intro i
  have he := (abs_le.mp (spectralGood_relative_error n hh hs hs1 hcost hlam i)).2
  nlinarith [orderedJacobiGaps_nonneg n i]

lemma spectralGood_top_close {n : ℕ} {lam : Fin (n+1) → ℝ} {h L : ℝ}
    (hh : 0 ≤ h) (hL : 1696 ≤ L) (hs1 : naturalEdgeScale n L ≤ 1)
    (hfit : 12*edgeLength n ≤ n) (hcost : traceCost n h (naturalEdgeScale n L) ≤ 1/100)
    (hlam : lam ∈ spectralGood n h (naturalEdgeScale n L))
    (i : Fin (n+1)) (hi : i.val < 3) :
    |lam i-2| ≤ naturalEdgeScale n L/4 := by
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hs := naturalEdgeScale_pos n hLp
  have hg : orderedJacobiGaps n i ≤ naturalEdgeScale n L/8 := by
    apply (orderedJacobiGaps_natural_top hfit i hi).trans
    calc
      _ ≤ (L/8)/(edgeLength n:ℝ)^2 :=
        div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)
      _ = _ := by unfold naturalEdgeScale; ring
  have he := abs_le.mp (spectralGood_relative_error n hh hs hs1 hcost hlam i)
  have hg0 := orderedJacobiGaps_nonneg n i
  exact abs_le.mpr ⟨by linarith,by linarith⟩


lemma finite_cover_sum {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    (J : Finset κ) (S : κ → Finset ι) (f : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) (hc : ∀ i, ∃ j ∈ J, i ∈ S j) :
    (∑ i, f i) ≤ ∑ j ∈ J, ∑ i ∈ S j, f i := by
  calc
    _ ≤ ∑ i, ∑ j ∈ J, if i ∈ S j then f i else 0 := by
      apply Finset.sum_le_sum
      intro i _
      obtain ⟨j, hj, hij⟩ := hc i
      calc
        f i = (if i ∈ S j then f i else 0) := by rw [ite_eq_left hij]
        _ ≤ _ := Finset.single_le_sum (f := fun k => if i ∈ S k then f i else 0)
          (fun k _ => by split_ifs <;> simp [hf]) hj
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      simp only [← Finset.sum_filter]
      congr
      ext; simp

lemma dyadic_real_cover {x s : ℝ} (_hx : 0 ≤ x) (hs : 0 < s) :
    x ≤ s ∨ ∃ j : ℕ, (2 : ℝ)^j * s ≤ x ∧ x ≤ (2 : ℝ)^(j + 1) * s := by
  by_cases hxs : x ≤ s
  · exact Or.inl hxs
  right
  have hratio : 1 ≤ x / s := (le_div_iff₀ hs).mpr (by linarith)
  obtain ⟨j, hj, hj'⟩ := exists_nat_pow_near hratio (by norm_num : (1 : ℝ) < 2)
  exact ⟨j, (le_div_iff₀ hs).mp hj, (div_le_iff₀ hs).mp hj'.le⟩

lemma rpow_dyadic_shell {s : ℝ} (hs : 0 < s) (j : ℕ) :
    ((2 : ℝ)^(j + 1) * s) ^ (3 / 2 : ℝ) *
      ((2 : ℝ)^j * s) ^ (-13 / 8 : ℝ) =
    (2 : ℝ) ^ (3 / 2 : ℝ) * s ^ (-1 / 8 : ℝ) *
      ((2 : ℝ) ^ (-1 / 8 : ℝ)) ^ j := by
  rw [Real.mul_rpow (by positivity) hs.le, Real.mul_rpow (by positivity) hs.le,
    ← Real.rpow_pow_comm (by norm_num), ← Real.rpow_pow_comm (by norm_num), pow_succ]
  calc
    _ = (2 : ℝ) ^ (3 / 2 : ℝ) * (s ^ (3 / 2 : ℝ) * s ^ (-13 / 8 : ℝ)) *
        (((2 : ℝ) ^ (3 / 2 : ℝ)) ^ j * ((2 : ℝ) ^ (-13 / 8 : ℝ)) ^ j) := by ring
    _ = _ := by
      rw [← Real.rpow_add hs, ← mul_pow, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      norm_num

lemma fractional_resolvent_counting {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι → ℝ) (he : ∀ i, 0 ≤ e i) {s C : ℝ} (hs : 0 < s) (hC : 0 ≤ C)
    (hc : ∀ t, s ≤ t → ((Finset.univ.filter fun i => e i ≤ t).card : ℝ) ≤
      C * t ^ (3 / 2 : ℝ)) :
    (∑ i, (s + e i) ^ (-13 / 8 : ℝ)) ≤
      C * (1 + (2 : ℝ) ^ (3 / 2 : ℝ) / (1 - (2 : ℝ) ^ (-1 / 8 : ℝ))) *
        s ^ (-1 / 8 : ℝ) := by
  let rho : ℝ := (2 : ℝ) ^ (-1 / 8 : ℝ)
  have hrho0 : 0 ≤ rho := by dsimp [rho]; positivity
  have hrho : rho < 1 := by
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  let small : Finset ι := Finset.univ.filter fun i => e i ≤ s
  let shell (j : ℕ) : Finset ι :=
    Finset.univ.filter fun i => (2 : ℝ)^j * s ≤ e i ∧ e i ≤ (2 : ℝ)^(j + 1) * s
  have hcover : ∀ i, ∃ j : ℕ, i ∈ (if j = 0 then small else shell (j - 1)) := by
    intro i
    rcases dyadic_real_cover (he i) hs with hi | ⟨j, hj, hj'⟩
    · exact ⟨0, by simp [small, hi]⟩
    · exact ⟨j + 1, by simp [shell, hj, hj']⟩
  choose j hj using hcover
  let J : Finset ℕ := Finset.univ.image j
  have hsum0 : (∑ i ∈ small, (s + e i) ^ (-13 / 8 : ℝ)) ≤ C * s ^ (-1 / 8 : ℝ) := by
    calc
      _ ≤ ∑ _i ∈ small, s ^ (-13 / 8 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        exact Real.rpow_le_rpow_of_nonpos hs (le_add_of_nonneg_right (he i)) (by norm_num)
      _ = (small.card : ℝ) * s ^ (-13 / 8 : ℝ) := by simp
      _ ≤ (C * s ^ (3 / 2 : ℝ)) * s ^ (-13 / 8 : ℝ) :=
        mul_le_mul_of_nonneg_right (hc s le_rfl) (by positivity)
      _ = _ := by rw [mul_assoc, ← Real.rpow_add hs]; norm_num
  have hshell (k : ℕ) : (∑ i ∈ shell k, (s + e i) ^ (-13 / 8 : ℝ)) ≤
      C * (2 : ℝ) ^ (3 / 2 : ℝ) * s ^ (-1 / 8 : ℝ) * rho ^ k := by
    have ht : s ≤ (2 : ℝ)^(k + 1) * s := by
      have : (1 : ℝ) ≤ 2^(k + 1) := one_le_pow₀ (by norm_num)
      nlinarith
    have hcard : (shell k).card ≤ (Finset.univ.filter fun i => e i ≤ (2 : ℝ)^(k + 1) * s).card :=
      Finset.card_le_card (by intro i hi; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2.2⟩)
    calc
      _ ≤ ∑ _i ∈ shell k, ((2 : ℝ)^k * s) ^ (-13 / 8 : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by norm_num)
        have := (Finset.mem_filter.mp hi).2.1
        linarith
      _ = ((shell k).card : ℝ) * ((2 : ℝ)^k * s) ^ (-13 / 8 : ℝ) := by simp
      _ ≤ (C * ((2 : ℝ)^(k + 1) * s) ^ (3 / 2 : ℝ)) *
          ((2 : ℝ)^k * s) ^ (-13 / 8 : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have hcardR : ((shell k).card : ℝ) ≤
          ((Finset.univ.filter fun i => e i ≤ (2 : ℝ)^(k + 1) * s).card : ℝ) := by
          exact_mod_cast hcard
        exact hcardR.trans (hc _ ht)
      _ = _ := by rw [mul_assoc, rpow_dyadic_shell hs k]; dsimp [rho]; ring
  have hcover' : ∀ i, ∃ k ∈ J, i ∈ (if k = 0 then small else shell (k - 1)) :=
    fun i => ⟨j i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, hj i⟩
  have hbound := finite_cover_sum J (fun k => if k = 0 then small else shell (k - 1))
    (fun i => (s + e i) ^ (-13 / 8 : ℝ)) (fun i => Real.rpow_nonneg (by linarith [he i]) _) hcover'
  have hterm (k : ℕ) : (∑ i ∈ (if k = 0 then small else shell (k - 1)),
      (s + e i) ^ (-13 / 8 : ℝ)) ≤
      (if k = 0 then C * s ^ (-1 / 8 : ℝ) else
        C * (2 : ℝ) ^ (3 / 2 : ℝ) * s ^ (-1 / 8 : ℝ) * rho ^ (k - 1)) := by
    split_ifs
    · exact hsum0
    · exact hshell _
  let f (k : ℕ) : ℝ := if k = 0 then C * s ^ (-1 / 8 : ℝ) else
    C * (2 : ℝ) ^ (3 / 2 : ℝ) * s ^ (-1 / 8 : ℝ) * rho ^ (k - 1)
  have hf0 : ∀ k, 0 ≤ f k := by intro k; dsimp [f]; split_ifs <;> positivity
  have hfsucc : (fun k => f (k + 1)) = (fun k => C * (2 : ℝ) ^ (3 / 2 : ℝ) *
      s ^ (-1 / 8 : ℝ) * rho ^ k) := by funext k; simp [f]
  have hgeom : Summable (fun k : ℕ => rho ^ k) := summable_geometric_of_lt_one hrho0 hrho
  have hfsum : Summable f := by
    rw [← summable_nat_add_iff 1]
    rw [hfsucc]
    exact hgeom.mul_left _
  have htotal : (∑' k, f k) = C * s ^ (-1 / 8 : ℝ) +
      C * (2 : ℝ) ^ (3 / 2 : ℝ) * s ^ (-1 / 8 : ℝ) / (1 - rho) := by
    rw [hfsum.tsum_eq_zero_add, hfsucc, tsum_mul_left,
      tsum_geometric_of_lt_one hrho0 hrho]
    simp only [f, ite_eq_left rfl]
    ring
  calc
    _ ≤ ∑ k ∈ J, f k := hbound.trans (Finset.sum_le_sum (fun k _ => hterm k))
    _ ≤ ∑' k, f k := hfsum.sum_le_tsum J (fun k _ => hf0 k)
    _ = _ := by rw [htotal]; dsimp [rho]; ring

lemma rpow_three_halves {s : ℝ} (hs : 0 < s) :
    s ^ (3 / 2 : ℝ) = s * Real.sqrt s := by
  rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
    Real.rpow_add hs, Real.rpow_one]

lemma jacobi_fractional_resolvent {n : ℕ} (hn : 0 < n) {s : ℝ} (hs : 0 < s)
    (hscale : 2 ≤ (n : ℝ) * s * Real.sqrt s) :
    (n : ℝ)⁻¹ * (∑ i, (s + jacobiGaps n i) ^ (-13 / 8 : ℝ)) ≤
      16 * (1 + (2 : ℝ) ^ (3 / 2 : ℝ) / (1 - (2 : ℝ) ^ (-1 / 8 : ℝ))) *
        s ^ (-1 / 8 : ℝ) := by
  have h := fractional_resolvent_counting (jacobiGaps n) (jacobiGaps_nonneg n)
    hs (C := 16 * n) (by positivity) ?_
  · have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have h' := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (Nat.cast_nonneg n))
    convert! h' using 1
    field_simp
  · intro t ht
    have ht0 : 0 < t := hs.trans_le ht
    have hst : (n : ℝ) * s * Real.sqrt s ≤ n * t * Real.sqrt t := by gcongr
    simpa only [rpow_three_halves ht0, mul_assoc] using
      jacobi_gap_counting hn ht0 (hscale.trans hst)

lemma semicircleResolvent_deficit_lower {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    Real.sqrt s/2 ≤ 1-semicircleResolvent s := by
  have hsroot : s ≤ Real.sqrt s := by
    nlinarith [Real.sq_sqrt hs,Real.sqrt_nonneg s,Real.sqrt_le_sqrt hs1]
  have hc := semicircle_discriminant_lower hs
  unfold semicircleResolvent
  linarith

lemma sum_pair_tail_real {n : ℕ} (v : Fin (n+2) → ℝ) :
    (∑ i, v i) = v 0+v 1+∑ i : Fin n, v i.succ.succ := by
  rw [Fin.sum_univ_succ,Fin.sum_univ_succ]
  simp only [Fin.succ_zero_eq_one]
  ring

def fixedEdgeVariance {ι : Type*} (lam : ι → ℝ) (s : ℝ) (i : ι) : NNReal :=
  ⟨max 0 ((2+s-lam i)⁻¹),le_max_left _ _⟩

lemma fixedEdgeVariance_coe {ι : Type*} {lam : ι → ℝ} {s : ℝ}
    (hgap : ∀ i, 0 < 2+s-lam i) (i : ι) :
    (fixedEdgeVariance lam s i:ℝ) = (2+s-lam i)⁻¹ :=
  max_eq_right (inv_nonneg.mpr (hgap i).le)

lemma fixedEdgeVariance_pos {ι : Type*} {lam : ι → ℝ} {s : ℝ}
    (hgap : ∀ i, 0 < 2+s-lam i) (i : ι) : fixedEdgeVariance lam s i ≠ 0 := by
  rw [← NNReal.coe_ne_zero,fixedEdgeVariance_coe hgap]
  exact inv_ne_zero (hgap i).ne'

lemma fixedEdgeVariance_inverse {ι : Type*} {lam : ι → ℝ} {s : ℝ}
    (hgap : ∀ i, 0 < 2+s-lam i) (i : ι) :
    (fixedEdgeVariance lam s i:ℝ)⁻¹ = 2+s-lam i := by
  rw [fixedEdgeVariance_coe hgap,inv_inv]

lemma bulk_fixedTilt_bounds {n : ℕ} (v : Fin (n+2) → ℝ) {s : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hv : ∀ i, 0 ≤ v i)
    (htrace : |(∑ i, v i)/(n+2)-semicircleResolvent s| ≤ (1/100)*Real.sqrt s)
    (hsq : (∑ i, v i^2) ≤ 16*(n+2)/Real.sqrt s)
    (hmax : ∀ i, v i ≤ 2/s)
    (hspace : 32768 ≤ (n+2:ℝ)*s*Real.sqrt s) :
    let d : ℝ := (n+2)-(∑ i : Fin n, v i.succ.succ)
    (n+2:ℝ)*Real.sqrt s/4 ≤ d ∧ d ≤ 3*(n+2:ℝ)*Real.sqrt s ∧
      128*(∑ i : Fin n, (v i.succ.succ)^2) ≤ d^2 := by
  have hN : (0:ℝ) < n+2 := by positivity
  have hr : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have ht := abs_le.mp htrace
  have hlowR := semicircleResolvent_deficit_lower hs.le hs1
  have huppR := semicircleResolvent_deficit hs.le
  have hfull_upper : (∑ i, v i) ≤ (n+2)-(n+2)*Real.sqrt s/4 := by
    have hh : (∑ i, v i)/(n+2) ≤ 1-Real.sqrt s/4 := by linarith
    have hm := (div_le_iff₀ hN).mp hh
    nlinarith
  have hfull_lower : (n+2)-(∑ i, v i) ≤ 2*(n+2)*Real.sqrt s := by
    have hh : 1-2*Real.sqrt s ≤ (∑ i, v i)/(n+2) := by linarith
    have hm := (le_div_iff₀ hN).mp hh
    nlinarith
  have hpair_le : v 0+v 1 ≤ (n+2)*Real.sqrt s := by
    have hh : 4/s ≤ (n+2)*Real.sqrt s := by
      rw [div_le_iff₀ hs]
      nlinarith
    have h0 := hmax 0
    have h1 := hmax 1
    ring_nf at h0 h1 hh ⊢
    linarith
  have hsplit := sum_pair_tail_real v
  dsimp only
  have hd : (n+2:ℝ)*Real.sqrt s/4 ≤ (n+2)-(∑ i : Fin n, v i.succ.succ) := by
    linarith [hv 0,hv 1]
  refine ⟨hd,by linarith,?_⟩
  have htail : (∑ i : Fin n, (v i.succ.succ)^2) ≤ (∑ i, v i^2) := by
    rw [sum_pair_tail_real (fun i => v i^2)]
    linarith [sq_nonneg (v 0),sq_nonneg (v 1)]
  have hid : ((n+2:ℝ)*Real.sqrt s/4)^2*Real.sqrt s =
      ((n+2:ℝ)/16)*((n+2:ℝ)*s*Real.sqrt s) := by
    rw [div_pow,mul_pow,Real.sq_sqrt hs.le]
    ring
  have hmid : 2048*(n+2:ℝ)/Real.sqrt s ≤ ((n+2:ℝ)*Real.sqrt s/4)^2 := by
    rw [div_le_iff₀ hr,hid]
    have hh := mul_le_mul_of_nonneg_left hspace (div_nonneg hN.le (by norm_num : (0:ℝ) ≤ 16))
    linarith
  calc
    _ ≤ 128*(16*(n+2:ℝ)/Real.sqrt s) := mul_le_mul_of_nonneg_left (htail.trans hsq) (by norm_num)
    _ = 2048*(n+2:ℝ)/Real.sqrt s := by ring
    _ ≤ ((n+2:ℝ)*Real.sqrt s/4)^2 := hmid
    _ ≤ _ := pow_le_pow_left₀ (by positivity) hd 2

lemma fixedEdgeVariance_upper {ι : Type*} {lam : ι → ℝ} {s : ℝ} (hs : 0 < s)
    (hgap : ∀ i, s/2 ≤ 2+s-lam i) (i : ι) :
    (fixedEdgeVariance lam s i:ℝ) ≤ 2/s := by
  have hp (j : ι) : 0 < 2+s-lam j := lt_of_lt_of_le (by positivity) (hgap j)
  rw [fixedEdgeVariance_coe hp]
  have hh := (inv_le_inv₀ (hp i) (by positivity : (0:ℝ) < s/2)).2 (hgap i)
  simpa only [inv_div,inv_one,one_div] using hh

lemma fixedEdgeVariance_lower {ι : Type*} {lam : ι → ℝ} {s : ℝ} (hs : 0 < s)
    (hgap : ∀ i, 0 < 2+s-lam i) (i : ι) (hi : |lam i-2| ≤ s/4) :
    1/(2*s) ≤ (fixedEdgeVariance lam s i:ℝ) := by
  rw [fixedEdgeVariance_coe hgap,one_div]
  exact (inv_le_inv₀ (by positivity : (0:ℝ) < 2*s) (hgap i)).2 (by
    have hh := (abs_le.mp hi).1; linarith)

lemma spectralGood_fixed_variance {n : ℕ} {lam : Fin (n+2) → ℝ} {h s : ℝ}
    (hh : 0 ≤ h) (hs : 0 < s) (hs1 : s ≤ 1)
    (hcost : traceCost (n+1) h s ≤ 1/100) (hlam : lam ∈ spectralGood (n+1) h s)
    (hspace : 32768 ≤ (n+2:ℝ)*s*Real.sqrt s) :
    (∀ i, 0 < 2+s-lam i) ∧
    (∀ i, (fixedEdgeVariance lam s i:ℝ) ≤ 2/s) ∧
    |(∑ i, (fixedEdgeVariance lam s i:ℝ))/(n+2)-semicircleResolvent s| ≤ (1/100)*Real.sqrt s ∧
    (∑ i, (fixedEdgeVariance lam s i:ℝ)^2) ≤ 16*(n+2)/Real.sqrt s := by
  have hup := spectralGood_top_upper (n+1) hh hs hs1 (by norm_num : (1/100:ℝ) ≤ 1) hcost hlam
  have hgap (i) : s/2 ≤ 2+s-lam i := by linarith [hup i]
  have hpos (i) : 0 < 2+s-lam i := lt_of_lt_of_le (by positivity) (hgap i)
  have hsmall : formA (n+1) h*s^(-5/8:ℝ)+formB (n+1)/s+formC (n+1) ≤ 1/2 :=
    (traceCost_small (n+1) hh hs hs1 hcost).trans (by norm_num)
  have hspace' : 2 ≤ (n+1+1:ℝ)*s*Real.sqrt s := by linarith
  have hN : (0:ℝ) < n+2 := by positivity
  have ht := spectralGood_relative_trace (n+1) hh hs le_rfl hsmall
    (by simpa only [Nat.cast_add,Nat.cast_one] using hspace') hlam hcost
  have hq := (spectralGood_resolvent (n+1) hh hs le_rfl hsmall
    (by simpa only [Nat.cast_add,Nat.cast_one] using hspace') hlam).2.1
  simp only [Nat.cast_add,Nat.cast_one,show (n:ℝ)+1+1=n+2 by ring] at ht hq
  refine ⟨hpos,fixedEdgeVariance_upper hs hgap,?_,?_⟩
  · simpa only [fixedEdgeVariance_coe hpos] using ht
  · simp only [fixedEdgeVariance_coe hpos]
    have he := (div_le_iff₀ hN).mp hq
    convert he using 1; first | rfl | ring

lemma spectralGood_fixed_bulk {n : ℕ} {lam : Fin (n+2) → ℝ} {h s : ℝ}
    (hh : 0 ≤ h) (hs : 0 < s) (hs1 : s ≤ 1)
    (hcost : traceCost (n+1) h s ≤ 1/100) (hlam : lam ∈ spectralGood (n+1) h s)
    (hspace : 32768 ≤ (n+2:ℝ)*s*Real.sqrt s) :
    let d : ℝ := (n+2)-(∑ i : Fin n, (fixedEdgeVariance lam s i.succ.succ:ℝ))
    (n+2:ℝ)*Real.sqrt s/4 ≤ d ∧ d ≤ 3*(n+2:ℝ)*Real.sqrt s ∧
      128*(∑ i : Fin n, (fixedEdgeVariance lam s i.succ.succ:ℝ)^2) ≤ d^2 := by
  have hi := spectralGood_fixed_variance hh hs hs1 hcost hlam hspace
  exact bulk_fixedTilt_bounds (fun i => (fixedEdgeVariance lam s i:ℝ)) hs hs1
    (fun i => NNReal.coe_nonneg _) hi.2.2.1 hi.2.2.2 hi.2.1 hspace

end CriticalSK

end

end OAI
