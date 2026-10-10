import Mathlib
import OAI.Probability.BinarySweep.GridBounds.GridDenseCost

namespace OAI

noncomputable section

section

open Filter Asymptotics
open scoped Topology

namespace BinaryCoordinateSweeps

lemma hook_polynomial_error_eventually (q : ℕ) : ∀ᶠ s : ℝ in atTop,
    ∀ u v p c : ℝ, 1≤u → 1≤v → 0≤p → p≤ s^(1/100:ℝ) →
      u≤ s^(4/5:ℝ) → v≤ s^(4/5:ℝ) → 0≤c → c≤2 →
      (1+4*c+2*(q:ℝ))*(2*p)^2*(v*Real.log (u+1)+u*Real.log (v+1)) ≤
        s^(9/10:ℝ) := by
  let C : ℝ := 16*(9+2*(q:ℝ))
  have hC : 0<C := by dsimp [C]; positivity
  have ho := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<2/25)).bound (inv_pos.mpr hC)
  filter_upwards [ho,eventually_ge_atTop (2:ℝ)] with s hs hs2
  have hs1 : 1≤ s := by linarith
  have hs0 : 0<s := by linarith
  have hl : 0≤Real.log s := Real.log_nonneg hs1
  have hlog : Real.log s ≤ C⁻¹*s^(2/25:ℝ) := by
    simpa only [Real.norm_of_nonneg hl,Real.norm_of_nonneg (Real.rpow_nonneg hs0.le _)] using hs
  intro u v p c hu hv hp hps hus hvs hc hc2
  have hu0 : 0<u := by linarith
  have hv0 : 0<v := by linarith
  have hup : u≤ s := hus.trans (by simpa using Real.rpow_le_rpow_of_exponent_le hs1 (show (4/5:ℝ)≤1 by norm_num))
  have hvp : v≤ s := hvs.trans (by simpa using Real.rpow_le_rpow_of_exponent_le hs1 (show (4/5:ℝ)≤1 by norm_num))
  have logle (w : ℝ) (hw : 1≤w) (hws : w≤ s) : Real.log (w+1)≤2*Real.log s := by
    have hsq : w+1≤ s*s := by nlinarith
    calc
      _ ≤ Real.log (s*s) := Real.log_le_log (by linarith) hsq
      _ = _ := by rw [Real.log_mul hs0.ne' hs0.ne']; ring
  have hlu := logle u hu hup
  have hlv := logle v hv hvp
  have hsum : v*Real.log (u+1)+u*Real.log (v+1)≤4*s^(4/5:ℝ)*Real.log s := by
    have h1 := mul_le_mul hlu hvs (by positivity) (mul_nonneg (by norm_num) hl)
    have h2 := mul_le_mul hlv hus (by positivity) (mul_nonneg (by norm_num) hl)
    nlinarith
  have hpp : (2*p)^2≤4*s^(1/50:ℝ) := by
    have hp2 := pow_le_pow_left₀ hp hps 2
    rw [←Real.rpow_mul_natCast hs0.le] at hp2
    norm_num at hp2
    nlinarith
  have hsum0 : 0≤v*Real.log (u+1)+u*Real.log (v+1) := by
    have h1 := Real.log_nonneg (show 1≤u+1 by linarith)
    have h2 := Real.log_nonneg (show 1≤v+1 by linarith)
    positivity
  calc
    _ ≤ (9+2*(q:ℝ))*(4*s^(1/50:ℝ))*(4*s^(4/5:ℝ)*Real.log s) := by
      gcongr
      linarith
    _ = C*s^(41/50:ℝ)*Real.log s := by
      rw [show (9+2*(q:ℝ))*(4*s^(1/50:ℝ))*(4*s^(4/5:ℝ)*Real.log s)=
        C*(s^(1/50:ℝ)*s^(4/5:ℝ))*Real.log s by dsimp [C]; ring,
        ←Real.rpow_add hs0]
      norm_num
    _ ≤ C*s^(41/50:ℝ)*(C⁻¹*s^(2/25:ℝ)) := by gcongr
    _ = s^(9/10:ℝ) := by
      rw [show C*s^(41/50:ℝ)*(C⁻¹*s^(2/25:ℝ))=
        (C*C⁻¹)*(s^(41/50:ℝ)*s^(2/25:ℝ)) by ring,mul_inv_cancel₀ hC.ne',one_mul,
        ←Real.rpow_add hs0]
      norm_num

lemma child_exponent_gap {s u : ℝ} (hs : 0<Real.log s) (hu : 0<Real.log u)
    (hbalance : Real.log u≤(4/5:ℝ)*Real.log s) :
    (11/10:ℝ)/Real.sqrt (Real.log s) ≤ 1/Real.sqrt (Real.log u) := by
  have hsqrt : 0<Real.sqrt (Real.log s) := Real.sqrt_pos.mpr hs
  have huqrt : 0<Real.sqrt (Real.log u) := Real.sqrt_pos.mpr hu
  have hsq := Real.sq_sqrt hu.le
  have hss := Real.sq_sqrt hs.le
  have hb : (11:ℝ)*Real.sqrt (Real.log u)≤10*Real.sqrt (Real.log s) := by
    nlinarith [Real.sqrt_nonneg (Real.log u),Real.sqrt_nonneg (Real.log s)]
  apply (div_le_div_iff₀ hsqrt huqrt).mpr
  nlinarith

lemma hook_strengthened_scalar {s F h C c e E : ℝ}
    (hs : 1600≤Real.log s) (hF : 0≤F) (hh : 0≤h)
    (hc : c0+(11/10:ℝ)/Real.sqrt (Real.log s)≤c) (hc2 : c≤2)
    (he : e≤e0-(11/10:ℝ)/Real.sqrt (Real.log s)) (hE : E≤ s^(9/10:ℝ)) :
    -c*F+e*h*Real.log s-C+c*h+E ≤
      -(c0+1/Real.sqrt (Real.log s)+inductionGap s)*F+
      (e0-1/Real.sqrt (Real.log s)-inductionGap s)*h*Real.log s-C+s^(9/10:ℝ) := by
  have hl : 0<Real.log s := by linarith
  have hsq : 0<Real.sqrt (Real.log s) := Real.sqrt_pos.mpr hl
  have hs40 : 40≤Real.sqrt (Real.log s) := Real.le_sqrt_of_sq_le (by norm_num; exact hs)
  have hsqe := Real.sq_sqrt hl.le
  have hgap : inductionGap s = (1/20:ℝ)/Real.sqrt (Real.log s) := by
    unfold inductionGap
    ring
  rw [hgap]
  have hsave : (1/20:ℝ)/Real.sqrt (Real.log s)*Real.log s≥2 := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hsq).mpr
    nlinarith
  have hc' : c0+1/Real.sqrt (Real.log s)+(1/20:ℝ)/Real.sqrt (Real.log s)≤c := by
    have hn := div_pos (show (1/20:ℝ)>0 by norm_num) hsq
    have heq : (11/10:ℝ)/Real.sqrt (Real.log s)=
      1/Real.sqrt (Real.log s)+(1/20:ℝ)/Real.sqrt (Real.log s)+(1/20:ℝ)/Real.sqrt (Real.log s) := by ring
    rw [heq] at hc
    linarith
  have he' : e*Real.log s+c≤(e0-1/Real.sqrt (Real.log s)-(1/20:ℝ)/Real.sqrt (Real.log s))*Real.log s := by
    have h1 := mul_le_mul_of_nonneg_right he hl.le
    have heq : (11/10:ℝ)/Real.sqrt (Real.log s)=
      1/Real.sqrt (Real.log s)+2*((1/20:ℝ)/Real.sqrt (Real.log s)) := by ring
    rw [heq] at h1
    nlinarith
  have hf := mul_le_mul_of_nonneg_right hc' hF
  have hholes := mul_le_mul_of_nonneg_right he' hh
  nlinarith

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical
open Filter

namespace BinaryCoordinateSweeps.GridSplit
open Irrep Representation Signed

lemma typeF_nonneg {n : ℕ} (α : n.Partition) : 0≤typeF α := by
  apply Real.log_nonneg
  exact_mod_cast irreducible_finrank_pos (Young.partitionHilbertRep α)

lemma cExponent_nonneg (s : ℕ) : 0≤cExponent s := by
  unfold cExponent c0
  positivity

lemma cExponent_le_two {s : ℕ} (hs : 1≤Real.log s) : cExponent s≤2 := by
  have hsq : 1≤Real.sqrt (Real.log s) := Real.le_sqrt_of_sq_le (by norm_num; exact hs)
  have hi := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hsq
  unfold cExponent c0
  norm_num at hi ⊢
  linarith

theorem hook_auxiliary_eventually (q : ℕ) (hq : 2≤q) : ∀ᶠ s : ℕ in atTop,
    ∀ m n h : ℕ, ∀ bits : Fin (m+n) → ℕ, ∀ H : PathFamily bits h,
    gridSize bits=s →
    1≤Real.log (gridSize (leftBits bits)) → 1≤Real.log (gridSize (rightBits bits)) →
    Real.log (gridSize (leftBits bits))≤(4/5:ℝ)*Real.log s →
    Real.log (gridSize (rightBits bits))≤(4/5:ℝ)*Real.log s →
    ∀ t : ℕ, 0<t → (t:ℝ)≤(s:ℝ)^(1/100:ℝ) →
    ∀ α : (junctionSize bits H).Partition, Young.InHook (Young.diagram α) t → ∀z : ℝ,
    (∀y (a : ActiveType (Prod.fst : Bool × Fin t → Bool) (rowFreeSize bits H y)),
      evenMoment q (groupAverage (Young.partitionHilbertRep a.val) (rowChildWeight bits H z y))≤
        Real.exp (-cExponent (gridSize (leftBits bits))*typeF a.val+
          eExponent (gridSize (leftBits bits))*Fintype.card (RowLabels bits H y)*
          Real.log (gridSize (leftBits bits))-pathCost (rowFamily bits H y))) →
    (∀x (a : ActiveType (Prod.fst : Bool × Fin t → Bool) (columnFreeSize bits H x)),
      evenMoment q (groupAverage (Young.partitionHilbertRep a.val) (columnChildWeight bits H z x))≤
        Real.exp (-cExponent (gridSize (rightBits bits))*typeF a.val+
          eExponent (gridSize (rightBits bits))*Fintype.card (ColumnLabels bits H x)*
          Real.log (gridSize (rightBits bits))-pathCost (columnFamily bits H x))) →
    evenMoment q (groupAverage ((Young.partitionHilbertRep α).comp
      (inputToJunction bits H).permCongrHom.toMonoidHom)
      (fun a => (conditionalGroupLaw H z a:ℂ)))≤
      Real.exp (-(cExponent s+inductionGap s)*typeF α+
        (eExponent s-inductionGap s)*h*Real.log s-pathCost H+(s:ℝ)^(9/10:ℝ)) := by
  have hcast : Tendsto (fun s : ℕ => (s:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hcast.eventually (hook_polynomial_error_eventually q),
    (Real.tendsto_log_atTop.comp hcast).eventually_ge_atTop 1600] with s herr hs
  intro m n h bits H hsize hu hv hub hvb t ht hts α hα z hR hC
  let u := gridSize (leftBits bits)
  let v := gridSize (rightBits bits)
  let c := min (cExponent u) (cExponent v)
  let e := max (eExponent u) (eExponent v)
  have hq0 : 0<q := by omega
  have hc : 0≤c := le_min (cExponent_nonneg _) (cExponent_nonneg _)
  have hc2 : c≤2 := (min_le_left _ _).trans (cExponent_le_two hu)
  have hcq : c≤q := hc2.trans (by exact_mod_cast hq)
  have hl0 : 0<Real.log s := by linarith
  have hu0 : 0<Real.log u := by dsimp [u]; linarith
  have hv0 : 0<Real.log v := by dsimp [v]; linarith
  have hcg : c0+(11/10:ℝ)/Real.sqrt (Real.log s)≤c := by
    apply le_min <;> unfold cExponent
    · linarith [child_exponent_gap hl0 hu0 hub]
    · linarith [child_exponent_gap hl0 hv0 hvb]
  have heg : e≤e0-(11/10:ℝ)/Real.sqrt (Real.log s) := by
    apply max_le <;> unfold eExponent
    · linarith [child_exponent_gap hl0 hu0 hub]
    · linarith [child_exponent_gap hl0 hv0 hvb]
  have weaken (U N : ℕ) (F C : ℝ) (hF : 0≤F) (hU : 0≤Real.log U)
      (hcu : c≤cExponent U) (heu : eExponent U≤e) :
      -cExponent U*F+eExponent U*N*Real.log U-C≤-c*F+e*N*Real.log U-C := by
    have h1 := mul_le_mul_of_nonneg_right hcu hF
    have h2 := mul_le_mul_of_nonneg_right heu
      (mul_nonneg (Nat.cast_nonneg N) hU)
    nlinarith
  have hRR : ∀y (a : ActiveType (Prod.fst : Bool × Fin t → Bool) (rowFreeSize bits H y)),
      evenMoment q (groupAverage (Young.partitionHilbertRep a.val) (rowChildWeight bits H z y))≤
        Real.exp (-c*typeF a.val+e*Fintype.card (RowLabels bits H y)*
          Real.log (gridSize (leftBits bits))-pathCost (rowFamily bits H y)) := by
    intro y a
    exact (hR y a).trans (Real.exp_le_exp.mpr
      (weaken u _ _ _ (typeF_nonneg _) hu0.le (min_le_left _ _) (le_max_left _ _)))
  have hCC : ∀x (a : ActiveType (Prod.fst : Bool × Fin t → Bool) (columnFreeSize bits H x)),
      evenMoment q (groupAverage (Young.partitionHilbertRep a.val) (columnChildWeight bits H z x))≤
        Real.exp (-c*typeF a.val+e*Fintype.card (ColumnLabels bits H x)*
          Real.log (gridSize (rightBits bits))-pathCost (columnFamily bits H x)) := by
    intro x a
    exact (hC x a).trans (Real.exp_le_exp.mpr
      (weaken v _ _ _ (typeF_nonneg _) hv0.le (min_le_right _ _) (le_max_right _ _)))
  have hup : (u:ℝ)≤(s:ℝ)^(4/5:ℝ) := by
    rw [←Real.exp_log (show 0<(u:ℝ) by exact_mod_cast gridSize_pos (leftBits bits)),Real.rpow_def_of_pos (by
      rw [←hsize]; exact_mod_cast gridSize_pos bits)]
    exact Real.exp_le_exp.mpr (by simpa only [mul_comm] using hub)
  have hvp : (v:ℝ)≤(s:ℝ)^(4/5:ℝ) := by
    rw [←Real.exp_log (show 0<(v:ℝ) by exact_mod_cast gridSize_pos (rightBits bits)),Real.rpow_def_of_pos (by
      rw [←hsize]; exact_mod_cast gridSize_pos bits)]
    exact Real.exp_le_exp.mpr (by simpa only [mul_comm] using hvb)
  have hE := herr u v t c (by exact_mod_cast gridSize_pos (leftBits bits))
    (by exact_mod_cast gridSize_pos (rightBits bits)) (by positivity) hts hup hvp hc hc2
  refine (conditional_hook_with_cost bits H ht α hα z hq0 c e hc hcq hRR hCC).trans ?_
  apply Real.exp_le_exp.mpr
  rw [hsize]
  exact hook_strengthened_scalar hs (typeF_nonneg _) (by positivity) hcg hc2 heg hE

end BinaryCoordinateSweeps.GridSplit

end

end OAI
