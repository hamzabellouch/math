import OAI.NumberTheory.Ostmann.Construction.CounterpartNormalizationBoundPriors
import OAI.NumberTheory.Ostmann.Construction.CounterpartNormalizationBoundProduct

namespace OAI

open Erdos970

noncomputable section
open Filter
namespace Ostmann.Construction
open Arithmetic.HistoryProductWindows CounterpartNormalizationBound

def counterpartNormalizationConstant : ℝ := 24+Real.log 1000

lemma counterpartNormalizationConstant_pos : 0<counterpartNormalizationConstant := by
  have := Real.log_pos (by norm_num : (1:ℝ)<1000)
  unfold counterpartNormalizationConstant
  linarith

lemma counterpartNormalizationConstant_le : counterpartNormalizationConstant≤34 := by
  have h2 : (2:ℝ)≤Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) h2 10
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp
  have hl : Real.log (1000:ℝ)≤10 :=
    (Real.log_le_iff_le_exp (by norm_num)).mpr (by linarith)
  unfold counterpartNormalizationConstant
  linarith

theorem remainingNormalization_exp_bound_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    {k : ℕ} (hk : 0<k) :
    ∀ᶠ L : ℝ in atTop, ∀(E:Finset ℕ)(C:InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase →
      C.blockBase+favorableBlockWidth L≤Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
      ∀l:ℕ,C.remainingNormalization
          (Template.remainder (l+1) (Template.current (Template.initial (Conclusion.bulkSize k L) k) l))≤
        Real.exp ((counterpartNormalizationConstant-Real.log L)*((2:ℝ)^l*(Conclusion.bulkSize k L:ℝ))) := by
  filter_upwards [sourceNormalization_exp_bound_eventually d Bs BD Bz hk,
    eventually_ge_atTop (4:ℝ)] with L hpriors hL4
  intro E C hG hGu hcl hcu hb hd l
  obtain ⟨hgiant,hsource⟩ := hpriors E C hG hGu hcl hcu hb hd
  have hL : 0≤L := by linarith
  have hprod := remaining_product_bound (Conclusion.bulkSize k L) k l C.sourceNormalization
    (Real.log 1000-Real.log L) L hL
    (fun q _ => sourceNormalization_nonneg C q.origin)
    (fun q hq => let hm := remaining_origin_metadata (Conclusion.bulkSize k L) k l q hq
      hsource q hm.1 hm.2)
  have hpnonneg : 0≤((Template.remainder (l+1)
      (Template.current (Template.initial (Conclusion.bulkSize k L) k) l)).map
      (fun q => C.sourceNormalization q.origin)).prod := by
    apply List.prod_nonneg
    intro z hz
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hz
    exact sourceNormalization_nonneg C q.origin
  have hcost := mul_le_mul_of_nonneg_left (RepeatedPriorBounds.cell_count_cost hk hL4)
    (show 0≤(2:ℝ)^l by positivity)
  have hr : (1:ℝ)≤2^l := one_le_pow₀ (by norm_num)
  have hLr := mul_le_mul_of_nonneg_right hr hL
  have hN : L+L*((2:ℝ)^l*(6+4*(k:ℝ)))≤24*((2:ℝ)^l*(Conclusion.bulkSize k L:ℝ)) := by
    push_cast at hcost
    nlinarith
  unfold InitialSourceChoice.remainingNormalization
  calc
    _ ≤ Real.exp L*Real.exp ((Real.log 1000-Real.log L)*((2:ℝ)^l*(Conclusion.bulkSize k L:ℝ))+
        L*((2:ℝ)^l*(6+4*(k:ℝ)))) :=
      mul_le_mul hgiant hprod hpnonneg (Real.exp_pos _).le
    _ = Real.exp (L+(Real.log 1000-Real.log L)*((2:ℝ)^l*(Conclusion.bulkSize k L:ℝ))+
        L*((2:ℝ)^l*(6+4*(k:ℝ)))) := by rw [← Real.exp_add,add_assoc]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      unfold counterpartNormalizationConstant
      nlinarith

theorem remainingNormalization_bound_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    {k : ℕ} (hk : 0<k) :
    ∀ᶠ L : ℝ in atTop, ∀(E:Finset ℕ)(C:InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase →
      C.blockBase+favorableBlockWidth L≤Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
      ∀l:ℕ,C.remainingNormalization
          (Template.remainder (l+1) (Template.current (Template.initial (Conclusion.bulkSize k L) k) l))≤
        Real.exp (counterpartNormalizationConstant*((2:ℝ)^l*(Conclusion.bulkSize k L:ℝ)))/
          L^(2^l*Conclusion.bulkSize k L) := by
  filter_upwards [remainingNormalization_exp_bound_eventually d Bs BD Bz hk,
    eventually_gt_atTop (0:ℝ)] with L hbound hL
  intro E C hG hGu hcl hcu hb hd l
  have h := hbound E C hG hGu hcl hcu hb hd l
  have he : Real.exp (Real.log L*((2:ℝ)^l*(Conclusion.bulkSize k L:ℝ)))=
      L^(2^l*Conclusion.bulkSize k L) := by
    rw [show Real.log L*((2:ℝ)^l*(Conclusion.bulkSize k L:ℝ))=
      ((2^l*Conclusion.bulkSize k L:ℕ):ℝ)*Real.log L by push_cast; ring,
      Real.exp_nat_mul,Real.exp_log hL]
  rw [sub_mul,Real.exp_sub,he] at h
  exact h

end Ostmann.Construction

end

end OAI
