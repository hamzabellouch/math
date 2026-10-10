import Mathlib
import OAI.Probability.BinarySweep.YoungTheory.HookScalar

namespace OAI

noncomputable section

section

open scoped BigOperators Classical
open Filter

namespace BinaryCoordinateSweeps.GridSplit
open Irrep Representation Signed

variable {m n h : ℕ} (bits : Fin (m+n) → ℕ) (H : PathFamily bits h)

theorem conditional_occurring_with_cost {t : ℕ} (ht : 0<t)
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin (junctionSize bits H))) V) [ρ.IsIrreducible]
    (hρ : ∀g v, ‖ρ g v‖=‖v‖)
    (hocc : 0<Module.finrank ℂ (IntertwiningMap ρ
      (hilbertTensorRep (Prod.fst : Bool × Fin t → Bool) (junctionSize bits H))))
    (z : ℝ) {q : ℕ} (hq : 0<q) (c e : ℝ) (hc : 0≤c) (hcq : c≤q)
    (hchildR : ∀y (a : ActiveType (Prod.fst : Bool × Fin t → Bool) (rowFreeSize bits H y)),
      evenMoment q (groupAverage (Young.partitionHilbertRep a.val) (rowChildWeight bits H z y))≤
        Real.exp (-c*typeF a.val+e*Fintype.card (RowLabels bits H y)*
          Real.log (gridSize (leftBits bits))-pathCost (rowFamily bits H y)))
    (hchildC : ∀x (a : ActiveType (Prod.fst : Bool × Fin t → Bool) (columnFreeSize bits H x)),
      evenMoment q (groupAverage (Young.partitionHilbertRep a.val) (columnChildWeight bits H z x))≤
        Real.exp (-c*typeF a.val+e*Fintype.card (ColumnLabels bits H x)*
          Real.log (gridSize (rightBits bits))-pathCost (columnFamily bits H x))) :
    evenMoment q (groupAverage (ρ.comp
      (inputToJunction bits H).permCongrHom.toMonoidHom)
      (fun a => (conditionalGroupLaw H z a:ℂ)))≤
      Real.exp (-c*Real.log (Module.finrank ℂ V:ℝ)+e*h*Real.log (gridSize bits)-pathCost H+c*h+
        (1+4*c+2*(q:ℝ))*(2*(t:ℝ))^2*
          ((gridSize (rightBits bits):ℝ)*Real.log (gridSize (leftBits bits)+1:ℝ)+
           (gridSize (leftBits bits):ℝ)*Real.log (gridSize (rightBits bits)+1:ℝ))) := by
  have hr : ∀y (a : ActiveType (Prod.fst : Bool × Fin t → Bool) (rowFreeSize bits H y)),
      evenMoment q (groupAverage (Young.partitionHilbertRep a.val) (rowChildWeight bits H z y))≤
        Real.exp (-c*typeF a.val+(e*Fintype.card (RowLabels bits H y)*
          Real.log (gridSize (leftBits bits))-pathCost (rowFamily bits H y))) := by
    intros; simpa only [add_sub_assoc] using hchildR _ _
  have hc' : ∀x (a : ActiveType (Prod.fst : Bool × Fin t → Bool) (columnFreeSize bits H x)),
      evenMoment q (groupAverage (Young.partitionHilbertRep a.val) (columnChildWeight bits H z x))≤
        Real.exp (-c*typeF a.val+(e*Fintype.card (ColumnLabels bits H x)*
          Real.log (gridSize (rightBits bits))-pathCost (columnFamily bits H x))) := by
    intros; simpa only [add_sub_assoc] using hchildC _ _
  let : NeZero t := ⟨ne_of_gt ht⟩
  have hh := conditional_dense_bound bits H ρ hρ (Prod.fst : Bool × Fin t → Bool)
    hocc z hq c hc hcq _ _ hr hc'
  simp only [Fintype.card_prod,Fintype.card_bool,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat] at hh
  refine hh.trans ?_
  apply Real.exp_le_exp.mpr
  rw [add_assoc (-c*Real.log (Module.finrank ℂ V:ℝ)),child_error_sum]
  have hb := mul_le_mul_of_nonneg_left (blocksLog_le bits H)
    (by positivity : 0≤(1+4*c+2*(q:ℝ))*(2*(t:ℝ))^2)
  linarith

theorem occurring_auxiliary_eventually (q : ℕ) (hq : 2≤q) : ∀ᶠ s : ℕ in atTop,
    ∀ m n h : ℕ, ∀ bits : Fin (m+n) → ℕ, ∀ H : PathFamily bits h,
    gridSize bits=s →
    1≤Real.log (gridSize (leftBits bits)) → 1≤Real.log (gridSize (rightBits bits)) →
    Real.log (gridSize (leftBits bits))≤(4/5:ℝ)*Real.log s →
    Real.log (gridSize (rightBits bits))≤(4/5:ℝ)*Real.log s →
    ∀ t : ℕ, 0<t → (t:ℝ)≤(s:ℝ)^(1/100:ℝ) →
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V],
    ∀ (ρ : Representation ℂ (Equiv.Perm (Fin (junctionSize bits H))) V) [ρ.IsIrreducible],
    (∀g v, ‖ρ g v‖=‖v‖) →
    0<Module.finrank ℂ (IntertwiningMap ρ
      (hilbertTensorRep (Prod.fst : Bool × Fin t → Bool) (junctionSize bits H))) → ∀z : ℝ,
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
    evenMoment q (groupAverage (ρ.comp
      (inputToJunction bits H).permCongrHom.toMonoidHom)
      (fun a => (conditionalGroupLaw H z a:ℂ)))≤
      Real.exp (-(cExponent s+inductionGap s)*Real.log (Module.finrank ℂ V:ℝ)+
        (eExponent s-inductionGap s)*h*Real.log s-pathCost H+(s:ℝ)^(9/10:ℝ)) := by
  have hcast : Tendsto (fun s : ℕ => (s:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hcast.eventually (hook_polynomial_error_eventually q),
    (Real.tendsto_log_atTop.comp hcast).eventually_ge_atTop 1600] with s herr hs
  intro m n h bits H hsize hu hv hub hvb t ht hts V _ _ _ ρ _ hρ hocc z hR hC
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
  refine (conditional_occurring_with_cost bits H ht ρ hρ hocc z hq0 c e hc hcq hRR hCC).trans ?_
  apply Real.exp_le_exp.mpr
  rw [hsize]
  exact hook_strengthened_scalar hs (Real.log_nonneg (by exact_mod_cast irreducible_finrank_pos ρ)) (by positivity) hcg hc2 heg hE

end BinaryCoordinateSweeps.GridSplit

end

open scoped BigOperators Classical
open Filter

namespace BinaryCoordinateSweeps.GridSplit
open Irrep Representation Signed Young

theorem specht_hook_auxiliary_eventually (q : ℕ) (hq : 2≤q) : ∀ᶠ s : ℕ in atTop,
    ∀ m n h : ℕ, ∀ bits : Fin (m+n) → ℕ, ∀ H : PathFamily bits h,
    gridSize bits=s →
    1≤Real.log (gridSize (leftBits bits)) → 1≤Real.log (gridSize (rightBits bits)) →
    Real.log (gridSize (leftBits bits))≤(4/5:ℝ)*Real.log s →
    Real.log (gridSize (rightBits bits))≤(4/5:ℝ)*Real.log s →
    ∀ t : ℕ, 0<t → (t:ℝ)≤(s:ℝ)^(1/100:ℝ) →
    ∀ μ : YoungDiagram, InHook μ t → ∀ e : Cell μ ≃ FreeSlot H 0, ∀z : ℝ,
    (∀y (a : ActiveType (Prod.fst : Bool × Fin t → Bool) (rowFreeSize bits H y)),
      evenMoment q (groupAverage (partitionHilbertRep a.val) (rowChildWeight bits H z y))≤
        Real.exp (-cExponent (gridSize (leftBits bits))*typeF a.val+
          eExponent (gridSize (leftBits bits))*Fintype.card (RowLabels bits H y)*
          Real.log (gridSize (leftBits bits))-pathCost (rowFamily bits H y))) →
    (∀x (a : ActiveType (Prod.fst : Bool × Fin t → Bool) (columnFreeSize bits H x)),
      evenMoment q (groupAverage (partitionHilbertRep a.val) (columnChildWeight bits H z x))≤
        Real.exp (-cExponent (gridSize (rightBits bits))*typeF a.val+
          eExponent (gridSize (rightBits bits))*Fintype.card (ColumnLabels bits H x)*
          Real.log (gridSize (rightBits bits))-pathCost (columnFamily bits H x))) →
    evenMoment q (groupAverage ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom)
      (fun a => (conditionalGroupLaw H z a:ℂ)))≤
      Real.exp (-(cExponent s+inductionGap s)*Real.log (Module.finrank ℂ (SpechtSpace μ):ℝ)+
        (eExponent s-inductionGap s)*h*Real.log s-pathCost H+(s:ℝ)^(9/10:ℝ)) := by
  filter_upwards [occurring_auxiliary_eventually q hq] with s hs
  intro m n h bits H hsize hu hv hub hvb t ht hts μ hμ e z hR hC
  let eJ := e.trans (inputToJunction bits H)
  let ρ : Representation ℂ (Equiv.Perm (Fin (junctionSize bits H))) (SpechtHilbert μ) := (hilbertSpecht μ).comp eJ.symm.permCongrHom.toMonoidHom
  let : ρ.IsIrreducible := irreducible_comp_equiv eJ.symm.permCongrHom (hilbertSpecht μ)
  have hρ : ∀g v, ‖ρ g v‖=‖v‖ := fun g v => hilbertSpecht_unitary μ _ v
  have hb := hs m n h bits H hsize hu hv hub hvb t ht hts (SpechtHilbert μ) ρ hρ
    (hookHilbert_occursAt μ hμ eJ) z hR hC
  have he : ρ.comp (inputToJunction bits H).permCongrHom.toMonoidHom =
      (hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom := by
    apply MonoidHom.ext
    intro g
    change hilbertSpecht μ (eJ.symm.permCongr ((inputToJunction bits H).permCongr g)) =
      hilbertSpecht μ (e.symm.permCongr g)
    apply congrArg (hilbertSpecht μ)
    apply Equiv.ext
    intro a
    simp [eJ,Equiv.permCongr_apply]
  rw [he,hilbertSpecht_finrank] at hb
  exact hb

end BinaryCoordinateSweeps.GridSplit

end

end OAI
