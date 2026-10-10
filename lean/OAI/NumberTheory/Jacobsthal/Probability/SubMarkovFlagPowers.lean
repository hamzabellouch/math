import OAI.NumberTheory.Jacobsthal.Renewal.FlaggedOccupationBound

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.SubMarkovFlagPowers

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open PersistentFailureFlag FlaggedOccupationBound ActualCouplingFinite

variable {α : Type*} [MeasurableSpace α]

instance marked_sfinite (K : Kernel α α) [IsSFiniteKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) : IsSFiniteKernel (marked K hBad) := by
  unfold marked
  infer_instance

theorem marked_eq_map_sfinite (K : Kernel α α) [IsSFiniteKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) (z : FlagState α) :
    marked K hBad z = (K z.1).map (fun y => (y,z.2 || badBit Bad y)) := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [marked,Kernel.map_apply _ (update_measurable hBad),lintegral_map hF (update_measurable hBad)]
  calc
    _ = ∫⁻ y,F (y,z.2 || badBit Bad y) ∂K z.1 :=
      Kernel.lintegral_id_prod (f:=fun p : FlagState α × α => F (update Bad p))
        (hF.comp (update_measurable hBad)) _ z
    _ = _ := (lintegral_map hF (row_update_measurable hBad z.2)).symm

theorem marked_map_sfinite (K : Kernel α α) [IsSFiniteKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) (z : FlagState α) :
    (marked K hBad z).map Prod.fst = K z.1 := by
  rw [marked_eq_map_sfinite K hBad z,Measure.map_map (f:=fun y => (y,z.2 || badBit Bad y))
    (g:=Prod.fst) measurable_fst (row_update_measurable hBad z.2)]
  exact Measure.map_id

noncomputable def goodSelect (F : α → ℝ≥0∞) : FlagState α → ℝ≥0∞ := failedᶜ.indicator (fun z => F z.1)

theorem goodSelect_measurable {F : α → ℝ≥0∞} (hF : Measurable F) : Measurable (goodSelect F) :=
  (hF.comp measurable_fst).indicator failed_measurable.compl

noncomputable def goodKernel (K : Kernel α α) {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) : Kernel α α := K.restrict hBad.compl

instance goodKernel_sfinite (K : Kernel α α) [IsSFiniteKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) : IsSFiniteKernel (goodKernel K hBad) := by
  unfold goodKernel
  infer_instance

theorem good_row_lift (K : Kernel α α) [IsSFiniteKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) {F : α → ℝ≥0∞} (hF : Measurable F) (q : FlagState α) :
    (∫⁻ y,goodSelect F y ∂marked K hBad q) =
      goodSelect (fun x => ∫⁻ y,F y ∂goodKernel K hBad x) q := by
  classical
  rw [marked_eq_map_sfinite K hBad q,lintegral_map (goodSelect_measurable hF) (row_update_measurable hBad q.2)]
  rcases q with ⟨x,b⟩
  cases b with
  | true => simp [goodSelect,failed]
  | false =>
    simp only [goodSelect,failed,mem_compl_iff,mem_ofPred_eq,Bool.false_eq_true,not_false_eq_true,
      indicator_of_mem,Bool.false_or]
    rw [goodKernel,Kernel.restrict_apply,← lintegral_indicator hBad.compl]
    apply lintegral_congr
    intro y
    by_cases hy : Bad y <;> simp [badBit,hy]

theorem good_power_lift (K : Kernel α α) [IsSFiniteKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) {F : α → ℝ≥0∞} (hF : Measurable F)
    (n : ℕ) (q : FlagState α) :
    (∫⁻ y,goodSelect F y ∂((marked K hBad)^n) q) =
      goodSelect (fun x => ∫⁻ y,F y ∂((goodKernel K hBad)^n) x) q := by
  induction n generalizing q with
  | zero =>
    change (∫⁻ y,goodSelect F y ∂Measure.dirac q) = _
    rw [lintegral_dirac' _ (goodSelect_measurable hF)]
    have he : (fun x => ∫⁻ y,F y ∂((goodKernel K hBad)^0) x) = F := by
      funext x
      change (∫⁻ y,F y ∂Measure.dirac x) = F x
      rw [lintegral_dirac' _ hF]
    rw [he]
  | succ n ih =>
    have hp : (marked K hBad)^(n+1) = ((marked K hBad)^n) ∘ₖ marked K hBad := pow_succ _ _
    have hg : (goodKernel K hBad)^(n+1) = ((goodKernel K hBad)^n) ∘ₖ goodKernel K hBad := pow_succ _ _
    rw [hp,Kernel.lintegral_comp _ _ _ (goodSelect_measurable hF)]
    calc
      _ = ∫⁻ y,goodSelect (fun x => ∫⁻ a,F a ∂((goodKernel K hBad)^n) x) y ∂marked K hBad q := lintegral_congr ih
      _ = goodSelect (fun x => ∫⁻ y,∫⁻ a,F a ∂((goodKernel K hBad)^n) y ∂goodKernel K hBad x) q :=
        good_row_lift K hBad hF.lintegral_kernel q
      _ = _ := by
        have he : (fun x => ∫⁻ y,∫⁻ a,F a ∂((goodKernel K hBad)^n) y ∂goodKernel K hBad x) =
            (fun x => ∫⁻ a,F a ∂((goodKernel K hBad)^(n+1)) x) := by
          funext x
          rw [hg,Kernel.lintegral_comp _ _ _ hF]
        rw [he]

theorem finite_integral_partition (K : Kernel α α) [IsSFiniteKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) {F : α → ℝ≥0∞} (hF : Measurable F) (n : ℕ) (x : α) :
    (∫⁻ y,F y ∂(K^n) x) = (∫⁻ y,F y ∂((goodKernel K hBad)^n) x)+
      (∫⁻ y,selected F y ∂((marked K hBad)^n) (x,false)) := by
  classical
  have hmap := map_power_of_step (marked K hBad) K measurable_fst (marked_map_sfinite K hBad) n (x,false)
  rw [← hmap,lintegral_map hF measurable_fst]
  have he : (fun y : FlagState α => F y.1) = fun y => goodSelect F y+selected F y := by
    funext y
    rcases y with ⟨z,b⟩
    cases b <;> simp [goodSelect,selected,failed]
  rw [he,lintegral_add_left (goodSelect_measurable hF),good_power_lift K hBad hF]
  simp [goodSelect,failed]

end NumberTheoryLean.SubMarkovFlagPowers

end

end Erdos970

end OAI
