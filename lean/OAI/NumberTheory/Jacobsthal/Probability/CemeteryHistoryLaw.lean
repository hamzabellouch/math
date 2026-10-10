import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.WithDensity
import OAI.NumberTheory.Jacobsthal.Paths.FiniteHistorySupport

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.CemeteryKernel

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α]

abbrev Space (α : Type*) := α ⊕ Unit

def dead : Space α := Sum.inr ()

noncomputable def cemeteryPart (K : Kernel α α) : Kernel α (Space α) :=
  (Kernel.const α (Measure.dirac dead)).withDensity (fun x _ => 1-K x univ)

theorem cemeteryPart_measurable (K : Kernel α α) :
    Measurable (Function.uncurry (fun (x : α) (_ : Space α) => 1-K x univ)) :=
  measurable_const.sub ((K.measurable_coe MeasurableSet.univ).comp measurable_fst)

theorem cemeteryPart_apply (K : Kernel α α) (x : α) :
    cemeteryPart K x = (1-K x univ) • Measure.dirac dead := by
  rw [cemeteryPart, Kernel.withDensity_apply _ (cemeteryPart_measurable K) x, Kernel.const_apply, withDensity_const]

noncomputable def liveRow (K : Kernel α α) : Kernel α (Space α) := K.map Sum.inl + cemeteryPart K

theorem liveRow_apply (K : Kernel α α) (x : α) :
    liveRow K x = (K x).map Sum.inl + (1-K x univ) • Measure.dirac dead := by
  rw [liveRow, _root_.add_apply, Kernel.map_apply _ measurable_inl, cemeteryPart_apply]

noncomputable def complete (K : Kernel α α) : Kernel (Space α) (Space α) where
  toFun := Sum.elim (liveRow K) (fun _ => Measure.dirac dead)
  measurable' := (liveRow K).measurable.sumElim measurable_const

@[simp] theorem complete_live (K : Kernel α α) (x : α) : complete K (.inl x) = liveRow K x := rfl
@[simp] theorem complete_dead (K : Kernel α α) : complete K dead = Measure.dirac dead := rfl

theorem complete_isMarkov (K : Kernel α α) (hK : ∀ x, K x univ ≤ 1) : IsMarkovKernel (complete K) := by
  constructor
  intro z
  constructor
  cases z with
  | inl x =>
    rw [complete_live, liveRow_apply, Measure.add_apply, Measure.map_apply measurable_inl MeasurableSet.univ,
      Set.preimage_univ, Measure.smul_apply]
    simp only [measure_univ, smul_eq_mul, mul_one]
    exact add_tsub_cancel_of_le (hK x)
  | inr u =>
    cases u
    change Measure.dirac (dead : Space α) univ = 1
    exact measure_univ

theorem complete_live_mass (K : Kernel α α) (x : α) {B : Set α} (hB : MeasurableSet B) :
    complete K (.inl x) (Sum.inl '' B) = K x B := by
  rw [complete_live, liveRow_apply, Measure.add_apply,
    Measure.map_apply measurable_inl hB.inl_image, Measure.smul_apply]
  have hpre : Sum.inl ⁻¹' (Sum.inl '' B : Set (Space α)) = B := Set.preimage_image_eq _ Sum.inl_injective
  rw [hpre]
  have hd : Measure.dirac (dead : Space α) (Sum.inl '' B) = 0 := by
    rw [Measure.dirac_apply' _ hB.inl_image, indicator_of_notMem (by simp [dead])]
  rw [hd, smul_zero, add_zero]

end NumberTheoryLean.CemeteryKernel

end

section

namespace NumberTheoryLean.CemeteryPowers

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open CemeteryKernel

variable {α : Type*} [MeasurableSpace α]

noncomputable def liftReward (F : α → ℝ≥0∞) : Space α → ℝ≥0∞ := Sum.elim F (fun _ => 0)

theorem liftReward_measurable {F : α → ℝ≥0∞} (hF : Measurable F) : Measurable (liftReward F) :=
  hF.sumElim measurable_const

theorem row_lift (K : Kernel α α) {F : α → ℝ≥0∞} (hF : Measurable F) (q : Space α) :
    (∫⁻ y,liftReward F y ∂complete K q) = liftReward (fun z => ∫⁻ y,F y ∂K z) q := by
  cases q with
  | inl z =>
    rw [complete_live,liveRow_apply,lintegral_add_measure,
      lintegral_map (liftReward_measurable hF) measurable_inl,
      lintegral_smul_measure,lintegral_dirac' _ (liftReward_measurable hF)]
    simp only [liftReward,Sum.elim_inl,dead,Sum.elim_inr,smul_eq_mul,mul_zero,add_zero]
  | inr u =>
    cases u
    change (∫⁻ y,liftReward F y ∂Measure.dirac dead) = 0
    rw [lintegral_dirac' _ (liftReward_measurable hF)]
    rfl

theorem power_lift (K : Kernel α α) {F : α → ℝ≥0∞} (hF : Measurable F) (n : ℕ) (q : Space α) :
    (∫⁻ y,liftReward F y ∂((complete K)^n) q) = liftReward (fun z => ∫⁻ y,F y ∂(K^n) z) q := by
  induction n generalizing q with
  | zero =>
    change (∫⁻ y,liftReward F y ∂Measure.dirac q) = _
    rw [lintegral_dirac' _ (liftReward_measurable hF)]
    cases q with
    | inl z =>
      change F z = ∫⁻ y,F y ∂Measure.dirac z
      rw [lintegral_dirac' _ hF]
    | inr u => rfl
  | succ n ih =>
    have hp : (complete K)^(n+1) = ((complete K)^n) ∘ₖ complete K := pow_succ _ _
    have hl : K^(n+1) = (K^n) ∘ₖ K := pow_succ _ _
    rw [hp,Kernel.lintegral_comp _ _ _ (liftReward_measurable hF)]
    calc
      _ = ∫⁻ y,liftReward (fun z => ∫⁻ a,F a ∂(K^n) z) y ∂complete K q := lintegral_congr ih
      _ = liftReward (fun y => ∫⁻ z,∫⁻ a,F a ∂(K^n) z ∂K y) q := row_lift K hF.lintegral_kernel q
      _ = _ := by
        cases q with
        | inl z =>
          change _ = ∫⁻ y,F y ∂(K^(n+1)) z
          rw [hl,Kernel.lintegral_comp _ _ _ hF]
          rfl
        | inr u => rfl

end NumberTheoryLean.CemeteryPowers

end

section

namespace NumberTheoryLean.CemeteryHistoryMap

open Set MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal
open FiniteHistoryTransport CemeteryKernel

variable {X : Type*} [MeasurableSpace X]

def live (z : Space X) : Prop := Sum.elim (fun _ => True) (fun _ => False) z

theorem live_measurable : MeasurableSet {z : Space X | live z} :=
  measurableSet_sum_iff.mpr ⟨MeasurableSet.univ,MeasurableSet.empty⟩

noncomputable def killStep (E : Set X) (z : Space X) (x : X) : Space X := by
  classical
  exact if live z ∧ x ∈ E then Sum.inl x else dead

theorem killStep_measurable {E : Set X} (hE : MeasurableSet E) :
    Measurable (fun p : Space X × X => killStep E p.1 p.2) := by
  classical
  exact Measurable.ite ((measurable_fst live_measurable).inter (measurable_snd hE))
    (measurable_inl.comp measurable_snd) measurable_const

omit [MeasurableSpace X] in
theorem killStep_eq_or_dead (E : Set X) (z : Space X) (x : X) :
    killStep E z x = Sum.inl x ∨ killStep E z x = dead := by
  classical
  unfold killStep
  split_ifs <;> simp

theorem extend_restrict (n : ℕ) (h : Hist X n) (x : X) :
    frestrictLe₂ (π := fun _ => X) n.le_succ (extend n h x) = h := by
  ext k
  simp [frestrictLe₂, FiniteHistoryTransport.extend, IicProdIoc_def,
    show (k:ℕ) ≤ n from Finset.mem_Iic.mp k.2]

noncomputable def killHist (E : Set X) : (n : ℕ) → Hist X n → Hist (Space X) n
  | 0,h => mapHist (fun x : X => (Sum.inl x : Space X)) 0 h
  | n+1,h =>
      let past := killHist E n (frestrictLe₂ (π := fun _ => X) n.le_succ h)
      extend n past (killStep E (last n past) (last (n+1) h))

theorem killHist_measurable {E : Set X} (hE : MeasurableSet E) (n : ℕ) :
    Measurable (killHist E n) := by
  induction n with
  | zero => exact mapHist_measurable (measurable_inl (α := X) (β := Unit)) 0
  | succ n ih =>
    have hp := ih.comp (measurable_frestrictLe₂ (X := fun _ => X) n.le_succ)
    exact (extend_measurable n).comp (hp.prodMk ((killStep_measurable hE).comp
      (((last_measurable n).comp hp).prodMk (last_measurable (n+1)))))

theorem killHist_extend (E : Set X) (n : ℕ) (h : Hist X n) (x : X) :
    killHist E (n+1) (extend n h x) =
      extend n (killHist E n h) (killStep E (last n (killHist E n h)) x) := by
  simp only [killHist, extend_restrict, extend_last]

theorem killHist_last (E : Set X) (n : ℕ) (h : Hist X n) :
    last n (killHist E n h) = Sum.inl (last n h) ∨ last n (killHist E n h) = dead := by
  cases n with
  | zero => exact Or.inl rfl
  | succ n =>
    simp only [killHist, extend_last]
    exact killStep_eq_or_dead _ _ _

end NumberTheoryLean.CemeteryHistoryMap

end

section

namespace NumberTheoryLean.CemeteryHistoryMap

open Set MeasureTheory ProbabilityTheory Preorder
open FiniteHistoryTransport CemeteryKernel

attribute [local instance] Classical.propDecidable

variable {X : Type*} [MeasurableSpace X]

def aliveThrough (E : Set X) (n : ℕ) (h : Hist X n) : Prop :=
  ∀ j : Finset.Iic n, 0 < (j:ℕ) → h j ∈ E

omit [MeasurableSpace X] in
theorem aliveThrough_succ (E : Set X) (n : ℕ) (h : Hist X (n+1)) :
    aliveThrough E (n+1) h ↔
      aliveThrough E n (frestrictLe₂ (π := fun _ => X) n.le_succ h) ∧ last (n+1) h ∈ E := by
  constructor
  · intro ha
    refine ⟨?_,ha ⟨n+1,by simp⟩ (Nat.succ_pos n)⟩
    intro j hj
    exact ha ⟨j,by have := Finset.mem_Iic.mp j.2; simp; omega⟩ hj
  · rintro ⟨ha,hx⟩ ⟨j,hj⟩ hpos
    have hj' := Finset.mem_Iic.mp hj
    by_cases hle : j ≤ n
    · exact ha ⟨j,by simpa using hle⟩ hpos
    · have heq : j = n+1 := by omega
      subst j
      exact hx

theorem killHist_restrict (E : Set X) (n k : ℕ) (hk : k ≤ n) (h : Hist X n) :
    frestrictLe₂ (π := fun _ => Space X) hk (killHist E n h) =
      killHist E k (frestrictLe₂ (π := fun _ => X) hk h) := by
  induction n generalizing k with
  | zero =>
    have : k = 0 := by omega
    subst k
    rfl
  | succ n ih =>
    by_cases hkn : k ≤ n
    · calc
        _ = frestrictLe₂ (π := fun _ => Space X) hkn
            (frestrictLe₂ (π := fun _ => Space X) n.le_succ (killHist E (n+1) h)) := rfl
        _ = frestrictLe₂ (π := fun _ => Space X) hkn
            (killHist E n (frestrictLe₂ (π := fun _ => X) n.le_succ h)) := by
          rw [killHist,extend_restrict]
        _ = _ := ih k hkn _
    · have heq : k = n+1 := by omega
      subst k
      rfl

theorem killHist_last_exact (E : Set X) (n : ℕ) (h : Hist X n) :
    last n (killHist E n h) = if aliveThrough E n h then Sum.inl (last n h) else dead := by
  classical
  induction n with
  | zero =>
    have ha : aliveThrough E 0 h := by
      intro j hj
      have := Finset.mem_Iic.mp j.2
      omega
    simp only [ite_eq_left ha]
    rfl
  | succ n ih =>
    rw [killHist,extend_last,ih]
    simp only [aliveThrough_succ]
    by_cases hp : aliveThrough E n (frestrictLe₂ (π := fun _ => X) n.le_succ h) <;>
      by_cases hx : last (n+1) h ∈ E <;> simp [hp,hx,killStep,live,dead]

theorem killHist_coordinate (E : Set X) (n k : ℕ) (hk : k ≤ n) (h : Hist X n) :
    (killHist E n h) ⟨k,by simpa using hk⟩ =
      if aliveThrough E k (frestrictLe₂ (π := fun _ => X) hk h)
      then Sum.inl (h ⟨k,by simpa using hk⟩) else dead := by
  classical
  have heq := congrArg (last k) (killHist_restrict E n k hk h)
  rw [killHist_last_exact] at heq
  exact heq

end NumberTheoryLean.CemeteryHistoryMap

end

section

namespace NumberTheoryLean.CemeteryHistoryMap

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open CemeteryKernel FiniteHistoryTransport

variable {X : Type*} [MeasurableSpace X]
variable (K : Kernel X X) [IsMarkovKernel K] {E : Set X} (hE : MeasurableSet E)

theorem killStep_live_map (x : X) :
    (K x).map (killStep E (Sum.inl x)) = complete (K.restrict hE) (Sum.inl x) := by
  classical
  have hf : Measurable (killStep E (Sum.inl x)) :=
    (killStep_measurable hE).comp measurable_prodMk_left
  have hA : ((K x).restrict E).map (killStep E (Sum.inl x)) = ((K x).restrict E).map Sum.inl := by
    apply Measure.map_congr
    filter_upwards [ae_restrict_mem hE] with y hy
    simp [killStep,live,hy]
  have hB : ((K x).restrict Eᶜ).map (killStep E (Sum.inl x)) =
      ((K x).restrict Eᶜ).map (fun _ => (dead : Space X)) := by
    apply Measure.map_congr
    filter_upwards [ae_restrict_mem hE.compl] with y hy
    change y ∉ E at hy
    simp [killStep,live,hy]
  calc
    _ = (((K x).restrict E)+((K x).restrict Eᶜ)).map (killStep E (Sum.inl x)) := by
      rw [Measure.restrict_add_restrict_compl hE]
    _ = ((K x).restrict E).map Sum.inl + (1-K x E) • Measure.dirac dead := by
      rw [Measure.map_add _ _ hf, hA, hB, Measure.map_const, Measure.restrict_apply_univ,
        measure_compl hE (measure_ne_top _ _), measure_univ]
    _ = _ := by
      rw [complete_live,liveRow_apply,Kernel.restrict_apply,Measure.restrict_apply_univ]

theorem killStep_dead_map (x : X) :
    (K x).map (killStep E dead) = complete (K.restrict hE) dead := by
  classical
  have hf : killStep E (dead : Space X) = fun _ => dead := by
    funext y
    simp [killStep,live,dead]
  rw [hf,Measure.map_const,measure_univ,one_smul,complete_dead]

theorem killHist_step_map (n : ℕ) (h : Hist X n) :
    (K (last n h)).map (killStep E (last n (killHist E n h))) =
      complete (K.restrict hE) (last n (killHist E n h)) := by
  rcases killHist_last E n h with hl | hd
  · rw [hl]
    exact killStep_live_map K hE _
  · rw [hd]
    exact killStep_dead_map K hE _

instance restricted_complete_markov : IsMarkovKernel (complete (K.restrict hE)) := by
  apply complete_isMarkov
  intro x
  rw [Kernel.restrict_apply,Measure.restrict_apply_univ]
  exact (measure_mono (subset_univ E)).trans_eq (measure_univ (μ := K x))

end NumberTheoryLean.CemeteryHistoryMap

end

section

namespace NumberTheoryLean.CemeteryHistoryMap

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open CemeteryKernel FiniteHistoryTransport

variable {X : Type*} [MeasurableSpace X]
variable (K : Kernel X X) [IsMarkovKernel K] {E : Set X} (hE : MeasurableSet E)

theorem lintegral_killHist (n : ℕ) (h₀ : Hist X 0)
    {F : Hist (Space X) n → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ h, F (killHist E n h) ∂pathKernel K n h₀ =
      ∫⁻ h, F h ∂pathKernel (complete (K.restrict hE)) n (mapHist Sum.inl 0 h₀) := by
  induction n with
  | zero =>
    simp only [pathKernel,Kernel.partialTraj_self,Kernel.id_apply]
    rw [lintegral_dirac' _ (by exact hF.comp (killHist_measurable hE 0)),lintegral_dirac' _ hF]
    rfl
  | succ n ih =>
    rw [lintegral_pathKernel_succ K n h₀ (by exact hF.comp (killHist_measurable hE (n+1))),
      lintegral_pathKernel_succ (complete (K.restrict hE)) n (mapHist Sum.inl 0 h₀) hF]
    have hG : Measurable (fun h : Hist (Space X) n =>
        ∫⁻ y, F (FiniteHistoryTransport.extend n h y) ∂complete (K.restrict hE) (last n h)) := by
      have hm : Measurable (Function.uncurry (fun h : Hist (Space X) n => fun y : Space X =>
          F (FiniteHistoryTransport.extend n h y))) := hF.comp (extend_measurable n)
      simpa only [pastKernel,Kernel.comap_apply] using
        (hm.lintegral_kernel_prod_right (κ := pastKernel (complete (K.restrict hE)) n))
    calc
      _ = ∫⁻ h, ∫⁻ y, F (FiniteHistoryTransport.extend n (killHist E n h) y)
          ∂complete (K.restrict hE) (last n (killHist E n h)) ∂pathKernel K n h₀ := by
        apply lintegral_congr
        intro h
        simp only [killHist_extend]
        rw [← killHist_step_map K hE n h,lintegral_map]
        · exact hF.comp ((extend_measurable n).comp measurable_prodMk_left)
        · exact (killStep_measurable hE).comp measurable_prodMk_left
      _ = _ := ih hG

theorem pathMeasure_killHist (n : ℕ) (h₀ : Hist X 0) :
    (pathKernel K n h₀).map (killHist E n) =
      pathKernel (complete (K.restrict hE)) n (mapHist Sum.inl 0 h₀) := by
  have hk : (pathKernel K n).map (killHist E n) =
      (pathKernel (complete (K.restrict hE)) n).comap (mapHist Sum.inl 0)
        (mapHist_measurable measurable_inl 0) := by
    apply Kernel.ext_fun
    intro h F hF
    rw [Kernel.lintegral_map _ (killHist_measurable hE n) _ hF,Kernel.comap_apply]
    exact lintegral_killHist K hE n h hF
  rw [← Kernel.map_apply _ (killHist_measurable hE n),hk,Kernel.comap_apply]

end NumberTheoryLean.CemeteryHistoryMap

end

end Erdos970

end OAI
