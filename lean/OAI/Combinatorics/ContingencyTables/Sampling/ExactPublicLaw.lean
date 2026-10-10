import OAI.Combinatorics.ContingencyTables.Sampling.ExactPublicPrefix
import OAI.Combinatorics.ContingencyTables.Sampling.PhysicalPublicLaw

namespace OAI

/-! # Exact public output law and almost-sure termination -/

namespace ContingencyTables.ExactPublicLaw
open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost Turing
open PhysicalEventBounds PhysicalPublicLaw ExactPublicPrefix SmallGraphProfiles
open scoped BigOperators Classical
noncomputable section
attribute [local irreducible] ExactPublicPrefix.program ExactPublicPrefix.output
  ExactTablePrefix.experiment correctionPrecision
  PublishedInputs.FiniteBoxPrekopaLeindler PublishedInputs.FiniteCheeger
  CompletionCounts.dimensionAllowance

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
local notation "d" => CompletionCounts.dimensionAllowance (I := Fin m) (J := Fin n)

def prefixError (N : ℕ) : ℝ :=
  (1/(2:ℝ)^(correctionPrecision r c))*(1/2:ℝ)^N

lemma error_limit : Filter.Tendsto (prefixError r c) Filter.atTop (nhds 0) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2)
    (by norm_num : (1/2:ℝ)<1)).const_mul (1/(2:ℝ)^correctionPrecision r c)
  change Filter.Tendsto (fun N => (1/(2:ℝ)^(correctionPrecision r c))*(1/2:ℝ)^N) _ _
  simpa only [mul_zero] using h

lemma event_output (X Y : Table r c) :
    outputs (Algorithms.encodeMatrix X.val) (output r c (some Y)) ↔ Y=X := by
  simp only [outputs,output_halted,output_tape,true_and]
  constructor
  · intro h
    exact Subtype.ext (Algorithms.blankMatrix_injective _ _ h)
  · rintro rfl; rfl

section Conditional
variable
    (hPL : ∀ q,PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : ∀ q k,PublishedInputs.FiniteCheeger
      (GridBoundary.Grid (I := Fin q) (4*k^8)))
    (htotal : (∑ i,r i)=∑ j,c j)
include hPL hCheeger htotal

lemma prefix_error (N : ℕ) :
    ((ExactTablePrefix.experiment r c N).mean (fun o => if o=none then 1 else 0):ℝ)≤prefixError r c N := by
  have h := ExactTablePrefix.failure_bound r c (hPL _) (hCheeger _ d) htotal N
  have hR := (Rat.cast_le (K := ℝ)).mpr h
  simpa only [prefixError,Rat.cast_mul,Rat.cast_div,Rat.cast_pow,Rat.cast_one,Rat.cast_ofNat] using hR

theorem tableMass_limit (X : Table r c) :
    Filter.Tendsto (fun t => Algorithms.tableMass machine (Algorithms.encodeMargins r c) t X.val)
      Filter.atTop (nhds ((Fintype.card (Table r c):ℝ)⁻¹)) := by
  apply tendsto_of_prefix_bounds _
    (fun N => ((ExactTablePrefix.experiment r c N).mean (fun o => if o=some X then 1 else 0):ℝ))
    (prefixError r c) _ (ExactTablePrefix.point_limit r c (hPL _) (hCheeger _ d) htotal X) (error_limit r c)
  intro N
  obtain ⟨p,hp,hm⟩ := prefix_correct r c htotal N
  refine ⟨p.cost,?_⟩
  intro t ht
  have h := stopped_event_bounds program.table (output r c)
    (program.initial (Tape.mk₁ (ExactTablePrefix.input r c))) p hp
    (output_halted r c) (outputs (Algorithms.encodeMatrix X.val)) t ht
  have he : (fun o : Option (Table r c) => o.elim 0
      (fun Y => event (outputs (Algorithms.encodeMatrix X.val)) (output r c (some Y))))=
      (fun o => if o=some X then 1 else 0) := by
    funext o
    cases o with
    | none => simp
    | some Y => simp only [Option.elim_some,event,event_output,Option.some.injEq]
  rw [he,hm,hm] at h
  have hl : ((ExactTablePrefix.experiment r c N).mean
      (fun o => if o=some X then 1 else 0):ℝ)≤
      ((experiment program.table t (program.initial (Tape.mk₁ (Algorithms.encodeMargins r c)))).mean
        (event (outputs (Algorithms.encodeMatrix X.val))):ℝ) := by exact_mod_cast h.1
  have hu : ((experiment program.table t (program.initial (Tape.mk₁ (Algorithms.encodeMargins r c)))).mean
        (event (outputs (Algorithms.encodeMatrix X.val))):ℝ)≤
      ((ExactTablePrefix.experiment r c N).mean (fun o => if o=some X then 1 else 0):ℝ)+
        ((ExactTablePrefix.experiment r c N).mean (fun o => if o=none then 1 else 0):ℝ) := by
    exact_mod_cast h.2
  have hm : Algorithms.tableMass machine (Algorithms.encodeMargins r c) t X.val=
      ((experiment program.table t (program.initial (Tape.mk₁ (Algorithms.encodeMargins r c)))).mean
        (event (outputs (Algorithms.encodeMatrix X.val))):ℝ) := tableMass_eq program _ t X.val
  exact ⟨hl.trans_eq hm.symm,hm.le.trans
    (hu.trans (add_le_add le_rfl (prefix_error r c hPL hCheeger htotal N)))⟩

theorem tail_limit :
    Filter.Tendsto (PhysicalRetryTail.tail program.table
      (program.initial (Tape.mk₁ (Algorithms.encodeMargins r c)))) Filter.atTop (nhds 0) := by
  apply tendsto_of_prefix_bounds _ (fun _ => 0) (prefixError r c) 0 tendsto_const_nhds (error_limit r c)
  intro N
  obtain ⟨p,hp,hm⟩ := prefix_correct r c htotal N
  refine ⟨p.cost,?_⟩
  intro t ht
  have h := PhysicalRetryTail.tail_le_failure program.table (output r c) _ p hp
    (output_halted r c) t ht
  rw [hm] at h
  exact ⟨PhysicalRetryTail.tail_nonnegative _ _ _,
    (h.trans (prefix_error r c hPL hCheeger htotal N)).trans_eq (zero_add _).symm⟩

theorem haltMass_limit :
    Filter.Tendsto (Algorithms.haltMass machine (Algorithms.encodeMargins r c))
      Filter.atTop (nhds 1) := by
  have h := (tail_limit r c hPL hCheeger htotal).const_sub 1
  have he : (fun t => 1-PhysicalRetryTail.tail program.table
      (program.initial (Tape.mk₁ (Algorithms.encodeMargins r c))) t)=
      Algorithms.haltMass machine (Algorithms.encodeMargins r c) := by
    funext t
    rw [←tail_eq]
    change 1-(1-Algorithms.haltMass program.machine (Algorithms.encodeMargins r c) t)=
      Algorithms.haltMass program.machine (Algorithms.encodeMargins r c) t
    ring
  simpa only [he,sub_zero] using h

/-- Every finite halted public execution is feasible, including events of
arbitrarily small positive probability. -/
theorem halted_feasible (t : ℕ) (bits : Bits t)
    (hh : (MatchingFPRAS.run machine (Algorithms.encodeMargins r c) bits).state=none) :
    ∃ X : Table r c,Algorithms.OutputsTable machine (Algorithms.encodeMargins r c) bits X.val := by
  let bad : Cfg Symbol program.State → Prop := fun cfg => cfg.state=none ∧
    ¬∃ X : Table r c,cfg.tape.right₀=ListBlank.mk (Algorithms.encodeMatrix X.val)
  have hb (N : ℕ) :
      ((experiment program.table t (program.initial (Tape.mk₁ (Algorithms.encodeMargins r c)))).mean
        (event bad):ℝ)≤prefixError r c N := by
    obtain ⟨p,hp,hm⟩ := prefix_correct r c htotal N
    have h := absent_event_bound program.table (output r c) _ p hp (output_halted r c) bad
      (fun cfg hd => hd.1) (by intro X hX; exact hX.2 ⟨X,output_tape r c X⟩) t
    rw [hm] at h
    exact (show ((experiment program.table t (program.initial
      (Tape.mk₁ (Algorithms.encodeMargins r c)))).mean (event bad):ℝ)≤
      ((ExactTablePrefix.experiment r c N).mean (fun o => if o=none then 1 else 0):ℝ) by
        exact_mod_cast h).trans (prefix_error r c hPL hCheeger htotal N)
  have hzR := ge_of_tendsto' (error_limit r c) hb
  have hz : (experiment program.table t (program.initial (Tape.mk₁ (Algorithms.encodeMargins r c)))).mean
      (event bad)=0 := by
    have hnonneg := (experiment program.table t (program.initial (Tape.mk₁ (Algorithms.encodeMargins r c)))).mean_nonneg
      (event bad) ((Experiment.all_true _).mono (fun cfg _ => event_nonneg bad cfg))
    exact le_antisymm (by exact_mod_cast hzR) hnonneg
  have hall : (experiment program.table t (program.initial
      (Tape.mk₁ (Algorithms.encodeMargins r c)))).All (fun cfg => ¬bad cfg) := by
    rw [Experiment.all_indicator]
    change (experiment program.table t (program.initial
      (Tape.mk₁ (Algorithms.encodeMargins r c)))).mean (fun cfg => if ¬bad cfg then 0 else 1)=0
    have he : (fun cfg : Cfg Symbol program.State => if ¬bad cfg then (0:ℚ) else 1)=event bad := by
      funext cfg
      by_cases hb : bad cfg <;> simp [event,hb]
    rw [he]
    exact hz
  have hn := Experiment.all_run _ _ hall (extend bits)
  rw [experiment_run] at hn
  have hh' := (run_halted_iff program (Algorithms.encodeMargins r c) t bits).mp hh
  have hout : ∃ X : Table r c,(execute program.table t (program.initial
      (Tape.mk₁ (Algorithms.encodeMargins r c))) (extend bits)).tape.right₀=
      ListBlank.mk (Algorithms.encodeMatrix X.val) := by
    by_contra h
    exact hn ⟨hh',h⟩
  obtain ⟨X,hX⟩ := hout
  exact ⟨X,hh,(congrArg Tape.right₀ (Program.run_tape program _ t bits)).trans hX⟩

end Conditional
end
end ContingencyTables.ExactPublicLaw

end OAI
