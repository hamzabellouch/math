import OAI.Combinatorics.ContingencyTables.Sampling.ExactCoreProgram

namespace OAI

/-! # The actual finite prefixes of the fixed exact-sampling program -/

namespace ContingencyTables.ExactCoreProgram
open MatchingFPRAS.PhysicalStream ProfilePrograms
attribute [local irreducible] rareBranch exactOrdinary correctionPrefix exactPrecision

lemma bool_mean (p : Experiment Bool) (a b : ℚ) :
    p.mean (fun x => if x then b else a)=
      (1-p.mean (fun x => if x then 1 else 0))*a+
        p.mean (fun x => if x then 1 else 0)*b := by
  induction p with
  | done x => cases x <;> simp [Experiment.mean]
  | delay n p ih => exact ih
  | read p ih =>
    simp only [Experiment.mean,ih]
    ring

lemma prefix_mean (z : DensePrograms.CompletionMargins) (N : ℕ)
    (g : Option DensePrograms.MatrixCode → ℚ) :
    (prefixExperiment z N).mean g=
      (1-1/(2:ℚ)^(exactPrecision z))*((exactOrdinary z).map some).mean g+
        (1/(2:ℚ)^(exactPrecision z))*(correctionPrefix z N).mean g := by
  rw [prefixExperiment,Experiment.mean_bind]
  have he (b : Bool) :
      (if b then correctionPrefix z N else (exactOrdinary z).map some).mean g=
        if b then (correctionPrefix z N).mean g else ((exactOrdinary z).map some).mean g := by
    cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  simp_rw [he]
  rw [bool_mean,rareBranch_probability]

end ContingencyTables.ExactCoreProgram

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms MatchingFPRAS MatchingFPRAS.PhysicalStream
open ResidualMixture FirstSuccess CompletionCounts
attribute [local irreducible] scheduledTableDraw exactOrdinary exactOrdinaryWord
  exactSamplingParameters ExactCoreProgram.prefixExperiment correctionPrefix
open scoped BigOperators Classical
noncomputable section

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "D" => correctionPrecision r c
local notation "q" => largeTailCount r (d^20)*largeTailCount c (d^20)

lemma exactOrdinary_mean (htotal : (∑ i,r i)=∑ j,c j) (g : MatrixCode → ℚ) :
    (exactOrdinary (List.ofFn r,List.ofFn c)).mean g=
      average (fun bits : Bits (finiteSamplerBits r c (2*D)) =>
        g (matrixCode (scheduledTableDraw r c htotal (2*D) bits).val)) := by
  rw [exactOrdinary,FiniteWordExecution.experiment_mean,exactOrdinaryBits_ofFn]
  simp_rw [exactOrdinaryWord_code r c htotal]

lemma table_event_average {L : ℕ} (draw : Bits L → Table r c) (X : Table r c) :
    average (fun bits => if matrixCode (draw bits).val=matrixCode X.val then (1:ℚ) else 0)=
      (mapLaw (uniformLaw (α := Bits L)) draw).mass X := by
  have he (Y : Table r c) : matrixCode Y.val=matrixCode X.val ↔ Y=X := by
    constructor
    · intro h
      apply Subtype.ext
      change List.ofFn (fun i => List.ofFn (Y.val i))=List.ofFn (fun i => List.ofFn (X.val i)) at h
      funext i
      exact List.ofFn_injective (congrFun (List.ofFn_injective h) i)
    · rintro rfl; rfl
  simp_rw [he]
  simp only [average,mapLaw,uniformLaw,uniformMass,Fintype.card_fun,Fintype.card_bool,
    Fintype.card_fin,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro bits _
  split_ifs <;> simp

lemma exactOrdinary_mass (htotal : (∑ i,r i)=∑ j,c j) (X : Table r c) :
    (exactOrdinary (List.ofFn r,List.ofFn c)).mean
      (fun Y => if Y=matrixCode X.val then 1 else 0)=
      (mapLaw (uniformLaw (α := Bits (finiteSamplerBits r c (2*D))))
        (scheduledTableDraw r c htotal (2*D))).mass X :=
  (exactOrdinary_mean r c htotal _).trans (table_event_average r c _ X)

lemma exactPrefix_failure
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : PublishedInputs.FiniteCheeger (GridBoundary.Grid (I := Fin q) (4*d^8)))
    (htotal : (∑ i,r i)=∑ j,c j) (N : ℕ) :
    (ExactCoreProgram.prefixExperiment (List.ofFn r,List.ofFn c) N).mean
      (fun o => if o=none then 1 else 0)≤(1/(2:ℚ)^D)*(1/2:ℚ)^N := by
  rw [ExactCoreProgram.prefix_mean,exactPrecision_ofFn,Experiment.mean_map]
  have hz : (exactOrdinary (List.ofFn r,List.ofFn c)).mean
      (fun a => if some a=none then (1:ℚ) else 0)=0 := by
    rw [exactOrdinary_mean r c htotal]
    simp only [reduceCtorEq,ite_false,average_const]
  rw [hz,mul_zero,zero_add]
  exact mul_le_mul_of_nonneg_left (correctionPrefix_failure r c hPL hCheeger htotal N)
    (by positivity)

lemma exactPrefix_limit
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : PublishedInputs.FiniteCheeger (GridBoundary.Grid (I := Fin q) (4*d^8)))
    (htotal : (∑ i,r i)=∑ j,c j) (X : Table r c) :
    Filter.Tendsto (fun N => ((ExactCoreProgram.prefixExperiment (List.ofFn r,List.ofFn c) N).mean
      (fun o => if o=some (matrixCode X.val) then 1 else 0):ℝ))
      Filter.atTop (nhds ((Fintype.card (Table r c):ℝ)⁻¹)) := by
  have ht := corrected_prefix_limit r c hPL hCheeger htotal X
  convert ht using 1
  funext N
  rw [ExactCoreProgram.prefix_mean,exactPrecision_ofFn,Experiment.mean_map]
  simp only [Option.some.injEq,exactOrdinary_mass r c htotal,Rat.cast_add,Rat.cast_mul,
    Rat.cast_sub,Rat.cast_div,Rat.cast_pow,Rat.cast_one,Rat.cast_ofNat]

end
end ContingencyTables.SmallGraphProfiles

end OAI
