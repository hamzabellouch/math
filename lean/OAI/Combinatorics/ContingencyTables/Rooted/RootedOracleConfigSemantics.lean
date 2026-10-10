import OAI.Combinatorics.ContingencyTables.Rooted.RootedOracleConfigProgram

namespace OAI

/-! # Exact schedules in the computed weight-oracle configuration -/

namespace ContingencyTables.RootedOracleConfigProgram

open MatchingFPRAS CompanionFactorialApplication CompanionOracleDensity GridBoundary
open scoped Classical
noncomputable section
variable {m n : ℕ}

lemma scalar_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : TreeFraction.Fraction)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (reserve : List Bool) (e : ScalarScheduleProgram.Expr) :
    scalar e (data A C K j xi z v reserve)=e.eval [A.d,K,rationalHeight A C,j] := by
  rw [scalar,fields_data]

lemma timeInput_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : TreeFraction.Fraction)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) :
    timeInput (data A C K j xi z v reserve)=
      (2*(10000*A.d^2*K)^2,rationalHeight A C+A.d*K+2) := by
  simp only [timeInput,scalar_data,mixing,allowance,dim,grid,height,
    ScalarScheduleProgram.Expr.eval_power,ScalarScheduleProgram.Expr.eval,List.getD_cons_zero,List.getD_cons_succ]

lemma correction_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : TreeFraction.Fraction)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) :
    TreeFraction.val (correction (data A C K j xi z v reserve))=
      correctionTheta (innerTolerance (TreeFraction.val xi/2) j) := by
  rw [correction,TreeFraction.div_val,inner_data]
  simp only [TreeFraction.val,Nat.cast_ofNat,Nat.cast_one,div_one,correctionTheta,Rat.cast_div,Rat.cast_ofNat]

lemma samples_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : TreeFraction.Fraction)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) :
    samples (data A C K j xi z v reserve)=sampleCount j (innerTolerance (TreeFraction.val xi/2) j) 1 := by
  unfold samples
  rw [CountingOracleScheduleProgram.sampleCount_val,inner_data]
  simp only [data,TreeFraction.val,Nat.cast_one,div_one]

lemma ratioTime_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : TreeFraction.Fraction)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) :
    ratioTime (data A C K j xi z v reserve)=
      oracleTime A C K 1 (innerTolerance (TreeFraction.val xi/2) j) := by
  rw [ratioTime,timeInput_data,CountingOracleScheduleProgram.oracleTime_instance,inner_data]

lemma correctionTime_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : TreeFraction.Fraction)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) :
    correctionTime (data A C K j xi z v reserve)=
      oracleTime A C K 1 (correctionTheta (innerTolerance (TreeFraction.val xi/2) j)) := by
  rw [correctionTime,timeInput_data,CountingOracleScheduleProgram.oracleTime_instance,correction_data]

lemma offsetAccuracy_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : TreeFraction.Fraction)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) :
    offsetAccuracy (data A C K j xi z v reserve)=
      CompanionOracleDensity.offsetAccuracy A (innerTolerance (TreeFraction.val xi/2) j) := by
  rw [offsetAccuracy,CountingOracleScheduleProgram.offsetAccuracy_val,inner_data,scalar_data]
  rfl

lemma context_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : TreeFraction.Fraction)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) :
    context (data A C K j xi z v reserve)=
      RootedEstimatorMedianProgram.context A C K j (TreeFraction.val xi) z v := by
  unfold context output schedule
  rw [samples_data,ratioTime_data,correctionTime_data,offsetAccuracy_data]
  rfl

lemma output_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : TreeFraction.Fraction)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) :
    output (data A C K j xi z v reserve)=
      RootedLabelWeightProgram.config A C K j (TreeFraction.val xi) (TreeFraction.val xi) z v
        (reserve.take (rootDegree (data A C K j xi z v reserve)))
        (reserve.take (depth (data A C K j xi z v reserve))) := by
  have hc := context_data A C K j xi z v reserve
  have hr := repeats_data A C K j xi z v reserve
  change ((context _,repeats _),markers _)=_
  rw [hc,hr]
  rfl

lemma rootDegree_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : TreeFraction.Fraction)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) :
    rootDegree (data A C K j xi z v reserve)=
      PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (TreeFraction.val xi/2) j)) := by
  rw [rootDegree,CountingOracleScheduleProgram.ceiling_val,TreeFraction.div_val,inner_data]
  unfold PowerOfTwoApproximation.rootDegree roundingTolerance
  congr 1
  simp only [TreeFraction.val,Nat.cast_ofNat,Nat.cast_one,div_one,div_div_eq_mul_div]
  ring

lemma depth_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : TreeFraction.Fraction)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) :
    depth (data A C K j xi z v reserve)=
      PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (TreeFraction.val xi/2) j)) := by
  rw [depth,rootDegree_data]
  rfl

lemma marker_lengths (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : TreeFraction.Fraction)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool)
    (hdegree : rootDegree (data A C K j xi z v reserve) ≤ reserve.length)
    (hdepth : depth (data A C K j xi z v reserve) ≤ reserve.length) :
    (markers (data A C K j xi z v reserve)).1.length=
        PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (TreeFraction.val xi/2) j)) ∧
    (markers (data A C K j xi z v reserve)).2.length=
        PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (TreeFraction.val xi/2) j)) := by
  simp only [markers,data,List.length_take]
  exact ⟨(min_eq_left hdegree).trans (rootDegree_data A C K j xi z v reserve),
    (min_eq_left hdepth).trans (depth_data A C K j xi z v reserve)⟩

lemma wordWidth_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : TreeFraction.Fraction)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) :
    wordWidth (data A C K j xi z v reserve)=
      medianEstimatorBits A C K j (TreeFraction.val xi) (TreeFraction.val xi) := by
  rw [wordWidth,contextWidth,context_data,repeats_data,
    RootedEstimatorMedianProgram.context,RootedEstimatorWordProgram.scheduledWordWidth]
  rfl

end
end ContingencyTables.RootedOracleConfigProgram

end OAI
