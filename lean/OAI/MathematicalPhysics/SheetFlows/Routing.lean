import Mathlib
import OAI.MathematicalPhysics.SheetFlows.ShearCore

namespace OAI

/-! SheetFlows routing. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Solenoidal

@[simp] theorem StationaryPulse.apply_of_field_zero (p : StationaryPulse) {x : Space}
    (h : p.field x = 0) : p.apply x = x := by
  rw [StationaryPulse.apply, h, add_zero]

@[simp] theorem StationaryPulse.scale_apply_of_field_zero (p : StationaryPulse) (c : ℝ)
    {x : Space} (h : p.field x = 0) : (p.scale c).apply x = x := by
  apply StationaryPulse.apply_of_field_zero
  rw [StationaryPulse.scale_field, h, smul_zero]

theorem verticalPulse_apply (d : Collar) (R : Rectangle) (hR : R.inCodingSquare)
    {s : ℝ} (hs : s ∈ Set.Icc 0 4) {y : Plane} (hy : y ∈ R.carrier) (z c : ℝ) :
    ((verticalPulse d R hR s).scale c).apply (lifted s z y) = lifted s (z+c) y := by
  rw [StationaryPulse.apply, StationaryPulse.scale_field, verticalPulse_own d R hR hs hy]
  ext i; fin_cases i <;> simp [lifted, basis]

def evacuateProgram (d : Collar) (R : Rectangle) (hR : R.inCodingSquare) :
    List StationaryPulse :=
  [(verticalPulse d R hR 0).scale 3] ++ travelProgram d ![4,0] ++
    [(verticalPulse d R hR 4).scale (-3)]

theorem evacuateProgram_on (d : Collar) (R : Rectangle) (hR : R.inCodingSquare)
    {y : Plane} (hy : y ∈ R.carrier) :
    runProgram (evacuateProgram d R hR) (lifted 0 2 y) = lifted 4 2 y := by
  have h₁ := verticalPulse_apply d R hR (s := 0) (by norm_num) hy 2 3
  have h₂ := verticalPulse_apply d R hR (s := 4) (by norm_num) hy 5 (-3)
  norm_num only at h₁ h₂
  simp only [evacuateProgram, runProgram_append, runProgram_cons, runProgram_nil, h₁]
  rw [show runProgram (travelProgram d ![4,0]) (lifted 0 5 y) = lifted 4 5 y by
    simp only [lifted, travelProgram_on, Matrix.cons_val_zero, Matrix.cons_val_one, add_zero]]
  exact h₂

theorem evacuateProgram_off_input {N : ℕ} (d : Collar) (R : Fin N → Rectangle)
    (hR : ∀ i, (R i).inCodingSquare) (hs : Rectangle.CollarSeparated R d.size)
    {i j : Fin N} (hij : i ≠ j) {y : Plane} (hy : y ∈ (R j).carrier) :
    runProgram (evacuateProgram d (R i) (hR i)) (lifted 0 2 y) = lifted 0 2 y := by
  have h₀ := verticalPulse_off_same d R hR hs hij (s := 0) (by norm_num) hy 2
  have h₄ := verticalPulse_off_far d (R i) (R j) (hR i) (hR j)
    (s := 4) (t := 0) (by norm_num) (by norm_num) (by norm_num) hy 2
  simp only [evacuateProgram, runProgram_append, runProgram_cons, runProgram_nil,
    StationaryPulse.scale_apply_of_field_zero _ _ h₀,
    travelProgram_off d _ _ (by rfl : (lifted 0 2 y) 2 = 2),
    StationaryPulse.scale_apply_of_field_zero _ _ h₄]

theorem evacuateProgram_off_output {N : ℕ} (d : Collar) (R : Fin N → Rectangle)
    (hR : ∀ i, (R i).inCodingSquare) (hs : Rectangle.CollarSeparated R d.size)
    {i j : Fin N} (hij : i ≠ j) {y : Plane} (hy : y ∈ (R j).carrier) :
    runProgram (evacuateProgram d (R i) (hR i)) (lifted 4 2 y) = lifted 4 2 y := by
  have h₀ := verticalPulse_off_far d (R i) (R j) (hR i) (hR j)
    (s := 0) (t := 4) (by norm_num) (by norm_num) (by norm_num) hy 2
  have h₄ := verticalPulse_off_same d R hR hs hij (s := 4) (by norm_num) hy 2
  simp only [evacuateProgram, runProgram_append, runProgram_cons, runProgram_nil,
    StationaryPulse.scale_apply_of_field_zero _ _ h₀,
    travelProgram_off d _ _ (by rfl : (lifted 4 2 y) 2 = 2),
    StationaryPulse.scale_apply_of_field_zero _ _ h₄]

def instructionProgram {N : ℕ} (d : Collar) (D : SheetData N) (i : Fin N) :
    List StationaryPulse :=
  [(verticalPulse d (D.source i) (D.source_inside i) 4).scale 3] ++
  travelProgram d ![1-(D.source i).center 0,6-(D.source i).center 1] ++
  processingProgram d (D.ratio i 0) (D.ratio i 1) ++
  travelProgram d ![(D.target i).center 0-5,(D.target i).center 1-6] ++
  [(verticalPulse d (D.target i) (D.target_inside i) 0).scale (-3)]

theorem SheetData.image_mem {N : ℕ} (D : SheetData N) (i : Fin N)
    {y : Plane} (hy : y ∈ (D.source i).carrier) :
    diagonalMap (D.source i) (D.target i) (D.ratio i) y ∈ (D.target i).carrier := by
  rw [← D.image_eq i]
  exact Set.mem_image_of_mem _ hy

theorem instructionProgram_on {N : ℕ} (d : Collar) (D : SheetData N) (i : Fin N)
    {y : Plane} (hy : y ∈ (D.source i).carrier) :
    runProgram (instructionProgram d D i) (lifted 4 2 y) =
      lifted 0 2 (diagonalMap (D.source i) (D.target i) (D.ratio i) y) := by
  let r := y 0 - (D.source i).center 0
  let s := y 1 - (D.source i).center 1
  have hr : |r| ≤ 1/2 := (D.source i).offset_bound (D.source_inside i) hy 0
  have hs : |s| ≤ 1/2 := (D.source i).offset_bound (D.source_inside i) hy 1
  have hlr : |(D.ratio i 0:ℝ)*r| ≤ 1/2 := D.scaled_offset_bound i hy 0
  have hms : |(D.ratio i 1:ℝ)*s| ≤ 1/2 := D.scaled_offset_bound i hy 1
  have hl : (D.ratio i 0:ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast D.ratio_positive i 0)
  have hm : (D.ratio i 1:ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast D.ratio_positive i 1)
  have hlift := verticalPulse_apply d (D.source i) (D.source_inside i) (s := 4)
    (by norm_num) hy 2 3
  norm_num only at hlift
  have hgo : runProgram (travelProgram d ![1-(D.source i).center 0,6-(D.source i).center 1])
      (lifted 4 5 y) = ![5+r,6+s,5] := by
    rw [lifted, travelProgram_on]
    ext j; fin_cases j <;> simp [r,s] <;> ring
  have hback : runProgram (travelProgram d ![(D.target i).center 0-5,(D.target i).center 1-6])
      ![5+(D.ratio i 0:ℝ)*r,6+(D.ratio i 1:ℝ)*s,5] =
      lifted 0 5 (diagonalMap (D.source i) (D.target i) (D.ratio i) y) := by
    rw [travelProgram_on]
    ext j; fin_cases j <;> simp [r,s,lifted,diagonalMap] <;> ring
  have hdrop := verticalPulse_apply d (D.target i) (D.target_inside i) (s := 0)
    (by norm_num) (D.image_mem i hy) 5 (-3)
  norm_num only at hdrop
  simp only [instructionProgram, runProgram_append, runProgram_cons, runProgram_nil,
    hlift, hgo, processingProgram_on d hl hm hr hs hlr hms, hback, hdrop]

theorem instructionProgram_off_input {N : ℕ} (d : Collar) (D : SheetData N)
    (hsource : Rectangle.CollarSeparated D.source d.size)
    {i j : Fin N} (hij : i ≠ j) {y : Plane} (hy : y ∈ (D.source j).carrier) :
    runProgram (instructionProgram d D i) (lifted 4 2 y) = lifted 4 2 y := by
  have h₁ := verticalPulse_off_same d D.source D.source_inside hsource hij
    (s := 4) (by norm_num) hy 2
  have h₂ := verticalPulse_off_far d (D.target i) (D.source j)
    (D.target_inside i) (D.source_inside j) (s := 0) (t := 4)
    (by norm_num) (by norm_num) (by norm_num) hy 2
  have hx : (lifted 4 2 y) 1 ∈ Set.Icc 2 3 :=
    (D.source j).point_bounds (D.source_inside j) hy 1
  have hz : (lifted 4 2 y) 2 = 2 := rfl
  simp only [instructionProgram, runProgram_append, runProgram_cons, runProgram_nil,
    StationaryPulse.scale_apply_of_field_zero _ _ h₁, travelProgram_off d _ _ hz,
    processingProgram_off d _ _ _ hx hz, StationaryPulse.scale_apply_of_field_zero _ _ h₂]

theorem instructionProgram_off_output {N : ℕ} (d : Collar) (D : SheetData N)
    (htarget : Rectangle.CollarSeparated D.target d.size)
    {i j : Fin N} (hij : i ≠ j) {y : Plane} (hy : y ∈ (D.target j).carrier) :
    runProgram (instructionProgram d D i) (lifted 0 2 y) = lifted 0 2 y := by
  have h₁ := verticalPulse_off_far d (D.source i) (D.target j)
    (D.source_inside i) (D.target_inside j) (s := 4) (t := 0)
    (by norm_num) (by norm_num) (by norm_num) hy 2
  have h₂ := verticalPulse_off_same d D.target D.target_inside htarget hij
    (s := 0) (by norm_num) hy 2
  have hx : (lifted 0 2 y) 1 ∈ Set.Icc 2 3 :=
    (D.target j).point_bounds (D.target_inside j) hy 1
  have hz : (lifted 0 2 y) 2 = 2 := rfl
  simp only [instructionProgram, runProgram_append, runProgram_cons, runProgram_nil,
    StationaryPulse.scale_apply_of_field_zero _ _ h₁, travelProgram_off d _ _ hz,
    processingProgram_off d _ _ _ hx hz, StationaryPulse.scale_apply_of_field_zero _ _ h₂]

theorem runProgram_flatMap_fixed {ι : Type*} (l : List ι)
    (P : ι → List StationaryPulse) (a : Space)
    (h : ∀ i ∈ l, runProgram (P i) a = a) :
    runProgram (l.flatMap P) a = a := by
  induction l with
  | nil => rfl
  | cons i l ih =>
      rw [List.flatMap_cons, runProgram_append, h i (by simp)]
      exact ih (fun j hj => h j (by simp [hj]))

theorem runProgram_separate_branches {ι A : Type*} (l : List ι) (hl : l.Nodup)
    (P : ι → List StationaryPulse) (domain : ι → Set A)
    (input output : ι → A → Space)
    (hown : ∀ i a, a ∈ domain i → runProgram (P i) (input i a) = output i a)
    (hin : ∀ i j, i ≠ j → ∀ a ∈ domain j,
      runProgram (P i) (input j a) = input j a)
    (hout : ∀ i j, i ≠ j → ∀ a ∈ domain j,
      runProgram (P i) (output j a) = output j a) :
    ∀ i ∈ l, ∀ a ∈ domain i, runProgram (l.flatMap P) (input i a) = output i a := by
  classical
  induction l with
  | nil => simp
  | cons j l ih =>
      rcases List.nodup_cons.mp hl with ⟨hjl,hl⟩
      intro i hi a ha
      rw [List.flatMap_cons, runProgram_append]
      rcases List.mem_cons.mp hi with rfl | hi
      · rw [hown i a ha]
        exact runProgram_flatMap_fixed l P (output i a) (fun k hk =>
          hout k i (fun h => hjl (h ▸ hk)) a ha)
      · have hji : j ≠ i := fun h => hjl (h ▸ hi)
        rw [hin j i hji a ha]
        exact ih hl i hi a ha

def sheetProgram {N : ℕ} (d : Collar) (D : SheetData N) : List StationaryPulse :=
  (List.finRange N).flatMap (fun i => evacuateProgram d (D.source i) (D.source_inside i)) ++
  (List.finRange N).flatMap (instructionProgram d D)

theorem sheetProgram_on {N : ℕ} (d : Collar) (D : SheetData N)
    (hsource : Rectangle.CollarSeparated D.source d.size)
    (htarget : Rectangle.CollarSeparated D.target d.size)
    (i : Fin N) {y : Plane} (hy : y ∈ (D.source i).carrier) :
    runProgram (sheetProgram d D) (sheet y) =
      sheet (diagonalMap (D.source i) (D.target i) (D.ratio i) y) := by
  have hev := runProgram_separate_branches (List.finRange N) (List.nodup_finRange N)
    (fun i => evacuateProgram d (D.source i) (D.source_inside i))
    (fun i => (D.source i).carrier) (fun _ => lifted 0 2) (fun _ => lifted 4 2)
    (fun i _ hy => evacuateProgram_on d (D.source i) (D.source_inside i) hy)
    (fun _ _ hij _ hj => evacuateProgram_off_input d D.source D.source_inside hsource hij hj)
    (fun _ _ hij _ hj => evacuateProgram_off_output d D.source D.source_inside hsource hij hj)
    i (List.mem_finRange i) y hy
  have hop := runProgram_separate_branches (List.finRange N) (List.nodup_finRange N)
    (instructionProgram d D) (fun i => (D.source i).carrier) (fun _ => lifted 4 2)
    (fun i y => lifted 0 2 (diagonalMap (D.source i) (D.target i) (D.ratio i) y))
    (fun i _ hy => instructionProgram_on d D i hy)
    (fun _ _ hij _ hj => instructionProgram_off_input d D hsource hij hj)
    (fun _ j hij _ hj => instructionProgram_off_output d D htarget hij (D.image_mem j hj))
    i (List.mem_finRange i) y hy
  have hs (y : Plane) : sheet y = lifted 0 2 y := by simp [sheet,lifted]
  rw [sheetProgram, runProgram_append, hs, hev, hop, hs]

end Solenoidal
end

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Solenoidal

theorem sheet_theorem_analytic {N : ℕ} (D : SheetData N) (ν : ℝ) (hν : 0 < ν) :
    ∃ f u : Field, ∃ X : ℝ → Space → Space,
      SpatiallyPeriodic f ∧ SpatiallyPeriodic u ∧ Smooth f ∧ Smooth u ∧
      MeanZero f ∧ DivergenceFree f ∧ OnePeriodic f ∧
      ClassicalSolution ν f u (0 : Pressure) ∧
      (∀ v : Field, ∀ p : Pressure, ClassicalSolution ν f v p →
        ∀ t, 0 ≤ t → ∀ x, v t x = u t x ∧ p t x = 0) ∧
      MaterialFlow u X ∧
      (∀ i : Fin N, ∀ y ∈ (D.source i).carrier,
        toTorus (X 1 (sheet y)) =
          toTorus (sheet (diagonalMap (D.source i) (D.target i) (D.ratio i) y))) ∧
      IntegerCollars u ∧ (∀ t x, advection u t x = 0) ∧
      (∀ α, ∃ B : ℝ, 0 ≤ B ∧ ∀ z, ‖mixedDerivative f α z‖ ≤ B) ∧
      (∀ α, ∃ B : ℝ, 0 ≤ B ∧ ∀ z, ‖mixedDerivative u α z‖ ≤ B) ∧
      (N = 0 → f = 0 ∧ u = 0) := by
  cases N with
  | zero =>
      refine ⟨0,0,fun _ a => a, zero_spatially_periodic, zero_spatially_periodic,
        zero_smooth, zero_smooth, zero_mean_zero, zero_divergence_free,
        zero_one_periodic, zero_classical_solution ν, ?_, zero_material_flow,
        ?_, zero_integer_collars, ?_, ?_, ?_, by simp⟩
      · intro v p hv t ht x
        exact (zero_classical_solution ν).unique hv hν.le ht x
      · intro i
        exact Fin.elim0 i
      · intro t x
        simp
      · exact zero_effective_bounds.bounded
      · exact zero_effective_bounds.bounded
  | succ N =>
      obtain ⟨δ,hδ,hδsmall,hs,ht⟩ := D.exists_rational_collar
      have hδsmall' : (δ:ℝ) ≤ 1/10 := by
        have hc : δ*10 ≤ 1 := (le_div_iff₀ (by norm_num)).mp hδsmall
        have hc' : (δ:ℝ)*10 ≤ 1 := by exact_mod_cast hc
        linarith
      let d : Collar := ⟨(δ:ℝ), by exact_mod_cast hδ, hδsmall'⟩
      obtain ⟨f,u,X,hfsp,husp,hfs,hus,hmean,hdiv,hper,hsol,huniq,hflow,hend,hcol,hadv,hfb,hub⟩ :=
        program_realization (sheetProgram d D) ν hν.le
      refine ⟨f,u,X,hfsp,husp,hfs,hus,hmean,hdiv,hper,hsol,huniq,hflow,?_,hcol,hadv,hfb,hub,?_⟩
      · intro i y hy
        rw [hend, sheetProgram_on d D hs ht i hy]
      · simp

end Solenoidal
end

end OAI
