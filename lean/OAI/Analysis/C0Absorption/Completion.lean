import OAI.Analysis.C0Absorption.Norm

namespace OAI

namespace C0Absorption

open scoped BigOperators NNReal ENNReal
noncomputable section
open Finset

section CompletedSeminorms

open UniformSpace Completion

variable {X : Type*} [SeminormedAddCommGroup X] [NormedSpace ℝ X]

theorem seminorm_lipschitz (q : Seminorm ℝ X) (C : ℝ≥0)
    (h : ∀ x, q x ≤ C * ‖x‖) : LipschitzWith C q := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, dist_eq_norm]
  exact (seminorm_abs_sub_le q x y).trans (h (x - y))

theorem completion_lipschitz {X : Type*} [SeminormedAddCommGroup X] [NormedSpace ℝ X]
    {Y : Type*} [MetricSpace Y] [CompleteSpace Y]
    {f : X → Y} {C : ℝ≥0} (hf : LipschitzWith C f) :
    LipschitzWith C (Completion.extension f) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  induction x, y using Completion.induction_on₂ with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih x y =>
    simpa only [Completion.extension_coe hf.uniformContinuous, Completion.dist_eq] using hf.dist_le_mul x y

def completedSeminorm (q : Seminorm ℝ X) (C : ℝ≥0) (h : ∀ x, q x ≤ C * ‖x‖) :
    Seminorm ℝ (Completion X) :=
  Seminorm.of (Completion.extension q)
    (by
      intro x y
      induction x, y using Completion.induction_on₂ with
      | hp =>
        exact isClosed_le
          (Completion.continuous_extension.comp (continuous_fst.add continuous_snd))
          ((Completion.continuous_extension.comp continuous_fst).add
            (Completion.continuous_extension.comp continuous_snd))
      | ih x y =>
        simpa only [← Completion.coe_add,
          Completion.extension_coe (seminorm_lipschitz q C h).uniformContinuous] using
          map_add_le_add q x y)
    (by
      intro a x
      induction x using Completion.induction_on with
      | hp =>
        exact isClosed_eq
          (Completion.continuous_extension.comp (continuous_const_smul a))
          (continuous_const.mul Completion.continuous_extension)
      | ih x =>
        simpa only [← Completion.coe_smul,
          Completion.extension_coe (seminorm_lipschitz q C h).uniformContinuous] using
          map_smul_eq_mul q a x)

@[simp] theorem completedSeminorm_coe (q : Seminorm ℝ X) (C : ℝ≥0)
    (h : ∀ x, q x ≤ C * ‖x‖) (x : X) : completedSeminorm q C h (x : Completion X) = q x :=
  Completion.extension_coe (seminorm_lipschitz q C h).uniformContinuous x

theorem completedSeminorm_continuous (q : Seminorm ℝ X) (C : ℝ≥0)
    (h : ∀ x, q x ≤ C * ‖x‖) : Continuous (completedSeminorm q C h) :=
  Completion.continuous_extension

theorem completedSeminorm_le (q : Seminorm ℝ X) (C : ℝ≥0)
    (h : ∀ x, q x ≤ C * ‖x‖) (x : Completion X) : completedSeminorm q C h x ≤ C * ‖x‖ := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_le (completedSeminorm_continuous q C h) (by fun_prop)
  | ih x => simpa using h x

end CompletedSeminorms

section SelectedCompletion

open UniformSpace Completion

variable {S : Type*} [MetricSpace S] (L : ℕ → Set (S → ℝ)) (o : S)

def PreSpace (_L : ℕ → Set (S → ℝ)) (_o : S) : Type _ := Molecule S

instance : SeminormedAddCommGroup (PreSpace L o) :=
  (selectedNorm L o).toAddGroupSeminorm.toSeminormedAddCommGroup
instance : NormedSpace ℝ (PreSpace L o) where
  __ : Module ℝ (PreSpace L o) := inferInstanceAs (Module ℝ (Molecule S))
  norm_smul_le a x := by
    change selectedNorm L o (a • x) ≤ ‖a‖ * selectedNorm L o x
    exact (map_smul_eq_mul (selectedNorm L o) a x).le

instance : IsBoundedSMul ℝ (PreSpace L o) :=
  NormedSpace.toIsBoundedSMul (𝕜 := ℝ) (E := PreSpace L o)

def TestSpace := Completion (PreSpace L o)

instance : NormedAddCommGroup (TestSpace L o) :=
  inferInstanceAs (NormedAddCommGroup (Completion (PreSpace L o)))
instance : NormedSpace ℝ (TestSpace L o) :=
  inferInstanceAs (NormedSpace ℝ (Completion (PreSpace L o)))
instance : CompleteSpace (TestSpace L o) :=
  inferInstanceAs (CompleteSpace (Completion (PreSpace L o)))

def toTestSpace : PreSpace L o →L[ℝ] TestSpace L o :=
  (Completion.toComplL : PreSpace L o →L[ℝ] Completion (PreSpace L o))

@[simp] theorem norm_toTestSpace (m : PreSpace L o) :
    ‖toTestSpace L o m‖ = selectedNorm L o m := Completion.norm_coe m

def initialCoordinates (m : PreSpace L o) : lp (fun _ : ℕ => ℝ) 2 :=
  squareVector (selectedCoordinate L) (selectedCoordinate_summable L o) m

theorem initialCoordinates_lipschitz : LipschitzWith 1 (initialCoordinates L o) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  exact squareVector_sub_norm_le (selectedCoordinate L) (selectedCoordinate_summable L o) x y

def normCoordinates : TestSpace L o → lp (fun _ : ℕ => ℝ) 2 :=
  Completion.extension (initialCoordinates L o)

theorem normCoordinates_continuous : Continuous (normCoordinates L o) :=
  Completion.continuous_extension

@[simp] theorem normCoordinates_coe (m : PreSpace L o) :
    normCoordinates L o (toTestSpace L o m) = initialCoordinates L o m :=
  Completion.extension_coe (initialCoordinates_lipschitz L o).uniformContinuous m

theorem normCoordinates_norm (z : TestSpace L o) : ‖normCoordinates L o z‖ = ‖z‖ := by
  induction z using Completion.induction_on with
  | hp => exact isClosed_eq (normCoordinates_continuous L o).norm continuous_norm
  | ih m =>
    change ‖normCoordinates L o (toTestSpace L o m)‖ = ‖toTestSpace L o m‖
    rw [normCoordinates_coe, norm_toTestSpace]
    rfl

theorem selectedCoordinate_le_norm (n : ℕ) (m : PreSpace L o) :
    selectedCoordinate L n m ≤ (1 : ℝ≥0) * ‖m‖ := by
  change selectedCoordinate L n m ≤ (1 : ℝ) * selectedNorm L o m
  rw [one_mul]
  exact coordinate_le_squareSeminorm (selectedCoordinate L) (selectedCoordinate_summable L o) n m

def completedCoordinate (n : ℕ) : Seminorm ℝ (TestSpace L o) :=
  completedSeminorm (X := PreSpace L o) (selectedCoordinate L n) 1
    (selectedCoordinate_le_norm L o n)

theorem completedCoordinate_continuous (n : ℕ) : Continuous (completedCoordinate L o n) :=
  completedSeminorm_continuous _ _ _

@[simp] theorem completedCoordinate_coe (n : ℕ) (m : PreSpace L o) :
    completedCoordinate L o n (toTestSpace L o m) = selectedCoordinate L n m :=
  completedSeminorm_coe _ _ _ m

theorem normCoordinates_apply (z : TestSpace L o) (n : ℕ) :
    normCoordinates L o z n = completedCoordinate L o n z := by
  induction z using Completion.induction_on with
  | hp =>
    exact isClosed_eq
      ((lp.lipschitzWith_one_eval 2 n).continuous.comp (normCoordinates_continuous L o))
      (completedCoordinate_continuous L o n)
  | ih m =>
    change normCoordinates L o (toTestSpace L o m) n =
      completedCoordinate L o n (toTestSpace L o m)
    rw [normCoordinates_coe, completedCoordinate_coe]
    rfl

theorem completedCoordinate_summable (z : TestSpace L o) :
    Summable (fun n => (completedCoordinate L o n z) ^ 2) := by
  have h := (lp.memℓp (normCoordinates L o z)).summable (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs,
    normCoordinates_apply] using h

theorem completedNorm_sq (z : TestSpace L o) :
    ‖z‖ ^ 2 = ∑' n, (completedCoordinate L o n z) ^ 2 := by
  have h := lp.norm_rpow_eq_tsum
    (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) (normCoordinates L o z)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs,
    normCoordinates_norm, normCoordinates_apply] using h

def prePoint (s : S) : PreSpace L o := molecule s o

theorem prePoint_lipschitz : LipschitzWith 1 (prePoint L o) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [dist_eq_norm]
  change selectedNorm L o (molecule s o - molecule t o) ≤ (1 : ℝ) * dist s t
  rw [molecule_sub_molecule, one_mul]
  exact selectedNorm_molecule_le L o s t

theorem prePoint_span : Submodule.span ℝ (Set.range (prePoint L o)) = ⊤ := by
  classical
  apply Submodule.eq_top_iff'.mpr
  intro m
  have heq : m = ∑ s ∈ m.val.support, m.val s • prePoint L o s := molecule_decomposition m o
  rw [heq]
  apply Submodule.sum_mem
  intro s hs
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)

instance [TopologicalSpace.SeparableSpace S] : TopologicalSpace.SeparableSpace (PreSpace L o) := by
  have hsep := (TopologicalSpace.isSeparable_range (prePoint_lipschitz L o).continuous).span (R := ℝ)
  rw [prePoint_span, Submodule.top_coe] at hsep
  exact TopologicalSpace.isSeparable_univ_iff.mp hsep

instance [TopologicalSpace.SeparableSpace S] : TopologicalSpace.SeparableSpace (TestSpace L o) :=
  inferInstanceAs (TopologicalSpace.SeparableSpace (Completion (PreSpace L o)))

def zeta (s : S) : TestSpace L o := toTestSpace L o (prePoint L o s)

@[simp] theorem zeta_base : zeta L o o = 0 := by
  have h : prePoint L o o = (0 : PreSpace L o) := molecule_self o
  rw [zeta, h, map_zero]

theorem zeta_lipschitz : LipschitzWith 1 (zeta L o) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  change dist ((prePoint L o s : PreSpace L o) : Completion (PreSpace L o))
    ((prePoint L o t : PreSpace L o) : Completion (PreSpace L o)) ≤ (1 : ℝ) * dist s t
  rw [Completion.dist_eq]
  exact (prePoint_lipschitz L o).dist_le_mul s t

end SelectedCompletion

end
end C0Absorption

end OAI
