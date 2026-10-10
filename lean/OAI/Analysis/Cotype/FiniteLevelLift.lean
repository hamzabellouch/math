import OAI.Analysis.Cotype.L2MomentLifts
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace OAI

noncomputable section
open scoped BigOperators
open WithLp
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem rademacherSum_L2_le {m : ℕ} (z : Fin m → X) :
    cubeL2 X (rademacherSum X z) ≤ Real.sqrt m * Real.sqrt (∑ i, ‖z i‖^2) := by
  apply cubeL2_bound (by positivity)
  intro ε
  calc
    _ ≤ ∑ i, ‖sign (ε i) • z i‖ := norm_sum_le _ _
    _ = ∑ i, ‖z i‖ := by
      apply Finset.sum_congr rfl
      intro i _
      cases h : ε i <;> simp [sign]
    _ ≤ _ := by
      simpa using Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
        (fun _ : Fin m => (1 : ℝ)) (fun i => ‖z i‖)

theorem exists_finiteLevel_lift [CompleteSpace X] {m : ℕ} {D : ℝ}
    (hD : FixedCotypeBound (X →L[ℝ] ℝ) m D) (hDp : 0 < D)
    (E : Submodule ℝ X) [FiniteDimensional ℝ E] :
    ∃ F : Submodule ℝ X, E ≤ F ∧ FiniteDimensional ℝ F ∧
      ∀ z : Fin m → E, ∃ H : Cube m → F,
        (∀ i, moment X (fun ε => (H ε : X)) i = (z i : X)) ∧
        cubeL2 F H ≤ 3 * D * Real.sqrt (∑ i, ‖z i‖^2) := by
  classical
  let Z := PiLp 2 (fun _ : Fin m => E)
  let η := D / (Real.sqrt m + 1)
  have hη : 0 < η := div_pos hDp (by positivity)
  obtain ⟨s, hs, hsf, hcover⟩ :=
    (isCompact_closedBall (0 : Z) 1).finite_cover_balls hη
  let : Fintype s := hsf.fintype
  have hlift (a : s) : ∃ H : Cube m → X,
      (∀ i, moment X H i = ((a.val i : E) : X)) ∧ cubeL2 X H ≤ 2 * D := by
    obtain ⟨H, hH, hn⟩ := exists_L2_moment_lift hD hDp (fun i => ((a.val i : E) : X))
    refine ⟨H, hH, hn.trans ?_⟩
    have ha : ‖a.val‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hs a.property
    have hn' : Real.sqrt (∑ i, ‖((a.val i : E) : X)‖^2) = ‖a.val‖ := by
      rw [PiLp.norm_eq_of_L2]; rfl
    rw [hn']
    exact mul_le_of_le_one_right (by positivity) ha
  choose lifts hmom hnorm using hlift
  let values : Set X := Set.range (fun p : s × Cube m => lifts p.1 p.2)
  let F := E ⊔ Submodule.span ℝ values
  have hEF : E ≤ F := le_sup_left
  have : FiniteDimensional ℝ (Submodule.span ℝ values) :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
  have hunit (z : Z) (hz : ‖z‖ ≤ 1) : ∃ H : Cube m → X,
      (∀ ε, H ε ∈ F) ∧ (∀ i, moment X H i = ((z i : E) : X)) ∧ cubeL2 X H ≤ 3 * D := by
    have hzmem : z ∈ Metric.closedBall (0 : Z) 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hz
    obtain ⟨a, ha, hza⟩ := Set.mem_iUnion₂.mp (hcover hzmem)
    let a' : s := ⟨a, ha⟩
    let e : Fin m → X := fun i => ((z i - a i : E) : X)
    refine ⟨fun ε => lifts a' ε + rademacherSum X e ε, ?_, ?_, ?_⟩
    · intro ε
      apply F.add_mem
      · exact (show Submodule.span ℝ values ≤ F from le_sup_right)
          (Submodule.subset_span ⟨(a', ε), rfl⟩)
      · apply hEF
        exact E.sum_mem (fun i _ => E.smul_mem _ (E.sub_mem (z i).property (a i).property))
    · intro i
      have he := moment_rademacherSum X e i
      simpa only [moment, average, smul_add, Finset.sum_add_distrib] using
        show moment X (fun ε => lifts a' ε) i + moment X (rademacherSum X e) i = ((z i : E) : X) by
          rw [hmom, he]; dsimp [e, a']; simp
    · have heN : Real.sqrt (∑ i, ‖e i‖^2) = ‖z - a‖ := by
        rw [PiLp.norm_eq_of_L2]; rfl
      have hdist : ‖z - a‖ < η := by
        change dist z a < η at hza
        rwa [show dist z a = ‖z-a‖ from dist_eq_norm z a] at hza
      have hηbound : Real.sqrt m * η ≤ D := by
        have heq : η * (Real.sqrt m + 1) = D := by dsimp [η]; field_simp
        nlinarith [Real.sqrt_nonneg (m : ℝ)]
      have hr : cubeL2 X (rademacherSum X e) ≤ D := by
        calc
          _ ≤ Real.sqrt m * ‖z-a‖ := by simpa [heN] using rademacherSum_L2_le e
          _ ≤ Real.sqrt m * η := mul_le_mul_of_nonneg_left hdist.le (Real.sqrt_nonneg _)
          _ ≤ D := hηbound
      exact (cubeL2_add_le _ _).trans (by linarith [hnorm a'])
  refine ⟨F, hEF, inferInstance, fun z => ?_⟩
  let z' : Z := toLp 2 z
  by_cases hz : z' = 0
  · have hzval (i : Fin m) : z i = 0 := congrArg (fun t : Z => t i) hz
    refine ⟨fun _ => 0, ?_, ?_⟩
    · intro i; simp [moment, average, hzval]
    · simp [cubeL2, average, hzval]
  · have hzp : 0 < ‖z'‖ := norm_pos_iff.mpr hz
    obtain ⟨H, hHF, hHm, hHn⟩ := hunit (‖z'‖⁻¹ • z') (by
      simp [norm_smul, Real.norm_eq_abs, abs_of_pos hzp, hzp.ne'])
    refine ⟨fun ε => ⟨‖z'‖ • H ε, F.smul_mem _ (hHF ε)⟩, ?_, ?_⟩
    · intro i
      change moment X (fun ε => ‖z'‖ • H ε) i = _
      have he : moment X (fun ε => ‖z'‖ • H ε) i = ‖z'‖ • moment X H i := by
        simp [moment, average, Finset.smul_sum, smul_smul, mul_comm, mul_assoc]
      rw [he, hHm]
      change ‖z'‖ • (‖z'‖⁻¹ • ((z i : E) : X)) = _
      rw [smul_smul, mul_inv_cancel₀ hzp.ne', one_smul]
    · have he : cubeL2 F (fun ε => (⟨‖z'‖ • H ε, F.smul_mem _ (hHF ε)⟩ : F)) =
          ‖z'‖ * cubeL2 X H := by
        change cubeL2 X (fun ε => ‖z'‖ • H ε) = _
        rw [cubeL2_smul, abs_of_nonneg (norm_nonneg _)]
      rw [he]
      have hn : ‖z'‖ = Real.sqrt (∑ i, ‖z i‖^2) := PiLp.norm_eq_of_L2 _
      nlinarith [mul_le_mul_of_nonneg_left hHn (norm_nonneg z')]

end Cotype

end

end OAI
