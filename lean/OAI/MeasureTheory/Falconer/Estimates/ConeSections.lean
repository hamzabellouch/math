import OAI.MeasureTheory.Falconer.Fourier.ConeIntegration
import OAI.MeasureTheory.Falconer.Angular.GnomonicCone

namespace OAI

/-! # Fiber volumes of the Euclidean cone over a gnomonic chart -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal Pointwise

noncomputable def euclideanCons {n : ℕ} (r : ℝ) (y : Space n) : Space (n+1) :=
  WithLp.toLp 2 (Fin.cons r (WithLp.ofLp y))

@[simp] theorem euclideanCons_zero {n : ℕ} (r : ℝ) (y : Space n) : euclideanCons r y 0 = r := rfl
@[simp] theorem euclideanCons_succ {n : ℕ} (r : ℝ) (y : Space n) (i : Fin n) :
    euclideanCons r y i.succ = y i := by simp [euclideanCons]

@[simp] theorem euclideanCons_self {n : ℕ} (z : Space (n+1)) :
    euclideanCons (z 0) (euclideanTail z) = z := by
  apply PiLp.ext
  intro i
  refine Fin.cases rfl (fun _ => rfl) i

theorem euclideanCons_continuous (n : ℕ) : Continuous (fun z : ℝ × Space n => euclideanCons z.1 z.2) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin (n+1) => ℝ)).comp
  apply continuous_pi
  intro i
  refine Fin.cases continuous_fst (fun j => ?_) i
  exact (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) j).comp continuous_snd

theorem euclideanCons_smul {n : ℕ} (r : ℝ) (x : Space n) :
    euclideanCons r (r • x) = gnomonicConePoint r x := by
  apply PiLp.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp

theorem gnomonicCone_section_positive {n : ℕ} (A : Set (Space n)) (r : ℝ) (hr : 0 < r) :
    {y : Space n | euclideanCons r y ∈ gnomonicCone A} =
      r • {x : Space n | x ∈ A ∧ r < ‖northLift x‖⁻¹} := by
  ext y
  constructor
  · intro hy
    refine ⟨r⁻¹ • y,?_,smul_inv_smul₀ hr.ne' y⟩
    apply (gnomonicConePoint_mem_iff A r hr (r⁻¹ • y)).mp
    rw [← euclideanCons_smul,smul_inv_smul₀ hr.ne']
    exact hy
  · rintro ⟨x,hx,rfl⟩
    change euclideanCons r (r • x) ∈ gnomonicCone A
    rw [euclideanCons_smul]
    exact (gnomonicConePoint_mem_iff A r hr x).mpr hx

theorem gnomonicCone_section_volume {n : ℕ} (A : Set (Space n)) (r : ℝ) (hr : 0 < r) :
    volume {y : Space n | euclideanCons r y ∈ gnomonicCone A} =
      ENNReal.ofReal (r^n)*volume {x : Space n | x ∈ A ∧ r < ‖northLift x‖⁻¹} := by
  rw [gnomonicCone_section_positive A r hr,Measure.addHaar_smul_of_nonneg volume hr.le]
  simp [Space]

theorem gnomonicCone_section_nonpositive {n : ℕ} (A : Set (Space n)) (r : ℝ) (hr : r ≤ 0) :
    {y : Space n | euclideanCons r y ∈ gnomonicCone A} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro y hy
  rw [gnomonicCone_eq] at hy
  exact (not_lt.mpr hr) hy.1

theorem gnomonicCone_volume_slices {n : ℕ} {A : Set (Space n)} (hA : MeasurableSet A) :
    volume (gnomonicCone A) = ∫⁻ r : ℝ,
      volume {y : Space n | euclideanCons r y ∈ gnomonicCone A} := by
  let F : ℝ × Space n → ℝ≥0∞ := fun z => (gnomonicCone A).indicator (fun _ => (1 : ℝ≥0∞)) (euclideanCons z.1 z.2)
  have hC := gnomonicCone_measurable hA
  have hF : Measurable F := (measurable_const.indicator hC).comp (euclideanCons_continuous n).measurable
  calc
    volume (gnomonicCone A) = ∫⁻ z : Space (n+1), F (z 0,euclideanTail z) := by
      simp only [F,euclideanCons_self]
      exact (lintegral_indicator_one hC).symm
    _ = ∫⁻ r : ℝ, ∫⁻ y : Space n, F (r,y) := lintegral_euclidean_coordinate_split F hF
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards with r
      have hm : MeasurableSet {y : Space n | euclideanCons r y ∈ gnomonicCone A} :=
        hC.preimage ((euclideanCons_continuous n).comp (continuous_const.prodMk continuous_id)).measurable
      change (∫⁻ y : Space n, (gnomonicCone A).indicator (fun _ => (1 : ℝ≥0∞)) (euclideanCons r y)) = _
      have he : (fun y : Space n => (gnomonicCone A).indicator (fun _ => (1 : ℝ≥0∞)) (euclideanCons r y)) =
          {y : Space n | euclideanCons r y ∈ gnomonicCone A}.indicator (fun _ => (1 : ℝ≥0∞)) := by
        funext y
        by_cases hy : euclideanCons r y ∈ gnomonicCone A <;> simp [hy]
      rw [he]
      exact lintegral_indicator_one hm

end Falconer

end OAI
