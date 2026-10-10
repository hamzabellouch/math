import Mathlib
import OAI.MathematicalPhysics.SheetFlows.ScheduledForce

namespace OAI

/-! SheetFlows classical regularity. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators

open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace Solenoidal

structure TorusC1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : Space → E) : Prop where
  differentiable : Differentiable ℝ g
  continuous_partial : ∀ j, Continuous (fun x => fderiv ℝ g x (basis j))
  periodic : ∀ x k, g (x + deck k) = g x

theorem TorusC1.of_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : Space → E} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hp : ∀ x k, g (x + deck k) = g x) : TorusC1 g :=
  ⟨hg.differentiable (by simp), fun j => (directional_contDiff hg (basis j)).continuous, hp⟩

theorem TorusC1.const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : E) : TorusC1 (fun _ : Space => c) := by
  refine ⟨differentiable_const c, ?_, fun _ _ => rfl⟩
  intro j
  simpa using (continuous_const : Continuous (fun _ : Space => (0 : E)))

theorem TorusC1.add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g h : Space → E} (hg : TorusC1 g) (hh : TorusC1 h) : TorusC1 (g + h) := by
  refine ⟨hg.differentiable.add hh.differentiable, ?_, ?_⟩
  · intro j
    have he (x : Space) : fderiv ℝ (g + h) x (basis j) =
        fderiv ℝ g x (basis j) + fderiv ℝ h x (basis j) := by
      rw [fderiv_add (hg.differentiable x) (hh.differentiable x)]
      rfl
    simpa only [he] using (hg.continuous_partial j).fun_add (hh.continuous_partial j)
  · intro x k
    simp only [Pi.add_apply, hg.periodic, hh.periodic]

theorem TorusC1.sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g h : Space → E} (hg : TorusC1 g) (hh : TorusC1 h) : TorusC1 (g - h) := by
  refine ⟨hg.differentiable.sub hh.differentiable, ?_, ?_⟩
  · intro j
    have he (x : Space) : fderiv ℝ (g - h) x (basis j) =
        fderiv ℝ g x (basis j) - fderiv ℝ h x (basis j) := by
      rw [fderiv_sub (hg.differentiable x) (hh.differentiable x)]
      rfl
    simpa only [he] using (hg.continuous_partial j).fun_sub (hh.continuous_partial j)
  · intro x k
    simp only [Pi.sub_apply, hg.periodic, hh.periodic]

theorem scalarPartial_mul {g h : Space → ℝ}
    (hg : Differentiable ℝ g) (hh : Differentiable ℝ h) (x : Space) (j : Fin 3) :
    fderiv ℝ (g * h) x (basis j) =
      g x * fderiv ℝ h x (basis j) + h x * fderiv ℝ g x (basis j) := by
  rw [fderiv_mul (hg x) (hh x)]
  rfl

theorem TorusC1.mul {g h : Space → ℝ} (hg : TorusC1 g) (hh : TorusC1 h) :
    TorusC1 (g * h) := by
  refine ⟨hg.differentiable.mul hh.differentiable, ?_, ?_⟩
  · intro j
    simp only [scalarPartial_mul hg.differentiable hh.differentiable]
    exact (hg.differentiable.continuous.fun_mul (hh.continuous_partial j)).add
      (hh.differentiable.continuous.fun_mul (hg.continuous_partial j))
  · intro x k
    simp only [Pi.mul_apply, hg.periodic, hh.periodic]

theorem TorusC1.sum {ι : Type*} [Fintype ι] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ι → Space → E)
    (hg : ∀ i, TorusC1 (g i)) : TorusC1 (∑ i, g i) := by
  classical
  refine ⟨Differentiable.sum (fun i _ => (hg i).differentiable), ?_, ?_⟩
  · intro j
    have he (x : Space) : fderiv ℝ (∑ i, g i) x (basis j) =
        ∑ i, fderiv ℝ (g i) x (basis j) := by
      rw [fderiv_sum (fun i _ => (hg i).differentiable x), sum_apply]
    simpa only [he] using continuous_finsetSum _ (fun i _ => (hg i).continuous_partial j)
  · intro x k
    simp only [Finset.sum_apply, fun i => (hg i).periodic]

theorem fderiv_component {g : Space → Space} (hg : Differentiable ℝ g)
    (k : Fin 3) (x v : Space) :
    fderiv ℝ (fun y => g y k) x v = fderiv ℝ g x v k := by
  rw [fderiv_pi (φ := fun j y => g y j) (fun j =>
    (differentiable_apply j).fun_comp hg |>.differentiableAt)]
  rfl

theorem TorusC1.component {g : Space → Space} (hg : TorusC1 g) (k : Fin 3) :
    TorusC1 (fun x => g x k) := by
  refine ⟨(differentiable_apply k).fun_comp hg.differentiable, ?_, ?_⟩
  · intro j
    simp only [fderiv_component hg.differentiable]
    exact (continuous_apply k).comp (hg.continuous_partial j)
  · intro x l
    rw [hg.periodic]

theorem periodic_integral_divergence_zero_C1 {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (g : Fin 3 → Space → E) (hg : ∀ j, TorusC1 (g j)) :
    (∫ x in fundamentalCell, ∑ j : Fin 3, fderiv ℝ (g j) x (basis j)) = 0 := by
  rw [setIntegral_congr_set cell_ae_eq_Icc]
  have hc := continuous_finsetSum Finset.univ (fun j _ => (hg j).continuous_partial j)
  simp only [basis] at *
  rw [integral_divergence_of_hasFDerivAt_off_countable' (0 : Space) (fun _ => 10)
    (fun _ => by norm_num) g (fun j => fderiv ℝ (g j)) ∅ Set.countable_empty
    (fun j => (hg j).differentiable.continuous.continuousOn)
    (fun x _ j => (hg j).differentiable x |>.hasFDerivAt)
    hc.integrableOn_Icc]
  apply Finset.sum_eq_zero
  intro j _
  have he : (fun y : Fin 2 → ℝ => g j (j.insertNth 10 y)) =
      (fun y : Fin 2 → ℝ => g j (j.insertNth 0 y)) := by
    funext y
    rw [face_front_eq_back_deck]
    exact (hg j).periodic _ _
  change (∫ y in Set.Icc _ _, g j (j.insertNth 10 y)) -
    (∫ y in Set.Icc _ _, g j (j.insertNth 0 y)) = 0
  rw [he, sub_self]

theorem periodic_integral_partial_zero_C1 {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {g : Space → E} (hg : TorusC1 g) (j : Fin 3) :
    (∫ x in fundamentalCell, fderiv ℝ g x (basis j)) = 0 := by
  classical
  have h := periodic_integral_divergence_zero_C1 (fun k => if k = j then g else 0)
    (fun k => by split_ifs <;> first | exact hg | exact TorusC1.const 0)
  have he (k : Fin 3) (x : Space) :
      fderiv ℝ (if k = j then g else 0) x (basis k) =
        if k = j then fderiv ℝ g x (basis j) else 0 := by
    by_cases hk : k = j
    · subst k
      simp
    · simp [hk]
  simpa only [he, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using h

theorem periodic_integration_by_parts {g h : Space → ℝ}
    (hg : TorusC1 g) (hh : TorusC1 h) (j : Fin 3) :
    (∫ x in fundamentalCell, g x * fderiv ℝ h x (basis j)) =
      -(∫ x in fundamentalCell, h x * fderiv ℝ g x (basis j)) := by
  have hz := periodic_integral_partial_zero_C1 (hg.mul hh) j
  simp only [scalarPartial_mul hg.differentiable hh.differentiable] at hz
  rw [integral_add (f := fun x => g x * fderiv ℝ h x (basis j))
    (g := fun x => h x * fderiv ℝ g x (basis j))
    (continuous_integrableOn_cell (hg.differentiable.continuous.fun_mul (hh.continuous_partial j)))
    (continuous_integrableOn_cell (hh.differentiable.continuous.fun_mul (hg.continuous_partial j)))] at hz
  linarith

theorem cylinder_spatial_slice {E : Type*} [TopologicalSpace E]
    {g : ℝ → Space → E} {T t : ℝ}
    (hg : ContinuousOn (fun z : SpaceTime => g z.1 z.2) (cylinder T))
    (ht : t ∈ Set.Icc 0 T) : Continuous (g t) := by
  simpa only [Function.comp_def, id_eq] using hg.comp_continuous
    (continuous_const.prodMk continuous_id) (fun x => ⟨ht, Set.mem_univ x⟩)

theorem spatialPartial_periodic_of_differentiable {u : Field} {t : ℝ}
    (hu : Differentiable ℝ (u t)) (hp : SpatiallyPeriodic u) (j : Fin 3) (x : Space) (k : Fin 3 → ℤ) :
    spatialPartial u j t (x + deck k) = spatialPartial u j t x :=
  directional_translation hu (fun y => hp t y k) (basis j) x

theorem ClassicalSolution.spatialC1 {ν : ℝ} {f u : Field} {p : Pressure}
    (h : ClassicalSolution ν f u p) {t : ℝ} (ht : 0 ≤ t) : TorusC1 (u t) := by
  refine ⟨h.differentiable_x t ht, ?_, h.spatial_periodic_u t⟩
  intro j
  exact cylinder_spatial_slice (h.continuous_x t ht j) ⟨ht, le_refl t⟩

theorem ClassicalSolution.spatialPartialC1 {ν : ℝ} {f u : Field} {p : Pressure}
    (h : ClassicalSolution ν f u p) {t : ℝ} (ht : 0 ≤ t) (j : Fin 3) :
    TorusC1 (spatialPartial u j t) := by
  refine ⟨h.differentiable_xx t ht j, ?_, ?_⟩
  · intro k
    exact cylinder_spatial_slice (h.continuous_xx t ht j k) ⟨ht, le_refl t⟩
  · exact spatialPartial_periodic_of_differentiable (h.differentiable_x t ht)
      h.spatial_periodic_u j

theorem ClassicalSolution.pressureC1 {ν : ℝ} {f u : Field} {p : Pressure}
    (h : ClassicalSolution ν f u p) {t : ℝ} (ht : 0 ≤ t) : TorusC1 (p t) := by
  refine ⟨h.differentiable_p t ht, ?_, h.spatial_periodic_p t⟩
  intro j
  exact (continuous_apply j).comp
    (cylinder_spatial_slice (h.continuous_px t ht) ⟨ht, le_refl t⟩)

theorem fderiv_apply_eq_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : Space → E) (x d : Space) :
    fderiv ℝ g x d = ∑ j : Fin 3, d j • fderiv ℝ g x (basis j) := by
  have hd : d = ∑ j : Fin 3, d j • basis j := by
    ext k
    fin_cases k <;> simp [basis, Fin.sum_univ_succ]
  conv_lhs => rw [hd]
  simp only [map_sum, map_smul]

theorem periodic_transport_zero {q : Space → ℝ} {v : Space → Space}
    (hq : TorusC1 q) (hv : TorusC1 v)
    (hdiv : ∀ x, ∑ j : Fin 3, fderiv ℝ v x (basis j) j = 0) :
    (∫ x in fundamentalCell, fderiv ℝ q x (v x)) = 0 := by
  have hz := periodic_integral_divergence_zero_C1
    (fun j x => q x * v x j) (fun j => hq.mul (hv.component j))
  have he (x : Space) :
      (∑ j, fderiv ℝ (fun y => q y * v y j) x (basis j)) =
        fderiv ℝ q x (v x) := by
    have hmul (j : Fin 3) : fderiv ℝ (fun y => q y * v y j) x (basis j) =
        q x * fderiv ℝ (fun y => v y j) x (basis j) +
          v x j * fderiv ℝ q x (basis j) :=
      scalarPartial_mul hq.differentiable (hv.component j).differentiable x j
    simp only [hmul, fderiv_component hv.differentiable, Finset.sum_add_distrib,
      ← Finset.mul_sum, hdiv, mul_zero, zero_add]
    rw [fderiv_apply_eq_sum]
    rfl
  simpa only [he] using hz

def kineticDensity (a : Space) : ℝ := ∑ i : Fin 3, a i * a i / 2

theorem kineticDensity_nonneg (a : Space) : 0 ≤ kineticDensity a := by
  unfold kineticDensity
  exact Finset.sum_nonneg (fun i _ => div_nonneg (mul_self_nonneg _) (by norm_num))

theorem kineticDensity_continuous : Continuous kineticDensity := by
  unfold kineticDensity
  exact continuous_finsetSum Finset.univ (fun i _ =>
    ((continuous_apply i).fun_mul (continuous_apply i)).div_const 2)

theorem fderiv_kineticDensity {w : Space → Space} (hw : Differentiable ℝ w)
    (x d : Space) :
    fderiv ℝ (fun y => kineticDensity (w y)) x d =
      ∑ i : Fin 3, w x i * (fderiv ℝ w x d) i := by
  have hg (i : Fin 3) : Differentiable ℝ (fun y => w y i) :=
    (differentiable_apply i).fun_comp hw
  have he : (fun y => kineticDensity (w y)) = ∑ i : Fin 3, (fun y => w y i * w y i * (1/2 : ℝ)) := by
    funext y
    simp [kineticDensity, div_eq_mul_inv]
  rw [he, fderiv_sum (fun i _ => (((hg i).fun_mul (hg i)).mul_const (1/2 : ℝ)) x), sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [fderiv_mul_const (((hg i).fun_mul (hg i)) x), fderiv_fun_mul ((hg i) x) ((hg i) x)]
  simp only [smul_apply, add_apply,
    smul_eq_mul, fderiv_component hw]
  ring

theorem TorusC1.kineticDensity {w : Space → Space} (hw : TorusC1 w) :
    TorusC1 (fun y => kineticDensity (w y)) := by
  have hc (i : Fin 3) := ((hw.component i).mul (hw.component i)).mul (TorusC1.const (1/2 : ℝ))
  convert TorusC1.sum (fun i : Fin 3 => fun y => w y i * w y i * (1/2 : ℝ)) hc using 1
  ext y
  simp [Solenoidal.kineticDensity, div_eq_mul_inv]

theorem periodic_transport_energy_zero {w v : Space → Space}
    (hw : TorusC1 w) (hv : TorusC1 v)
    (hdiv : ∀ x, ∑ j : Fin 3, fderiv ℝ v x (basis j) j = 0) :
    (∫ x in fundamentalCell, ∑ i : Fin 3, w x i * (fderiv ℝ w x (v x)) i) = 0 := by
  simpa only [fderiv_kineticDensity hw.differentiable] using
    periodic_transport_zero hw.kineticDensity hv hdiv

end Solenoidal
end

end OAI
