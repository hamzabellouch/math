import Mathlib
import OAI.MathematicalPhysics.SheetFlows.ClassicalRegularity

namespace OAI

/-! SheetFlows energy identities. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace Solenoidal

theorem measurableSet_fundamentalCell : MeasurableSet fundamentalCell :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Ico)

theorem fundamentalCell_subset_cube : fundamentalCell ⊆ Set.Icc (0 : Space) (fun _ => 10) := by
  intro x hx
  exact ⟨fun j => (hx j (Set.mem_univ j)).1, fun j => (hx j (Set.mem_univ j)).2.le⟩

theorem cylinder_uniform_bound {E : Type*} [NormedAddCommGroup E]
    {g : ℝ → Space → E} {T : ℝ}
    (hc : ContinuousOn (fun z : SpaceTime => g z.1 z.2) (cylinder T)) :
    ∃ B : ℝ, ∀ t ∈ Set.Icc 0 T, ∀ x ∈ fundamentalCell, ‖g t x‖ ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod (isCompact_Icc (a := (0 : Space))
    (b := fun _ => 10))).exists_bound_of_continuousOn
      (hc.mono (fun z hz => ⟨hz.1, Set.mem_univ z.2⟩))
  exact ⟨B, fun t ht x hx => hB (t, x) ⟨ht, fundamentalCell_subset_cube hx⟩⟩

theorem cylinder_integral_continuousOn {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {g : ℝ → Space → E} {T : ℝ}
    (hc : ContinuousOn (fun z : SpaceTime => g z.1 z.2) (cylinder T)) :
    ContinuousOn (fun t => ∫ x in fundamentalCell, g t x) (Set.Icc 0 T) := by
  obtain ⟨B, hB⟩ := cylinder_uniform_bound hc
  apply continuousOn_of_dominated (bound := fun _ : Space => B)
  · intro t ht
    exact (continuous_integrableOn_cell (cylinder_spatial_slice hc ht)).aestronglyMeasurable
  · intro t ht
    filter_upwards [ae_restrict_mem measurableSet_fundamentalCell] with x hx
    exact hB t ht x hx
  · exact continuous_integrableOn_cell continuous_const
  · exact Filter.Eventually.of_forall (fun x =>
      hc.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun _ ht => ⟨ht, Set.mem_univ x⟩))

theorem cylinder_integral_hasDerivAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {g g' : ℝ → Space → E}
    (hc : ∀ T, 0 ≤ T → ContinuousOn (fun z : SpaceTime => g z.1 z.2) (cylinder T))
    (hc' : ∀ T, 0 ≤ T → ContinuousOn (fun z : SpaceTime => g' z.1 z.2) (cylinder T))
    (hd : ∀ t, 0 < t → ∀ x, HasDerivAt (fun s => g s x) (g' t x) t)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => ∫ x in fundamentalCell, g s x)
      (∫ x in fundamentalCell, g' t x) t := by
  have hT : 0 ≤ t + 1 := by linarith
  have htT : t ∈ Set.Icc 0 (t + 1) := ⟨ht.le, by linarith⟩
  have hn : Set.Ioo 0 (t + 1) ∈ 𝓝 t := isOpen_Ioo.mem_nhds ⟨ht, by linarith⟩
  obtain ⟨B, hB⟩ := cylinder_uniform_bound (hc' (t+1) hT)
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (bound := fun _ : Space => B) (s := Set.Ioo 0 (t+1)) hn ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [hn] with s hs
    exact (continuous_integrableOn_cell (cylinder_spatial_slice (hc (t+1) hT)
      ⟨hs.1.le, hs.2.le⟩)).aestronglyMeasurable
  · exact continuous_integrableOn_cell (cylinder_spatial_slice (hc (t+1) hT) htT)
  · exact (continuous_integrableOn_cell (cylinder_spatial_slice (hc' (t+1) hT) htT)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_fundamentalCell] with x hx
    exact fun s hs => hB s ⟨hs.1.le, hs.2.le⟩ x hx
  · exact continuous_integrableOn_cell continuous_const
  · exact Filter.Eventually.of_forall (fun x s hs => hd s hs.1 x)

theorem hasDerivAt_kineticDensity {w : ℝ → Space} {w' : Space} {t : ℝ}
    (hw : HasDerivAt w w' t) :
    HasDerivAt (fun s => kineticDensity (w s))
      (∑ i : Fin 3, w t i * w' i) t := by
  have hi (i : Fin 3) : HasDerivAt (fun s => w s i) (w' i) t :=
    (ContinuousLinearMap.proj i : Space →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t hw
  have hf : HasDerivAt (fun s => ∑ i : Fin 3, w s i * w s i / 2)
      (∑ i : Fin 3, (w' i * w t i + w t i * w' i) / 2) t := by
    exact HasDerivAt.fun_sum (fun i _ => ((hi i).fun_mul (hi i)).div_const 2)
  have he : (∑ i : Fin 3, (w' i * w t i + w t i * w' i) / 2) =
      ∑ i : Fin 3, w t i * w' i := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  simpa only [he, kineticDensity] using hf

def euclidDot (a b : Space) : ℝ := ∑ i : Fin 3, a i * b i

theorem continuous_euclidDot {A : Type*} [TopologicalSpace A] {a b : A → Space}
    (ha : Continuous a) (hb : Continuous b) : Continuous (fun x => euclidDot (a x) (b x)) := by
  unfold euclidDot
  exact continuous_finsetSum _ (fun i _ =>
    ((continuous_apply i).comp ha).fun_mul ((continuous_apply i).comp hb))

@[simp] theorem euclidDot_add (a b c : Space) :
    euclidDot a (b + c) = euclidDot a b + euclidDot a c := by
  simp [euclidDot, mul_add, Finset.sum_add_distrib]

@[simp] theorem euclidDot_sub (a b c : Space) :
    euclidDot a (b - c) = euclidDot a b - euclidDot a c := by
  simp [euclidDot, mul_sub, Finset.sum_sub_distrib]

@[simp] theorem euclidDot_neg (a b : Space) : euclidDot a (-b) = -euclidDot a b := by
  simp [euclidDot, Finset.sum_neg_distrib]

@[simp] theorem euclidDot_smul (a b : Space) (c : ℝ) :
    euclidDot a (c • b) = c * euclidDot a b := by
  simp [euclidDot, ← Finset.mul_sum, mul_left_comm]

theorem TorusC1.fderiv_along_continuous {w : Space → Space} (hw : TorusC1 w)
    {v : Space → Space} (hv : Continuous v) :
    Continuous (fun x => fderiv ℝ w x (v x)) := by
  have he : (fun x => fderiv ℝ w x (v x)) =
      (fun x => ∑ j : Fin 3, v x j • fderiv ℝ w x (basis j)) :=
    funext (fun x => fderiv_apply_eq_sum w x (v x))
  rw [he]
  exact continuous_finsetSum _ (fun j _ =>
    ((continuous_apply j).comp hv).smul (hw.continuous_partial j))

theorem periodic_pressure_energy_zero {w : Space → Space} {q : Space → ℝ}
    (hw : TorusC1 w) (hq : TorusC1 q)
    (hdiv : ∀ x, ∑ j : Fin 3, fderiv ℝ w x (basis j) j = 0) :
    (∫ x in fundamentalCell, euclidDot (w x) (fun j => fderiv ℝ q x (basis j))) = 0 := by
  have he (x : Space) : fderiv ℝ q x (w x) =
      euclidDot (w x) (fun j => fderiv ℝ q x (basis j)) := by
    rw [fderiv_apply_eq_sum]
    rfl
  simpa only [he] using periodic_transport_zero hq hw hdiv

theorem periodic_viscous_energy_nonpos {w : Space → Space}
    (hw : TorusC1 w) (hww : ∀ j, TorusC1 (fun x => fderiv ℝ w x (basis j))) :
    (∫ x in fundamentalCell, euclidDot (w x)
      (∑ j : Fin 3, fderiv ℝ (fun y => fderiv ℝ w y (basis j)) x (basis j))) ≤ 0 := by
  have hint (j i : Fin 3) : IntegrableOn
      (fun x => w x i * fderiv ℝ (fun y => fderiv ℝ w y (basis j)) x (basis j) i)
      fundamentalCell :=
    continuous_integrableOn_cell (((continuous_apply i).comp hw.differentiable.continuous).fun_mul
      ((continuous_apply i).comp ((hww j).continuous_partial j)))
  have hsum (x : Space) : euclidDot (w x)
      (∑ j : Fin 3, fderiv ℝ (fun y => fderiv ℝ w y (basis j)) x (basis j)) =
        ∑ j : Fin 3, ∑ i : Fin 3,
          w x i * fderiv ℝ (fun y => fderiv ℝ w y (basis j)) x (basis j) i := by
    simp only [euclidDot, Finset.sum_apply, Finset.mul_sum]
    exact Finset.sum_comm
  simp_rw [hsum]
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun i _ => hint j i))]
  apply Finset.sum_nonpos
  intro j _
  rw [integral_finsetSum _ (fun i _ => hint j i)]
  apply Finset.sum_nonpos
  intro i _
  have hparts := periodic_integration_by_parts (hw.component i) ((hww j).component i) j
  simp only [fderiv_component hw.differentiable,
    fderiv_component (hww j).differentiable] at hparts
  rw [hparts]
  exact neg_nonpos.mpr (integral_nonneg (fun x => mul_self_nonneg _))

theorem stretching_energy_bound {u : Space → Space} (x : Space) (w : Space) {B : ℝ}
    (hB : 0 ≤ B) (hgrad : ∀ j, ‖fderiv ℝ u x (basis j)‖ ≤ B) :
    -euclidDot w (fderiv ℝ u x w) ≤ (6 * B) * kineticDensity w := by
  have hterm (i j : Fin 3) :
      -(w i * (w j * fderiv ℝ u x (basis j) i)) ≤
        B * (w i * w i + w j * w j) / 2 := by
    have hd : |fderiv ℝ u x (basis j) i| ≤ B := by
      exact (norm_le_pi_norm (fderiv ℝ u x (basis j)) i).trans (hgrad j)
    have hww : |w i| * |w j| ≤ (w i * w i + w j * w j) / 2 := by
      nlinarith [sq_nonneg (|w i| - |w j|), sq_abs (w i), sq_abs (w j)]
    calc
      -(w i * (w j * fderiv ℝ u x (basis j) i)) ≤
          |w i * (w j * fderiv ℝ u x (basis j) i)| := neg_le_abs _
      _ = (|w i| * |w j|) * |fderiv ℝ u x (basis j) i| := by rw [abs_mul, abs_mul, mul_assoc]
      _ ≤ (|w i| * |w j|) * B := mul_le_mul_of_nonneg_left hd (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ ≤ ((w i * w i + w j * w j) / 2) * B := mul_le_mul_of_nonneg_right hww hB
      _ = B * (w i * w i + w j * w j) / 2 := by ring
  have he : -euclidDot w (fderiv ℝ u x w) =
      ∑ i : Fin 3, ∑ j : Fin 3, -(w i * (w j * fderiv ℝ u x (basis j) i)) := by
    rw [fderiv_apply_eq_sum]
    simp [euclidDot, Finset.mul_sum, Finset.sum_neg_distrib]
  rw [he]
  calc
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, B * (w i * w i + w j * w j) / 2 :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm i j))
    _ = (6 * B) * kineticDensity w := by simp [kineticDensity, Fin.sum_univ_succ]; ring

theorem spatialPartial_sub_at {u v : Field} {t : ℝ}
    (hu : Differentiable ℝ (u t)) (hv : Differentiable ℝ (v t)) (j : Fin 3) :
    spatialPartial (v - u) j t = spatialPartial v j t - spatialPartial u j t := by
  funext x
  change fderiv ℝ (v t - u t) x (basis j) = _
  rw [fderiv_sub (hv x) (hu x)]
  rfl

theorem laplacian_sub_at {u v : Field} {t : ℝ}
    (hu : Differentiable ℝ (u t)) (hv : Differentiable ℝ (v t))
    (huu : ∀ j, Differentiable ℝ (spatialPartial u j t))
    (hvv : ∀ j, Differentiable ℝ (spatialPartial v j t)) :
    laplacian (v - u) t = laplacian v t - laplacian u t := by
  funext x
  change (∑ j, fderiv ℝ (spatialPartial (v-u) j t) x (basis j)) = _
  simp only [spatialPartial_sub_at hu hv, fderiv_sub (hvv _ x) (huu _ x), sub_apply,
    Finset.sum_sub_distrib]
  rfl

theorem advection_sub_identity {u v : Field} {t : ℝ}
    (hu : Differentiable ℝ (u t)) (hv : Differentiable ℝ (v t)) (x : Space) :
    advection v t x - advection u t x =
      fderiv ℝ (v t - u t) x (v t x) + fderiv ℝ (u t) x (v t x - u t x) := by
  rw [fderiv_sub (hv x) (hu x), map_sub]
  simp only [sub_apply, advection]
  abel

theorem gradient_sub_at {p r : Pressure} {t : ℝ}
    (hp : Differentiable ℝ (p t)) (hr : Differentiable ℝ (r t)) :
    gradient (p-r) t = gradient p t - gradient r t := by
  funext x j
  change fderiv ℝ (p t - r t) x (basis j) = _
  rw [fderiv_sub (hp x) (hr x)]
  rfl

theorem ClassicalSolution.difference_equation {ν : ℝ} {f u v : Field} {p r : Pressure}
    (hu : ClassicalSolution ν f u r) (hv : ClassicalSolution ν f v p)
    {t : ℝ} (ht : 0 ≤ t) (x : Space) :
    timePartial v t x - timePartial u t x =
      -gradient (p-r) t x + ν • laplacian (v-u) t x -
        fderiv ℝ (v t-u t) x (v t x) - fderiv ℝ (u t) x (v t x-u t x) := by
  have hul := hu.differentiable_x t ht
  have hvl := hv.differentiable_x t ht
  have ha := advection_sub_identity hul hvl x
  rw [gradient_sub_at (hv.differentiable_p t ht) (hu.differentiable_p t ht),
    laplacian_sub_at hul hvl (hu.differentiable_xx t ht) (hv.differentiable_xx t ht)]
  rw [eq_sub_of_add_eq (hv.equation t ht x), eq_sub_of_add_eq (hu.equation t ht x)]
  simp only [Pi.sub_apply, smul_sub]
  conv_rhs => rw [sub_sub, ← ha]
  abel

theorem ClassicalSolution.hasDerivAt {ν : ℝ} {f u : Field} {p : Pressure}
    (h : ClassicalSolution ν f u p) {t : ℝ} (ht : 0 < t) (x : Space) :
    HasDerivAt (fun s => u s x) (timePartial u t x) t :=
  (h.differentiable_t t ht.le x).hasDerivWithinAt.hasDerivAt (Ici_mem_nhds ht)

def relativeEnergy (u v : Field) (t : ℝ) : ℝ :=
  ∫ x in fundamentalCell, kineticDensity (v t x - u t x)

theorem relativeEnergy_nonneg (u v : Field) (t : ℝ) : 0 ≤ relativeEnergy u v t :=
  integral_nonneg (fun _ => kineticDensity_nonneg _)

theorem ClassicalSolution.relativeEnergy_zero {ν : ℝ} {f u v : Field} {p r : Pressure}
    (hu : ClassicalSolution ν f u r) (hv : ClassicalSolution ν f v p) :
    relativeEnergy u v 0 = 0 := by
  simp [relativeEnergy, hu.initial, hv.initial, kineticDensity]

theorem continuousOn_euclidDot {A : Type*} [TopologicalSpace A] {s : Set A}
    {a b : A → Space} (ha : ContinuousOn a s) (hb : ContinuousOn b s) :
    ContinuousOn (fun x => euclidDot (a x) (b x)) s := by
  unfold euclidDot
  exact continuousOn_finsetSum _ (fun i _ =>
    ((continuous_apply i).comp_continuousOn ha).fun_mul ((continuous_apply i).comp_continuousOn hb))

theorem ClassicalSolution.relativeEnergy_continuousOn {ν : ℝ} {f u v : Field} {p r : Pressure}
    (hu : ClassicalSolution ν f u r) (hv : ClassicalSolution ν f v p) {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (relativeEnergy u v) (Set.Icc 0 T) :=
  cylinder_integral_continuousOn (kineticDensity_continuous.comp_continuousOn
    ((hv.continuous_u T hT).sub (hu.continuous_u T hT)))

theorem ClassicalSolution.relativeEnergy_hasDerivAt {ν : ℝ} {f u v : Field} {p r : Pressure}
    (hu : ClassicalSolution ν f u r) (hv : ClassicalSolution ν f v p) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (relativeEnergy u v)
      (∫ x in fundamentalCell, euclidDot (v t x-u t x) (timePartial v t x-timePartial u t x)) t := by
  apply cylinder_integral_hasDerivAt
    (g := fun t x => kineticDensity (v t x-u t x))
    (g' := fun t x => euclidDot (v t x-u t x) (timePartial v t x-timePartial u t x))
  · intro T hT
    exact kineticDensity_continuous.comp_continuousOn
      ((hv.continuous_u T hT).sub (hu.continuous_u T hT))
  · intro T hT
    exact continuousOn_euclidDot ((hv.continuous_u T hT).sub (hu.continuous_u T hT))
      ((hv.continuous_t T hT).sub (hu.continuous_t T hT))
  · intro s hs x
    exact hasDerivAt_kineticDensity ((hv.hasDerivAt hs x).fun_sub (hu.hasDerivAt hs x))
  · exact ht

theorem ClassicalSolution.gradient_cylinder_bound {ν : ℝ} {f u : Field} {p : Pressure}
    (hu : ClassicalSolution ν f u p) {T : ℝ} (hT : 0 ≤ T) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Set.Icc 0 T, ∀ x ∈ fundamentalCell, ∀ j : Fin 3,
      ‖spatialPartial u j t x‖ ≤ B := by
  have hc : ContinuousOn (fun z : SpaceTime => fun j : Fin 3 => spatialPartial u j z.1 z.2)
      (cylinder T) := continuousOn_pi.mpr (hu.continuous_x T hT)
  obtain ⟨B, hB⟩ := cylinder_uniform_bound
    (g := fun t x => fun j : Fin 3 => spatialPartial u j t x) hc
  exact ⟨max B 0, le_max_right _ _, fun t ht x hx j =>
    (norm_le_pi_norm (fun j => spatialPartial u j t x) j).trans
      ((hB t ht x hx).trans (le_max_left _ _))⟩

theorem ClassicalSolution.relativeEnergy_derivative_bound
    {ν : ℝ} {f u v : Field} {p r : Pressure}
    (hu : ClassicalSolution ν f u r) (hv : ClassicalSolution ν f v p)
    (hν : 0 ≤ ν) {t B : ℝ} (ht : 0 ≤ t) (hB : 0 ≤ B)
    (hgrad : ∀ x ∈ fundamentalCell, ∀ j, ‖spatialPartial u j t x‖ ≤ B) :
    (∫ x in fundamentalCell, euclidDot (v t x-u t x)
      (timePartial v t x-timePartial u t x)) ≤ (6*B) * relativeEnergy u v t := by
  let w : Space → Space := v t - u t
  let q : Space → ℝ := p t - r t
  let G : Space → Space := fun x j => fderiv ℝ q x (basis j)
  let L : Space → Space := laplacian (v-u) t
  let A : Space → Space := fun x => fderiv ℝ w x (v t x)
  let C : Space → Space := fun x => fderiv ℝ (u t) x (w x)
  have hw : TorusC1 w := (hv.spatialC1 ht).sub (hu.spatialC1 ht)
  have hq : TorusC1 q := (hv.pressureC1 ht).sub (hu.pressureC1 ht)
  have hww (j : Fin 3) : TorusC1 (fun x => fderiv ℝ w x (basis j)) := by
    change TorusC1 (spatialPartial (v-u) j t)
    rw [spatialPartial_sub_at (hu.differentiable_x t ht) (hv.differentiable_x t ht)]
    exact (hv.spatialPartialC1 ht j).sub (hu.spatialPartialC1 ht j)
  have hdivw (x : Space) : ∑ j : Fin 3, fderiv ℝ w x (basis j) j = 0 := by
    dsimp only [w]
    rw [fderiv_sub (hv.differentiable_x t ht x) (hu.differentiable_x t ht x)]
    simp only [sub_apply, Pi.sub_apply, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr ((hv.incompressible t ht x).trans (hu.incompressible t ht x).symm)
  have hIG : IntegrableOn (fun x => euclidDot (w x) (G x)) fundamentalCell :=
    continuous_integrableOn_cell (continuous_euclidDot hw.differentiable.continuous
      (continuous_pi hq.continuous_partial))
  have hIL : IntegrableOn (fun x => euclidDot (w x) (L x)) fundamentalCell :=
    continuous_integrableOn_cell (continuous_euclidDot hw.differentiable.continuous
      (continuous_finsetSum _ (fun j _ => (hww j).continuous_partial j)))
  have hIA : IntegrableOn (fun x => euclidDot (w x) (A x)) fundamentalCell :=
    continuous_integrableOn_cell (continuous_euclidDot hw.differentiable.continuous
      (hw.fderiv_along_continuous (hv.differentiable_x t ht).continuous))
  have hIC : IntegrableOn (fun x => euclidDot (w x) (C x)) fundamentalCell :=
    continuous_integrableOn_cell (continuous_euclidDot hw.differentiable.continuous
      ((hu.spatialC1 ht).fderiv_along_continuous hw.differentiable.continuous))
  have hg : (∫ x in fundamentalCell, euclidDot (w x) (G x)) = 0 :=
    periodic_pressure_energy_zero hw hq hdivw
  have ha : (∫ x in fundamentalCell, euclidDot (w x) (A x)) = 0 :=
    periodic_transport_energy_zero hw (hv.spatialC1 ht) (hv.incompressible t ht)
  have hl : (∫ x in fundamentalCell, euclidDot (w x) (L x)) ≤ 0 :=
    periodic_viscous_energy_nonpos hw hww
  have he (x : Space) : timePartial v t x-timePartial u t x =
      -G x + ν • L x - A x - C x := hu.difference_equation hv ht x
  have hIE : IntegrableOn (fun x => (6*B) * kineticDensity (w x)) fundamentalCell :=
    (continuous_integrableOn_cell (kineticDensity_continuous.comp hw.differentiable.continuous)).const_mul _
  have hb : -(∫ x in fundamentalCell, euclidDot (w x) (C x)) ≤
      (6*B) * relativeEnergy u v t := by
    have hb' := integral_mono_ae hIC.fun_neg hIE (by
      filter_upwards [ae_restrict_mem measurableSet_fundamentalCell] with x hx
      exact stretching_energy_bound x (w x) hB (hgrad x hx))
    simpa only [integral_neg, integral_const_mul, relativeEnergy, w, Pi.sub_apply] using hb'
  have hmul := mul_nonpos_of_nonneg_of_nonpos hν hl
  change (∫ x in fundamentalCell, euclidDot (w x)
    (timePartial v t x-timePartial u t x)) ≤ _
  simp_rw [he, euclidDot_sub, euclidDot_add, euclidDot_neg, euclidDot_smul]
  rw [integral_sub ((hIG.fun_neg.fun_add (hIL.const_mul ν)).fun_sub hIA) hIC,
    integral_sub (hIG.fun_neg.fun_add (hIL.const_mul ν)) hIA,
    integral_add hIG.fun_neg (hIL.const_mul ν), integral_neg, integral_const_mul, hg, ha]
  linarith

end Solenoidal
end

end OAI
