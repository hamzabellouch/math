import Mathlib
import OAI.MathematicalPhysics.SheetFlows.EnergyIdentities

namespace OAI

/-! SheetFlows uniqueness. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace Solenoidal

theorem energy_zero_of_differential_inequality {e e' : ℝ → ℝ} {T C : ℝ}
    (hT : 0 ≤ T) (hc : ContinuousOn e (Set.Icc 0 T)) (he0 : e 0 = 0)
    (hn : ∀ t ∈ Set.Icc 0 T, 0 ≤ e t)
    (hd : ∀ t ∈ Set.Ioo 0 T, HasDerivAt e (e' t) t)
    (hb : ∀ t ∈ Set.Ioo 0 T, e' t ≤ C * e t) :
    ∀ t ∈ Set.Icc 0 T, e t = 0 := by
  let φ : ℝ → ℝ := fun t => Real.exp (-C*t) * e t
  let φ' : ℝ → ℝ := fun t => Real.exp (-C*t) * (e' t - C * e t)
  have hcφ : ContinuousOn φ (Set.Icc 0 T) :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).fun_mul hc
  have hdφ (t : ℝ) (ht : t ∈ Set.Ioo 0 T) : HasDerivAt φ (φ' t) t := by
    have h : HasDerivAt φ
        (Real.exp (-C*t) * (-C) * e t + Real.exp (-C*t) * e' t) t := by
      simpa only [mul_one, id_eq, φ] using
        ((((hasDerivAt_id t).const_mul (-C)).exp).fun_mul (hd t ht))
    have heq : Real.exp (-C*t) * (-C) * e t + Real.exp (-C*t) * e' t = φ' t := by
      dsimp [φ']
      ring
    exact heq ▸ h
  have hbφ (t : ℝ) (ht : t ∈ Set.Ioo 0 T) : φ' t ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (sub_nonpos.mpr (hb t ht))
  have ha : AntitoneOn φ (Set.Icc 0 T) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _) hcφ
      (fun t ht => (hdφ t (by simpa only [interior_Icc] using ht)).hasDerivWithinAt)
      (fun t ht => hbφ t (by simpa only [interior_Icc] using ht))
  intro t ht
  have hl := ha ⟨le_refl 0, hT⟩ ht ht.1
  change Real.exp (-C*t) * e t ≤ Real.exp (-C*0) * e 0 at hl
  rw [he0, mul_zero] at hl
  exact le_antisymm (le_of_mul_le_mul_left (by simpa only [mul_zero] using hl)
    (Real.exp_pos (-C*t))) (hn t ht)

theorem ClassicalSolution.relativeEnergy_eq_zero {ν : ℝ} {f u v : Field} {p r : Pressure}
    (hu : ClassicalSolution ν f u r) (hv : ClassicalSolution ν f v p)
    (hν : 0 ≤ ν) {t : ℝ} (ht : 0 ≤ t) : relativeEnergy u v t = 0 := by
  obtain ⟨B, hB, hgrad⟩ := hu.gradient_cylinder_bound ht
  apply energy_zero_of_differential_inequality (T := t) (C := 6*B) ht
    (hu.relativeEnergy_continuousOn hv ht) (hu.relativeEnergy_zero hv)
    (fun s _ => relativeEnergy_nonneg u v s)
    (fun s hs => hu.relativeEnergy_hasDerivAt hv hs.1)
    (fun s hs => hu.relativeEnergy_derivative_bound hv hν hs.1.le hB
      (hgrad s ⟨hs.1.le, hs.2.le⟩)) t ⟨ht, le_refl t⟩

theorem cube_subset_closure_interior :
    Set.Icc (0 : Space) (fun _ => 10) ⊆ closure (interior (Set.Icc (0 : Space) (fun _ => 10))) := by
  have hp : Set.Icc (0 : Space) (fun _ => 10) =
      Set.pi Set.univ (fun _ : Fin 3 => Set.Icc (0 : ℝ) 10) := by
    ext x
    simp [Set.mem_Icc, Pi.le_def]
  rw [hp, interior_pi_set (Set.toFinite _), closure_pi_set]
  simp only [interior_Icc, closure_Ioo (by norm_num : (0:ℝ) ≠ 10)]
  exact Set.Subset.rfl

theorem kineticDensity_eq_zero_iff (a : Space) : kineticDensity a = 0 ↔ a = 0 := by
  constructor
  · intro ha
    ext j
    have hj : a j * a j / 2 ≤ kineticDensity a :=
      Finset.single_le_sum (f := fun i => a i * a i / 2)
        (fun i _ => div_nonneg (mul_self_nonneg _) (by norm_num))
        (Finset.mem_univ j)
    rw [ha] at hj
    change a j = 0
    nlinarith [sq_nonneg (a j)]
  · rintro rfl
    simp [kineticDensity]

theorem periodic_energy_zero_implies_zero {w : Space → Space}
    (hc : Continuous w) (hp : ∀ x k, w (x+deck k) = w x)
    (he : (∫ x in fundamentalCell, kineticDensity (w x)) = 0) : ∀ x, w x = 0 := by
  have hcont := kineticDensity_continuous.comp hc
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => kineticDensity_nonneg (w x))
    (continuous_integrableOn_cell hcont)).mp he
  rw [Measure.restrict_congr_set cell_ae_eq_Icc] at hae
  have hon := Measure.eqOn_of_ae_eq hae hcont.continuousOn continuousOn_const
    cube_subset_closure_interior
  intro x
  have hz : kineticDensity (w (wrapSpace x)) = 0 := hon (wrapSpace_mem x)
  have hper := hp (wrapSpace x) (fun j => ⌊x j / 10⌋)
  rw [wrapSpace_add_deck] at hper
  exact (kineticDensity_eq_zero_iff (w x)).mp (hper ▸ hz)

theorem ClassicalSolution.velocity_unique {ν : ℝ} {f u v : Field} {p r : Pressure}
    (hu : ClassicalSolution ν f u r) (hv : ClassicalSolution ν f v p)
    (hν : 0 ≤ ν) {t : ℝ} (ht : 0 ≤ t) (x : Space) : v t x = u t x := by
  have hw := (hv.spatialC1 ht).sub (hu.spatialC1 ht)
  have he := periodic_energy_zero_implies_zero hw.differentiable.continuous hw.periodic
    (hu.relativeEnergy_eq_zero hv hν ht) x
  exact sub_eq_zero.mp he

theorem volume_fundamentalCell : volume fundamentalCell = 1000 := by
  norm_num [fundamentalCell, volume_pi, Measure.pi_pi]

theorem ClassicalSolution.pressure_gradient_unique {ν : ℝ} {f u v : Field} {p r : Pressure}
    (hu : ClassicalSolution ν f u r) (hv : ClassicalSolution ν f v p)
    (hν : 0 ≤ ν) {t : ℝ} (ht : 0 ≤ t) (x : Space) : gradient p t x = gradient r t x := by
  have hvel (s : ℝ) (hs : 0 ≤ s) : v s = u s :=
    funext (fun y => hu.velocity_unique hv hν hs y)
  have htime : timePartial v t x = timePartial u t x :=
    derivWithin_congr (fun s hs => congrFun (hvel s hs) x) (congrFun (hvel t ht) x)
  have hadv : advection v t x = advection u t x := by simp only [advection, hvel t ht]
  have hlap : laplacian v t x = laplacian u t x := by
    unfold laplacian spatialPartial
    rw [hvel t ht]
  have hve := hv.equation t ht x
  rw [htime, hadv, hlap] at hve
  have hue := hu.equation t ht x
  have hneg := add_right_cancel (add_right_cancel (hve.symm.trans hue))
  exact neg_injective hneg

theorem ClassicalSolution.pressure_unique {ν : ℝ} {f u v : Field} {p r : Pressure}
    (hu : ClassicalSolution ν f u r) (hv : ClassicalSolution ν f v p)
    (hν : 0 ≤ ν) {t : ℝ} (ht : 0 ≤ t) (x : Space) : p t x = r t x := by
  let q : Space → ℝ := p t - r t
  have hq : Differentiable ℝ q := (hv.differentiable_p t ht).sub (hu.differentiable_p t ht)
  have hd (y : Space) : fderiv ℝ q y = 0 := by
    have hj (j : Fin 3) : fderiv ℝ q y (basis j) = 0 := by
      change gradient (p-r) t y j = 0
      rw [gradient_sub_at (hv.differentiable_p t ht) (hu.differentiable_p t ht)]
      simp only [Pi.sub_apply, hu.pressure_gradient_unique hv hν ht y, sub_self]
    ext d
    rw [fderiv_apply_eq_sum]
    simp only [hj, smul_zero, Finset.sum_const_zero, zero_apply]
  have hconst (y : Space) : q y = q 0 := is_const_of_fderiv_eq_zero hq hd y 0
  have hint : (∫ y in fundamentalCell, q y) = 0 := by
    change (∫ y in fundamentalCell, p t y-r t y) = 0
    rw [integral_sub (continuous_integrableOn_cell (hv.differentiable_p t ht).continuous)
      (continuous_integrableOn_cell (hu.differentiable_p t ht).continuous),
      hv.pressure_mean_zero t ht, hu.pressure_mean_zero t ht, sub_self]
  simp only [hconst] at hint
  have h0 : q 0 = 0 := by
    simpa [measureReal_def, volume_fundamentalCell] using hint
  exact sub_eq_zero.mp ((hconst x).trans h0)

theorem ClassicalSolution.unique {ν : ℝ} {f u v : Field} {p r : Pressure}
    (hu : ClassicalSolution ν f u r) (hv : ClassicalSolution ν f v p)
    (hν : 0 ≤ ν) {t : ℝ} (ht : 0 ≤ t) (x : Space) :
    v t x = u t x ∧ p t x = r t x :=
  ⟨hu.velocity_unique hv hν ht x, hu.pressure_unique hv hν ht x⟩

end Solenoidal
end

end OAI
