import OAI.Analysis.LipschitzEquivalence.TriangularDuals

namespace OAI

universe uH

noncomputable section
namespace LipschitzCounterexample.CompactWSC
open scoped ContDiff BigOperators NNReal Topology
open Set Filter MeasureTheory FreeSpace
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem grad_integrable (f : Smooth H) (p q : H) :
    IntervalIntegrable (fun t : ℝ => ‖Smooth.grad (edge p q t) f‖) volume 0 1 :=
  ((f.grad_continuous.comp (edge_continuous p q)).norm).intervalIntegrable _ _

theorem grad_sq_integrable (f : Smooth H) (p q : H) :
    IntervalIntegrable (fun t : ℝ => ‖Smooth.grad (edge p q t) f‖^2) volume 0 1 :=
  ((f.grad_continuous.comp (edge_continuous p q)).norm.pow 2).intervalIntegrable _ _

theorem gradEnergy_le_cost (a : MolecularData H) (f : Smooth H)
    (hf : LipschitzWith 1 (f : H → ℝ)) : gradEnergy a f ≤ a.cost := by
  apply Finset.sum_le_sum
  intro i _
  have hi : (∫ t in (0:ℝ)..1, ‖Smooth.grad (edge (a.p i) (a.q i) t) f‖^2) ≤ 1 := by
    calc
      _ ≤ ∫ _t in (0:ℝ)..1, (1:ℝ) := intervalIntegral.integral_mono_on (by norm_num)
        (grad_sq_integrable f _ _) (intervalIntegrable_const) (fun t _ => by
          have := f.grad_norm_le hf (edge (a.p i) (a.q i) t)
          norm_num only [NNReal.coe_one] at this
          nlinarith [norm_nonneg (Smooth.grad (edge (a.p i) (a.q i) t) f)])
      _ = 1 := by simp
  simpa using mul_le_mul_of_nonneg_left hi (mul_nonneg (abs_nonneg (a.coeff i)) dist_nonneg)

theorem gradEnergy_smul (a : MolecularData H) (c : ℝ) (f : Smooth H) :
    gradEnergy a (c • f) = c^2*gradEnergy a f := by
  simp only [gradEnergy,map_smul,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
  simp only [intervalIntegral.integral_const_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem gradMass_le_young (a : MolecularData H) (f : Smooth H) {t : ℝ} (ht : 0 < t) :
    gradMass a f ≤ t*a.cost+(4*t)⁻¹*gradEnergy a f := by
  have hedge (p q : H) :
      (∫ s in (0:ℝ)..1, ‖Smooth.grad (edge p q s) f‖) ≤
        t+(4*t)⁻¹*(∫ s in (0:ℝ)..1, ‖Smooth.grad (edge p q s) f‖^2) := by
    calc
      _ ≤ ∫ s in (0:ℝ)..1, t+(4*t)⁻¹*‖Smooth.grad (edge p q s) f‖^2 := by
        apply intervalIntegral.integral_mono_on (by norm_num) (grad_integrable f p q)
          (intervalIntegrable_const.add ((grad_sq_integrable f p q).const_mul _))
        intro s _
        have hsq := sq_nonneg (‖Smooth.grad (edge p q s) f‖-2*t)
        have hpos : 0 < 4*t := by positivity
        have hinv : (4*t)*((4*t)⁻¹) = 1 := mul_inv_cancel₀ hpos.ne'
        calc
          _ ≤ (t*(4*t)+‖Smooth.grad (edge p q s) f‖^2)/(4*t) :=
            (le_div_iff₀ hpos).mpr (by nlinarith)
          _ = _ := by field_simp
      _ = _ := by rw [intervalIntegral.integral_add intervalIntegrable_const
          ((grad_sq_integrable f p q).const_mul _),intervalIntegral.integral_const_mul]; simp
  calc
    gradMass a f ≤ ∑ i, (|a.coeff i| * dist (a.p i) (a.q i))*
        (t+(4*t)⁻¹*(∫ s in (0:ℝ)..1, ‖Smooth.grad (edge (a.p i) (a.q i) s) f‖^2)) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (hedge _ _) (mul_nonneg (abs_nonneg _) dist_nonneg)
    _ = t*a.cost+(4*t)⁻¹*gradEnergy a f := by
      simp only [MolecularData.cost,gradEnergy,Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring

def augmentedEnergy (a : MolecularData H) (S : Finset H) (D : ℝ) (f : Smooth H) : ℝ :=
  gradEnergy a f+∑ p ∈ S, (D*f.val p)^2

theorem augmentedEnergy_nonneg (a : MolecularData H) (S : Finset H) (D : ℝ) (f : Smooth H) :
    0 ≤ augmentedEnergy a S D f :=
  add_nonneg (gradEnergy_nonneg _ _)
    (Finset.sum_nonneg (fun point _ => sq_nonneg (D * f.val point)))

theorem augmentedEnergy_midpoint (a : MolecularData H) (S : Finset H) (D : ℝ)
    (f g : Smooth H) :
    augmentedEnergy a S D ((1/2:ℝ) • (f+g)) =
      (augmentedEnergy a S D f+augmentedEnergy a S D g)/2-augmentedEnergy a S D (f-g)/4 := by
  have he (p : H) : (D*((((1/2:ℝ) • (f+g)) : Smooth H).val p))^2 =
      ((D*f.val p)^2+(D*g.val p)^2)/2-(D*((f-g).val p))^2/4 := by
    change (D*((1/2:ℝ)*(f.val p+g.val p)))^2 =
      ((D*f.val p)^2+(D*g.val p)^2)/2-(D*(f.val p-g.val p))^2/4
    ring
  simp only [augmentedEnergy,gradEnergy_midpoint,he,Finset.sum_sub_distrib,
    ← Finset.sum_div,Finset.sum_add_distrib]
  ring

theorem gradEnergy_le_augmentedEnergy (a : MolecularData H) (S : Finset H) (D : ℝ) (f : Smooth H) :
    gradEnergy a f ≤ augmentedEnergy a S D f :=
  le_add_of_nonneg_right (Finset.sum_nonneg (fun point _ => sq_nonneg (D * f.val point)))

theorem sq_value_le_augmentedEnergy (a : MolecularData H) (S : Finset H) (D : ℝ) (f : Smooth H)
    {p : H} (hp : p ∈ S) : (D*f.val p)^2 ≤ augmentedEnergy a S D f := by
  exact (Finset.single_le_sum (fun p _ => sq_nonneg (D*f.val p)) hp).trans
    (le_add_of_nonneg_left (gradEnergy_nonneg _ _))

end LipschitzCounterexample.CompactWSC
end

end OAI
