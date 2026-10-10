import OAI.Analysis.AncientFlat.Evolution.InitialModel
import OAI.Analysis.AncientFlat.Regularity.WithinInterpolation
import OAI.Analysis.AncientFlat.Regularity.HolderProducts

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction Laplacian
namespace ParabolicInitial
open ParabolicInterior ParabolicSchauder ParametrixEvolution ClassicalIBP
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem exists_initial_jet_model (α : ℝ) (hα : 0<α) (hα1 : α<1) :
    ∃ C : ℝ, 0<C ∧ ∀ (g : C₀(V,ℂ)) (F : ℝ), 0≤F → ‖g‖≤F →
      (∀ x y, ‖g x-g y‖≤F*‖x-y‖^α) →
      ∃ u : ℝ → V → ℂ, (∀ x, u 0 x=0) ∧
        (∀ t∈Icc 0 (1/2:ℝ), ContDiff ℝ 4 (u t)) ∧
        JetBound α {p : V × ℝ | ‖p.1‖<3 ∧ p.2∈Icc 0 (1/2:ℝ)} u
          (fun t x => g x-Δ (Δ (u t)) x) (C*F) ∧
        (∀ t∈Icc 0 (1/2:ℝ), ∀ x, HasDerivWithinAt (fun s => u s x)
          (g x-Δ (Δ (u t)) x) (Icc 0 (1/2:ℝ)) t) := by
  obtain ⟨C,hC,H⟩ := exists_initial_model (V := V) α hα hα1
  obtain ⟨L,hL,HI⟩ := within_lower_jet_interpolation (V := V) (E := ℂ) α 1 3 4 hα hα1
    zero_lt_one (by norm_num)
  let T := (traceFour : (V [×4]→L[ℝ] ℂ) →L[ℝ] ℂ)
  let D := C+(1+L)*C+1+‖T‖*C
  have hD : 0<D := by dsimp [D]; positivity
  refine ⟨D,hD,?_⟩
  intro g F hF hg hh
  obtain ⟨u,hu0,hs,h4,hd,hu,hut⟩ := H g F hF hg hh
  have hlow := HI (fun t x => u t x) (fun t x => g x-Δ (Δ (fun y => u t y)) x)
    0 (1/2) (by norm_num) (C*F) (C*F) (mul_nonneg hC.le hF) (mul_nonneg hC.le hF) hs
    (fun t ht x _ => hd t ht x) (fun t ht x _ => hut t ht x) (fun t ht x _ => hu t ht x)
    (fun t ht x _ => h4.1 (x,t) ht)
  have hG : HolderBound α {p : V × ℝ | ‖p.1‖<3 ∧ p.2∈Icc 0 (1/2:ℝ)}
      (fun p => g p.1) F := by
    refine ⟨fun p _ => (g.toBCF.norm_coe_le_norm p.1).trans hg,?_⟩
    intro p _ q _
    exact (hh p.1 q.1).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) (le_add_of_nonneg_right
        (Real.rpow_nonneg (abs_nonneg _) _)) hα.le) hF)
  have hT := hG.add ((h4.restrict (fun _ ht => ht.2)).clm T).neg
  have he (p : V × ℝ) (hp : ‖p.1‖<3 ∧ p.2∈Icc 0 (1/2:ℝ)) :
      g p.1-Δ (Δ (fun y => u p.2 y)) p.1=
        g p.1+-T (iteratedFDeriv ℝ 4 (fun y => u p.2 y) p.1) := by
    rw [bilaplacian_eq_traceFour _ (hs p.2 hp.2)]; rfl
  refine ⟨fun t x => u t x,fun x => by simp [hu0],hs,⟨?_,?_⟩,hd⟩
  · intro j hj
    by_cases hj3 : j≤3
    · apply (hlow j hj3).mono
      dsimp [D]
      nlinarith [mul_nonneg (norm_nonneg T) hC.le,mul_nonneg (norm_nonneg T) (mul_nonneg hC.le hF)]
    · have hj4 : j=4 := by omega
      subst j
      apply (h4.restrict (fun _ hp => hp.2)).mono
      exact mul_le_mul_of_nonneg_right (by dsimp [D]; nlinarith [mul_nonneg (norm_nonneg T) hC.le, mul_nonneg hL.le hC.le]) hF
  · have hh : F+‖T‖*(C*F)≤D*F := by dsimp [D]; nlinarith [mul_nonneg hC.le hF,mul_nonneg hL.le (mul_nonneg hC.le hF)]
    refine ⟨fun p hp => ?_,fun p hp q hq => ?_⟩
    · dsimp only
      rw [he p hp]
      exact (hT.1 p hp).trans hh
    · dsimp only
      rw [he p hp,he q hq]
      exact (hT.2 p hp q hq).trans (mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg (pdist_nonneg p q) α))
end ParabolicInitial

end

end OAI
