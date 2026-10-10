import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FiniteTensorProjection
import OAI.Analysis.CoulombRadii.FormDomain.SmoothCompact
import OAI.Analysis.CoulombRadii.FieldAnalysis.WedgeMultiplicity
import OAI.Analysis.CoulombRadii.FieldAnalysis.PairRegroup

namespace OAI

/-! Full spin-space coordinates preserve the actual tensor coefficients
and antisymmetry. No restriction to a fixed spin sector is made. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem spinConfiguration_complex_integral {n : ℕ}
    (F : SpinConfiguration n → Configuration n → ℂ) (hF : ∀ s, Integrable (F s)) :
    (∫ z, F ((Coulomb.spinCubeEquiv n) z).1 (WithLp.toLp 2 ((Coulomb.spinCubeEquiv n) z).2)
      ∂(Measure.pi fun _ : Fin n => Coulomb.spinSpaceMeasure)) = ∑ s, ∫ x, F s x := by
  rw [(Coulomb.spinCubeEquiv_full_measurePreserving n).integral_comp'
    (fun sx => F sx.1 (WithLp.toLp 2 sx.2))]
  have hm : MeasurePreserving (MeasurableEquiv.toLp 2 ((Fin n × Fin 3) → ℝ)) volume volume :=
    PiLp.volume_preserving_toLp _
  rw [Coulomb.integral_finite_count_prod _ (fun s => hm.integrable_comp_of_integrable (hF s))]
  apply Finset.sum_congr rfl
  intro s _
  exact hm.integral_comp' (F s)

theorem fullSpin_scalarCoefficient {n : ℕ} {α : Type*}
    (u : Coulomb.H1Vector n) (v : α → Position → Fin 2 → ℂ)
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2) (b : Fin n → α) :
    Coulomb.scalarCoefficient (μ := Coulomb.spinSpaceMeasure) (Coulomb.cubeState u)
      (fun a => Coulomb.flatSpinOrbital (v a)) b = Coulomb.orbitalCoefficient u v b := by
  have h := spinConfiguration_complex_integral
    (fun s x => star (Coulomb.tensorOrbital v b s x)*u.value s x)
    (fun s => (Coulomb.tensorOrbital_memLp v hL2 b s).star.integrable_mul (u.value_L2 s))
  exact h

theorem fullSpin_antisymmetric {n : ℕ} (u : Coulomb.H1Vector n)
    (hu : Coulomb.Antisymmetric u) :
    Coulomb.ProductAntisymmetric (μ := Coulomb.spinSpaceMeasure) (Coulomb.cubeState u) := by
  intro p
  have hs (s : SpinConfiguration n) : ∀ᵐ x ∂volume,
      u.value (s ∘ p) (Coulomb.permute p (WithLp.toLp 2 x)) =
        ((p.sign : ℤ):ℂ)*u.value s (WithLp.toLp 2 x) :=
    (PiLp.volume_preserving_toLp (Fin n × Fin 3)).quasiMeasurePreserving.ae (hu p s)
  have hp := (Measure.quasiMeasurePreserving_snd
    (μ := (Measure.count : Measure (SpinConfiguration n)))).ae (ae_all_iff.mpr hs)
  have ht := (Coulomb.spinCubeEquiv_full_measurePreserving n).quasiMeasurePreserving.ae hp
  filter_upwards [ht] with z hz
  exact hz (fun i => (z i).1)

theorem finiteTensorRemainder_antisymmetric {n : ℕ} {α : Type*} [Fintype α]
    (v : α → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2) (u : Coulomb.H1Vector n) (hu : Coulomb.Antisymmetric u) :
    Coulomb.Antisymmetric (finiteTensorRemainder v hv hL2 hpartial u) :=
  hu.add (Coulomb.antisymmetric_scale _ (finiteTensorProjection_antisymmetric v hv hL2 hpartial u hu) _)

end ContinuumCoulomb

end

end OAI
