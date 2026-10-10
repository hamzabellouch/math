import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.OrbitalComplementCount
import OAI.Analysis.CoulombRadii.FieldAnalysis.HighProjection

namespace OAI

/-! Parseval identifies the coefficient occupation count with the actual
partial integrals of a many-electron wave function. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem first_fiber_occupation_eq {A ι : Type*} [MeasurableSpace A]
    {μ : Measure A} [SigmaFinite μ] [Countable ι] {n : ℕ}
    (v : ι → A → ℂ) (hv : ∀ a, MemLp (v a) 2 μ)
    (ho : ∀ a b, (∫ x, star (v a x)*v b x ∂μ) = if a=b then (1:ℂ) else 0)
    (hc : Coulomb.CompleteOrbitals μ v)
    (f : (Fin (n+1) → A) → ℂ) (hf : MemLp f 2 (Measure.pi fun _ => μ)) (S : Finset ι) :
    (∑ a ∈ S, ∫ y, ‖Coulomb.fiberContract (μ := μ) (v a) (Coulomb.firstFiber f) y‖^2
      ∂(Measure.pi fun _ : Fin n => μ)) =
    ∑' b, if b 0 ∈ S then ‖Coulomb.scalarCoefficient (μ := μ) f v b‖^2 else (0:ℝ) := by
  have hs := Coulomb.scalarCoefficient_summable f hf v hv ho
  have hsingle (a : ι) :
      (∫ y, ‖Coulomb.fiberContract (μ := μ) (v a) (Coulomb.firstFiber f) y‖^2
        ∂(Measure.pi fun _ : Fin n => μ)) =
      ∑' b, if b 0 = a then ‖Coulomb.scalarCoefficient (μ := μ) f v b‖^2 else (0:ℝ) := by
    calc
      _ = ∑' b : Fin n → ι, ‖Coulomb.scalarCoefficient (μ := μ)
          (Coulomb.fiberContract (μ := μ) (v a) (Coulomb.firstFiber f)) v b‖^2 :=
        (Coulomb.scalarCoefficient_parseval _
          (Coulomb.fiberContract_memLp (hv a) (Coulomb.firstFiber_memLp hf)) v hv ho hc).symm
      _ = ∑' b : Fin n → ι, ‖Coulomb.scalarCoefficient (μ := μ) f v (Fin.cons a b)‖^2 := by
        apply tsum_congr
        intro b
        exact congrArg (fun z : ℂ => ‖z‖^2) (Coulomb.scalarCoefficient_contract f hf v hv a b).symm
      _ = _ := (Coulomb.tsum_fixed_zero (fun b => ‖Coulomb.scalarCoefficient (μ := μ) f v b‖^2) a).symm
  simp_rw [hsingle]
  rw [← Summable.tsum_finsetSum (fun a _ =>
    Summable.of_nonneg_of_le (fun b => by positivity)
      (fun b => by split_ifs <;> first | exact le_rfl | exact sq_nonneg _) hs)]
  apply tsum_congr
  intro b
  simp

theorem first_fiber_complement_bound {A ι : Type*} [MeasurableSpace A]
    {μ : Measure A} [SigmaFinite μ] [Countable ι] {n : ℕ}
    (v : ι → A → ℂ) (hv : ∀ a, MemLp (v a) 2 μ)
    (ho : ∀ a b, (∫ x, star (v a x)*v b x ∂μ) = if a=b then (1:ℂ) else 0)
    (hc : Coulomb.CompleteOrbitals μ v)
    (f : (Fin (n+1) → A) → ℂ) (hf : MemLp f 2 (Measure.pi fun _ => μ))
    (ha : Coulomb.ProductAntisymmetric (μ := μ) f) (S : Finset ι)
    (hzero : ∀ b, (∀ i, b i ∈ S) → Coulomb.scalarCoefficient (μ := μ) f v b = 0) :
    (n+1:ℕ)*(∑ a ∈ S, ∫ y, ‖Coulomb.fiberContract (μ := μ) (v a) (Coulomb.firstFiber f) y‖^2
      ∂(Measure.pi fun _ : Fin n => μ)) ≤
      (n:ℝ)*(∫ x, ‖f x‖^2 ∂(Measure.pi fun _ : Fin (n+1) => μ)) := by
  rw [first_fiber_occupation_eq v hv ho hc f hf S,
    ← Coulomb.scalarCoefficient_parseval f hf v hv ho hc]
  simpa only [Finset.mem_coe] using complement_coefficient_single_occupation (S : Set ι)
    (Coulomb.scalarCoefficient (μ := μ) f v) (Coulomb.scalarCoefficient_antisymmetric ha v)
    hzero (Coulomb.scalarCoefficient_summable f hf v hv ho) 0

end ContinuumCoulomb

end

end OAI
