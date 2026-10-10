import Mathlib
import OAI.Geometry.PrescribedRicci.GlobalKahlerIntegral
import OAI.Geometry.PrescribedRicci.IntegratedKahlerEnergy
import OAI.Geometry.PrescribedRicci.KahlerGradientEnergy

namespace OAI

/-! Kahler Green Identity. -/

section

 

noncomputable section
open Matrix Filter Set Topology MeasureTheory
open scoped ContDiff ComplexOrder Classical
namespace Anticanonical.SourceSmooth
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}
namespace KaehlerMetric

lemma holRealDeriv_sum {ι : Type*} (s : Finset ι) {f : ι → Coordinates d → ℝ}
    {z : Coordinates d} (hf : ∀ k ∈ s, DifferentiableAt ℝ (f k) z) :
    holRealDeriv (fun y => ∑ k ∈ s, f k y) z = fun j => ∑ k ∈ s, holRealDeriv (f k) z j := by
  funext j
  unfold holRealDeriv
  rw [fderiv_fun_sum hf, map_sum]

lemma gradientPair_sum_left {ι : Type*} (s : Finset ι) (H : Matrix (Fin d) (Fin d) ℂ)
    (p : ι → Fin d → ℂ) (q : Fin d → ℂ) :
    gradientPair H (fun j => ∑ k ∈ s, p k j) q = ∑ k ∈ s, gradientPair H (p k) q := by
  simp only [gradientPair, star_sum, Finset.mul_sum, Finset.sum_mul]
  simp_rw [Finset.sum_comm (s := Finset.univ) (t := s)]

lemma energy_partition [T2Space X] [CompactSpace X] (g : KaehlerMetric A)
    (ψ φ : SmoothRealFunction A) (x : X) :
    ∑ i, (g.energy ((chartPartition i).product ψ) φ).value x = (g.energy ψ φ).value x := by
  obtain ⟨a, ha⟩ := A.covers x
  have hz := (A.chart a).mapsTo ha
  have he (i : Fin A.count) := g.energy_local ((chartPartition i).product ψ) φ a hz
  have he' := g.energy_local ψ φ a hz
  simp only [SmoothRealFunction.localExpression, Function.comp_apply, (A.chart a).left_inv ha] at he he'
  simp_rw [he, he', ← Complex.re_sum]
  rw [← gradientPair_sum_left]
  have hs : (fun y => ∑ i, ((chartPartition i).product ψ).localExpression a y) = ψ.localExpression a := by
    funext y
    change (∑ i, (chartPartition i).value ((A.chart a).symm y) * ψ.value ((A.chart a).symm y)) = _
    rw [← Finset.sum_mul, chartPartition_sum, one_mul]
    rfl
  have hd := holRealDeriv_sum Finset.univ
    (f := fun i => ((chartPartition i).product ψ).localExpression a)
    (fun i _ => ((((chartPartition i).product ψ).smooth a).contDiffAt
      ((A.chart a).open_target.mem_nhds hz)).differentiableAt (by simp))
  rw [hs] at hd
  exact congrArg (fun p => (gradientPair (g.matrix a (A.chart a x)) p
    (holRealDeriv (φ.value ∘ (A.chart a).symm) (A.chart a x))).re) hd.symm

 
theorem green_identity [T2Space X] [CompactSpace X] (g : KaehlerMetric A)
    (ψ φ : SmoothRealFunction A) :
    g.integral (fun x => ψ.value x * (g.laplacian φ).value x) =
      -g.integral (g.energy ψ φ).value := by
  have hs (i : Fin A.count) : tsupport ((chartPartition i).product ψ).value ⊆ (A.chart i).source :=
    tsupport_mul_subset_left.trans (chartPartition_support i)
  have he (i : Fin A.count) :
      g.chartIntegral i (fun x => (chartPartition i).value x * (ψ.value x * (g.laplacian φ).value x)) =
        -g.integral (g.energy ((chartPartition i).product ψ) φ).value := by
    rw [g.integral_chart i (g.energy ((chartPartition i).product ψ) φ).continuous
      ((g.energy_support _ _).trans (hs i))]
    have hh := g.chart_energy_identity ((chartPartition i).product ψ) φ i (hs i)
    convert hh using 1
    congr 1
    funext x
    change _ = ((chartPartition i).value x * ψ.value x) * (g.laplacian φ).value x
    ring
  change (∑ i, g.chartIntegral i (fun x => (chartPartition i).value x *
    (ψ.value x * (g.laplacian φ).value x))) = _
  simp_rw [he]
  rw [Finset.sum_neg_distrib, ← g.integral_sum Finset.univ _
    (fun i _ => (g.energy ((chartPartition i).product ψ) φ).continuous)]
  simp_rw [g.energy_partition ψ φ]

lemma integral_laplacian_mul_symm [T2Space X] [CompactSpace X] (g : KaehlerMetric A)
    (ψ φ : SmoothRealFunction A) :
    g.integral (fun x => ψ.value x * (g.laplacian φ).value x) =
      g.integral (fun x => φ.value x * (g.laplacian ψ).value x) := by
  rw [g.green_identity, g.green_identity, g.energy_symm]

lemma integral_laplacian_self_nonpos [T2Space X] [CompactSpace X] (g : KaehlerMetric A)
    (φ : SmoothRealFunction A) : g.integral (fun x => φ.value x * (g.laplacian φ).value x) ≤ 0 := by
  rw [g.green_identity]
  exact neg_nonpos.mpr (g.integral_nonneg (g.energy_nonneg φ))

end KaehlerMetric
end Anticanonical.SourceSmooth

end
end

end OAI
