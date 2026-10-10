import OAI.Geometry.Kahler.BasePhaseSupport

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

lemma phaseSum_conj (s : Finset ℤ) (a : ℤ → ℂ) (z : Circle) :
    star (phaseSum s a z) = phaseSum (s.image Neg.neg) (fun n => star (a (-n))) z := by
  classical
  unfold phaseSum
  rw [star_sum]
  simp only [star_mul,phaseChar_conj]
  rw [Finset.sum_image (s := s) (g := Neg.neg) (fun n _ m _ he => neg_injective he)]
  simp [mul_comm]

lemma phaseSum_real_band {s : Finset ℤ} {ℓ : ℕ} (hs : ∀ n ∈ s, |n| ≤ (ℓ:ℤ))
    (a : ℤ → ℂ) : ∃ b : ℤ → ℂ, ∀ z : Circle,
      ((phaseSum s a z).re:ℂ) = phaseSum (phaseBand ℓ) b z := by
  classical
  let t := s.image Neg.neg
  let a' : ℤ → ℂ := fun n => if n ∈ s then a n else 0
  let b' : ℤ → ℂ := fun n => if n ∈ t then star (a (-n)) else 0
  have hs' : s ⊆ phaseBand ℓ := fun n hn => (mem_phaseBand ℓ n).mpr (hs n hn)
  have ht' : t ⊆ phaseBand ℓ := by
    intro n hn
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hn
    exact (mem_phaseBand ℓ (-m)).mpr (by simpa using hs m hm)
  refine ⟨fun n => (a' n + b' n)/2,?_⟩
  intro z
  have hr : ((phaseSum s a z).re:ℂ) = (phaseSum s a z+star (phaseSum s a z))/2 := by
    apply Complex.ext <;> simp
  rw [hr,phaseSum_conj,phaseSum_extend hs' a z,phaseSum_extend ht' (fun n => star (a (-n))) z]
  simp only [phaseSum,← Finset.sum_add_distrib,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  dsimp [a',b',t]
  ring

lemma phaseSum_integral {s : Finset ℤ} (a : ℤ → ℂ) (hs : 0 ∉ s) :
    (∫ z : Circle, phaseSum s a z ∂circleMeasure) = 0 := by
  rw [phaseSum_mean,ite_eq_right hs]

end PinchedHartogs.BaseConstruction

end

end OAI
