import OAI.NumberTheory.CubicMoment.Decomposition.PrimeProductHeight
import OAI.NumberTheory.CubicMoment.Estimates.PrimeDetectorCutoff

namespace OAI

/-! Apply the manuscript's exact prime detector to the actual central
integral kernel. The support is a concrete subset of the primary lattice,
with both norm endpoints enforced before the detector is invoked. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primeProductEnvelope_zero_lower {x : ℝ} (hx : x ≤ 1/2) :
    primeProductEnvelope x = 0 := by
  have h : primeProductBump x = 0 := by
    apply primeProductBump.zero_of_le_dist
    change 1 ≤ |x-3/2|
    exact (by linarith : (1:ℝ) ≤ -(x-3/2)).trans (neg_le_abs _)
  simp only [primeProductEnvelope,h,Complex.ofReal_zero]

def primeProductSupport (X : ℝ) : Finset Eisenstein :=
  (squarefreeProductEnvelope (3*X)).filter (fun n => X/2 ≤ norm n)

lemma primeProductSupport_spec {X : ℝ} {n : Eisenstein}
    (hn : n ∈ primeProductSupport X) :
    primary n ∧ Squarefree n ∧ X/2 ≤ norm n ∧ norm n ≤ 3*X := by
  obtain ⟨hn,hl⟩ := Finset.mem_filter.mp hn
  obtain ⟨hn,hs⟩ := Finset.mem_filter.mp hn
  exact ⟨(mem_primaryElementBall.mp hn).1,hs,hl,(mem_primaryElementBall.mp hn).2⟩

lemma primeProductLowHeight_support (ℓ : ℤ) (H T : ℝ) {X : ℝ} (hX : 0 < X) :
    primeProductLowHeight ℓ H T X =
      ∑ p ∈ (primeProductSupport X).filter Prime,
        centeredHeightKernel ℓ primeProductEnvelope H T X X p := by
  have hsub : (primeProductSupport X).filter Prime ⊆ primeCutoff (4*X) := by
    intro p hp
    obtain ⟨hp,hprime⟩ := Finset.mem_filter.mp hp
    have hs := primeProductSupport_spec hp
    exact mem_primeCutoff.mpr ⟨⟨hs.1,hprime⟩,by linarith [hs.2.2.2]⟩
  unfold primeProductLowHeight
  symm
  apply Finset.sum_subset hsub
  intro p hp hout
  have hprime := (mem_primeCutoff.mp hp).1
  have hz : primeProductEnvelope (norm p/X) = 0 := by
    by_cases hu : norm p ≤ 3*X
    · have hl : norm p < X/2 := lt_of_not_ge (fun hl => hout (Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
          ⟨mem_primaryElementBall.mpr ⟨hprime.1,hu⟩,hprime.2.squarefree⟩,hl⟩,hprime.2⟩))
      exact primeProductEnvelope_zero_lower ((div_le_iff₀ hX).mpr (by linarith))
    · exact primeProductEnvelope_zero ((le_div_iff₀ hX).mpr (le_of_lt (lt_of_not_ge hu)))
  simp only [centeredHeightKernel,hz,mul_zero,zero_mul]

def centralRoughProduct (ℓ : ℤ) (H T X : ℝ) : ℂ :=
  ∑ n ∈ primeProductSupport X,
    (roughProduct primeDetectorCutoff (X^(2/5:ℝ)) n:ℂ)*
      centeredHeightKernel ℓ primeProductEnvelope H T X X n

def centralSemiprimeProduct (ℓ : ℤ) (H T X : ℝ) : ℂ :=
  ∑ n ∈ primeProductSupport X with (primeFactors n).card = 2,
    (roughProduct primeDetectorCutoff (X^(2/5:ℝ)) n:ℂ)*
      centeredHeightKernel ℓ primeProductEnvelope H T X X n

theorem primeProductLowHeight_detector (ℓ : ℤ) :
    ∀ᶠ X : ℝ in atTop, ∀ H T : ℝ,
      primeProductLowHeight ℓ H T X =
        centralRoughProduct ℓ H T X-centralSemiprimeProduct ℓ H T X := by
  filter_upwards [concrete_prime_detector (by norm_num : (0:ℝ) < 1/2)
    (by norm_num : (0:ℝ) < 3),eventually_gt_atTop (0:ℝ)] with X hdet hX
  intro H T
  rw [primeProductLowHeight_support ℓ H T hX]
  apply hdet (primeProductSupport X) (centeredHeightKernel ℓ primeProductEnvelope H T X X)
  · intro n hn
    have hs := primeProductSupport_spec hn
    exact ⟨by linarith [hs.2.2.1],hs.2.2.2⟩
  · intro n hn hns
    exact (hns (primeProductSupport_spec hn).2.1).elim

end CubicFirstMoment

end

end OAI
