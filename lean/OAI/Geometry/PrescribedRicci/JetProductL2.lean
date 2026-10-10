import Mathlib
import OAI.Geometry.PrescribedRicci.FamilyJetNorm
import OAI.Geometry.PrescribedRicci.HolderFiniteProduct

namespace OAI

/-! Jet Product L2. -/

section

 

noncomputable section
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Classical BigOperators
namespace TameInterpolation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]

theorem jet_product_L2 (e : ι → E) (f : κ → E → ℝ)
    (hf : ∀ a, ContDiff ℝ ∞ (f a)) (hc : ∀ a, HasCompactSupport (f a))
    (m : ℕ) (hm : 0 < m) {ν : Type*} (s : Finset ν)
    (a : ν → κ) (j : ν → ℕ) (w : (i : ν) → Fin (j i) → ι)
    (hs : ∑ i ∈ s, j i = m) :
    lpNorm (fun x => ∏ i ∈ s, jet e (f (a i)) (w i) x) 2 volume ≤
      (2*(m:ℝ))^(∑ i ∈ s, j i*(m-j i)) *
        (familyJetNorm e f 0 ∞)^(s.card-1) * familyJetNorm e f m 2 := by
  have hi (i : ν) : MemLp (jet e (f (a i)) (w i)) (exponent m (j i)) volume :=
    (jet_smooth e (hf (a i)) (w i)).continuous.memLp_of_hasCompactSupport
      (jet_compact e (hc (a i)) (w i))
  have hh := lpNorm_finite_prod (μ:=volume) s
    (fun i => jet e (f (a i)) (w i)) (fun i => exponent m (j i)) (fun i _ => hi i)
  rw [exponent_sum_inverse s j m hm hs] at hh
  apply hh.trans
  apply le_trans _ (family_jet_tame_many e f hf hc m hm s j hs)
  apply Finset.prod_le_prod₀
  · intro i _; exact lpNorm_nonneg
  · intro i _
    exact (lpNorm_jet_le e (f (a i)) (w i) (exponent m (j i))).trans
      (jetNorm_le_family e f (a i) (j i) (exponent m (j i)))
end TameInterpolation

end
end

end OAI
