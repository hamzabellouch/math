import Mathlib
import OAI.Probability.CriticalPercolation.Entropy.BinaryInverseCost
import OAI.Probability.CriticalPercolation.Entropy.BinaryReferenceLikelihood

namespace OAI

section
section
noncomputable section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation ExactExposure FiniteEntropy MarkedBits

variable {V E : Type*} [Fintype V] [Fintype E]
local instance outputEntropyFinDec (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (s n : ℕ) (D : FixedDescriptor n)

noncomputable def outputMass : (E → Bool) → ℝ :=
  pushMass (fun z => stage n D z.1 z.2 n) (conditionedMass G order d x p w s n D)

lemma inverseLog_expectation (Q : ((E → Bool) × (Fin n → Option E)) → ℝ) :
    (∑ z, Q z * inverseLog G order d x p w n D z.1 z.2) =
      2*(∑ i ∈ activeSteps n D, ∑ z, Q z * Real.log (1+selectedCost G order d x p w n D i z.1 (z.2 i))) +
      ∑ z, Q z * logContactMass (scheduleWeight G order d x p w n (fun j => (D j).1)) (configuration z.1) := by
  simp only [inverseLog,mul_add,Finset.sum_add_distrib]
  congr 1
  simp_rw [mul_left_comm (Q _) 2,Finset.mul_sum]
  rw [Finset.sum_comm]

theorem conditioned_output_entropy (horder : LazyDFS.GoodDarts G order)
    (ho : LazyDFS.Exhaustive G order) (hd : 0<d) (hp : p ∈ Set.Ioo 0 1)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    {c : ℝ} (hc : 0<c) (hc1 : c≤1)
    (hconn : ∀ j, 0<j → j<d → c ≤ prob w (fun ω => (G.openGraph ω).Reachable (x 0) (x j)))
    (hδ : 0 < prob w (endpointEvent G (x 0) (x d) s))
    (hD : 0 < descriptorMass G order d x p w s n D) :
    divergence (outputMass G order d x p w s n D) (FiniteProduct.density (QueryTree.bitWeight p)) ≤
      (4*(16/(2*p*(1-p)))+6)*constructionCost G order d x p w c s n D +
        (2*(16/(2*p*(1-p)))+5)*n*Real.log 4 := by
  let Q := conditionedMass G order d x p w s n D
  let μ : (E → Bool) → ℝ := FiniteProduct.density (QueryTree.bitWeight p)
  let L := constructionCost G order d x p w c s n D
  have hQ : ∀ z, 0 ≤ Q z := conditionedMass_nonneg G order d x p w s n hp h0 h1 hδ D hD
  have hQ1 : ∑ z, Q z = 1 := by
    have he := conditionedMass_normalized G order d x p w s n D hD
    refine Eq.trans ?_ he
    apply Finset.sum_congr
    · ext z; simp only [Finset.mem_univ]
    · intro z _; rfl
  have hm := mapped_entropy_le Q hQ (recorded n D)
    (fun z z' hz hz' he => supported_opening_injective G order d x p w s n D z z' hz hz' he)
    Prod.fst (inverseReference G order d x p w n D)
    (inverseReference_nonneg G order d x p w n D hp h0 h1) μ
    (inverseReference_marginal G order d x p w n D hp h0 h1)
    (fun z => L+inverseLog G order d x p w n D z.1 z.2)
    (conditioned_reference_density_le G order d x p w n D s hd hp h0 h1 hc hc1 hconn hδ hD)
  have he : (∑ z, Q z*(L+inverseLog G order d x p w n D z.1 z.2)) =
      L + (2*(∑ i ∈ activeSteps n D, ∑ z, Q z*Real.log (1+selectedCost G order d x p w n D i z.1 (z.2 i))) +
      ∑ z, Q z*logContactMass (scheduleWeight G order d x p w n (fun j => (D j).1)) (configuration z.1)) := by
    simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul,hQ1,one_mul]
    rw [inverseLog_expectation G order d x p w n D Q]
  rw [he] at hm
  have hi := conditioned_inverse_cost G order d x p w s n D horder ho hd hp h0 h1 hc hc1 hconn hδ hD
  have hl := (conditioned_configuration_entropy G order d x p w ho hd hp h0 h1 hc hc1 hconn s n D hδ hD).2
  change divergence (outputMass G order d x p w s n D) μ ≤ _ at hm
  change _ ≤ (4*(16/(2*p*(1-p)))+6)*L+(2*(16/(2*p*(1-p)))+5)*n*Real.log 4
  calc
    _ ≤ _ := hm
    _ ≤ L + (2*(((16/(2*p*(1-p)))*(2*L+n*Real.log 4))+2*L+2*n*Real.log 4) + (L+n*Real.log 4)) :=
      add_le_add (le_refl L) (add_le_add (mul_le_mul_of_nonneg_left hi (by norm_num : (0:ℝ) ≤ 2)) hl)
    _ = _ := by ring

end CriticalPercolation.BinaryLaw
end
end
end

end OAI
