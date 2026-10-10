import Mathlib
import OAI.Analysis.WeakInfiniteness.NonunitalCentralization

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra ComplexOrder Topology

open Filter

universe u

section

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma finiteCompression_approximate_initial {n : ℕ} (v : Fin n → A)
    (ε : ℝ) (hε : 0<ε) :
    ∃ e : A,0≤e ∧ ‖e‖≤1 ∧ ‖finiteCompression v e-nonunitalCoefficientMap v 1‖<ε := by
  let l := CStarAlgebra.approximateUnit A
  let hl := CStarAlgebra.increasingApproximateUnit A
  have ht : Tendsto (finiteCompression v) l (𝓝 (nonunitalCoefficientMap v 1)) := by
    rw [nonunitalCoefficientMap_initial]
    have hs := tendsto_finsetSum Finset.univ (fun i _ =>
      (hl.tendsto_mul_right (v i)).const_mul (star (v i)))
    change Tendsto (fun e => ∑ i, star (v i) * e * v i)
      (CStarAlgebra.approximateUnit A) (𝓝 (∑ i, star (v i) * v i))
    simpa only [mul_assoc] using hs
  have he : ∀ᶠ e in l,‖finiteCompression v e-nonunitalCoefficientMap v 1‖<ε := by
    exact (Metric.tendsto_nhds.mp ht ε hε).mono fun e he => by
      simpa only [dist_eq_norm] using he
  obtain ⟨e,he0,hen,hee⟩ := (hl.eventually_nonneg.and (hl.eventually_norm.and he)).exists
  exact ⟨e,he0,hen,hee⟩

lemma nuclear_weaklyPurelyInfinite_relative_cpc_averaging
    (hN : Nuclear A) (hW : WeaklyPurelyInfinite A)
    (F : Finset A) (ε : ℝ) (hε : 0<ε) :
    ∃ n : ℕ,1≤n ∧∃ v : Fin n → A,∃ e : A,0≤e ∧ ‖e‖≤1 ∧
      CompletelyPositive (finiteCompressionContinuous v) ∧
      ‖finiteCompressionContinuous v‖≤1 ∧
      ∀ a∈F,‖finiteCompression v e*a-a‖<ε ∧
        ‖a*finiteCompression v e-a‖<ε ∧
        ∀ r : A,‖r‖≤1 → ‖a*finiteCompression v r-finiteCompression v r*a‖<ε := by
  classical
  obtain ⟨n,hn,φ,v,_,_,_,hcp,hcn,happ⟩ :=
    nuclear_weaklyPurelyInfinite_nonunital_centralizing_compression hN hW F (ε/2) (by positivity)
  let M : ℝ := 1+∑ a∈F,‖a‖
  have hM : 0<M := by dsimp only [M]; positivity
  have haM (a : A) (ha : a∈F) : ‖a‖<M := by
    have ht := Finset.single_le_sum (f := fun a : A => ‖a‖) (fun _ _ => norm_nonneg _) ha
    dsimp only [M]
    linarith
  let η : ℝ := ε/(2*M)
  have hη : 0<η := div_pos hε (by positivity)
  have hηM : η*M=ε/2 := by dsimp only [η]; field_simp
  obtain ⟨e,he,hen,hee⟩ := finiteCompression_approximate_initial v η hη
  refine ⟨n,hn,v,e,he,hen,hcp,hcn,?_⟩
  intro a ha
  have hbound : ‖finiteCompression v e-nonunitalCoefficientMap v 1‖*‖a‖≤ε/2 := by
    calc
      _ ≤ η*M := mul_le_mul hee.le (haM a ha).le (norm_nonneg _) hη.le
      _ = _ := hηM
  refine ⟨?_,?_,?_⟩
  · calc
      _ ≤ ‖finiteCompression v e*a-nonunitalCoefficientMap v 1*a‖+
          ‖nonunitalCoefficientMap v 1*a-a‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ‖finiteCompression v e-nonunitalCoefficientMap v 1‖*‖a‖+
          ‖nonunitalCoefficientMap v 1*a-a‖ := by
        rw [← sub_mul]
        exact add_le_add (norm_mul_le _ _) le_rfl
      _ < ε/2+ε/2 := add_lt_add_of_le_of_lt hbound (happ a ha).2.1
      _ = _ := by ring
  · calc
      _ ≤ ‖a*finiteCompression v e-a*nonunitalCoefficientMap v 1‖+
          ‖a*nonunitalCoefficientMap v 1-a‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ‖a‖*‖finiteCompression v e-nonunitalCoefficientMap v 1‖+
          ‖a*nonunitalCoefficientMap v 1-a‖ := by
        rw [← mul_sub]
        exact add_le_add (norm_mul_le _ _) le_rfl
      _ < ε/2+ε/2 := add_lt_add_of_le_of_lt (by simpa only [mul_comm] using hbound)
        (happ a ha).2.2.1
      _ = _ := by ring
  · intro r hr
    exact ((happ a ha).2.2.2 r hr).trans (by linarith)

end

end

end WeakPureInfiniteness
end

end OAI
