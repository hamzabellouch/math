import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.PolicyDescriptors
import OAI.MeasureTheory.FalconerCompletion.Graphs.AeOccupiedOriginal

namespace OAI

/-! Measures and the conditional distance-set completion. -/

open _root_.OAI.PlanarFalconer

section
section
namespace GraphLiteralSupport.CurrentFalconer.TreeND
open Set Metric MeasureTheory PlanarFalconer
open scoped Classical ENNReal
variable {n : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin (n+1))
noncomputable def assemblyTestFailures {ι κ : Type*} {μ : Measure V} {N B : ℕ} {chi sig : ℝ}
    (F : AssemblyClassFamily ι μ N B chi sig) (J : ℕ) (good : Set (V×V)) (dir : V×V → V)
    (L : ι → κ → Finset PolicyDescriptor) : Set (V×V) :=
  ⋃ i, ⋃ j, ⋃ b∈L i j, {z | z.1∈F.domain i ∧ z∈good ∧
    (z.1,dir z)∉endpointGood (assemblyClassLaw μ (F.domain i)) (F.mass i)
      N sig (1000*(n+2:ℝ)) J 0 b}
lemma assemblyTestFailures_measurable {ι κ : Type*} [Fintype ι] [Fintype κ]
    {μ : Measure V} [IsProbabilityMeasure μ] {N B : ℕ} {chi sig : ℝ}
    (F : AssemblyClassFamily ι μ N B chi sig) (J : ℕ) (good : Set (V×V)) (hg : MeasurableSet good)
    (dir : V×V → V) (hdir : Measurable dir) (L : ι → κ → Finset PolicyDescriptor) :
    MeasurableSet (assemblyTestFailures F J good dir L) := by
  apply MeasurableSet.iUnion
  intro i
  apply MeasurableSet.iUnion
  intro j
  apply Finset.measurableSet_biUnion
  intro b hb
  let := F.law_probability i
  exact ((F.measurable i).preimage measurable_fst).inter (hg.inter
    ((measurable_endpointGood _ _ _ _ _ _ _ _).preimage (measurable_fst.prodMk hdir)).compl)

theorem uniform_original_family_failure_bound (sig : ℝ) (hsig : 0<sig) :
    ∃ N₀ : ℕ, ∀ N≥N₀, ∀ {ι κ : Type*} [Fintype ι] [Fintype κ],
      ∀ (μ ν : Measure V) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      ∀ (B : ℕ) (chi : ℝ) (F : AssemblyClassFamily ι μ N B chi sig),
      ∀ good : Set (V×V), MeasurableSet good →
      ∀ dir : V×V → V, Measurable dir → (∀ z∈good, ‖dir z‖=1) →
      (∀ᵐ x ∂μ, ∀ w : V, ‖w‖=1 → ∀ r : ℝ, ((2:ℝ)^N)⁻¹ ≤ r → r ≤ 1 →
        ν {y | (x,y)∈good ∧ dir (x,y)∈ball w r} ≤
          ENNReal.ofReal (((2:ℝ)^N)^sig*r^((n+1:ℝ)/2))) →
      ∀ (J K : ℕ) (L : ι → κ → Finset PolicyDescriptor),
      (∀ i j b, b∈L i j → descriptorValid N b) → (∀ i j, (L i j).card ≤ K) →
      (μ.prod ν) (assemblyTestFailures F J good dir L) ≤
        ENNReal.ofReal ((Fintype.card κ:ℝ)*(K:ℝ)*((2:ℝ)^N)^(-sig)) := by
  obtain ⟨N₀,hpair⟩ := uniform_original_pair_test_bound (n:=n) sig hsig
  refine ⟨N₀,?_⟩
  intro N hN ι κ _ _ μ ν _ _ B chi F good hgood dir hdir hunit hcap J K L hvalid hcard
  have hmass : ∑ i, μ (F.domain i) ≤ 1 := by
    have he := measure_iUnion (μ:=μ) (fun i j hij => F.disjoint hij) F.measurable
    rw [tsum_fintype] at he
    rw [←he]
    exact prob_le_one
  let eps : ENNReal := ENNReal.ofReal (((2:ℝ)^N)^(-sig))
  have hsingle (i : ι) (j : κ) (b : PolicyDescriptor) (hb : b∈L i j) :
      (μ.prod ν) {z | z.1∈F.domain i ∧ z∈good ∧
        (z.1,dir z)∉endpointGood (assemblyClassLaw μ (F.domain i)) (F.mass i)
          N sig (1000*(n+2:ℝ)) J 0 b} ≤ μ (F.domain i)*eps :=
    hpair N hN μ ν B chi F good hgood dir hdir hunit hcap i J b (hvalid i j b hb)
  calc
    _ ≤ ∑ i, ∑ j, ∑ b∈L i j, (μ.prod ν) {z |
        z.1∈F.domain i ∧ z∈good ∧ (z.1,dir z)∉endpointGood
          (assemblyClassLaw μ (F.domain i)) (F.mass i) N sig (1000*(n+2:ℝ)) J 0 b} := by
      apply (measure_iUnion_fintype_le _ _).trans
      apply Finset.sum_le_sum
      intro i _
      apply (measure_iUnion_fintype_le _ _).trans
      apply Finset.sum_le_sum
      intro j _
      exact measure_biUnion_finset_le _ _
    _ ≤ ∑ i, ∑ _j : κ, (K:ENNReal)*(μ (F.domain i)*eps) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      calc
        _ ≤ ∑ _b∈L i j, μ (F.domain i)*eps := Finset.sum_le_sum (fun b hb => hsingle i j b hb)
        _ = ((L i j).card:ENNReal)*(μ (F.domain i)*eps) := by simp
        _ ≤ _ := mul_le_mul_left (Nat.cast_le.mpr (hcard i j)) _
    _ = (Fintype.card κ:ENNReal)*(K:ENNReal)*eps*(∑ i, μ (F.domain i)) := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ (Fintype.card κ:ENNReal)*(K:ENNReal)*eps := by
      simpa only [mul_one] using mul_le_mul_right hmass ((Fintype.card κ:ENNReal)*(K:ENNReal)*eps)
    _ = _ := by rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_mul (by positivity)]; simp [eps]
end GraphLiteralSupport.CurrentFalconer.TreeND
end
end

end OAI
