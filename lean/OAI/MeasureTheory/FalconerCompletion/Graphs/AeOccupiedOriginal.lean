import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.PolicyDescriptors
import OAI.MeasureTheory.FalconerCompletion.Graphs.LawProbability
import OAI.MeasureTheory.FalconerCompletion.Measures.AssemblyClassLaw
import OAI.MeasureTheory.FalconerCompletion.Recursion.DescriptorValid

namespace OAI

/-! Graph energies and pair estimates. -/

open _root_.OAI.PlanarFalconer

section
section
namespace GraphLiteralSupport.CurrentFalconer.TreeND
open Set Metric MeasureTheory PlanarFalconer
open scoped Classical ENNReal
variable {n : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin (n+1))
namespace AssemblyClassFamily
variable {ι : Type*} {μ : Measure (EuclideanSpace ℝ (Fin (n+1)))} [IsProbabilityMeasure μ]
variable {N B : ℕ} {chi sig : ℝ} (F : AssemblyClassFamily ι μ N B chi sig)
lemma ae_occupied_original (i : ι) (p : ℕ) :
    ∀ᵐ x ∂μ.restrict (F.domain i), ∃ P∈dyadicPaths p,
      x∈treeCell P ∧ 0<assemblyClassLaw μ (F.domain i) (treeCell P) := by
  let := F.law_probability i
  have hr : assemblyClassLaw μ (F.domain i) (treeCell [])ᶜ=0 := by
    rw [measure_compl (measurableSet_treeCell _) (measure_ne_top _ _),measure_univ,F.law_root i]
    simp
  rw [←F.coefficient_law i]
  exact Measure.ae_smul_measure (ae_occupied_anchor _ p hr) _
end AssemblyClassFamily

theorem uniform_original_pair_test_bound (sig : ℝ) (hsig : 0<sig) :
    ∃ N₀ : ℕ, ∀ N≥N₀, ∀ {ι : Type*},
      ∀ (μ ν : Measure V) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      ∀ (B : ℕ) (chi : ℝ) (F : AssemblyClassFamily ι μ N B chi sig),
      ∀ good : Set (V×V), MeasurableSet good →
      ∀ dir : V×V → V, Measurable dir → (∀ z∈good, ‖dir z‖=1) →
      (∀ᵐ x ∂μ, ∀ w : V, ‖w‖=1 → ∀ r : ℝ, ((2:ℝ)^N)⁻¹ ≤ r → r ≤ 1 →
        ν {y | (x,y)∈good ∧ dir (x,y)∈ball w r} ≤
          ENNReal.ofReal (((2:ℝ)^N)^sig*r^((n+1:ℝ)/2))) →
      ∀ (i : ι) (J : ℕ) (b : PolicyDescriptor), descriptorValid N b →
      (μ.prod ν) {z | z.1∈F.domain i ∧ z∈good ∧
        (z.1,dir z)∉endpointGood (assemblyClassLaw μ (F.domain i)) (F.mass i)
          N sig (1000*(n+2:ℝ)) J 0 b} ≤ μ (F.domain i)*ENNReal.ofReal (((2:ℝ)^N)^(-sig)) := by
  obtain ⟨N₀,hfiber⟩ := uniform_original_fiber_test_bound (d:=n+1) sig hsig
  refine ⟨N₀,?_⟩
  intro N hN ι μ ν _ _ B chi F good hgood dir hdir hunit hcap i J b hb
  let := F.law_probability i
  let bad : Set (V×V) := {z | z∈good ∧
    (z.1,dir z)∉endpointGood (assemblyClassLaw μ (F.domain i)) (F.mass i)
      N sig (1000*(n+2:ℝ)) J 0 b}
  have hm : MeasurableSet bad := hgood.inter
    ((measurable_endpointGood _ _ _ _ _ _ _ _).preimage (measurable_fst.prodMk hdir)).compl
  have he : (μ.restrict (F.domain i)).prod ν bad =
      (μ.prod ν) {z | z.1∈F.domain i ∧ z∈good ∧
        (z.1,dir z)∉endpointGood (assemblyClassLaw μ (F.domain i)) (F.mass i)
          N sig (1000*(n+2:ℝ)) J 0 b} := by
    rw [Measure.restrict_prod_eq_prod_univ,Measure.restrict_apply hm]
    congr 1
    ext z
    simp only [bad,mem_inter_iff,mem_ofPred_eq,mem_prod,mem_univ,and_true]
    tauto
  rw [←he,Measure.prod_apply hm]
  calc
    _ ≤ ∫⁻ _x, ENNReal.ofReal (((2:ℝ)^N)^(-sig)) ∂μ.restrict (F.domain i) := by
      apply lintegral_mono_ae
      filter_upwards [F.ae_occupied_original i (descriptorAnchor b),ae_restrict_of_ae hcap] with x hx hc
      have h := hfiber N hN (assemblyClassLaw μ (F.domain i)) (F.mass i) B
        ((n+1:ℝ)/2+chi) (F.profile i) ν (Prod.mk x ⁻¹' good) (hgood.preimage measurable_prodMk_left)
        (fun y => dir (x,y)) (hdir.comp measurable_prodMk_left) (fun y hy => hunit _ hy)
        (by simpa only [Nat.cast_add,Nat.cast_one,mem_preimage] using hc) J b hb x hx
      simpa [bad,Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using h
    _ = μ (F.domain i)*ENNReal.ofReal (((2:ℝ)^N)^(-sig)) := by simp [mul_comm]
end GraphLiteralSupport.CurrentFalconer.TreeND
end
end

end OAI
