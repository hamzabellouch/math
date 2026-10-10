import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.FreeResidues
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.AvgAdd
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SpecificationSlotCount

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.ArithmeticSaving OrdinaryCorrelations.SharedSlotPatterns
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.FiniteIntegration
open Finset Classical
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h L : ℕ}
namespace Specification
variable (s : S.Specification D h L)

noncomputable def localIndicator (p : S.Index) (a : ZMod (p:ℕ)) : ℝ :=
  if s.ResidueTest p 0 a then 1 else 0
noncomputable def jointIndicator (r : S.Residues) : ℝ :=
  if ∀ p, s.ResidueTest p 0 (r p) then 1 else 0
lemma localIndicator_nonneg (p : S.Index) (a : ZMod (p:ℕ)) : 0 ≤ s.localIndicator p a := by
  unfold localIndicator; split_ifs <;> norm_num
lemma jointIndicator_nonneg (r : S.Residues) : 0 ≤ s.jointIndicator r := by
  unfold jointIndicator; split_ifs <;> norm_num
lemma jointIndicator_product (r : S.Residues) : s.jointIndicator r=∏ p, s.localIndicator p (r p) := by
  unfold jointIndicator localIndicator
  split_ifs with hr
  · simp only [hr,ite_true,prod_const_one]
  · obtain ⟨p,hp⟩ := not_forall.mp hr
    exact (prod_eq_zero (mem_univ p) (ite_eq_right hp)).symm

lemma localIndicator_mean (p : S.Index) :
    avg (s.localIndicator p) ≤ if p ∈ support (specPrimeCode s) then (p:ℝ)⁻¹ else 1 := by
  have he : p ∈ support (specPrimeCode s) ↔ (p:ℕ) ∈ s.primeSupport :=
    (mem_support _ p).trans (specPrimeCode_support s p).symm
  by_cases hp : (p:ℕ) ∈ s.primeSupport
  · rw [ite_eq_left (he.mpr hp)]
    have hh : ∃ v : ℤ, ∀ a : ZMod (p:ℕ), s.localIndicator p a ≤ PrimeSystem.activity (p:ℕ) a v := by
      rcases mem_insert.mp hp with hp | hp
      · refine ⟨0,?_⟩
        intro a
        unfold localIndicator
        split_ifs with ht
        · rw [PrimeSystem.activity,ite_eq_left (ht.1 hp)]
        · exact activity_nonneg p a _
      · obtain ⟨i,_,hpi⟩ := mem_biUnion.mp hp
        refine ⟨s.offset i.castSucc,?_⟩
        intro a
        unfold localIndicator
        split_ifs with ht
        · have hh := ht.2 i (Nat.mem_primeFactors.mp hpi).2.1
          simp only [zero_add] at hh
          rw [PrimeSystem.activity,ite_eq_left hh]
        · exact activity_nonneg p a _
    obtain ⟨v,hv⟩ := hh
    exact (avg_mono hv).trans_eq (activity_mean p v)
  · rw [ite_eq_right (mt he.mp hp)]
    have hh : s.localIndicator p=(fun _ => 1) := by
      funext a
      exact ite_eq_left (s.test_vacuous p hp 0 a)
    rw [hh,avg_const]

lemma jointIndicator_mean_le : avg s.jointIndicator ≤ s.primeWeight := by
  have hi : s.jointIndicator=fun r => ∏ p, s.localIndicator p (r p) := funext s.jointIndicator_product
  rw [hi]
  have he : avg (fun r : S.Residues => ∏ p, s.localIndicator p (r p)) =
      ∏ p : S.Index, avg (s.localIndicator p) := by
    convert avg_product (Ω:=fun p : S.Index => ZMod (p:ℕ)) s.localIndicator using 1
    congr 1
    exact Subsingleton.elim _ _
  rw [he]
  calc
    _ ≤ ∏ p : S.Index, if p ∈ support (specPrimeCode s) then (p:ℝ)⁻¹ else 1 :=
      prod_le_prod₀ (fun p _ => avg_nonneg (s.localIndicator_nonneg p))
        (fun p _ => s.localIndicator_mean p)
    _ = _ := by
      unfold primeWeight
      rw [prod_ite_mem,univ_inter]
end Specification

noncomputable def deletedIndicator (D : S.DivisorFamily B τ C₀) (h L : ℕ) (r : S.Residues) : ℝ :=
  if ∃ s : S.Specification D h L, s.Primitive ∧ ∀ p, s.ResidueTest p 0 (r p) then 1 else 0
noncomputable def deletedDensity (D : S.DivisorFamily B τ C₀) (h L : ℕ) : ℝ :=
  avg (deletedIndicator D h L)

lemma deletedIndicator_integer_zero (n : ℤ) :
    deletedIndicator D h L (S.integerResidues n)=0 ↔ VertexAllowed D h L n := by
  unfold deletedIndicator VertexAllowed
  simp only [ite_eq_right_iff,one_ne_zero,imp_false,not_exists,not_and]
  constructor
  · intro hn s hs
    have hh := s.qualifies_iff_residueTests n 0
    simp only [add_zero] at hh
    exact (hn s hs) ∘ hh.mp
  · intro hn s hs hh
    have he := s.qualifies_iff_residueTests n 0
    simp only [add_zero] at he
    exact hn s hs (he.mpr hh)

lemma deletedDensity_le_majorant : deletedDensity D h L ≤ specificationMajorant D h L := by
  have hp (r : S.Residues) : deletedIndicator D h L r ≤
      ∑ s : S.Specification D h L, s.jointIndicator r := by
    unfold deletedIndicator
    split_ifs with he
    · obtain ⟨s,_,hr⟩ := he
      have hi : s.jointIndicator r=1 := ite_eq_left hr
      rw [←hi]
      exact single_le_sum (fun t _ => t.jointIndicator_nonneg r) (mem_univ s)
    · exact sum_nonneg (fun s _ => s.jointIndicator_nonneg r)
  unfold deletedDensity specificationMajorant
  apply (avg_mono hp).trans
  rw [OrdinaryCorrelations.SourceCylinder.avg_sum']
  exact sum_le_sum (fun s _ => s.jointIndicator_mean_le)

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
