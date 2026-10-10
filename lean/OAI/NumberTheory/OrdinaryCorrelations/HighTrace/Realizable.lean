import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SourcePrimeUpper
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SupportEqUsed
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.WitnessTestDescriptor

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.ArithmeticSaving
open OrdinaryCorrelations.SharedSlotPatterns
open Finset Classical Filter
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L t : ℕ}
namespace WitnessConfiguration
variable (x : WitnessConfiguration D h ℓ L t)

def Realizable : Prop := JointlyRealizable x.line (x.primitives++List.ofFn x.family.witness)
noncomputable def primeWeight : ℝ := ∏ p ∈ support x.primeCode, (p:ℝ)⁻¹
lemma primeWeight_nonneg : 0 ≤ x.primeWeight := prod_nonneg (fun p hp => by positivity)

structure Certificate (P K : ℝ) (r : ℕ) where
  code : WitnessTemplateCode ℓ L ⌈C₀*Real.log B⌉₊ t (support x.primeCode).card
  metadata_eq : code.1=x.metadata
  pattern_eq : code.2.1=pattern x.primeCode
  formed : code.WellFormed h
  rank_ge : r ≤ code.rank
  admissible : (code.system h formed).Admissible P K (fun a => (values x.primeCode a:ℕ))

end WitnessConfiguration

theorem source_configuration_certificate (h : ℕ) (hh : 0 < h) (τ C₀ : ℝ) (hτ : τ < 2) :
    ∀ᶠ B : ℝ in atTop, ∀ (D : (sourceSystem B).DivisorFamily B τ C₀)
      (x : WitnessConfiguration D h (sourceLength B) (pathLength B) (listCutoff B)),
      x.Realizable → Nonempty (x.Certificate (sourceMinPrime B)
        (PrivateFamily.testSize B C₀ h (sourceLength B) (pathLength B)) ⌈B^(2*epsilon)⌉₊) := by
  filter_upwards [source_crude_witness_tests h hh τ C₀ hτ,eventually_ge_atTop (1:ℝ)] with B hb hB
  intro D x hx
  obtain ⟨c,A,d,hcard,hd,hinj,hfuture,hnd,_⟩ := hb D x.line x.primitives x.family hx
  obtain ⟨r,hr⟩ := hx
  have hq (i) (p) : (x.family.witness i).spec.ResidueTest p (x.family.witness i).vertex (r p) :=
    hr (x.family.witness i) (List.mem_append_right _ (List.mem_ofFn.mpr ⟨i,rfl⟩)) p
  refine ⟨{ code := x.template c A d hd
            metadata_eq := rfl
            pattern_eq := rfl
            formed := x.template_wellFormed c A d hd hinj hfuture
            rank_ge := Nat.ceil_le.mpr hcard
            admissible := ?_ }⟩
  exact x.template_admissible c A d hd hinj hfuture hnd (by linarith) (sourceMinPrime B)
    (fun p => (source_prime_lower B hB p).le) (source_prime_upper B hB) r hq

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
