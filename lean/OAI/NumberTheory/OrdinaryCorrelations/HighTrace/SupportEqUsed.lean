import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Ordered
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
open Finset Classical
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L t : ℕ}
namespace WitnessConfiguration
variable (x : WitnessConfiguration D h ℓ L t)

lemma support_eq_used : support x.primeCode=x.family.used x.primitives := by
  ext p
  exact (mem_support _ p).trans (x.primeCode_support p)

noncomputable def name (p : S.Index) (hp : p ∈ support x.primeCode) :
    Fin (support x.primeCode).card := (FiniteSlotEncoding.enum (support x.primeCode)).symm ⟨p,hp⟩

lemma values_name (p : S.Index) (hp : p ∈ support x.primeCode) :
    values x.primeCode (x.name p hp)=p := by
  change ((FiniteSlotEncoding.enum (support x.primeCode))
    ((FiniteSlotEncoding.enum (support x.primeCode)).symm _)).val=p
  rw [Equiv.apply_symm_apply]

lemma selected_mem_support {j : Fin t} (d : x.family.Test j) (hd : d.Valid) :
    d.selected ∈ support x.primeCode := by
  rw [x.support_eq_used]
  exact x.family.test_support_used x.primitives d _ (d.selected_mem hd)

lemma modulus_mem_support {j : Fin t} (d : x.family.Test j) :
    d.modulus ∈ support x.primeCode := by
  rw [x.support_eq_used]
  exact x.family.test_support_used x.primitives d _ d.modulus_mem

noncomputable def template (c : PrivateFamily.Case) (A : Finset (Fin t))
    (d : ∀ j : A, x.family.Test j.val) (hd : ∀ j, (d j).Valid) :
    WitnessTemplateCode ℓ L ⌈C₀*Real.log B⌉₊ t (support x.primeCode).card :=
  (x.metadata,pattern x.primeCode,
    ⟨⟨A.card,Nat.lt_succ_of_le (by simpa using Finset.card_le_univ A)⟩,
      fun i => (x.shape (d (c.ordered A i)),
        x.name (d (c.ordered A i)).selected (x.selected_mem_support _ (hd _)),
        x.name (d (c.ordered A i)).modulus (x.modulus_mem_support _),
        decide (d (c.ordered A i)).Linear)⟩)

lemma template_selected (c : PrivateFamily.Case) (A : Finset (Fin t))
    (d : ∀ j : A, x.family.Test j.val) (hd : ∀ j, (d j).Valid) (i : Fin A.card) :
    values x.primeCode ((x.template c A d hd).selected i)=(d (c.ordered A i)).selected :=
  x.values_name _ _

lemma template_modulus (c : PrivateFamily.Case) (A : Finset (Fin t))
    (d : ∀ j : A, x.family.Test j.val) (hd : ∀ j, (d j).Valid) (i : Fin A.card) :
    values x.primeCode ((x.template c A d hd).modulus i)=(d (c.ordered A i)).modulus :=
  x.values_name _ _

lemma template_expression (c : PrivateFamily.Case) (A : Finset (Fin t))
    (d : ∀ j : A, x.family.Test j.val) (hd : ∀ j, (d j).Valid) (i : Fin A.card) :
    ((x.template c A d hd).expression h i).relabel (values x.primeCode)=
      (d (c.ordered A i)).symbolic x.labels :=
  x.pattern_shape_expression _

lemma template_wellFormed (c : PrivateFamily.Case) (A : Finset (Fin t))
    (d : ∀ j : A, x.family.Test j.val) (hd : ∀ j, (d j).Valid)
    (hinj : Function.Injective (fun j => (d j).selected))
    (hfuture : ∀ i j : A, c.Precedes i.val j.val → ((d j).selected:ℕ) ∉ (d i).support) :
    (x.template c A d hd).WellFormed h := by
  apply WitnessTemplateCode.wellFormed_of_relabel (x.template c A d hd) h (values x.primeCode)
    (PrivateFamily.testEmbedding c A d hinj) (PrivateFamily.testSystem x.labels c A d hd hinj hfuture)
  · exact x.template_selected c A d hd
  · exact x.template_expression c A d hd
  · exact x.template_modulus c A d hd
  · intro i; rfl

lemma template_admissible (c : PrivateFamily.Case) (A : Finset (Fin t))
    (d : ∀ j : A, x.family.Test j.val) (hd : ∀ j, (d j).Valid)
    (hinj : Function.Injective (fun j => (d j).selected))
    (hfuture : ∀ i j : A, c.Precedes i.val j.val → ((d j).selected:ℕ) ∉ (d i).support)
    (hnd : ∀ j, if (d j).Linear then ¬(((d j).modulus:ℕ):ℤ) ∣ (d j).coefficient
      else (d j).expression ≠ 0)
    (hB : 0 ≤ B) (P : ℝ) (hP : ∀ p : S.Index, P ≤ (p:ℝ))
    (hupper : ∀ p : S.Index, (p:ℝ) ≤ Real.exp B)
    (r : S.Residues) (hq : ∀ i p, (x.family.witness i).spec.ResidueTest p
      (x.family.witness i).vertex (r p)) :
    ((x.template c A d hd).system h (x.template_wellFormed c A d hd hinj hfuture)).Admissible
      P (PrivateFamily.testSize B C₀ h ℓ L) (fun a => (values x.primeCode a:ℕ)) := by
  apply WitnessTemplateCode.system_admissible_of_relabel (x.template c A d hd) h
    (x.template_wellFormed c A d hd hinj hfuture) (values x.primeCode)
    (PrivateFamily.testEmbedding c A d hinj) (PrivateFamily.testSystem x.labels c A d hd hinj hfuture)
    (x.template_selected c A d hd) (x.template_expression c A d hd)
    (x.template_modulus c A d hd) (fun _ => rfl)
  exact PrivateFamily.testSystem_admissible x.labels c A d hd hinj hfuture hnd hB P hP hupper r hq

end WitnessConfiguration
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
