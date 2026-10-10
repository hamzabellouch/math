import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedSupportTransportFamilies

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedSupportTransport
open SymbolicHistory TemplateSupportRemoval TemplateOneSidedSupportTelescoping
open TemplateOneSidedRelabel TemplateOneSidedBudget Template Preliminaries
attribute [local instance] Classical.propDecidable
variable {ι ν κ : Type*}

@[simp] theorem outsidePivotExpressions_relabel (π : ι → ν) (k : ℕ) (owner : κ)
    (j : ℕ) (o : SampleOrigins k j κ) (s : ℤ)
    (e : Expressions (ι:=ι) k j) (t : HistoryReconstruction.Tree j) :
    outsidePivotExpressions k owner j o s (relabelExpressions π e) t =
      (outsidePivotExpressions k owner j o s e t).map (relabel π) := by
  induction j generalizing s with
  | zero => rfl
  | succ j ih =>
    simp only [outsidePivotExpressions,pivotExpression_relabel,childExpressions_relabel,ih,
      List.map_append]
    split_ifs <;> simp only [List.map_cons,List.map_nil]

@[simp] theorem outsidePivotFamily_relabel (π : ι → ν) (k : ℕ) (owner : κ)
    (j : ℕ) (o : SampleOrigins k j κ) (s : ℤ)
    (e : Expressions (ι:=ι) k j) (t : HistoryReconstruction.Tree j) :
    outsidePivotFamily k owner j o s (relabelExpressions π e) t =
      (outsidePivotFamily k owner j o s e t).image (relabel π) := by
  simp only [outsidePivotFamily,outsidePivotExpressions_relabel]
  ext q
  simp only [List.mem_toFinset,List.mem_map,Finset.mem_image]

theorem relabel_actualFamilies_owner (k : ℕ) (width : κ → ℕ) (j : ℕ)
    (π : Equiv.Perm (Σr:κ,Fin (width r))) (o : SampleOrigins k j κ) (s : ℤ)
    (e : Expressions (ι:=(Σr:κ,Fin (width r))) k j) (t : HistoryReconstruction.Tree j)
    (i : Σr:κ,Fin (width r)) :
    relabelFamilies π (actualFamilies k width j o s e t) i =
      outsidePivotFamily k (π.symm i).1 j o s (relabelExpressions π e) t := by
  rw [outsidePivotFamily_relabel]
  rfl

theorem sampled_support_relabel_iff (k : ℕ) (width : κ → ℕ)
    (π : Equiv.Perm (Σr:κ,Fin (width r)))
    (B V : (j:ℕ)→State k (j+1)→ℤ)
    (extra : (j:ℕ)→ℤ→State k j→HistoryReconstruction.Tree j→Prop)
    (j : ℕ) (o : SampleOrigins k j κ) (s : ℤ)
    (e : Expressions (ι:=(Σr:κ,Fin (width r))) k j) (t : HistoryReconstruction.Tree j)
    (a : (Σr:κ,Fin (width r))→ℤ) :
    SampledTransferSupport k (fun r=>∏b,a (π ⟨r,b⟩)) B V extra j o s
      (evalExpressions a (relabelExpressions π e)) t ↔
    TransferCoreSupport k B V extra j s (evalExpressions a (relabelExpressions π e)) t ∧
      ∀i,familyCoprime (relabelFamilies π (actualFamilies k width j o s e t)) i a := by
  rw [relabelExpressions_eval]
  rw [sampled_support_iff_all_families k width B V extra j o s e t (fun i=>a (π i))]
  apply and_congr_right
  intro _
  constructor
  · intro h i
    obtain ⟨u,rfl⟩ := π.surjective i
    exact (familyCoprime_relabel π _ u a).mpr (h u)
  · intro h i
    exact (familyCoprime_relabel π _ i a).mp (h (π i))

def permutedSampledFamilies (k j : ℕ) (width : Role → ℕ)
    (π : Equiv.Perm ((schedule k j).Constituent width))
    (s : ℤ) (t : HistoryReconstruction.Tree j) :
    (schedule k j).Constituent width → Finset (Expr ((schedule k j).Constituent width)) :=
  relabelFamilies π.symm (actualFamilies k (fun u=>width ((schedule k j).role u)) j
    (SampleOrigins.root k j) s (sampledExpressions k j width) t)

theorem permutedSampledFamilies_owner (k j : ℕ) (width : Role → ℕ)
    (π : Equiv.Perm ((schedule k j).Constituent width)) (s : ℤ)
    (t : HistoryReconstruction.Tree j) (i : (schedule k j).Constituent width) :
    permutedSampledFamilies k j width π s t i =
      outsidePivotFamily k (π i).1 j (SampleOrigins.root k j) s
        (permutedSampledExpressions k j width π) t :=
  relabel_actualFamilies_owner k _ j π.symm _ s _ t i

theorem prime_permuted_transferSupport_iff_all_families {k Q : ℕ}
    (B V : (j:ℕ)→State k (j+1)→ℤ)
    (extra : (j:ℕ)→ℤ→State k j→HistoryReconstruction.Tree j→Prop)
    (j : ℕ) (hj : j≤k) (s : ℤ) (width : Role→ℕ)
    (π : Equiv.Perm ((schedule k j).Constituent width))
    (p : (schedule k j).Constituent width→PrimeUpTo Q) (t : HistoryReconstruction.Tree j)
    (hp : Pairwise (fun u v=>(p u).val.Coprime (p v).val)) :
    TransferSupport k B V extra j s
      (constituentSampleState (schedule k j) width (constituentAssignment (schedule k j) width π p)) t ↔
    TransferCoreSupport k B V extra j s
      (constituentSampleState (schedule k j) width (constituentAssignment (schedule k j) width π p)) t ∧
      ∀i,familyCoprime (permutedSampledFamilies k j width π s t) i (fun i=>((p i).val:ℤ)) := by
  have hp' : Pairwise (fun u v=>
      ((constituentAssignment (schedule k j) width π p) u).val.Coprime
        ((constituentAssignment (schedule k j) width π p) v).val) :=
    fun u v huv=>hp (fun h=>huv (π.symm.injective h))
  have hpair := ((constituent_prime_support_iff (schedule k j) width _).mp hp').1
  rw [transferSupport_iff_sampled B V extra j hj s _ t hpair]
  have hh := sampled_support_relabel_iff k (fun u=>width ((schedule k j).role u))
    π.symm B V extra j (SampleOrigins.root k j) s (sampledExpressions k j width) t
    (fun i=>((p i).val:ℤ))
  have he := permutedSampledExpressions_prime_eval k j width π p
  change evalExpressions (fun i=>((p i).val:ℤ))
    (relabelExpressions π.symm (sampledExpressions k j width)) = _ at he
  rw [he] at hh
  exact hh

end Ostmann.Characters.TemplateOneSidedSupportTransport

end

end OAI
