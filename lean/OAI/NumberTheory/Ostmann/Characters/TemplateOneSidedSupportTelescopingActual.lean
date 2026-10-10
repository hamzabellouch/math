import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedSupportTelescopingFamily

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedSupportTelescoping
open SymbolicHistory TemplateSupportRemoval Template Preliminaries
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {κ : Type*}

def actualFamilies (k : ℕ) (width : κ→ℕ) (j : ℕ) (o : SampleOrigins k j κ)
    (s : ℤ) (e : Expressions (ι:=(Σ r:κ,Fin (width r))) k j)
    (t : HistoryReconstruction.Tree j) (i : Σ r:κ,Fin (width r)) :
    Finset (Expr (Σ r:κ,Fin (width r))) := outsidePivotFamily k i.1 j o s e t

theorem actualFamilies_obstructions (k : ℕ) (width : κ→ℕ) (j : ℕ)
    (o : SampleOrigins k j κ) (s : ℤ)
    (e : Expressions (ι:=(Σ r:κ,Fin (width r))) k j) (t : HistoryReconstruction.Tree j)
    (b : Bool) (i : Σ r:κ,Fin (width r)) (q : Expr (Σ r:κ,Fin (width r)))
    (hq : q∈actualFamilies k width j o s e t i) :
    q∈obstructionExpressions k j b s e t :=
  outsidePivotFamily_mem_obstruction k i.1 j o b s e t q hq

theorem sampled_support_iff_all_families (k : ℕ) (width : κ→ℕ)
    (B V : (j:ℕ)→State k (j+1)→ℤ)
    (extra : (j:ℕ)→ℤ→State k j→HistoryReconstruction.Tree j→Prop)
    (j : ℕ) (o : SampleOrigins k j κ) (s : ℤ)
    (e : Expressions (ι:=(Σ r:κ,Fin (width r))) k j) (t : HistoryReconstruction.Tree j)
    (a : (Σ r:κ,Fin (width r))→ℤ) :
    SampledTransferSupport k (fun r=>∏b,a ⟨r,b⟩) B V extra j o s (evalExpressions a e) t ↔
      TransferCoreSupport k B V extra j s (evalExpressions a e) t ∧
        ∀i,familyCoprime (actualFamilies k width j o s e t) i a := by
  rw [sampledTransferSupport_iff_core_selected]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro i
  exact selectedOutsideCoprime_iff_family k i.1 (a i) j o s e t a

theorem sampled_value_eq_initial_hybrid [DecidableEq κ] (k : ℕ) (width : κ→ℕ)
    (B V : (j:ℕ)→State k (j+1)→ℤ)
    (extra : (j:ℕ)→ℤ→State k j→HistoryReconstruction.Tree j→Prop)
    (j : ℕ) (o : SampleOrigins k j κ) (s : ℤ)
    (e : Expressions (ι:=(Σ r:κ,Fin (width r))) k j) (t : HistoryReconstruction.Tree j)
    (mask : ((Σ r:κ,Fin (width r))→ℤ)→Bool) (f : ((Σ r:κ,Fin (width r))→ℤ)→ℂ)
    (a : (Σ r:κ,Fin (width r))→ℤ) :
    (if mask a then if SampledTransferSupport k (fun r=>∏b,a ⟨r,b⟩)
      B V extra j o s (evalExpressions a e) t then f a else 0 else 0)=
    hybridValue ∅ (fun x=>mask x=true ∧ TransferCoreSupport k B V extra j s (evalExpressions x e) t)
      (familyCoprime (actualFamilies k width j o s e t))
      (familyPolynomial (actualFamilies k width j o s e t)) f a := by
  rw [hybridValue_empty,sampled_support_iff_all_families]
  by_cases hm : mask a=true
  · simp only [hm,ite_true,true_and]
    have hp : (TransferCoreSupport k B V extra j s (evalExpressions a e) t ∧
        ∀i,familyCoprime (actualFamilies k width j o s e t) i a) ↔
        (TransferCoreSupport k B V extra j s (evalExpressions a e) t ∧
        ∀i,∀q∈actualFamilies k width j o s e t i,IsCoprime (a i) (q.integerEval a)) := Iff.rfl
    by_cases hg : TransferCoreSupport k B V extra j s (evalExpressions a e) t ∧
        ∀i,familyCoprime (actualFamilies k width j o s e t) i a
    · simp only [ite_eq_left hg,ite_eq_left (hp.mp hg)]
    · simp only [ite_eq_right hg,ite_eq_right (fun hh=>hg (hp.mpr hh))]
  · simp [hm]

theorem prime_transferSupport_iff_all_families {k Q : ℕ}
    (B V : (j:ℕ)→State k (j+1)→ℤ)
    (extra : (j:ℕ)→ℤ→State k j→HistoryReconstruction.Tree j→Prop)
    (j : ℕ) (hj : j≤k) (s : ℤ) (width : Role→ℕ)
    (p : (schedule k j).Constituent width→PrimeUpTo Q)
    (e : Expressions (ι:=(schedule k j).Constituent width) k j)
    (he : evalExpressions (fun i=>((p i).val:ℤ)) e=constituentSampleState (schedule k j) width p)
    (t : HistoryReconstruction.Tree j)
    (hp : Pairwise (fun u v=>(p u).val.Coprime (p v).val)) :
    TransferSupport k B V extra j s (evalExpressions (fun i=>((p i).val:ℤ)) e) t ↔
      TransferCoreSupport k B V extra j s (evalExpressions (fun i=>((p i).val:ℤ)) e) t ∧
        ∀i,familyCoprime (actualFamilies k (fun u=>width ((schedule k j).role u)) j
          (SampleOrigins.root k j) s e t) i (fun i=>((p i).val:ℤ)) := by
  have hpair : Pairwise (fun u v=>IsCoprime
      (evalExpressions (fun i=>((p i).val:ℤ)) e u)
      (evalExpressions (fun i=>((p i).val:ℤ)) e v)) := by
    rw [he]
    exact ((constituent_prime_support_iff (schedule k j) width p).mp hp).1
  have hs := transferSupport_iff_sampled B V extra j hj s
    (evalExpressions (fun i=>((p i).val:ℤ)) e) t hpair
  have hs' : TransferSupport k B V extra j s (evalExpressions (fun i=>((p i).val:ℤ)) e) t ↔
      SampledTransferSupport k (constituentSampleState (schedule k j) width p)
        B V extra j (SampleOrigins.root k j) s (evalExpressions (fun i=>((p i).val:ℤ)) e) t :=
    hs.trans (by rw [←he])
  exact hs'.trans (sampled_support_iff_all_families k (fun u=>width ((schedule k j).role u))
    B V extra j (SampleOrigins.root k j) s e t (fun i=>((p i).val:ℤ)))

end Ostmann.Characters.TemplateOneSidedSupportTelescoping

end

end OAI
