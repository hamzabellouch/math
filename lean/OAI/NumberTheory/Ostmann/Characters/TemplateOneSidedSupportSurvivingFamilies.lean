import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedSupportSurvivingExpressions
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedSupportTransportFamilies

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedSupportSurviving
open Template SymbolicHistory Preliminaries TemplateOneSidedRelabel
open TemplateOneSidedSupportTelescoping TemplateOneSidedSupportTransport
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def groupedPrimeAssignment {k j Q : ℕ} (width : Role→ℕ)
    (p : SurvivingPrimeIndex k j width→PrimeUpTo Q) :
    (Σi:SurvivingSlot k j,Fin (survivingWidth k j width i))→ℤ :=
  fun i=>((p (survivingPrimeEquiv k j width i)).val:ℤ)

theorem matched_transferSupport_iff_guarded_sampled {k j Q : ℕ} (hj : j<k)
    (B V : (l:ℕ)→State k (l+1)→ℤ)
    (extra : (l:ℕ)→ℤ→State k l→HistoryReconstruction.Tree l→Prop)
    (s : ℤ) (P : ℕ+) (width : Role→ℕ)
    (p : SurvivingPrimeIndex k j width→PrimeUpTo Q)
    (e : Equiv.Perm (CopiedConstituent (schedule k j) j width))
    (t : HistoryReconstruction.Tree j)
    (hpairs : Pairwise (fun i v=>(p i).val.Coprime (p v).val)) :
    let x:=groupedPrimeAssignment width p
    let π:=groupedPermutation k j width e
    TransferSupport k B V extra j s (evalExpressions x (groupedExpressions k j width P e)) t ↔
      pivotPrimeGuard width P p ∧ SampledTransferSupport k (fun u=>∏a,x (π ⟨u,a⟩))
        B V extra j (origins k j) s (evalExpressions x (groupedExpressions k j width P e)) t := by
  let E : Equiv.Perm (SurvivingPrimeIndex k j width) := Equiv.sumCongr e (Equiv.refl _)
  let p' := fun i=>p (E i)
  have hp' : Pairwise (fun i v=>(p' i).val.Coprime (p' v).val) := by
    intro i v hiv
    exact hpairs (fun h=>hiv (E.injective h))
  have hg : pivotPrimeGuard width P p' ↔ pivotPrimeGuard width P p := by
    constructor
    · intro h i
      simpa only [p',E.apply_symm_apply] using h (E.symm i)
    · intro h i
      exact h (E i)
  have he : evalExpressions (groupedPrimeAssignment width p) (groupedExpressions k j width P e) =
      sourceState k j P (copiedSampleState (schedule k j) j width (fun i=>p' (.inl i)))
        (outsideSampleState (schedule k j) j width (fun i=>p' (.inr i))) :=
    groupedExpressions_prime_eval k j width P e p
  have hξ : (fun u=>∏a,groupedPrimeAssignment width p (groupedPermutation k j width e ⟨u,a⟩)) =
      Sum.elim (copiedSampleState (schedule k j) j width (fun i=>p' (.inl i)))
        (outsideSampleState (schedule k j) j width (fun i=>p' (.inr i))) := by
    funext u
    cases u <;> simp only [groupedPrimeAssignment,groupedPermutation,Equiv.trans_apply,
      Equiv.apply_symm_apply] <;> rfl
  dsimp only
  rw [he,hξ]
  exact (prime_transferSupport_iff_guarded_sampled hj B V extra s P width p' t hp').trans
    (and_congr_left (fun _=>hg))

theorem matched_transferSupport_iff_guarded_families {k j Q : ℕ} (hj : j<k)
    (B V : (l:ℕ)→State k (l+1)→ℤ)
    (extra : (l:ℕ)→ℤ→State k l→HistoryReconstruction.Tree l→Prop)
    (s : ℤ) (P : ℕ+) (width : Role→ℕ)
    (p : SurvivingPrimeIndex k j width→PrimeUpTo Q)
    (e : Equiv.Perm (CopiedConstituent (schedule k j) j width))
    (t : HistoryReconstruction.Tree j)
    (hpairs : Pairwise (fun i v=>(p i).val.Coprime (p v).val)) :
    let x:=groupedPrimeAssignment width p
    let D:=actualFamilies k (survivingWidth k j width) j (origins k j) s
      (groupedExpressions k j width P (Equiv.refl _)) t
    TransferSupport k B V extra j s (evalExpressions x (groupedExpressions k j width P e)) t ↔
      pivotPrimeGuard width P p ∧
      TransferCoreSupport k B V extra j s (evalExpressions x (groupedExpressions k j width P e)) t ∧
      ∀i,familyCoprime (relabelFamilies (groupedPermutation k j width e) D) i x := by
  dsimp only
  have hh := matched_transferSupport_iff_guarded_sampled hj B V extra s P width p e t hpairs
  dsimp only at hh
  rw [hh]
  apply and_congr_right
  intro _
  rw [← groupedExpressions_relabel k j width P e,relabelExpressions_eval]
  rw [sampled_support_iff_all_families k (survivingWidth k j width) B V extra j
    (origins k j) s (groupedExpressions k j width P (Equiv.refl _)) t
    (fun i=>groupedPrimeAssignment width p (groupedPermutation k j width e i))]
  apply and_congr_right
  intro _
  constructor
  · intro h i
    obtain ⟨v,rfl⟩ := (groupedPermutation k j width e).surjective i
    exact (familyCoprime_relabel _ _ v _).mpr (h v)
  · intro h i
    exact (familyCoprime_relabel _ _ i _).mp (h (groupedPermutation k j width e i))

end Ostmann.Characters.TemplateOneSidedSupportSurviving

end

end OAI
