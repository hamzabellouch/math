import Mathlib
import OAI.Combinatorics.SharpRamsey.Exposure.ExposureMixture

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators NNReal
noncomputable section
variable {β C ι : Type} [Fintype β] [Fintype C] [Fintype ι] [DecidableEq ι]
namespace ExposureModel

abbrev FreshHistory (M : ExposureModel ι β C) := Σ z : M.History,C→Fin (M.remaining z)

def freshLaw (M : ExposureModel ι β C) (h : ∀ z,0<M.remaining z) : Law M.FreshHistory := by
  letI (z : M.History) : Nonempty (Fin (M.remaining z)) := ⟨⟨0,h z⟩⟩
  exact M.historyLaw.sigma (fun z=>Law.equiprobable (C→Fin (M.remaining z)))

omit [Fintype ι] [DecidableEq ι] in
lemma freshLaw_sum (M : ExposureModel ι β C) (h : ∀ z,0<M.remaining z)
    (φ : M.FreshHistory→ℝ) :
    (∑ x,(M.freshLaw h).mass x*φ x)=∑ z,M.historyLaw.mass z*
      ((∑ f : C→Fin (M.remaining z),φ ⟨z,f⟩)/Fintype.card (C→Fin (M.remaining z))) := by
  let (z : M.History) : Nonempty (Fin (M.remaining z)) := ⟨⟨0,h z⟩⟩
  unfold freshLaw
  rw [Law.sigma_sum]
  simp_rw [Law.equiprobable_sum]

omit [Fintype ι] [DecidableEq ι] in
lemma freshLaw_old (M : ExposureModel ι β C) (h : ∀ z,0<M.remaining z)
    (φ : M.History→ℝ) :
    (∑ x,(M.freshLaw h).mass x*φ x.1)=∑ z,M.historyLaw.mass z*φ z := by
  let (z : M.History) : Nonempty (Fin (M.remaining z)) := ⟨⟨0,h z⟩⟩
  rw [freshLaw_sum]
  apply sum_congr rfl
  intro z _
  congr 1
  change (∑ _f : C→Fin (M.remaining z),φ z)/_=φ z
  rw [sum_const,card_univ,nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ (ne_of_gt (show (0:ℝ)<Fintype.card (C→Fin (M.remaining z)) by exact_mod_cast Fintype.card_pos))

def afterDraw (M : ExposureModel ι β C) (h : ∀ z,0<M.remaining z) : ExposureModel ι β C where
  History := M.FreshHistory
  finiteHistory := inferInstance
  historyLaw := M.freshLaw h
  Index x := M.Index x.1
  finiteIndex _ := inferInstance
  decIndex _ := inferInstance
  tupleLaw x := M.tupleLaw x.1
  remaining x := M.remaining x.1
  embedding x := M.embedding x.1
  owner x := M.owner x.1
  origin x := M.origin x.1
  restore x := M.restore x.1
  restore_origin x := M.restore_origin x.1

omit [Fintype ι] [DecidableEq ι] in
lemma afterDraw_preserves (M : ExposureModel ι β C) (h : ∀ z,0<M.remaining z)
    (φ : (ι→β)→ℝ) : (M.afterDraw h).expectation φ=M.expectation φ :=
  M.freshLaw_old h (fun z=>∑ x,(M.tupleLaw z).mass x*φ (M.restore z x))

def freshBad (M : ExposureModel ι β C)
    (charge : ∀ z,M.Index z→M.Index z→NNReal) (J D a : ℝ) (x : M.FreshHistory) :
    Finset (M.Index x.1) :=
  badIndices (M.tupleLaw x.1) (M.embedding x.1) (M.owner x.1) (charge x.1) J D a x.2

def freshSelected (M : ExposureModel ι β C) (x : M.FreshHistory) : Finset (M.Index x.1) :=
  freshRepresentatives (M.embedding x.1) x.2

variable {A B K V : Type} [Fintype A] [Fintype B] [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

omit [Fintype ι] [DecidableEq ι] [FiniteDimensional K V] in
lemma fresh_bad_mean (M : ExposureModel ι (A×B) C) (h : ∀ z,0<M.remaining z)
    (v : B→V) (w : A→Module.Dual K V) (ρ : ℝ) (r s : ℕ) (J D a : ℝ) :
    (∑ x,(M.freshLaw h).mass x*
      ((M.freshBad (fun z=>reciprocalCharges (M.tupleLaw z) v w ρ r s) J D a x).card:ℝ))=
      M.mean (reciprocalBadStatistic v w ρ r s J D a) := by
  rw [freshLaw_sum]
  rfl

omit [Fintype ι] [DecidableEq ι] [FiniteDimensional K V] in
lemma fresh_selected_mean (M : ExposureModel ι (A×B) C) (h : ∀ z,0<M.remaining z)
    (v : B→V) (w : A→Module.Dual K V) (ρ : ℝ) (r s : ℕ) (J D a : ℝ) :
    (∑ x,(M.freshLaw h).mass x*((M.freshSelected x∩
      M.freshBad (fun z=>reciprocalCharges (M.tupleLaw z) v w ρ r s) J D a x).card:ℝ))=
      M.mean (reciprocalSelectedStatistic v w ρ r s J D a) := by
  rw [freshLaw_sum]
  rfl

end ExposureModel
end
end SharpLogRamsey.Selection

end

end OAI
