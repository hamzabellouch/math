import Mathlib
import OAI.Combinatorics.SharpRamsey.Exposure.ExposureRealization

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators
noncomputable section
variable {β C : Type} [Fintype β] [Fintype C]

abbrev StateStatistic (β C : Type) [Fintype β] :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (m : ℕ),
    Law (I→β)→(C×Fin m↪I)→(I→Option C)→ℝ

namespace ExposureModel
variable {ι : Type} [Fintype ι] [DecidableEq ι]

def mean (M : ExposureModel ι β C) (F : StateStatistic β C) : ℝ :=
  ∑ z,M.historyLaw.mass z*F (M.Index z) (M.remaining z) (M.tupleLaw z) (M.embedding z) (M.owner z)

omit [Fintype C] in
lemma initial_mean (p : Law (ι→β)) {m : ℕ} (e : C×Fin m↪ι) (own : ι→Option C)
    (F : StateStatistic β C) : (initial p e own).mean F=F ι m p e own := by
  change (∑ _z : Unit,(1/(Fintype.card Unit:ℝ))*F ι m p e own)=_
  simp

lemma join_mean {m : ℕ} (p : Law (ι→β)) (e : C×Fin (m+1)↪ι)
    (child : ∀ f : C→Fin (m+1), (freshRepresentatives e f→β)→
      ExposureModel ↥((freshRepresentatives e f)ᶜ) β C)
    (F : StateStatistic β C) :
    (join p e child).mean F=(∑ f : C→Fin (m+1),∑ z,
      (p.restrict (freshRepresentatives e f)).mass z*(child f z).mean F)/
        Fintype.card (C→Fin (m+1)) := by
  unfold mean
  change (∑ h,((Law.equiprobable (C→Fin (m+1))).sigma (fun f=>
    (p.restrict (freshRepresentatives e f)).sigma (fun z=>(child f z).historyLaw))).mass h*
      F ((child h.1 h.2.1).Index h.2.2) ((child h.1 h.2.1).remaining h.2.2)
        ((child h.1 h.2.1).tupleLaw h.2.2) ((child h.1 h.2.1).embedding h.2.2)
          ((child h.1 h.2.1).owner h.2.2))=_
  rw [Law.sigma_sum]
  simp_rw [Law.sigma_sum]
  exact Law.equiprobable_sum _ _

end ExposureModel

def exposureAverage (F : StateStatistic β C) (n : ℕ) : (k : ℕ)→ {ι : Type}→
    [Fintype ι] → [DecidableEq ι] → Law (ι→β)→(C×Fin (n+k)↪ι)→(ι→Option C)→Fin k→ℝ
  | 0,_,_,_,_,_,_,j => Fin.elim0 j
  | k+1,I,_,_,p,e,own,j => Fin.cases (F I (n+(k+1)) p e own)
    (fun t=>(∑ f : C→Fin (n+k+1),∑ z,(p.restrict (freshRepresentatives e f)).mass z*
      exposureAverage F n k ((p.cond (fun y (i:freshRepresentatives e f)=>y i) z).restrict
        (freshRepresentatives e f)ᶜ) (remainingEmbedding e f) (fun i=>own i) t)/
      Fintype.card (C→Fin (n+k+1))) j

theorem ExposureModel.atRound_mean (F : StateStatistic β C) (n k : ℕ)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : Law (ι→β)) (e : C×Fin (n+k)↪ι) (own : ι→Option C) (t : Fin k) :
    (atRound n k p e own t).mean F=exposureAverage F n k p e own t := by
  induction k generalizing ι with
  | zero => exact Fin.elim0 t
  | succ k ih =>
    refine Fin.cases ?_ (fun j=>?_) t
    · exact initial_mean p e own F
    · change (join p e _).mean F=_
      rw [join_mean]
      simp_rw [ih]
      rfl

variable {A B K V : Type} [Fintype A] [Fintype B] [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

def reciprocalBadStatistic (v : B→V) (w : A→Module.Dual K V) (ρ : ℝ) (r s : ℕ)
    (J D a : ℝ) : StateStatistic (A×B) C :=
  fun _ _ _ _ p e own=>roundBad p e own (reciprocalCharges p v w ρ r s) J D a

def reciprocalSelectedStatistic (v : B→V) (w : A→Module.Dual K V) (ρ : ℝ) (r s : ℕ)
    (J D a : ℝ) : StateStatistic (A×B) C :=
  fun _ _ _ _ p e own=>roundSelectedBad p e own (reciprocalCharges p v w ρ r s) J D a

omit [FiniteDimensional K V] in
lemma exposureAverage_bad (v : B→V) (w : A→Module.Dual K V) (ρ : ℝ) (r s n k : ℕ)
    (J D a : ℝ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : Law (ι→A×B)) (e : C×Fin (n+k)↪ι) (own : ι→Option C) (t : Fin k) :
    exposureAverage (reciprocalBadStatistic v w ρ r s J D a) n k p e own t=
      chargedBad v w ρ r s n J D a k p e own t := by
  induction k generalizing ι with
  | zero => exact Fin.elim0 t
  | succ k ih =>
    refine Fin.cases ?_ (fun j=>?_) t
    · rfl
    · change (∑ f : C→Fin (n+k+1),∑ z,(p.restrict (freshRepresentatives e f)).mass z*
        exposureAverage _ n k _ _ _ j)/_=_
      simp_rw [ih]
      rfl

omit [FiniteDimensional K V] in
lemma exposureAverage_selected (v : B→V) (w : A→Module.Dual K V) (ρ : ℝ) (r s n k : ℕ)
    (J D a : ℝ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : Law (ι→A×B)) (e : C×Fin (n+k)↪ι) (own : ι→Option C) (t : Fin k) :
    exposureAverage (reciprocalSelectedStatistic v w ρ r s J D a) n k p e own t=
      chargedSelectedBad v w ρ r s n J D a k p e own t := by
  induction k generalizing ι with
  | zero => exact Fin.elim0 t
  | succ k ih =>
    refine Fin.cases ?_ (fun j=>?_) t
    · rfl
    · change (∑ f : C→Fin (n+k+1),∑ z,(p.restrict (freshRepresentatives e f)).mass z*
        exposureAverage _ n k _ _ _ j)/_=_
      simp_rw [ih]
      rfl

omit [FiniteDimensional K V] in
theorem ExposureModel.atRound_bad_selected
    (v : B→V) (w : A→Module.Dual K V) (ρ : ℝ) (r s n k : ℕ)
    (J D a : ℝ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : Law (ι→A×B)) (e : C×Fin (n+k)↪ι) (own : ι→Option C) (t : Fin k) :
    (atRound n k p e own t).mean (reciprocalBadStatistic v w ρ r s J D a)=
      chargedBad v w ρ r s n J D a k p e own t ∧
    (atRound n k p e own t).mean (reciprocalSelectedStatistic v w ρ r s J D a)=
      chargedSelectedBad v w ρ r s n J D a k p e own t := by
  constructor
  · rw [atRound_mean,exposureAverage_bad]
  · rw [atRound_mean,exposureAverage_selected]

end
end SharpLogRamsey.Selection

end

end OAI
