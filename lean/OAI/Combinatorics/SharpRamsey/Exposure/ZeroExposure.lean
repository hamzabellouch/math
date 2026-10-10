import Mathlib
import OAI.Combinatorics.SharpRamsey.Exposure.SourceExposure
import OAI.Combinatorics.SharpRamsey.Exposure.SourceZero

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators
noncomputable section
variable {β C : Type} [Fintype β] [Fintype C]

def zeroBadStatistic (J D a : ℝ) : StateStatistic β C :=
  fun _ _ _ _ p e own=>roundBad p e own (fun _ _=>0) J D a

def zeroSelectedStatistic (J D a : ℝ) : StateStatistic β C :=
  fun _ _ _ _ p e own=>roundSelectedBad p e own (fun _ _=>0) J D a

lemma exposureAverage_zero_bad (n k : ℕ) (J D a : ℝ)
    {ι : Type} [Fintype ι] [DecidableEq ι] (p : Law (ι→β))
    (e : C×Fin (n+k)↪ι) (own : ι→Option C) (t : Fin k) :
    exposureAverage (zeroBadStatistic J D a) n k p e own t=exposureBad n J D a k p e own t := by
  induction k generalizing ι with
  | zero => exact Fin.elim0 t
  | succ k ih =>
    refine Fin.cases ?_ (fun j=>?_) t
    · rfl
    · change (∑ f : C→Fin (n+k+1),∑ z,(p.restrict (freshRepresentatives e f)).mass z*
        exposureAverage _ n k _ _ _ j)/_=_
      simp_rw [ih]
      rfl

lemma exposureAverage_zero_selected (n k : ℕ) (J D a : ℝ)
    {ι : Type} [Fintype ι] [DecidableEq ι] (p : Law (ι→β))
    (e : C×Fin (n+k)↪ι) (own : ι→Option C) (t : Fin k) :
    exposureAverage (zeroSelectedStatistic J D a) n k p e own t=
      exposureSelectedBad n J D a k p e own t := by
  induction k generalizing ι with
  | zero => exact Fin.elim0 t
  | succ k ih =>
    refine Fin.cases ?_ (fun j=>?_) t
    · rfl
    · change (∑ f : C→Fin (n+k+1),∑ z,(p.restrict (freshRepresentatives e f)).mass z*
        exposureAverage _ n k _ _ _ j)/_=_
      simp_rw [ih]
      rfl

namespace ExposureModel
variable {ι Θ Ω : Type} [Fintype ι] [DecidableEq ι] [Fintype Θ] [Fintype Ω]

lemma contextual_positive_general (n k : ℕ) (hn : 0<n) (p : Law Ω) (θ : Ω→Θ) (G : Ω→ι→β)
    (e : Θ→C×Fin (n+k)↪ι) (own : Θ→ι→Option C) (t : Fin k)
    (z : (contextual n k p θ G e own t).History) :
    0<(contextual n k p θ G e own t).remaining z :=
  hn.trans_le (atRound_remaining n k ((p.cond θ z.1).map G) (e z.1) (own z.1) t z.2)

omit [Fintype ι] [DecidableEq ι] in
lemma fresh_zero_bad_mean (M : ExposureModel ι β C) (h : ∀ z,0<M.remaining z) (J D a : ℝ) :
    (∑ x,(M.freshLaw h).mass x*((M.freshBad (fun _ _ _=>0) J D a x).card:ℝ))=
      M.mean (zeroBadStatistic J D a) := by
  rw [freshLaw_sum]
  rfl

omit [Fintype ι] [DecidableEq ι] in
lemma fresh_zero_selected_mean (M : ExposureModel ι β C) (h : ∀ z,0<M.remaining z) (J D a : ℝ) :
    (∑ x,(M.freshLaw h).mass x*((M.freshSelected x∩M.freshBad (fun _ _ _=>0) J D a x).card:ℝ))=
      M.mean (zeroSelectedStatistic J D a) := by
  rw [freshLaw_sum]
  rfl

lemma contextual_zero_bad_mean (n k : ℕ) (p : Law Ω) (θ : Ω→Θ) (G : Ω→ι→β)
    (e : Θ→C×Fin (n+k)↪ι) (own : Θ→ι→Option C) (t : Fin k) (J D a : ℝ) :
    (contextual n k p θ G e own t).mean (zeroBadStatistic J D a)=
      ∑ z,(p.map θ).mass z*exposureBad n J D a k ((p.cond θ z).map G) (e z) (own z) t := by
  rw [contextual,mix_mean]
  simp_rw [atRound_mean,exposureAverage_zero_bad]

lemma contextual_zero_selected_mean (n k : ℕ) (p : Law Ω) (θ : Ω→Θ) (G : Ω→ι→β)
    (e : Θ→C×Fin (n+k)↪ι) (own : Θ→ι→Option C) (t : Fin k) (J D a : ℝ) :
    (contextual n k p θ G e own t).mean (zeroSelectedStatistic J D a)=
      ∑ z,(p.map θ).mass z*exposureSelectedBad n J D a k ((p.cond θ z).map G) (e z) (own z) t := by
  rw [contextual,mix_mean]
  simp_rw [atRound_mean,exposureAverage_zero_selected]
end ExposureModel
open ExposureModel

variable {ι Θ Ω : Type} [Fintype ι] [DecidableEq ι] [Fintype Θ] [Fintype Ω]

theorem actual_realized_zero (n k : ℕ) (hn : 2≤n) (hk : 0<k)
    (J D a budget : ℝ) (hD : 0<D) (ha : 0<a)
    (p : Law Ω) (θ : Ω→Θ) (G : Ω→ι→β)
    (e : Θ→C×Fin (n+k)↪ι) (own : Θ→ι→Option C)
    (hown : ∀ z b x,own z (e z (b,x))=some b)
    (S : Θ→ι→Finset β)
    (hS : ∀ x,p.mass x≠0→∀ i,G x i∈S (θ x) i)
    (hJ : ∀ z i,Real.log (S z i).card≤J)
    (hbudget : (∑ z,(p.map θ).mass z*((Fintype.card ι:ℝ)*J-
      entropy ((p.cond θ z).map G)))≤budget) :
    ∃ t : Fin k,
      let E:=contextual n k p θ G e own t
      let hp:=contextual_positive_general n k (by omega : 0<n) p θ G e own t
      let bad:=E.freshBad (fun _ _ _=>0) J D a
      (∑ x,(E.freshLaw hp).mass x*((bad x).card:ℝ))≤budget/D+2*budget/((k:ℝ)*a) ∧
      (n:ℝ)*(∑ x,(E.freshLaw hp).mass x*((E.freshSelected x∩bad x).card:ℝ))≤
        budget/D+2*budget/((k:ℝ)*a) ∧
      (E.afterDraw hp).joint.map (fun x=>(E.afterDraw hp).restore x.1 x.2)=p.map G := by
  obtain ⟨t,hb,hs⟩:=actual_source_exposure n k hn hk J D a budget hD ha
    p θ G e own hown S hS hJ hbudget
  refine ⟨t,?_,?_,?_⟩
  · rw [fresh_zero_bad_mean,contextual_zero_bad_mean]
    exact hb
  · rw [fresh_zero_selected_mean,contextual_zero_selected_mean]
    exact hs
  · apply restored_map
    intro φ
    rw [afterDraw_preserves,contextual_preserves,Law.sum_map]

end
end SharpLogRamsey.Selection

end

end OAI
