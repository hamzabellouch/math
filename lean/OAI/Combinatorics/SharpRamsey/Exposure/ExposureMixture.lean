import Mathlib
import OAI.Combinatorics.SharpRamsey.Exposure.ExposureAverages

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators
noncomputable section
variable {β C ι Θ : Type} [Fintype β] [Fintype C] [Fintype ι]
  [DecidableEq ι] [Fintype Θ]
namespace ExposureModel

def mix (ν : Law Θ) (M : Θ→ExposureModel ι β C) : ExposureModel ι β C where
  History := Σ z,(M z).History
  finiteHistory := inferInstance
  historyLaw := ν.sigma (fun z=>(M z).historyLaw)
  Index h := (M h.1).Index h.2
  finiteIndex _ := inferInstance
  decIndex _ := inferInstance
  tupleLaw h := (M h.1).tupleLaw h.2
  remaining h := (M h.1).remaining h.2
  embedding h := (M h.1).embedding h.2
  owner h := (M h.1).owner h.2
  origin h := (M h.1).origin h.2
  restore h := (M h.1).restore h.2
  restore_origin h := (M h.1).restore_origin h.2

omit [Fintype C] [Fintype ι] [DecidableEq ι] in
lemma mix_expectation (ν : Law Θ) (M : Θ→ExposureModel ι β C) (φ : (ι→β)→ℝ) :
    (mix ν M).expectation φ=∑ z,ν.mass z*(M z).expectation φ := by
  exact ν.sigma_sum (fun z=>(M z).historyLaw) _

omit [Fintype C] [Fintype ι] [DecidableEq ι] in
lemma mix_mean (ν : Law Θ) (M : Θ→ExposureModel ι β C) (F : StateStatistic β C) :
    (mix ν M).mean F=∑ z,ν.mass z*(M z).mean F := by
  exact ν.sigma_sum (fun z=>(M z).historyLaw) _

abbrev Joint (M : ExposureModel ι β C) := Σ z : M.History,M.Index z→β

def joint (M : ExposureModel ι β C) : Law M.Joint :=
  M.historyLaw.sigma M.tupleLaw

omit [Fintype C] [Fintype ι] [DecidableEq ι] in
lemma joint_expectation (M : ExposureModel ι β C) (φ : (ι→β)→ℝ) :
    (∑ x,M.joint.mass x*φ (M.restore x.1 x.2))=M.expectation φ :=
  M.historyLaw.sigma_sum _ _

omit [Fintype C] in
lemma restored_map (M : ExposureModel ι β C) (p : Law (ι→β))
    (h : ∀ φ,M.expectation φ=∑ x,p.mass x*φ x) :
    M.joint.map (fun x=>M.restore x.1 x.2)=p := by
  ext y
  have he := (M.joint_expectation (fun x=>if x=y then 1 else 0)).trans
    (h (fun x=>if x=y then 1 else 0))
  simpa only [Law.map,sum_filter,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',mem_univ,ite_true] using he

omit [Fintype C] in
lemma restore_support (M : ExposureModel ι β C) (p : Law (ι→β))
    (h : ∀ φ,M.expectation φ=∑ x,p.mass x*φ x)
    (z : M.History) (hz : M.historyLaw.mass z≠0) (x : M.Index z→β)
    (hx : (M.tupleLaw z).mass x≠0) : p.mass (M.restore z x)≠0 := by
  rw [←M.restored_map p h]
  have hp : 0<M.joint.mass ⟨z,x⟩ := lt_of_le_of_ne (M.joint.nonneg _) (Ne.symm (mul_ne_zero hz hx))
  exact ne_of_gt (hp.trans_le (M.joint.le_map (fun x=>M.restore x.1 x.2) ⟨z,x⟩))

def contextual (n k : ℕ) {Ω : Type} [Fintype Ω] (p : Law Ω) (θ : Ω→Θ)
    (G : Ω→ι→β) (e : Θ→C×Fin (n+k)↪ι) (own : Θ→ι→Option C) (t : Fin k) :
    ExposureModel ι β C :=
  mix (p.map θ) (fun z=>atRound n k ((p.cond θ z).map G) (e z) (own z) t)

theorem contextual_preserves (n k : ℕ) {Ω : Type} [Fintype Ω] (p : Law Ω) (θ : Ω→Θ)
    (G : Ω→ι→β) (e : Θ→C×Fin (n+k)↪ι) (own : Θ→ι→Option C) (t : Fin k)
    (φ : (ι→β)→ℝ) :
    (contextual n k p θ G e own t).expectation φ=∑ ω,p.mass ω*φ (G ω) := by
  rw [contextual,mix_expectation]
  simp_rw [atRound_preserves]
  have hm (z : Θ) : (∑ x,((p.cond θ z).map G).mass x*φ x)=
      ∑ ω,(p.cond θ z).mass ω*φ (G ω) := Law.sum_map _ _ _
  simp_rw [hm]
  exact p.history_sum θ _

theorem contextual_map (n k : ℕ) {Ω : Type} [Fintype Ω] (p : Law Ω) (θ : Ω→Θ)
    (G : Ω→ι→β) (e : Θ→C×Fin (n+k)↪ι) (own : Θ→ι→Option C) (t : Fin k) :
    (contextual n k p θ G e own t).joint.map
      (fun x=>(contextual n k p θ G e own t).restore x.1 x.2)=p.map G := by
  apply restored_map
  intro φ
  rw [contextual_preserves,Law.sum_map]

end ExposureModel
end
end SharpLogRamsey.Selection

end

end OAI
