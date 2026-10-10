import Mathlib
import OAI.Combinatorics.SharpRamsey.Exposure.ExposureContexts

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators
noncomputable section
variable {Θ Ω B ι β : Type*} [Fintype Θ] [Fintype Ω] [Fintype B]
  [Fintype ι] [DecidableEq ι] [Fintype β]

omit [Fintype Ω] in

theorem exists_context_good_zero (n k : ℕ) (hn : 2≤n) (hk : 0<k)
    (J D a budget : ℝ) (hD : 0<D) (ha : 0<a)
    (μ : Law Θ) (p : Θ→Law (ι→β)) (e : Θ→B×Fin (n+k) ↪ ι)
    (own : Θ→ι→Option B) (hown : ∀ θ b x,own θ (e θ (b,x))=some b)
    (S : Θ→ι→Finset β)
    (hS : ∀ θ,μ.mass θ≠0→tupleSupported (p θ) (S θ))
    (hJ : ∀ θ i,Real.log (S θ i).card≤J)
    (hbudget : contextAverage μ (fun θ=>tupleDeficit J (p θ))≤budget) :
    ∃ t : Fin k,
      contextAverage μ (fun θ=>exposureBad n J D a k (p θ) (e θ) (own θ) t)≤
        budget/D+2*budget/((k:ℝ)*a) ∧
      (n:ℝ)*contextAverage μ (fun θ=>exposureSelectedBad n J D a k (p θ) (e θ) (own θ) t)≤
        budget/D+2*budget/((k:ℝ)*a) := by
  have hTC : contextAverage μ (fun θ=>totalCorrelation (p θ))≤budget := by
    apply le_trans _ hbudget
    apply contextAverage_mono μ
    intro θ hθ
    exact totalCorrelation_le_tupleDeficit (p θ) J
      (tupleSupported_marginal_cap (p θ) (S θ) (hS θ hθ) J (hJ θ))
  obtain ⟨t,ht⟩:=exists_context_round n k hn hk μ p e own hown
  have hbθ (θ : Θ) (hθ : μ.mass θ≠0) :
      exposureBad n J D a k (p θ) (e θ) (own θ) t≤
        tupleDeficit J (p θ)/D+exposureScores n k (p θ) (e θ) (own θ) t/a := by
    exact (exposureBad_budget n k J D a hD ha (p θ) (e θ) (own θ)
      (S θ) (hS θ hθ) (hJ θ) t).trans (by
        have hd:=exposureDeficits_le n k J (p θ) (e θ) (S θ) (hS θ hθ) (hJ θ) t
        gcongr)
  have hb:=contextAverage_mono μ hbθ
  simp only [contextAverage_add,contextAverage_div] at hb
  have hb' : contextAverage μ (fun θ=>exposureBad n J D a k (p θ) (e θ) (own θ) t)≤
      budget/D+2*budget/((k:ℝ)*a) := by
    calc
      _ ≤ _ := hb
      _ ≤ budget/D+(2*budget/(k:ℝ))/a :=
        add_le_add (div_le_div_of_nonneg_right hbudget hD.le)
          (div_le_div_of_nonneg_right
            (ht.trans (div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hTC (by norm_num)) (Nat.cast_nonneg k))) ha.le)
      _ = _ := by rw [div_div]
  refine ⟨t,hb',le_trans ?_ hb'⟩
  rw [←contextAverage_mul]
  apply contextAverage_mono μ
  intro θ _
  exact exposureSelectedBad_le n k J D a (p θ) (e θ) (own θ) (hown θ) t

lemma conditional_tupleSupported (p : Law Ω) (θ : Ω→Θ) (G : Ω→ι→β)
    (S : Θ→ι→Finset β)
    (hS : ∀ x,p.mass x≠0→∀ i,G x i∈S (θ x) i)
    (z : Θ) (hz : (p.map θ).mass z≠0) :
    tupleSupported ((p.cond θ z).map G) (S z) := by
  intro f hf i
  obtain ⟨x,hx,rfl⟩ := (p.cond θ z).map_support G f hf
  obtain ⟨hx,he⟩:=p.cond_support θ z hz x hx
  simpa only [he] using hS x hx i

theorem actual_source_exposure (n k : ℕ) (hn : 2≤n) (hk : 0<k)
    (J D a budget : ℝ) (hD : 0<D) (ha : 0<a)
    (p : Law Ω) (θ : Ω→Θ) (G : Ω→ι→β)
    (e : Θ→B×Fin (n+k) ↪ ι) (own : Θ→ι→Option B)
    (hown : ∀ z b x,own z (e z (b,x))=some b)
    (S : Θ→ι→Finset β)
    (hS : ∀ x,p.mass x≠0→∀ i,G x i∈S (θ x) i)
    (hJ : ∀ z i,Real.log (S z i).card≤J)
    (hbudget : (∑ z,(p.map θ).mass z*((Fintype.card ι:ℝ)*J-
      entropy ((p.cond θ z).map G)))≤budget) :
    ∃ t : Fin k,
      (∑ z,(p.map θ).mass z*exposureBad n J D a k
        ((p.cond θ z).map G) (e z) (own z) t)≤budget/D+2*budget/((k:ℝ)*a) ∧
      (n:ℝ)*(∑ z,(p.map θ).mass z*exposureSelectedBad n J D a k
        ((p.cond θ z).map G) (e z) (own z) t)≤budget/D+2*budget/((k:ℝ)*a) := by
  exact exists_context_good_zero n k hn hk J D a budget hD ha (p.map θ)
    (fun z=>(p.cond θ z).map G) e own hown S
    (conditional_tupleSupported p θ G S hS) hJ hbudget

end
end SharpLogRamsey.Selection

end

end OAI
