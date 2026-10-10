import Mathlib
import OAI.Combinatorics.SharpRamsey.Exposure.SourceCoupling
import OAI.Combinatorics.SharpRamsey.Selection.FreshRepresentatives

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators
noncomputable section
variable {Θ Ω C ι A B K V : Type} [Fintype Θ] [Fintype Ω] [Fintype C]
  [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B] [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
namespace ExposureModel

lemma contextual_remaining (n k : ℕ) (p : Law Ω) (θ : Ω→Θ) (G : Ω→ι→A×B)
    (e : Θ→C×Fin (n+k)↪ι) (own : Θ→ι→Option C) (t : Fin k)
    (z : (contextual n k p θ G e own t).History) :
    n≤(contextual n k p θ G e own t).remaining z :=
  atRound_remaining n k ((p.cond θ z.1).map G) (e z.1) (own z.1) t z.2

lemma contextual_positive (n k : ℕ) (hn : 0<n) (p : Law Ω) (θ : Ω→Θ) (G : Ω→ι→A×B)
    (e : Θ→C×Fin (n+k)↪ι) (own : Θ→ι→Option C) (t : Fin k)
    (z : (contextual n k p θ G e own t).History) :
    0<(contextual n k p θ G e own t).remaining z :=
  hn.trans_le (contextual_remaining n k p θ G e own t z)

omit [FiniteDimensional K V] in
lemma contextual_bad_mean (n k : ℕ) (p : Law Ω) (θ : Ω→Θ) (G : Ω→ι→A×B)
    (e : Θ→C×Fin (n+k)↪ι) (own : Θ→ι→Option C) (t : Fin k)
    (v : B→V) (w : A→Module.Dual K V) (ρ : ℝ) (r s : ℕ) (J D a : ℝ) :
    (contextual n k p θ G e own t).mean (reciprocalBadStatistic v w ρ r s J D a)=
      ∑ z,(p.map θ).mass z*chargedBad v w ρ r s n J D a k ((p.cond θ z).map G)
        (e z) (own z) t := by
  rw [contextual,mix_mean]
  simp_rw [atRound_mean,exposureAverage_bad]

omit [FiniteDimensional K V] in
lemma contextual_selected_mean (n k : ℕ) (p : Law Ω) (θ : Ω→Θ) (G : Ω→ι→A×B)
    (e : Θ→C×Fin (n+k)↪ι) (own : Θ→ι→Option C) (t : Fin k)
    (v : B→V) (w : A→Module.Dual K V) (ρ : ℝ) (r s : ℕ) (J D a : ℝ) :
    (contextual n k p θ G e own t).mean (reciprocalSelectedStatistic v w ρ r s J D a)=
      ∑ z,(p.map θ).mass z*chargedSelectedBad v w ρ r s n J D a k ((p.cond θ z).map G)
        (e z) (own z) t := by
  rw [contextual,mix_mean]
  simp_rw [atRound_mean,exposureAverage_selected]

lemma contextual_unowned (n k : ℕ) (p : Law Ω) (θ : Ω→Θ) (G : Ω→ι→A×B)
    (e : Θ→C×Fin (n+k)↪ι) (own : Θ→ι→Option C)
    (hown : ∀ z b x,own z (e z (b,x))=some b) (t : Fin k)
    (z : (contextual n k p θ G e own t).History) (i : ι) (hi : own z.1 i=none) :
    ∃ j,(contextual n k p θ G e own t).origin z j=i :=
  atRound_unowned n k ((p.cond θ z.1).map G) (e z.1) (own z.1) (hown z.1) t z.2 i hi

end ExposureModel
open ExposureModel

theorem actual_realized_reciprocal (v : B→V) (w : A→Module.Dual K V)
    {ρ : ℝ} (hρ : 0≤ρ) {r s : ℕ} (hsum : Module.finrank K V=r+s)
    (n k : ℕ) (hn : 2≤n) (hk : 0<k) (J D a M budget : ℝ)
    (hD : 0<D) (ha : 0<a) (hM : 0≤M)
    (p : Law Ω) (θ : Ω→Θ) (G : Ω→ι→A×B)
    (e : Θ→C×Fin (n+k)↪ι) (own : Θ→ι→Option C)
    (hown : ∀ z b x,own z (e z (b,x))=some b)
    (S : Θ→ι→Finset (A×B))
    (hS : ∀ x,p.mass x≠0→∀ i,G x i∈S (θ x) i)
    (hJ : ∀ z i,Real.log (S z i).card≤J)
    (hf : ∀ x,p.mass x≠0→∀ i,w (G x i).1 (v (G x i).2)=0)
    (ho : ∀ x,p.mass x≠0→∀ W : Submodule K V,
      ((univ.filter (fun i=>G x i∈orthogonalRectangle v w W)).card:ℝ)≤M)
    (hbudget : (∑ z,(p.map θ).mass z*((Fintype.card ι:ℝ)*J-
      entropy ((p.cond θ z).map G)))≤budget) :
    ∃ t : Fin k,
      let E:=contextual n k p θ G e own t
      let hp:=contextual_positive n k (by omega : 0<n) p θ G e own t
      let bad:=E.freshBad (fun z=>reciprocalCharges (E.tupleLaw z) v w ρ r s) J D a
      (∑ x,(E.freshLaw hp).mass x*((bad x).card:ℝ))≤
        budget/D+2*budget/((k:ℝ)*a)+2*Fintype.card ι*M/((n:ℝ)*a) ∧
      (n:ℝ)*(∑ x,(E.freshLaw hp).mass x*((E.freshSelected x∩bad x).card:ℝ))≤
        budget/D+2*budget/((k:ℝ)*a)+2*Fintype.card ι*M/((n:ℝ)*a) ∧
      (E.afterDraw hp).joint.map (fun x=>(E.afterDraw hp).restore x.1 x.2)=p.map G := by
  obtain ⟨t,hb,hs⟩:=actual_source_reciprocal v w hρ hsum n k hn hk J D a M budget hD ha hM
    p θ G e own hown S hS hJ hf ho hbudget
  refine ⟨t,?_,?_,?_⟩
  ·
    rw [fresh_bad_mean,contextual_bad_mean]
    exact hb
  ·
    rw [fresh_selected_mean,contextual_selected_mean]
    exact hs
  · apply restored_map
    intro φ
    rw [afterDraw_preserves,contextual_preserves,Law.sum_map]

end
end SharpLogRamsey.Selection

end

end OAI
