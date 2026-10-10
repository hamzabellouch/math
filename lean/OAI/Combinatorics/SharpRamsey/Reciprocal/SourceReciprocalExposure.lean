import Mathlib
import OAI.Combinatorics.SharpRamsey.Exposure.ExposureContexts

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators
noncomputable section
universe u
variable {Θ Ω C ι : Type*} {A B : Type u} [Fintype Θ] [Fintype Ω] [Fintype C]
  [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B]
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

lemma reciprocal_conditional_supported (p : Law Ω) (θ : Ω→Θ) (G : Ω→ι→A×B)
    (S : Θ→ι→Finset (A×B))
    (hS : ∀ x,p.mass x≠0→∀ i,G x i∈S (θ x) i)
    (z : Θ) (hz : (p.map θ).mass z≠0) :
    tupleSupported ((p.cond θ z).map G) (S z) := by
  intro f hf i
  obtain ⟨x,hx,rfl⟩ := (p.cond θ z).map_support G f hf
  obtain ⟨hx,he⟩:=p.cond_support θ z hz x hx
  simpa only [he] using hS x hx i

omit [FiniteDimensional K V] in
lemma conditional_tupleFlags (p : Law Ω) (θ : Ω→Θ) (G : Ω→ι→A×B)
    (v : B→V) (w : A→Module.Dual K V)
    (hf : ∀ x,p.mass x≠0→∀ i,w (G x i).1 (v (G x i).2)=0)
    (z : Θ) (hz : (p.map θ).mass z≠0) :
    tupleFlags ((p.cond θ z).map G) v w := by
  intro f hf' i
  obtain ⟨x,hx,rfl⟩ := (p.cond θ z).map_support G f hf'
  exact hf x (p.cond_support θ z hz x hx).1 i

omit [FiniteDimensional K V] in
lemma conditional_rectangleBound (p : Law Ω) (θ : Ω→Θ) (G : Ω→ι→A×B)
    (v : B→V) (w : A→Module.Dual K V) (M : ℝ)
    (ho : ∀ x,p.mass x≠0→∀ W : Submodule K V,
      ((univ.filter (fun i=>G x i∈orthogonalRectangle v w W)).card:ℝ)≤M)
    (z : Θ) (hz : (p.map θ).mass z≠0) :
    rectangleBound ((p.cond θ z).map G) v w M := by
  intro f hf W
  obtain ⟨x,hx,rfl⟩ := (p.cond θ z).map_support G f hf
  exact ho x (p.cond_support θ z hz x hx).1 W

theorem actual_source_reciprocal (v : B→V) (w : A→Module.Dual K V)
    {ρ : ℝ} (hρ : 0≤ρ) {r s : ℕ} (hsum : Module.finrank K V=r+s)
    (n k : ℕ) (hn : 2≤n) (hk : 0<k) (J D a M budget : ℝ)
    (hD : 0<D) (ha : 0<a) (hM : 0≤M)
    (p : Law Ω) (θ : Ω→Θ) (G : Ω→ι→A×B)
    (e : Θ→C×Fin (n+k) ↪ ι) (own : Θ→ι→Option C)
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
      (∑ z,(p.map θ).mass z*chargedBad v w ρ r s n J D a k
        ((p.cond θ z).map G) (e z) (own z) t)≤
          budget/D+2*budget/((k:ℝ)*a)+2*Fintype.card ι*M/((n:ℝ)*a) ∧
      (n:ℝ)*(∑ z,(p.map θ).mass z*chargedSelectedBad v w ρ r s n J D a k
        ((p.cond θ z).map G) (e z) (own z) t)≤
          budget/D+2*budget/((k:ℝ)*a)+2*Fintype.card ι*M/((n:ℝ)*a) := by
  have hb : contextAverage (p.map θ) (fun z=>tupleDeficit J ((p.cond θ z).map G))≤budget := hbudget
  have hTC : contextAverage (p.map θ) (fun z=>totalCorrelation ((p.cond θ z).map G))≤budget := by
    apply le_trans _ hb
    apply contextAverage_mono
    intro z hz
    exact totalCorrelation_le_tupleDeficit _ J (tupleSupported_marginal_cap _ (S z)
      (reciprocal_conditional_supported p θ G S hS z hz) J (hJ z))
  obtain ⟨t,ht,ht'⟩ := exists_context_good_reciprocal v w hρ hsum n k hn hk J D a M hD ha hM
    (p.map θ) (fun z=>(p.cond θ z).map G) e own hown S
    (reciprocal_conditional_supported p θ G S hS) hJ
    (conditional_tupleFlags p θ G v w hf) (conditional_rectangleBound p θ G v w M ho)
  have hscale : contextAverage (p.map θ) (fun z=>tupleDeficit J ((p.cond θ z).map G))/D+
      2*contextAverage (p.map θ) (fun z=>totalCorrelation ((p.cond θ z).map G))/((k:ℝ)*a)+
      2*Fintype.card ι*M/((n:ℝ)*a)≤
        budget/D+2*budget/((k:ℝ)*a)+2*Fintype.card ι*M/((n:ℝ)*a) := by
    have hdenom : 0 ≤ (k : ℝ) * a := mul_nonneg (Nat.cast_nonneg k) ha.le
    exact add_le_add
      (add_le_add (div_le_div_of_nonneg_right hb hD.le)
        (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hTC (show (0 : ℝ) ≤ 2 by norm_num)) hdenom)) le_rfl
  exact ⟨t,ht.trans hscale,ht'.trans hscale⟩

end
end SharpLogRamsey.Selection

end

end OAI
