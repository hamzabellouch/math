import OAI.NumberTheory.DirichletL.Detector.IdealFactorization
import Mathlib.Analysis.Normed.Group.Tannery

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Filter
namespace SevenEighths.ProbeEulerFinsupp

lemma finitePi_fin {β : Type*} (n : ℕ) (f : Fin n→β→ℂ)
    (hf : ∀ i,Summable (fun b=>‖f i b‖)) :
    Summable (fun v : Fin n→β => ‖∏ i,f i (v i)‖) ∧
      (∑' v : Fin n→β,∏ i,f i (v i))=∏ i,∑' b,f i b := by
  induction n with
  | zero =>
    constructor
    · exact (hasSum_fintype _).summable
    · simp
  | succ n ih =>
    have ht := ih (fun i=>f i.succ) (fun i=>hf i.succ)
    let e := Fin.consEquiv (fun _ : Fin (n+1)=>β)
    have he (v : β×(Fin n→β)) :
        (∏ i,f i (e v i))=f 0 v.1*(∏ i,f i.succ (v.2 i)) := by
      rw [Fin.prod_univ_succ]
      rfl
    constructor
    · rw [←e.summable_iff]
      simp only [Function.comp_def,he]
      have hm : Summable (fun v : β×(Fin n→β)=>‖f 0 v.1‖ * ‖∏ i : Fin n,f i.succ (v.2 i)‖) :=
        (hf 0).mul_of_nonneg ht.1 (fun _=>norm_nonneg _) (fun _=>norm_nonneg _)
      simpa only [norm_mul] using hm
    · rw [←e.tsum_eq (fun v=>∏ i,f i (v i))]
      simp only [he]
      rw [←tsum_mul_tsum_of_summable_norm (f:=f 0)
        (g:=fun v : Fin n→β=>∏ i : Fin n,f i.succ (v i)) (hf 0) ht.1,ht.2,Fin.prod_univ_succ]

lemma finitePi {α β : Type*} [Fintype α] (f : α→β→ℂ)
    (hf : ∀ i,Summable (fun b=>‖f i b‖)) :
    Summable (fun v : α→β => ‖∏ i,f i (v i)‖) ∧
      (∑' v : α→β,∏ i,f i (v i))=∏ i,∑' b,f i b := by
  let e := Fintype.equivFin α
  let d := Equiv.arrowCongr e.symm (Equiv.refl β)
  have h := finitePi_fin (Fintype.card α) (fun i=>f (e.symm i)) (fun i=>hf (e.symm i))
  have hd (v : Fin (Fintype.card α)→β) :
      (∏ i,f i (d v i))=∏ j,f (e.symm j) (v j) := by
    apply Fintype.prod_equiv e
    intro i
    simp only [d,Equiv.arrowCongr_apply,Equiv.symm_symm,Equiv.refl_apply,e.symm_apply_apply,Function.comp_apply]
  constructor
  · rw [←d.summable_iff]
    simpa only [Function.comp_def,hd] using h.1
  · rw [←d.tsum_eq (fun v=>∏ i,f i (v i))]
    simp only [hd]
    rw [h.2]
    exact e.symm.prod_comp (fun i=>∑' b,f i b)

variable {α β : Type*} [AddCommMonoid β]

lemma finiteEuler (f : α→β→ℂ) (h0 : ∀a,f a 0=1)
    (hf : ∀a,Summable (fun b=>‖f a b‖)) (S : Finset α) :
    (∑' v : {v : α→₀β // (v.support:Set α)⊆S},v.val.prod f)=
      ∏ a∈S,∑' b,f a b := by
  let e : {v : α→₀β // (v.support:Set α)⊆S} ≃ (S→β) :=
    (Finsupp.restrictSupportEquiv (S:Set α) β).trans Finsupp.equivFunOnFinite
  have he (v : {v : α→₀β // (v.support:Set α)⊆S}) :
      v.val.prod f=∏ a:S,f a.val (e v a) := by
    rw [←Finsupp.prod_subtypeDomain_index (p:=fun a=>a∈S) (fun a ha=>v.property ha)]
    exact Finsupp.prod_fintype _ _ (fun a=>h0 a.val)
  simp_rw [he]
  rw [e.tsum_eq (fun v : S→β=>∏ a:S,f a.val (v a))]
  rw [(finitePi (fun a:S=>f a.val) (fun a=>hf a.val)).2]
  exact Finset.prod_coe_sort S (fun a=>∑' b,f a b)

theorem hasProd_of_summable (f : α→β→ℂ) (h0 : ∀a,f a 0=1)
    (hs : Summable (fun v : α→₀β=>‖v.prod f‖)) :
    HasProd (fun a=>∑' b,f a b) (∑' v : α→₀β,v.prod f) := by
  have hf (a : α) : Summable (fun b=>‖f a b‖) := by
    have hh := hs.comp_injective (Finsupp.single_injective a)
    simpa only [Function.comp_def,Finsupp.prod_single_index (h0 a)] using hh
  have ht : Tendsto (fun S : Finset α=>∑' v : α→₀β,
      if v.support⊆S then v.prod f else 0) atTop (𝓝 (∑' v : α→₀β,v.prod f)) := by
    apply tendsto_tsum_of_dominated_convergence hs
    · intro v
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop v.support] with S hS
      simp only [ite_eq_left hS]
    · apply Filter.Eventually.of_forall
      intro S v
      split_ifs
      · exact le_rfl
      · simpa only [norm_zero] using norm_nonneg (v.prod f)
  have he (S : Finset α) : (∑' v : α→₀β,if v.support⊆S then v.prod f else 0)=
      ∏a∈S,∑' b,f a b := by
    rw [←finiteEuler f h0 hf S]
    trans ∑' v : α→₀β, {v : α→₀β | (v.support:Set α)⊆S}.indicator (fun v=>v.prod f) v
    · apply tsum_congr
      intro v
      simp only [Set.indicator,Set.mem_ofPred_eq,Finset.coe_subset]
    · exact (tsum_subtype {v : α→₀β | (v.support:Set α)⊆S} (fun v=>v.prod f)).symm
  change Tendsto (fun S : Finset α=>∏a∈S,∑' b,f a b) atTop _
  simpa only [he] using ht

end SevenEighths.ProbeEulerFinsupp
end

end OAI
