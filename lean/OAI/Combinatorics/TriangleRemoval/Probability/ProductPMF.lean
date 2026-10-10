import Mathlib

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

noncomputable def productPMF {K V : Type*} [Fintype K] [DecidableEq K] [Fintype V]
    (ρ : K → PMF V) : PMF (K → V) :=
  PMF.ofFintype (fun ω => ∏ k, ρ k (ω k)) (by
    calc
      (∑ ω : K → V, ∏ k, ρ k (ω k)) = ∏ k, ∑ v, ρ k v :=
        (Fintype.prod_sum (fun (k : K) (v : V) => ρ k v)).symm
      _ = 1 := by
        apply Finset.prod_eq_one
        intro k _
        simpa only [tsum_fintype] using (ρ k).tsum_coe)

@[simp] theorem productPMF_apply {K V : Type*} [Fintype K] [DecidableEq K] [Fintype V]
    (ρ : K → PMF V) (ω : K → V) : productPMF ρ ω = ∏ k, ρ k (ω k) := rfl

@[simp] theorem productPMF_support {K V : Type*} [Fintype K] [DecidableEq K] [Fintype V]
    (ρ : K → PMF V) (ω : K → V) :
    ω ∈ (productPMF ρ).support ↔ ∀ k, ω k ∈ (ρ k).support := by
  simp [PMF.mem_support_iff, Finset.prod_ne_zero_iff]

theorem productPMF_update_apply {K V : Type*} [Fintype K] [DecidableEq K]
    [Fintype V] [DecidableEq V] (ρ : K → PMF V) (k : K) (v : V) (ω : K → V) :
    productPMF (Function.update ρ k (PMF.pure v)) ω =
      (if ω k = v then 1 else 0) * ∏ j ∈ Finset.univ.erase k, ρ j (ω j) := by
  rw [productPMF_apply, ← Finset.prod_erase_mul _ _ (Finset.mem_univ k)]
  have hh : (∏ j ∈ Finset.univ.erase k, Function.update ρ k (PMF.pure v) j (ω j)) =
      ∏ j ∈ Finset.univ.erase k, ρ j (ω j) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [hh, Function.update_self]
  simp only [PMF.pure_apply, eq_comm]
  exact mul_comm _ _

theorem productPMF_split {K V : Type*} [Fintype K] [DecidableEq K]
    [Fintype V] [DecidableEq V] (ρ : K → PMF V) (k : K) :
    productPMF ρ = (ρ k).bind (fun v => productPMF (Function.update ρ k (PMF.pure v))) := by
  ext ω
  rw [PMF.bind_apply, tsum_fintype]
  simp only [productPMF_update_apply]
  rw [Finset.sum_eq_single (ω k)]
  · simp only [ite_true, one_mul]
    rw [productPMF_apply, ← Finset.prod_erase_mul _ _ (Finset.mem_univ k)]
    exact mul_comm _ _
  · intro v _ hv
    simp only [ite_eq_right (Ne.symm hv), zero_mul, mul_zero]
  · simp

inductive ExposureTree (K V O : Type*) where
  | done : O → ExposureTree K V O
  | ask : K → (V → ExposureTree K V O) → ExposureTree K V O

namespace ExposureTree
variable {K V O : Type*}

def evaluate (ω : K → V) : ExposureTree K V O → O
  | .done o => o
  | .ask k f => evaluate ω (f (ω k))

noncomputable def fresh (ν : K → PMF V) : ExposureTree K V O → PMF O
  | .done o => PMF.pure o
  | .ask k f => (ν k).bind (fun v => fresh ν (f v))

noncomputable def coupled [DecidableEq K] (ν : K → PMF V) (ω : K → V) :
    ExposureTree K V O → Finset K → PMF (O × Bool)
  | .done o, _ => PMF.pure (o, false)
  | .ask k f, seen =>
      if k ∈ seen then
        (ν k).bind (fun v => (coupled ν ω (f v) seen).map (fun z => (z.1, true)))
      else coupled ν ω (f (ω k)) (insert k seen)

theorem coupled_agrees [DecidableEq K] (ν : K → PMF V) (ω : K → V)
    (P : ExposureTree K V O) (seen : Finset K) (o : O)
    (ho : (o, false) ∈ (coupled ν ω P seen).support) : evaluate ω P = o := by
  induction P generalizing seen with
  | done a =>
    have hh : (o, false) = (a, false) := by simpa [coupled] using ho
    exact (congrArg Prod.fst hh).symm
  | ask k f ih =>
    by_cases hk : k ∈ seen
    · simp only [coupled, ite_eq_left hk, PMF.mem_support_bind_iff] at ho
      obtain ⟨v, _, hv⟩ := ho
      rcases (PMF.mem_support_map_iff _ _ _).mp hv with ⟨z, _, hz⟩
      exact False.elim (by simpa using congrArg Prod.snd hz)
    · exact ih (ω k) (insert k seen) (by simpa [coupled, hk] using ho)

noncomputable def freshRecorded [DecidableEq K] (ν : K → PMF V) :
    ExposureTree K V O → Finset K → PMF (O × Bool)
  | .done o, _ => PMF.pure (o, false)
  | .ask k f, seen =>
      (ν k).bind (fun v => if k ∈ seen then
        (freshRecorded ν (f v) seen).map (fun z => (z.1, true))
        else freshRecorded ν (f v) (insert k seen))

theorem freshRecorded_outcome [DecidableEq K] (ν : K → PMF V)
    (P : ExposureTree K V O) (seen : Finset K) :
    (freshRecorded ν P seen).map Prod.fst = fresh ν P := by
  induction P generalizing seen with
  | done o => simp [freshRecorded, fresh, PMF.pure_map]
  | ask k f ih =>
    simp only [freshRecorded, PMF.map_bind, fresh]
    congr 1
    funext v
    by_cases hk : k ∈ seen
    · simp only [ite_eq_left hk, PMF.map_comp]
      exact ih v seen
    · simp only [ite_eq_right hk]
      exact ih v (insert k seen)

end ExposureTree

theorem pmf_bind_congr_on_support {α β : Type*} (p : PMF α) (f g : α → PMF β)
    (h : ∀ a ∈ p.support, f a = g a) : p.bind f = p.bind g := by
  ext b
  simp only [PMF.bind_apply]
  apply tsum_congr
  intro a
  by_cases ha : p a = 0
  · simp only [ha, zero_mul]
  · rw [h a ha]

namespace ExposureTree
variable {K V O : Type*} [Fintype K] [DecidableEq K] [Fintype V] [DecidableEq V]

theorem coupled_independent_law (ν : K → PMF V) (P : ExposureTree K V O)
    (seen : Finset K) (ρ : K → PMF V) (hρ : ∀ k ∉ seen, ρ k = ν k) :
    (productPMF ρ).bind (fun ω => coupled ν ω P seen) = freshRecorded ν P seen := by
  induction P generalizing seen ρ with
  | done o => simp [coupled, freshRecorded, PMF.bind_const]
  | ask k f ih =>
    by_cases hk : k ∈ seen
    · simp only [coupled, ite_eq_left hk, freshRecorded]
      rw [PMF.bind_comm]
      congr 1
      funext v
      rw [← PMF.map_bind]
      exact congrArg (fun p : PMF (O × Bool) => p.map (fun z => (z.1, true)))
        (ih v seen ρ hρ)
    · simp only [coupled, ite_eq_right hk, freshRecorded]
      rw [productPMF_split ρ k, PMF.bind_bind, hρ k hk]
      congr 1
      funext v
      let ρ' : K → PMF V := Function.update ρ k (PMF.pure v)
      have hv : ∀ ω ∈ (productPMF ρ').support, ω k = v := by
        intro ω hω
        have hh := (productPMF_support ρ' ω).mp hω k
        simpa only [ρ', Function.update_self, PMF.mem_support_pure_iff] using hh
      calc
        _ = (productPMF ρ').bind
            (fun ω => coupled ν ω (f v) (insert k seen)) := by
          apply pmf_bind_congr_on_support
          intro ω hω
          rw [hv ω hω]
        _ = freshRecorded ν (f v) (insert k seen) := by
          apply ih v (insert k seen) ρ'
          intro j hj
          have hjs : j ∉ seen := fun h => hj (Finset.mem_insert_of_mem h)
          have hjk : j ≠ k := fun h => hj (h ▸ Finset.mem_insert_self _ _)
          simp only [ρ', Function.update_of_ne hjk, hρ j hjs]

theorem coupled_independent_law_empty (ν : K → PMF V) (P : ExposureTree K V O) :
    (productPMF ν).bind (fun ω => coupled ν ω P ∅) = freshRecorded ν P ∅ :=
  coupled_independent_law ν P ∅ ν (fun _ _ => rfl)

noncomputable def jointLaw (ν : K → PMF V) (P : ExposureTree K V O) :
    PMF (O × (O × Bool)) :=
  (productPMF ν).bind (fun ω =>
    (coupled ν ω P ∅).map (fun z => (evaluate ω P, z)))

omit [DecidableEq V] in

theorem jointLaw_fixed (ν : K → PMF V) (P : ExposureTree K V O) :
    (jointLaw ν P).map Prod.fst = (productPMF ν).map (fun ω => evaluate ω P) := by
  simp only [jointLaw, PMF.map_bind, PMF.map_comp]
  change (productPMF ν).bind (fun ω =>
    (coupled ν ω P ∅).map (Function.const (O × Bool) (evaluate ω P))) = _
  simp only [PMF.map_const]
  rfl

theorem jointLaw_fresh (ν : K → PMF V) (P : ExposureTree K V O) :
    (jointLaw ν P).map Prod.snd = freshRecorded ν P ∅ := by
  simp only [jointLaw, PMF.map_bind, PMF.map_comp]
  change (productPMF ν).bind (fun ω => (coupled ν ω P ∅).map id) = _
  simp only [PMF.map_id]
  exact coupled_independent_law_empty ν P

omit [DecidableEq V] in

theorem jointLaw_agrees (ν : K → PMF V) (P : ExposureTree K V O)
    (z : O × (O × Bool)) (hz : z ∈ (jointLaw ν P).support) (hf : z.2.2 = false) :
    z.1 = z.2.1 := by
  rcases (PMF.mem_support_bind_iff _ _ _).mp hz with ⟨ω, _, hω⟩
  rcases (PMF.mem_support_map_iff _ _ _).mp hω with ⟨o, ho, hzo⟩
  subst z
  have he : o = (o.1, false) := Prod.ext rfl hf
  rw [he] at ho
  exact coupled_agrees ν ω P ∅ o.1 ho

end ExposureTree
end SharpTerminalLeave

end

end OAI
