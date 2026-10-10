import Mathlib
import OAI.Probability.CriticalPercolation.Exploration.ClusterUsers
import OAI.Probability.CriticalPercolation.Criticality.ReverseReference

namespace OAI

section
section
namespace CriticalPercolation.MarkedBits
open scoped Classical
open FiniteProduct ExactExposure

variable {E I : Type*}

noncomputable def opened (S : Finset I) (m : I → Option E) (ω : E → Bool) : E → Bool :=
  fun e => if ∃ i ∈ S, m i = some e then true else ω e

noncomputable def masked (S : Finset I) (m : I → Option E) : I → Option E :=
  fun i => if i ∈ S then m i else none

variable [Fintype I]

lemma masked_join (S : Finset I) (m : I → Option E) (i : I) :
    (if i ∈ S then masked S m i else masked Sᶜ m i) = m i := by
  simp only [masked,Finset.mem_compl]
  split_ifs <;> rfl

lemma masked_injective (S : Finset I) (m m' : I → Option E)
    (h1 : masked S m = masked S m') (h2 : masked Sᶜ m = masked Sᶜ m') : m=m' := by
  funext i
  rw [← masked_join S m i,← masked_join S m' i,h1,h2]

omit [Fintype I] in
lemma opened_empty (m : I → Option E) (ω : E → Bool) : opened ∅ m ω = ω := by
  funext e
  simp [opened]

omit [Fintype I] in
lemma opened_insert (S : Finset I) (m : I → Option E) (ω : E → Bool)
    (i : I) (e : E) (hm : m i = some e) :
    opened (insert i S) m ω = Function.update (opened S m ω) e true := by
  funext f
  by_cases hf : f=e
  · subst f
    simp only [Function.update_self,opened]
    rw [ite_eq_left ⟨i,Finset.mem_insert_self _ _,hm⟩]
  · rw [Function.update_of_ne hf]
    have he : (∃ j ∈ insert i S, m j = some f) ↔ ∃ j ∈ S, m j = some f := by
      constructor
      · rintro ⟨j,hj,hjm⟩
        rcases Finset.mem_insert.mp hj with rfl|hj
        · exact (hf (Option.some.inj (hjm.symm.trans hm))).elim
        · exact ⟨j,hj,hjm⟩
      · rintro ⟨j,hj,hjm⟩
        exact ⟨j,Finset.mem_insert_of_mem hj,hjm⟩
    simp only [opened,he]

omit [Fintype I] in
lemma opened_unchanged (S : Finset I) (m : I → Option E) (ω : E → Bool)
    (e : E) (he : ∀ i ∈ S, m i ≠ some e) : opened S m ω e = ω e := by
  apply ite_eq_right
  rintro ⟨i,hi,hie⟩
  exact he i hi hie

omit [Fintype I] in

lemma close_opened_insert (S : Finset I) (m : I → Option E) (ω : E → Bool)
    (i : I) (e : E) (hm : m i = some e) (hω : ω e = false)
    (hd : ∀ j ∈ S, m j ≠ some e) :
    Function.update (opened (insert i S) m ω) e false = opened S m ω := by
  rw [opened_insert S m ω i e hm,Function.update_idem]
  rw [← hω,← opened_unchanged S m ω e hd,Function.update_eq_self]

omit [Fintype I] in

lemma opened_injective_closed (S : Finset I) (m : I → Option E) (ω η : E → Bool)
    (hω : ∀ i ∈ S, ∀ e, m i = some e → ω e = false)
    (hη : ∀ i ∈ S, ∀ e, m i = some e → η e = false)
    (he : opened S m ω = opened S m η) : ω=η := by
  funext e
  by_cases hm : ∃ i ∈ S, m i = some e
  · obtain ⟨i,hi,him⟩ := hm
    rw [hω i hi e him,hη i hi e him]
  · have hh := congrFun he e
    simpa only [opened,ite_eq_right hm] using hh

omit [Fintype I] in
lemma configuration_update (ω : E → Bool) (e : E) (b : Bool) :
    configuration (Function.update ω e b) = Function.update (configuration ω) e (b=true) := by
  apply Set.ext
  intro f
  change (Function.update ω e b) f = true ↔ (Function.update (configuration ω : E → Prop) e (b=true)) f
  by_cases hf : f=e
  · subst f
    simp [Function.update]
  · simp only [Function.update,configuration,hf]
    rfl

omit [Fintype I] in
lemma density_open_likelihood [Fintype E] (p : ℝ) (ω : E → Bool) (e : E) (he : ω e = false) :
    FiniteProduct.density (QueryTree.bitWeight p) ω * p =
      FiniteProduct.density (QueryTree.bitWeight p) (Function.update ω e true) * (1-p) := by
  classical
  have hf (m : E → Bool) : FiniteProduct.density (QueryTree.bitWeight p) m =
      QueryTree.bitWeight p e (m e) * ∏ f ∈ Finset.univ.erase e, QueryTree.bitWeight p f (m f) :=
    (Finset.mul_prod_erase _ _ (Finset.mem_univ e)).symm
  rw [hf ω,hf (Function.update ω e true)]
  have ht : (∏ f ∈ Finset.univ.erase e, QueryTree.bitWeight p f ((Function.update ω e true) f)) =
      ∏ f ∈ Finset.univ.erase e, QueryTree.bitWeight p f (ω f) := by
    apply Finset.prod_congr rfl
    intro f hf
    rw [Function.update_of_ne (Finset.mem_erase.mp hf).1]
  rw [ht]
  simp only [he,Function.update_self,QueryTree.bitWeight,Bool.false_eq_true,ite_false,ite_true]
  ring

end CriticalPercolation.MarkedBits

namespace CriticalPercolation.ReverseReference
open scoped Classical

variable {X M : Type*}

lemma recover_trajectory (u : ℕ → X → M → X) (σ : ℕ → X) (m : ℕ → M)
    (n : ℕ) (hu : ∀ i < n, u i (σ (i+1)) (m i) = σ i) :
    recover u n (σ n) (fun i => m i.val) = σ 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [recover]
    dsimp only [Fin.val_last]
    rw [hu n (Nat.lt_succ_self n)]
    exact ih (fun i hi => hu i (hi.trans (Nat.lt_succ_self n)))

lemma weight_trajectory (k : ℕ → X → M → ℝ) (u : ℕ → X → M → X)
    (σ : ℕ → X) (m : ℕ → M) (v : ℕ → ℝ) (n : ℕ)
    (hu : ∀ i < n, u i (σ (i+1)) (m i) = σ i)
    (hk : ∀ i < n, k i (σ (i+1)) (m i) = v i) :
    weight k u n (σ n) (fun i => m i.val) = ∏ i : Fin n, v i.val := by
  induction n with
  | zero => simp [weight]
  | succ n ih =>
    rw [weight]
    dsimp only [Fin.val_last]
    rw [hk n (Nat.lt_succ_self n),hu n (Nat.lt_succ_self n)]
    change v n * weight k u n (σ n) (fun i => m i.val) = _
    rw [ih (fun i hi => hu i (hi.trans (Nat.lt_succ_self n)))
      (fun i hi => hk i (hi.trans (Nat.lt_succ_self n)))]
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last]
    ring

end CriticalPercolation.ReverseReference
end
end

end OAI
