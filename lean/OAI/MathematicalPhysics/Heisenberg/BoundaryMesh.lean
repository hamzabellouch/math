import OAI.MathematicalPhysics.Heisenberg.MeshPin

namespace OAI

section

noncomputable section
open scoped Classical BigOperators
namespace Heisenberg.Surface
open Heisenberg.Cycle Heisenberg.LayeredExchange Heisenberg.Exposure
variable {T V : Type*} [Fintype T] [Fintype V]

omit [Fintype V] in
lemma swap_preserves_boundary (a b : V) (D : Set V) (h : a∈D ↔ b∈D) (v : V) :
    Equiv.swap a b v ∈ D ↔ v∈D := by
  simp only [Equiv.swap_apply_def]
  split_ifs with h₁ h₂
  · subst v; exact h.symm
  · subst v; exact h
  · rfl

theorem mesh_boundary_count (s : Equiv.Perm T) (a b : T → V) (D : Set V)
    (K : Finset T) (hK : ∀ t,t∉K → (a t∈D ↔ b t∈D))
    (t₀ : T) (hs : ∀ t,∃ n : ℕ,(s^n) t=t₀) (c : T → Bool) :
    (hitClasses (layerHistory s (fun t=>Equiv.swap (a t) (b t)) c) {z | z.2∈D}).card ≤
      (Finset.univ.filter fun v : V=>v∈D).card+2*(K.filter fun t=>c t=true).card := by
  let π:=layerHistory s (fun t=>Equiv.swap (a t) (b t)) c
  let B : Set (T×V):={z | z.2∈D}
  let C : Set (T×V):={z | z.1=t₀}
  have hC : ∀ z,∃ n : ℕ,(π^n) z∈C := by
    intro z
    obtain ⟨n,hn⟩:=hs z.1
    refine ⟨n,?_⟩
    change ((wiring s (fun t=>if c t then Equiv.swap (a t) (b t) else 1)^n) z).1=t₀
    rw [wiring_pow]
    exact hn
  have hn:=(hitClasses_le_witnesses π B C hC).trans (witness_count π B C)
  have hbase : (Finset.univ.filter fun z : T×V=>z∈B∩C).card=
      (Finset.univ.filter fun v : V=>v∈D).card := by
    have he : (Finset.univ.filter fun z : T×V=>z∈B∩C)=
        (Finset.univ.filter fun v : V=>v∈D).image (fun v=>(t₀,v)) := by
      ext z
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Set.mem_inter_iff,
        Finset.mem_image,B,C,Set.mem_ofPred_eq]
      aesop
    rw [he,Finset.card_image_of_injective _ (fun _ _ h=>(Prod.mk.inj h).2)]
  have hsub : (Finset.univ.filter fun z : T×V=>z∈B ∧ π z∉B) ⊆
      (K.filter fun t=>c t=true).biUnion (fun t=>{(t,a t),(t,b t)}) := by
    intro z hz
    obtain ⟨hzD,hout⟩:=(Finset.mem_filter.mp hz).2
    have hout' : (if c z.1 then Equiv.swap (a z.1) (b z.1) z.2 else z.2)∉D := by
      change ((if c z.1 then Equiv.swap (a z.1) (b z.1) else 1) z.2)∉D at hout
      by_cases hh : c z.1=true <;> simpa [hh] using hout
    have hc : c z.1=true := by
      by_contra hc
      have hh : z.2∉D := by simpa [hc] using hout'
      exact hh hzD
    have hKz : z.1∈K := by
      by_contra hnK
      have hh:=(swap_preserves_boundary (a z.1) (b z.1) D (hK z.1 hnK) z.2).mpr hzD
      simp only [hc,ite_true] at hout'
      exact hout' hh
    have hzab : z.2=a z.1 ∨ z.2=b z.1 := by
      by_contra hh
      have hh':=not_or.mp hh
      simp only [hc,ite_true,Equiv.swap_apply_of_ne_of_ne hh'.1 hh'.2] at hout'
      exact hout' hzD
    refine Finset.mem_biUnion.mpr ⟨z.1,Finset.mem_filter.mpr ⟨hKz,hc⟩,?_⟩
    rcases hzab with h|h <;> simp [←h]
  have hexit : (Finset.univ.filter fun z : T×V=>z∈B ∧ π z∉B).card≤
      2*(K.filter fun t=>c t=true).card := by
    apply (Finset.card_le_card hsub).trans
    apply (Finset.card_biUnion_le).trans
    calc
      _ ≤ ∑ _t∈K.filter (fun t=>c t=true),2 := by
        apply Finset.sum_le_sum
        intro t _
        simpa using Finset.card_insert_le (t,a t) {(t,b t)}
      _ = _ := by simp [Nat.mul_comm]
  rw [hbase] at hn
  exact hn.trans (Nat.add_le_add_left hexit _)

lemma mean_active_marks (s : Equiv.Perm T) (a b : T → V) (P : Set (T×V))
    (p : T → ℝ) (hp : ∀ t,0≤p t ∧ p t≤1) (K : Finset T) :
    (∑ c,layerMass s a b P p c * ((K.filter fun t=>c t=true).card:ℝ)) ≤ ∑ t∈K,2*p t := by
  have he (c : T → Bool) : ((K.filter fun t=>c t=true).card:ℝ)=
      ∑ t∈K,if c t=true then (1:ℝ) else 0 := by simp
  simp_rw [he,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro t ht
  have hh:=layer_factorial_bound s a b P p hp {t}
  simpa only [Finset.mem_singleton,forall_eq,Finset.prod_singleton,mul_ite,mul_one,mul_zero] using hh

theorem mean_boundary_cycles (s : Equiv.Perm T) (a b : T → V) (D : Set V)
    (K : Finset T) (hK : ∀ t,t∉K → (a t∈D ↔ b t∈D))
    (t₀ : T) (hs : ∀ t,∃ n : ℕ,(s^n) t=t₀)
    (p : T → ℝ) (hp : ∀ t,0≤p t ∧ p t≤1) (P : Set (T×V)) :
    (∑ c,layerMass s a b P p c *
      ((hitClasses (layerHistory s (fun t=>Equiv.swap (a t) (b t)) c) {z | z.2∈D}).card:ℝ)) ≤
      (Finset.univ.filter fun v : V=>v∈D).card+4*∑ t∈K,p t := by
  have hb : (∑ c,layerMass s a b P p c *
      ((hitClasses (layerHistory s (fun t=>Equiv.swap (a t) (b t)) c) {z | z.2∈D}).card:ℝ)) ≤
      ∑ c,layerMass s a b P p c *
      ((Finset.univ.filter fun v : V=>v∈D).card+2*((K.filter fun t=>c t=true).card:ℝ)) := by
    apply Finset.sum_le_sum
    intro c _
    apply mul_le_mul_of_nonneg_left _ (layerMass_nonneg s a b P p hp c)
    exact_mod_cast mesh_boundary_count s a b D K hK t₀ hs c
  simp_rw [mul_add,Finset.sum_add_distrib,←mul_assoc] at hb
  rw [←Finset.sum_mul,layerMass_sum s a b P p hp,one_mul] at hb
  have he : (∑ c,layerMass s a b P p c * 2 * ((K.filter fun t=>c t=true).card:ℝ))=
      2*∑ c,layerMass s a b P p c * ((K.filter fun t=>c t=true).card:ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    ring
  rw [he] at hb
  have hm:=mean_active_marks s a b P p hp K
  rw [←Finset.mul_sum] at hm
  linarith

end Heisenberg.Surface
end
end

end OAI
