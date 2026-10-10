import Mathlib
import OAI.Combinatorics.SharpRamsey.Trees.TreeDecoder
import OAI.Combinatorics.SharpRamsey.Entropy.ProtocolEntropy

namespace OAI

section
namespace SharpLogRamsey.TreeCodeEntropy
open Finset Real BinaryTree TreeDecoder
open scoped Classical
noncomputable section
variable {A B C : Type*}

def codes (allowed : Domains A B→Finset C) (read : CapReader A B C) :
    BinaryTree Unit→Domains A B→Finset (BinaryTree C)
  | .nil,_ => {.nil}
  | .node _ l r,U => (allowed U).biUnion (fun c=>
      ((codes allowed read l ((read U c).1,U.2)) ×ˢ
        (codes allowed read r (U.1,(read U c).2))).image
          (fun z=>.node c z.1 z.2))

def cost (allowed : Domains A B→Finset C) (read : CapReader A B C) :
    BinaryTree C→Domains A B→ℝ
  | .nil,_ => 0
  | .node c l r,U => log (allowed U).card+
      cost allowed read l ((read U c).1,U.2)+cost allowed read r (U.1,(read U c).2)

lemma weight_node (allowed : Domains A B→Finset C) (read : CapReader A B C)
    (c : C) (l r : BinaryTree C) (U : Domains A B) :
    exp (-cost allowed read (.node c l r) U)=
      exp (-log (allowed U).card)*exp (-cost allowed read l ((read U c).1,U.2))*
        exp (-cost allowed read r (U.1,(read U c).2)) := by
  simp only [cost,neg_add,exp_add]

theorem kraft (allowed : Domains A B→Finset C) (read : CapReader A B C)
    (shape : BinaryTree Unit) (U : Domains A B) :
    (∑ t∈codes allowed read shape U,exp (-cost allowed read t U))≤1 := by
  induction shape generalizing U with
  | nil => simp [codes,cost]
  | node v l r hl hr =>
    rw [codes]
    rw [sum_biUnion]
    rotate_left
    · intro c hc c' hc' hne
      apply disjoint_left.mpr
      intro t ht ht'
      obtain ⟨z,hz,rfl⟩ := mem_image.mp ht
      obtain ⟨z',hz',he⟩ := mem_image.mp ht'
      exact hne (BinaryTree.node.inj he).1.symm
    have hone (c : C) :
        ∑ t∈(((codes allowed read l ((read U c).1,U.2)) ×ˢ
          (codes allowed read r (U.1,(read U c).2))).image
          (fun z=>BinaryTree.node c z.1 z.2)),exp (-cost allowed read t U) ≤
          exp (-log (allowed U).card) := by
      rw [sum_image]
      · simp_rw [weight_node]
        rw [sum_product]
        simp_rw [←mul_sum]
        rw [←sum_mul,←mul_sum]
        have hL := hl ((read U c).1,U.2)
        have hR := hr (U.1,(read U c).2)
        have hLn : 0≤∑ t∈codes allowed read l ((read U c).1,U.2),
            exp (-cost allowed read t ((read U c).1,U.2)) := sum_nonneg (fun _ _=>(exp_pos _).le)
        have hRn : 0≤∑ t∈codes allowed read r (U.1,(read U c).2),
            exp (-cost allowed read t (U.1,(read U c).2)) := sum_nonneg (fun _ _=>(exp_pos _).le)
        nlinarith [exp_pos (-log (allowed U).card),mul_le_mul hL hR hRn (by norm_num : (0:ℝ)≤1)]
      · intro z hz z' hz' he
        exact Prod.ext (BinaryTree.node.inj he).2.1 (BinaryTree.node.inj he).2.2
    apply (sum_le_sum (fun c _=>hone c)).trans
    by_cases he : (allowed U).card=0
    · simp [card_eq_zero.mp he]
    · have hp : (0:ℝ)<(allowed U).card := by exact_mod_cast Nat.pos_of_ne_zero he
      simp only [sum_const,nsmul_eq_mul]
      rw [exp_neg,exp_log hp]
      exact le_of_eq (mul_inv_cancel₀ hp.ne')

theorem card_le_exp (allowed : Domains A B→Finset C) (read : CapReader A B C)
    (shape : BinaryTree Unit) (U : Domains A B) (K : ℝ)
    (hK : ∀ t∈codes allowed read shape U,cost allowed read t U≤K) :
    ((codes allowed read shape U).card:ℝ)≤exp K := by
  have hh : ((codes allowed read shape U).card:ℝ)*exp (-K)≤1 := by
    calc
      _ = ∑ _t∈codes allowed read shape U,exp (-K) := by simp
      _ ≤ ∑ t∈codes allowed read shape U,exp (-cost allowed read t U) :=
        sum_le_sum (fun t ht=>exp_le_exp.mpr (neg_le_neg (hK t ht)))
      _ ≤ 1 := kraft allowed read shape U
  have hm := mul_le_mul_of_nonneg_right hh (exp_pos K).le
  rw [mul_assoc,←exp_add,neg_add_cancel,exp_zero,mul_one,one_mul] at hm
  exact hm

theorem card_subset_le_exp (allowed : Domains A B→Finset C) (read : CapReader A B C)
    (shape : BinaryTree Unit) (U : Domains A B) (S : Finset (BinaryTree C)) (K : ℝ)
    (hS : S⊆codes allowed read shape U)
    (hK : ∀ t∈S,cost allowed read t U≤K) : (S.card:ℝ)≤exp K := by
  have hh : (S.card:ℝ)*exp (-K)≤1 := by
    calc
      _ = ∑ _t∈S,exp (-K) := by simp
      _ ≤ ∑ t∈S,exp (-cost allowed read t U) :=
        sum_le_sum (fun t ht=>exp_le_exp.mpr (neg_le_neg (hK t ht)))
      _ ≤ ∑ t∈codes allowed read shape U,exp (-cost allowed read t U) :=
        sum_le_sum_of_subset_of_nonneg hS (fun _ _ _=>(exp_pos _).le)
      _ ≤ 1 := kraft allowed read shape U
  have hm := mul_le_mul_of_nonneg_right hh (exp_pos K).le
  rw [mul_assoc,←exp_add,neg_add_cancel,exp_zero,mul_one,one_mul] at hm
  exact hm

variable {Ω : Type*} [Fintype Ω]

theorem entropy_le (p : Selection.Law Ω) (allowed : Domains A B→Finset C)
    (read : CapReader A B C) (shape : BinaryTree Unit) (U : Domains A B) (K : ℝ)
    (F : Ω→codes allowed read shape U)
    (hK : ∀ t∈codes allowed read shape U,cost allowed read t U≤K) :
    Selection.entropy (p.map F)≤K := by
  have hn : 0<(codes allowed read shape U).card := by
    by_contra! hn
    have hz : codes allowed read shape U=∅ := card_eq_zero.mp (by omega)
    have ht : ∑ x,p.mass x=0 := by
      apply sum_eq_zero
      intro x _
      exact False.elim (by simpa [hz] using (F x).property)
    linarith [p.total]
  have h := Selection.entropy_le_log_card (p.map F) univ (fun x hx=>False.elim (hx (mem_univ x)))
  simp only [card_univ,Fintype.card_coe] at h
  apply h.trans
  exact (log_le_iff_le_exp (by exact_mod_cast hn)).mpr (card_le_exp allowed read shape U K hK)

end
end SharpLogRamsey.TreeCodeEntropy

end

end OAI
