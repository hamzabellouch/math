import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.TreeCodeEntropy
import OAI.Combinatorics.SharpRamsey.Trees.TreeShapes

namespace OAI

section
namespace SharpLogRamsey.TreeCodeEntropy
open Finset Real BinaryTree TreeDecoder
open scoped Classical
noncomputable section
variable {A B C Γ : Type*} [Fintype Γ]

def shape (t : BinaryTree C) : BinaryTree Unit := t.map (fun _=>())

omit [Fintype Γ] in
lemma shape_numNodes (t : BinaryTree C) : (shape t).numNodes=t.numNodes := by
  induction t with
  | nil => rfl
  | node _ l r hl hr => simpa only [shape,BinaryTree.map,numNodes] using congrArg₂ (fun x y=>x+y+1) hl hr

theorem tree_message_entropy (p : Selection.Law Γ)
    (allowed : Domains A B→Finset C) (read : CapReader A B C) (U : Domains A B)
    (m : Γ→BinaryTree C) (hinj : Function.Injective m) (N : ℕ) (K : ℝ)
    (hN : ∀ g,(m g).numNodes≤N)
    (hmem : ∀ g,m g∈codes allowed read (shape (m g)) U)
    (hK : ∀ g,cost allowed read (m g) U≤K) :
    Selection.entropy p≤((2*N+1:ℕ):ℝ)*log 2+K := by
  let R := univ.image (fun g=>shape (m g))
  let ctx : Γ→R := fun g=>⟨shape (m g),mem_image.mpr ⟨g,mem_univ _,rfl⟩⟩
  have hc (c : R) (hc : (p.map ctx).mass c≠0) : Selection.entropy (p.cond ctx c)≤K := by
    let S := univ.filter (fun g=>shape (m g)=c.val)
    let T := S.image m
    have hT : T⊆codes allowed read c.val U := by
      intro t ht
      obtain ⟨g,hg,rfl⟩ := mem_image.mp ht
      have he := (mem_filter.mp hg).2
      simpa only [he] using hmem g
    have hTK : ∀ t∈T,cost allowed read t U≤K := by
      intro t ht
      obtain ⟨g,hg,rfl⟩ := mem_image.mp ht
      exact hK g
    have hcard : (S.card:ℝ)≤exp K := by
      have h := card_subset_le_exp allowed read c.val U T K hT hTK
      simpa only [T,card_image_of_injective S hinj] using h
    have hp : S.Nonempty := by
      obtain ⟨g,hg,he⟩ := mem_image.mp c.property
      exact ⟨g,mem_filter.mpr ⟨mem_univ _,he⟩⟩
    have hb := Selection.entropy_le_log_card (p.cond ctx c) S (by
      intro g hg
      by_contra hn
      obtain ⟨hg',he⟩ := p.cond_support ctx c hc g hn
      have hv := congrArg Subtype.val he
      exact hg (mem_filter.mpr ⟨mem_univ _,hv⟩))
    exact hb.trans ((log_le_iff_le_exp (by exact_mod_cast card_pos.mpr hp)).mpr hcard)
  have hhead : Selection.entropy (p.map ctx)≤((2*N+1:ℕ):ℝ)*log 2 := by
    have h := Selection.entropy_le_log_card (p.map ctx) univ
      (fun c hc=>False.elim (hc (mem_univ c)))
    simp only [card_univ,Fintype.card_coe] at h
    have hR : R.Nonempty := by
      have hn : (univ:Finset Γ).Nonempty := by
        by_contra hn
        have hz : (univ:Finset Γ)=∅ := not_nonempty_iff_eq_empty.mp hn
        have ht := p.total
        rw [hz,sum_empty] at ht
        norm_num at ht
      exact hn.image _
    have hs : R.card≤2^(2*N+1) := TreeShapes.card_le N R (by
      intro t ht
      obtain ⟨g,hg,rfl⟩ := mem_image.mp ht
      simpa only [shape_numNodes] using hN g)
    apply h.trans
    have hpow : (R.card:ℝ)≤(2:ℝ)^(2*N+1) := by exact_mod_cast hs
    have hh := log_le_log (show (0:ℝ)<R.card by exact_mod_cast card_pos.mpr hR) hpow
    simpa only [log_pow] using hh
  rw [Selection.entropy_cond_self p ctx]
  apply add_le_add hhead
  calc
    _ ≤ ∑ c,(p.map ctx).mass c*K := by
      apply sum_le_sum
      intro c _
      by_cases hz : (p.map ctx).mass c=0
      · simp [hz]
      · exact mul_le_mul_of_nonneg_left (hc c hz) ((p.map ctx).nonneg c)
    _ = K := by rw [←sum_mul,(p.map ctx).total,one_mul]

end
end SharpLogRamsey.TreeCodeEntropy

end

end OAI
