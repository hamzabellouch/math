import Mathlib
import OAI.Combinatorics.ThinTrees.Continuation.ConcaveAlternative
import OAI.Combinatorics.ThinTrees.Continuation.PartitionLattice

namespace OAI

/-! Partition uncrossing. -/

section

namespace AlgorithmicThinTrees.Partitions
noncomputable section
open Finset
open scoped Classical

variable {V X : Type*} [Fintype V]

def Certificates (C : Set X) (f : Setoid V → X → ℝ) (b : ℝ) : Set (Setoid V → ℝ) :=
  {w | (∀p, 0 ≤ w p) ∧ (∑p, w p)=1 ∧ ∀x ∈ C, (∑p, w p*f p x) ≤ b}

lemma certificates_isClosed (C : Set X) (f : Setoid V → X → ℝ) (b : ℝ) :
    IsClosed (Certificates C f b) := by
  have h0 : IsClosed {w : Setoid V → ℝ | ∀p, 0 ≤ w p} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter (fun p => isClosed_le continuous_const (continuous_apply p))
  have h1 : IsClosed {w : Setoid V → ℝ | (∑p, w p)=1} :=
    isClosed_eq (continuous_finsetSum _ (fun p _ => continuous_apply p)) continuous_const
  have h2 : IsClosed {w : Setoid V → ℝ | ∀x ∈ C, (∑p, w p*f p x) ≤ b} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter (fun x => isClosed_iInter (fun _ => isClosed_le
      (continuous_finsetSum _ (fun p _ => (continuous_apply p).mul_const _)) continuous_const))
  exact h0.inter (h1.inter h2)

lemma certificates_compact (C : Set X) (f : Setoid V → X → ℝ) (b : ℝ) :
    IsCompact (Certificates C f b) := by
  have hbox : IsCompact {w : Setoid V → ℝ | ∀p, w p ∈ Set.Icc (0:ℝ) 1} :=
    isCompact_pi_infinite (fun _ => isCompact_Icc)
  apply hbox.of_isClosed_subset (certificates_isClosed C f b)
  intro w hw p
  refine ⟨hw.1 p,?_⟩
  have hh := single_le_sum (fun q _ => hw.1 q) (mem_univ p)
  exact hh.trans_eq hw.2.1

def uncrossWeight (w : Setoid V → ℝ) (p q : Setoid V) (δ : ℝ) : Setoid V → ℝ :=
  fun i => w i+(if i=p ⊓ q then δ else 0)+(if i=p ⊔ q then δ else 0)-
    (if i=p then δ else 0)-(if i=q then δ else 0)

omit [Fintype V] in
lemma uncrossWeight_nonneg (w : Setoid V → ℝ) (hw : ∀i, 0 ≤ w i)
    {p q : Setoid V} (hpq : p ≠ q) {δ : ℝ} (hδ : 0 ≤ δ)
    (hp : δ ≤ w p) (hq : δ ≤ w q) : ∀i, 0 ≤ uncrossWeight w p q δ i := by
  intro i
  have hmeet : 0 ≤ (if i=p ⊓ q then δ else 0) := by split_ifs <;> positivity
  have hjoin : 0 ≤ (if i=p ⊔ q then δ else 0) := by split_ifs <;> positivity
  unfold uncrossWeight
  by_cases hip : i=p
  · subst i
    simp only [ite_true,ite_eq_right hpq]
    linarith
  · by_cases hiq : i=q
    · subst i
      simp only [ite_eq_right hip,ite_true]
      linarith
    · simp only [ite_eq_right hip,ite_eq_right hiq,sub_zero]
      linarith [hw i]

lemma uncrossWeight_dot (w g : Setoid V → ℝ) (p q : Setoid V) (δ : ℝ) :
    (∑i, uncrossWeight w p q δ i*g i) =
      (∑i, w i*g i)+δ*g (p ⊓ q)+δ*g (p ⊔ q)-δ*g p-δ*g q := by
  simp [uncrossWeight,add_mul,sub_mul,sum_add_distrib,sum_sub_distrib,ite_mul]

lemma uncrossWeight_sum (w : Setoid V → ℝ) (p q : Setoid V) (δ : ℝ) :
    (∑i, uncrossWeight w p q δ i)=∑i, w i := by
  have hh := uncrossWeight_dot w (fun _ => 1) p q δ
  simpa only [mul_one,add_sub_cancel_right] using hh

theorem chain_certificate (C : Set X) (f : Setoid V → X → ℝ) (b : ℝ)
    (hsub : ∀x ∈ C, ∀p q, f (p ⊓ q) x+f (p ⊔ q) x ≤ f p x+f q x)
    (hne : (Certificates C f b).Nonempty) :
    ∃w ∈ Certificates C f b, IsChain (· ≤ ·) {p | 0 < w p} := by
  let Φ : (Setoid V → ℝ) → ℝ := fun w => ∑p, w p*potential p
  have hΦ : Continuous Φ := continuous_finsetSum _
    (fun p _ => (continuous_apply p).mul_const _)
  obtain ⟨w,hw,hmax⟩ := (certificates_compact C f b).exists_isMaxOn hne hΦ.continuousOn
  refine ⟨w,hw,?_⟩
  intro p hp q hq _
  by_contra hincomp
  have hpq : ¬p ≤ q := fun h => hincomp (Or.inl h)
  have hqp : ¬q ≤ p := fun h => hincomp (Or.inr h)
  have hnepq : p ≠ q := fun he => hpq (he ▸ le_rfl)
  let δ := min (w p) (w q)
  have hδ : 0 < δ := lt_min hp hq
  let w' := uncrossWeight w p q δ
  have hw' : w' ∈ Certificates C f b := by
    refine ⟨uncrossWeight_nonneg w hw.1 hnepq hδ.le (min_le_left _ _) (min_le_right _ _),?_,?_⟩
    · rw [uncrossWeight_sum]
      exact hw.2.1
    · intro x hx
      dsimp [w']
      rw [uncrossWeight_dot]
      have hh := mul_le_mul_of_nonneg_left (hsub x hx p q) hδ.le
      linarith [hw.2.2 x hx]
  have hgain := mul_pos hδ (sub_pos.mpr (potential_uncross hpq hqp))
  have hdot : Φ w' = Φ w+δ*potential (p ⊓ q)+δ*potential (p ⊔ q)-δ*potential p-δ*potential q :=
    uncrossWeight_dot w potential p q δ
  have hmax' := (isMaxOn_iff.mp hmax) w' hw'
  nlinarith only [hgain,hdot,hmax']

variable [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]

theorem feasible_of_chain_feasible (C : Set X) (hcompact : IsCompact C)
    (hne : C.Nonempty) (hconvex : Convex ℝ C) (f : Setoid V → X → ℝ)
    (hcontinuous : ∀p, ContinuousOn (f p) C)
    (hconcave : ∀p, ConcaveOn ℝ C (f p))
    (hsub : ∀x ∈ C, ∀p q, f (p ⊓ q) x+f (p ⊔ q) x ≤ f p x+f q x)
    (hchains : ∀J : Finset (Setoid V), IsChain (· ≤ ·) (J : Set (Setoid V)) →
      ∃x ∈ C, ∀p ∈ J, 0 ≤ f p x) :
    ∃x ∈ C, ∀p, 0 ≤ f p x := by
  by_contra hnone
  obtain ⟨ε,hε,w,hw,hws,hbound⟩ := ConvexAlternative.compact_concave_alternative C
    hcompact hne hconvex f hcontinuous hconcave hnone
  obtain ⟨v,hv,hvchain⟩ := chain_certificate C f (-ε) hsub ⟨w,hw,hws,hbound⟩
  let J := univ.filter (fun p => 0 < v p)
  have hJ : IsChain (· ≤ ·) (J : Set (Setoid V)) := by
    simpa only [J,coe_filter,coe_univ,Set.sep_univ,mem_univ,true_and] using hvchain
  obtain ⟨x,hx,hxJ⟩ := hchains J hJ
  have hnon : 0 ≤ ∑p, v p*f p x := by
    apply sum_nonneg
    intro p _
    by_cases hp : 0 < v p
    · exact mul_nonneg hp.le (hxJ p (mem_filter.mpr ⟨mem_univ p,hp⟩))
    · have he : v p=0 := le_antisymm (le_of_not_gt hp) (hv.1 p)
      simp [he]
  linarith only [hnon,hv.2.2 x hx,hε]

end
end AlgorithmicThinTrees.Partitions
end

end OAI
