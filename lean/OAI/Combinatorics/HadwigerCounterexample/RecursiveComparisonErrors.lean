import OAI.Combinatorics.HadwigerCounterexample.HeadPartitionComparison

namespace OAI

/-! # Recursive Comparison Errors -/

noncomputable section
namespace HadwigerCounterexample
open Finset Function Filter Matrix
open scoped BigOperators
variable {p : Shape} {I : Type} [Fintype I] [DecidableEq I] {n N : ℕ}
namespace Template
variable (v : Template p I)

theorem board_add (v : Template p I) (q : I→F) (U V : Wgt (Keys (p:=p) v.t N)) f :
    board v q (U+V) f=board v q U f+board v q V f := by
  unfold board curtain; simp only [Pi.add_apply,mul_add,add_mul,avg_add]

theorem shadow_add (v : Template p I) (q : I→F) (U V : Wgt (Keys (p:=p) v.t N))
    (r s : ℝ) (h : shadowed v q U r) (h' : shadowed v q V s) :
    shadowed v q (U+V) (r+s) := fun f hf => by
  rw [board_add]
  exact (abs_add_le _ _).trans (add_le_add (h f hf) (h' f hf))

theorem scene_join (v : Template p I) (q : I→ F) (U V : Wgt (Keys (p:=p) v.t N))
    (s : Script p I) (m : Mixer p n) (w : I→Wgt (Knobs p.g n))
    (x y : ℝ) (o : UnitType p n N)
    (h : exceeds v q (U+V) s m w (x+y) o) :
    exceeds v q U s m w x o ∨ exceeds v q V s m w y o := by
  classical
  obtain ⟨f,hf,h'⟩ := h
  have he :
      astonish v q (U+V) s m w f o=astonish v q U s m w f o+astonish v q V s m w f o := by
    simp only [astonish_val,Pi.add_apply,mul_add,add_mul,avg_add]
  change x+y < |astonish v q (U+V) s m w f o| at h'
  rw [he] at h'
  by_contra! hh
  have ht : |astonish v q U s m w f o|≤x := le_of_not_gt (fun h=>hh.1 ⟨f,hf,h⟩)
  have hv : |astonish v q V s m w f o|≤y := le_of_not_gt (fun h=>hh.2 ⟨f,hf,h⟩)
  exact not_lt_of_ge ((abs_add_le _ _).trans (add_le_add ht hv)) h'

def drained (m : Mixer p n) (C : ℝ) (w : Wgt (UnitType p n N)) :=
    let μ := raw m N; let H:=bp ((1/32:ℝ)*n)
    IsLaw w ∧ (∀ x,mapW w Prod.fst x ≤ H*μ x) ∧ (∀ x,mapW w Prod.snd x≤H*μ x) ∧
      ∀ x,w x ≤ bp (C*N)*pairW μ μ x

def engaged (v : Template p I) (q : I→F) (U : Wgt (Keys (p:=p) v.t N))
    (n : ℕ) (C e ε : ℝ) :=
  ∀ (m : Mixer p n),2*num (Full p n)<N →
    ∀ (w : Wgt (UnitType p n N)),drained m C w →
    ∀ (s : Script p I) (x : I→Wgt (Knobs p.g n)),(∀ i,IsLaw (x i)) →
      (∀ i,mapW (x i) (freePart p)=unif) → pr w (exceeds v q U s m x ε) ≤ e

set_option maxHeartbeats 800000 in
theorem gild_play (v : Template p I) (j : I) (q : I→F) (n N r : ℕ)
    (a : AtomKey (p:=p) (v.t j) N→Fin r) (B B' : Fin r→ Wgt (Keys (p:=p) (v.beyond j).t N))
    (U : Wgt (Keys (p:=p) v.t N)) (C ε x y : ℝ)
    (hs : shadowed v q (U-patched v j a B) ε)
    (h : engaged v q (U-patched v j a B) n C x ε)
    (hg : ∀ i,shadowed (v.beyond j) (v.boundTail j q) (B i-B' i) ε)
    (hh : ∀ i,engaged (v.beyond j) (v.boundTail j q) (B i-B' i) n C y ε) :
    let d:=U-patched v j a B'
    shadowed v q d (ε+ε) ∧ engaged v q d n C (x+r*y) (ε+ε) := by
  classical
  intro d
  let f:=U-patched v j a B
  let V z := B z - B' z
  let g:=patched v j a V
  have hd : d=f+g := by
    unfold d f g V; ext i; unfold patched; simp only [Pi.add_apply,Pi.sub_apply]
    ring
  rw [hd]
  refine ⟨shadow_add v q f g ε ε hs (patched_board v j q a V ε hg),?_⟩
  intro m hN w hw s u hu hz
  let W (i) := exceeds (v.beyond j) (v.boundTail j q) (V i) (scriptTail s j) m
    (fun i=>u i.val) ε
  have he (o) (hf : exceeds v q g s m u ε o) : ∃ i,W i o := by
    by_contra! hx
    exact patched_exceed v j q a V ε u hu s m o hx hf
  have hn := hw.1
  have hi :
      pr w (fun x => ∃ i:Fin r,W i x) ≤ (r:ℝ)*y := by
    refine (pr_exists_le hn.nz W).trans ((Finset.sum_le_sum
      (g:=fun _=>y) (fun i _=>?_)).trans_eq (by simp))
    exact hh i m hN w hw (scriptTail s j) _ (fun i =>hu i.val) (fun i =>hz i.val)
  apply (le_trans (pr_mono hn.nz (fun i => scene_join v q f g s m u _ _ i)) (pr_or_le hn.nz)).trans
  exact add_le_add (h m hN w hw s u hu hz) ((pr_mono hn.nz he).trans hi)
end Template
end HadwigerCounterexample

end

end OAI
