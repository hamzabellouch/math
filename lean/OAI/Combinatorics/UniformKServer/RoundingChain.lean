import Mathlib
import OAI.Combinatorics.UniformKServer.TreeDistribution

namespace OAI

                                    
section

/-! Chosen joint repairs form one adapted Markov chain on a fixed finite state
space. The choices use the old distribution and current geometric data only. -/
noncomputable section
namespace UniformKServer.TreeRounding
open Finset
open scoped Classical
variable {n k : ℕ} {S : Shape n} {X Ω : Type} [PseudoMetricSpace X]

theorem Distribution.ext {a : Allocation S k} {P Q : Distribution a}
    (h : P.law=Q.law) : P=Q := by cases P; cases Q; cases h; rfl

def chosenStep (w : Vertex n→ℝ) (hw : ∀ v,0≤w v)
    (hsep : ∀ v,v≠0 → 22*w v≤w (S.parent v))
    (a b : Allocation S k) (f g : Vertex n→X) (G : ℝ) (hG : 0≤G)
    (hgeo : ∀ u v,0<park S a.amount u → 0<park S b.amount v → u≠v →
      dist (f u) (g v)≤G*TreeAncestry.pathCost (S:=S) w u v)
    (P : Distribution a) : Coupling a b P :=
  Classical.choose (distribution_step w hw hsep a b f g G hG hgeo P)

theorem chosenStep_bound (w : Vertex n→ℝ) (hw : ∀ v,0≤w v)
    (hsep : ∀ v,v≠0 → 22*w v≤w (S.parent v))
    (a b : Allocation S k) (f g : Vertex n→X) (G : ℝ) (hG : 0≤G)
    (hgeo : ∀ u v,0<park S a.amount u → 0<park S b.amount v → u≠v →
      dist (f u) (g v)≤G*TreeAncestry.pathCost (S:=S) w u v)
    (P : Distribution a) :
    (chosenStep w hw hsep a b f g G hG hgeo P).joint.expect (fun st=>stateDistance f g st.1 st.2)≤
      G*132*variation w a b+∑ v,park S b.amount v*commonDistance a b f g v :=
  Classical.choose_spec (distribution_step w hw hsep a b f g G hG hgeo P)

structure ChainInput (S : Shape n) (k : ℕ) (X Ω : Type) [PseudoMetricSpace X] where
  allocation : ℕ→Ω→Allocation S k
  anchors : ℕ→Ω→Vertex n→X
  filtration : ℕ→Setoid Ω
  refines : ∀ t ω v,(filtration (t+1)).r ω v → (filtration t).r ω v
  allocation_causal : ∀ t ω v,(filtration t).r ω v → allocation t ω=allocation t v
  anchors_causal : ∀ t ω v,(filtration t).r ω v → anchors t ω=anchors t v
  weight : Vertex n→ℝ
  weight_nonneg : ∀ v,0≤weight v
  weight_separated : ∀ v,v≠0 → 22*weight v≤weight (S.parent v)
  factor : ℝ
  factor_nonneg : 0≤factor
  geometry : ∀ t ω u v,0<park S (allocation t ω).amount u →
    0<park S (allocation (t+1) ω).amount v → u≠v →
    dist (anchors t ω u) (anchors (t+1) ω v)≤factor*TreeAncestry.pathCost (S:=S) weight u v

namespace ChainInput
variable (D : ChainInput S k X Ω)

def step (t : ℕ) (ω : Ω) (P : Distribution (D.allocation t ω)) :=
  chosenStep D.weight D.weight_nonneg D.weight_separated (D.allocation t ω)
    (D.allocation (t+1) ω) (D.anchors t ω) (D.anchors (t+1) ω)
    D.factor D.factor_nonneg (D.geometry t ω) P

def distribution : (t : ℕ)→(ω : Ω)→Distribution (D.allocation t ω)
  | 0,ω => Classical.choice (distribution_initial (D.allocation 0 ω))
  | t+1,ω => (D.step t ω (distribution t ω)).next

theorem chosen_congr (w : Vertex n→ℝ) (hw : ∀ v,0≤w v)
    (hsep : ∀ v,v≠0 → 22*w v≤w (S.parent v))
    (a b a' b' : Allocation S k) (f g f' g' : Vertex n→X) (G : ℝ) (hG : 0≤G)
    (hgeo : ∀ u v,0<park S a.amount u → 0<park S b.amount v → u≠v →
      dist (f u) (g v)≤G*TreeAncestry.pathCost (S:=S) w u v)
    (hgeo' : ∀ u v,0<park S a'.amount u → 0<park S b'.amount v → u≠v →
      dist (f' u) (g' v)≤G*TreeAncestry.pathCost (S:=S) w u v)
    (P : Distribution a) (Q : Distribution a')
    (ha : a=a') (hb : b=b') (hf : f=f') (hg : g=g') (hp : P.law=Q.law) :
    (chosenStep w hw hsep a b f g G hG hgeo P).joint=
      (chosenStep w hw hsep a' b' f' g' G hG hgeo' Q).joint ∧
    (chosenStep w hw hsep a b f g G hG hgeo P).next.law=
      (chosenStep w hw hsep a' b' f' g' G hG hgeo' Q).next.law := by
  subst a'; subst b'; subst f'; subst g'
  have := Distribution.ext hp
  subst Q
  exact ⟨rfl,rfl⟩

theorem distribution_causal (t : ℕ) (ω v : Ω) (he : (D.filtration t).r ω v) :
    (D.distribution t ω).law=(D.distribution t v).law := by
  induction t with
  | zero =>
    have hi (a b : Allocation S k) (hab : a=b) :
        (Classical.choice (distribution_initial a)).law=(Classical.choice (distribution_initial b)).law := by
      subst b
      rfl
    exact hi _ _ (D.allocation_causal 0 ω v he)
  | succ t ih =>
    exact (chosen_congr D.weight D.weight_nonneg D.weight_separated _ _ _ _ _ _ _ _
      D.factor D.factor_nonneg (D.geometry t ω) (D.geometry t v) _ _
      (D.allocation_causal t ω v (D.refines t ω v he)) (D.allocation_causal (t+1) ω v he)
      (D.anchors_causal t ω v (D.refines t ω v he)) (D.anchors_causal (t+1) ω v he)
      (ih (D.refines t ω v he))).2

def joint (t : ℕ) (ω : Ω) := (D.step t ω (D.distribution t ω)).joint

theorem joint_causal (t : ℕ) (ω v : Ω) (he : (D.filtration (t+1)).r ω v) :
    D.joint t ω=D.joint t v :=
  (chosen_congr D.weight D.weight_nonneg D.weight_separated _ _ _ _ _ _ _ _
    D.factor D.factor_nonneg (D.geometry t ω) (D.geometry t v) _ _
    (D.allocation_causal t ω v (D.refines t ω v he)) (D.allocation_causal (t+1) ω v he)
    (D.anchors_causal t ω v (D.refines t ω v he)) (D.anchors_causal (t+1) ω v he)
    (D.distribution_causal t ω v (D.refines t ω v he))).1

theorem first (t : ℕ) (ω : Ω) (F : State S k→ℝ) :
    (D.joint t ω).expect (F ∘ Prod.fst)=(D.distribution t ω).law.expect F :=
  (D.step t ω (D.distribution t ω)).first F

theorem second (t : ℕ) (ω : Ω) (F : State S k→ℝ) :
    (D.joint t ω).expect (F ∘ Prod.snd)=(D.distribution (t+1) ω).law.expect F :=
  (D.step t ω (D.distribution t ω)).second F

theorem cost_bound (t : ℕ) (ω : Ω) :
    (D.joint t ω).expect (fun st=>stateDistance (D.anchors t ω) (D.anchors (t+1) ω) st.1 st.2)≤
      D.factor*132*variation D.weight (D.allocation t ω) (D.allocation (t+1) ω)+
        ∑ v,park S (D.allocation (t+1) ω).amount v*
          commonDistance (D.allocation t ω) (D.allocation (t+1) ω) (D.anchors t ω) (D.anchors (t+1) ω) v :=
  chosenStep_bound D.weight D.weight_nonneg D.weight_separated _ _ _ _
    D.factor D.factor_nonneg (D.geometry t ω) _

end ChainInput
end UniformKServer.TreeRounding

end


end

end OAI
