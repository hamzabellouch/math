import Mathlib
import OAI.Probability.LatticeSurface.Dynamics.ProjectionMesh

namespace OAI

namespace ProjectionComparison

open Set Filter

attribute [local instance] Classical.propDecidable

variable {V E : Type*} [Fintype V] [Fintype E]

def restrictedSystem (S : System V E) (W : Set V) :
    System W {e : E // S.left e∈W ∧ S.right e∈W} where
  left e := ⟨S.left e,e.property.1⟩
  right e := ⟨S.right e,e.property.2⟩
  cost e := S.cost e
  pins := {x | x.val∈S.pins}

omit [Fintype V] [Fintype E] in
lemma feasible_restrict (S : System V E) (W : Set V) (b h : V → ℝ)
    (hh : h∈feasible S b) :
    (fun x : W => h x)∈feasible (restrictedSystem S W) (fun x => b x) :=
  ⟨fun e => hh.1 e,fun x hx => hh.2 x hx⟩

end ProjectionComparison

namespace ProjectionComparison

open Set Filter

attribute [local instance] Classical.propDecidable

variable {V E : Type*} [Fintype V] [Fintype E]

lemma one_sided_tangent_variational (S : System V E) (b v h d : V → ℝ)
    (hp : IsProjection S b v h) (hpin : ∀x∈S.pins,d x=0)
    (hedge : ∀e,h (S.left e)-h (S.right e)=S.cost e → d (S.left e)-d (S.right e)≤0) :
    0 ≤ ∑x,(h x-v x)*d x := by
  have hev : ∀ᶠ t in nhds (0:ℝ),0≤t → (fun x => h x+t*d x)∈feasible S b := by
    have he : ∀ᶠ t in nhds (0:ℝ),∀e,0≤t →
        (h (S.left e)+t*d (S.left e))-(h (S.right e)+t*d (S.right e))≤S.cost e := by
      apply Filter.eventually_all.mpr
      intro e
      by_cases ha : h (S.left e)-h (S.right e)=S.cost e
      · exact Filter.Eventually.of_forall (fun t ht => by nlinarith [mul_nonpos_of_nonneg_of_nonpos ht (hedge e ha)])
      · have hs : h (S.left e)-h (S.right e)<S.cost e := lt_of_le_of_ne (hp.1.1 e) ha
        have hc : Continuous (fun t : ℝ => (h (S.left e)+t*d (S.left e))-(h (S.right e)+t*d (S.right e))) := by fun_prop
        have he0 : (h (S.left e)+(0:ℝ)*d (S.left e))-(h (S.right e)+0*d (S.right e))<S.cost e := by simpa using hs
        exact (hc.continuousAt.eventually (gt_mem_nhds he0)).mono fun t ht _ => ht.le
    filter_upwards [he] with t ht hn
    exact ⟨fun e => ht e hn,fun x hx => by simp [hpin x hx,hp.1.2 x hx]⟩
  obtain ⟨ε,hε,hball⟩ := Metric.eventually_nhds_iff.mp hev
  have ht : 0<ε/2 := by linarith
  have hv := variational S b v h hp (fun x => h x+(ε/2)*d x)
    (hball (by simpa only [Real.dist_eq,sub_zero,abs_of_pos ht] using (show ε/2<ε by linarith)) ht.le)
  have hid : (∑x,(h x-v x)*((h x+(ε/2)*d x)-h x))=(ε/2)*∑x,(h x-v x)*d x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl;intro x hx;ring
  rw [hid] at hv
  exact nonneg_of_mul_nonneg_right hv ht

end ProjectionComparison

namespace ProjectionComparison

open Set Filter

attribute [local instance] Classical.propDecidable

variable {V E : Type*} [Fintype V] [Fintype E]

theorem projection_restrict (S : System V E) (W : Set V) (hW : S.pins⊆W)
    (b v h : V → ℝ) (hp : IsProjection S b v h)
    (hcut : ∀e,h (S.left e)-h (S.right e)=S.cost e →
      S.left e∉S.pins → S.right e∉S.pins → (S.left e∈W ↔ S.right e∈W)) :
    IsProjection (restrictedSystem S W) (fun x => b x) (fun x => v x) (fun x => h x) := by
  refine ⟨feasible_restrict S W b h hp.1,?_⟩
  intro k hk
  let d : V → ℝ := fun x => if hx : x∈W then k ⟨x,hx⟩-h x else 0
  have hd (x : W) : d x=k x-h x := by simp [d,x.property]
  have hpins : ∀x∈S.pins,d x=0 := by
    intro x hx
    have hxW := hW hx
    rw [show d x=k ⟨x,hxW⟩-h x by simp [d,hxW]]
    rw [hk.2 ⟨x,hxW⟩ hx,hp.1.2 x hx,sub_self]
  have hdir (e : E) (ha : h (S.left e)-h (S.right e)=S.cost e) :
      d (S.left e)-d (S.right e)≤0 := by
    by_cases hl : S.left e∈W <;> by_cases hr : S.right e∈W
    · have hkedge := hk.1 ⟨e,hl,hr⟩
      change k ⟨S.left e,hl⟩-k ⟨S.right e,hr⟩≤S.cost e at hkedge
      simp only [d,dite_eq_left hl,dite_eq_left hr]
      linarith
    · have hpr : S.right e∉S.pins := fun hp => hr (hW hp)
      have hpl : S.left e∈S.pins := by
        by_contra hn
        exact hr ((hcut e ha hn hpr).mp hl)
      rw [hpins _ hpl]
      simp [d,hr]
    · have hpl : S.left e∉S.pins := fun hp => hl (hW hp)
      have hpr : S.right e∈S.pins := by
        by_contra hn
        exact hl ((hcut e ha hpl hn).mpr hr)
      rw [hpins _ hpr]
      simp [d,hl]
    · simp [d,hl,hr]
  have hv := one_sided_tangent_variational S b v h d hp hpins hdir
  have he : (∑x,(h x-v x)*d x)=∑x : W,(h x-v x)*(k x-h x) := by
    apply Finset.sum_congr_set W
    · intro x hx;rw [show d x=k ⟨x,hx⟩-h x by simp [d,hx]]
    · intro x hx;simp [d,hx]
  rw [he] at hv
  have hq : 0 ≤ ∑x : W,(k x-h x)^2 := Finset.sum_nonneg fun x _ => sq_nonneg _
  have hid : objective (fun x : W => v x) k=objective (fun x : W => v x) (fun x => h x)+
      2*(∑x : W,(h x-v x)*(k x-h x))+∑x : W,(k x-h x)^2 := by
    simp only [objective,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl;intro x hx;ring
  linarith

end ProjectionComparison

end OAI
