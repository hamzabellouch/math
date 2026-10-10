import Mathlib
import OAI.Probability.LatticeSurface.Dynamics.ProjectionExistence

namespace OAI

namespace ProjectionComparison

open Set

variable {V E : Type*}

def activeGraph (S : System V E) (h : V → ℝ) : SimpleGraph V where
  Adj x y := x≠y ∧ ∃ e,h (S.left e)-h (S.right e)=S.cost e ∧
    ((S.left e=x ∧ S.right e=y) ∨ (S.left e=y ∧ S.right e=x))
  symm := ⟨by rintro x y ⟨hne,e,he,hor⟩;exact ⟨hne.symm,e,he,hor.symm⟩⟩
  loopless := ⟨by intro x hx;exact hx.1 rfl⟩

noncomputable def activeComponent [Fintype V] (S : System V E) (h : V → ℝ) (x : V) : Finset V :=
  by classical exact {y | (activeGraph S h).Reachable x y}.toFinset

lemma mem_activeComponent [Fintype V] (S : System V E) (h : V → ℝ) (x y : V) :
    y∈activeComponent S h x ↔ (activeGraph S h).Reachable x y := by classical exact Set.mem_toFinset

end ProjectionComparison

namespace ProjectionComparison

open Set

variable {V E : Type*} [Fintype V] [Fintype E]

omit [Fintype V] in
lemma tangent_feasible (S : System V E) (b h w : V → ℝ) (hh : h∈feasible S b)
    (hw : ∀ x∈S.pins,w x=0)
    (he : ∀ e,h (S.left e)-h (S.right e)=S.cost e → w (S.left e)=w (S.right e)) :
    ∀ᶠ t in nhds (0:ℝ),(fun x => h x+t*w x)∈feasible S b := by
  have hedges : ∀ᶠ t in nhds (0:ℝ),∀ e,(h (S.left e)+t*w (S.left e))-(h (S.right e)+t*w (S.right e))≤S.cost e := by
    apply Filter.eventually_all.mpr
    intro e
    by_cases hact : h (S.left e)-h (S.right e)=S.cost e
    · exact Filter.Eventually.of_forall (fun t => by rw [he e hact];linarith)
    · have hs : h (S.left e)-h (S.right e)<S.cost e := lt_of_le_of_ne (hh.1 e) hact
      have hc : Continuous (fun t : ℝ => (h (S.left e)+t*w (S.left e))-(h (S.right e)+t*w (S.right e))) := by fun_prop
      have ht : (fun t : ℝ => (h (S.left e)+t*w (S.left e))-(h (S.right e)+t*w (S.right e))) 0<S.cost e := by simpa using hs
      exact (hc.continuousAt.eventually (gt_mem_nhds ht)).mono fun _ ht => ht.le
  filter_upwards [hedges] with t ht
  refine ⟨ht,?_⟩
  intro x hx
  dsimp only
  rw [hw x hx,hh.2 x hx,mul_zero,add_zero]

lemma tangent_balance (S : System V E) (b v h w : V → ℝ) (hp : IsProjection S b v h)
    (hw : ∀ x∈S.pins,w x=0)
    (he : ∀ e,h (S.left e)-h (S.right e)=S.cost e → w (S.left e)=w (S.right e)) :
    (∑ x,(h x-v x)*w x)=0 := by
  obtain ⟨ε,hε,hball⟩ := Metric.eventually_nhds_iff.mp (tangent_feasible S b h w hp.1 hw he)
  have hplus := variational S b v h hp (fun x => h x+(ε/2)*w x)
    (hball (by simpa only [Real.dist_eq,sub_zero,abs_of_pos (by linarith : 0<ε/2)] using (show ε/2<ε by linarith)))
  have hminus := variational S b v h hp (fun x => h x+(-ε/2)*w x)
    (hball (by rw [Real.dist_eq,sub_zero,abs_of_neg (by linarith : -ε/2<0)];linarith))
  have hid (t : ℝ) : (∑ x,(h x-v x)*((h x+t*w x)-h x))=t*(∑ x,(h x-v x)*w x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl;intro x hx;ring
  rw [hid] at hplus hminus
  nlinarith

omit [Fintype V] [Fintype E] in
lemma active_edge_reachable (S : System V E) (h : V → ℝ) (e : E)
    (he : h (S.left e)-h (S.right e)=S.cost e) :
    (activeGraph S h).Reachable (S.left e) (S.right e) := by
  by_cases heq : S.left e=S.right e
  · simpa only [heq] using (SimpleGraph.Reachable.refl (S.right e) : (activeGraph S h).Reachable (S.right e) (S.right e))
  · exact SimpleGraph.Adj.reachable (show (activeGraph S h).Adj (S.left e) (S.right e) from ⟨heq,e,he,Or.inl ⟨rfl,rfl⟩⟩)

lemma component_balance (S : System V E) (b v h : V → ℝ) (hp : IsProjection S b v h)
    (x : V) (hpin : ∀ p∈S.pins,¬(activeGraph S h).Reachable x p) :
    (∑ y ∈ activeComponent S h x, (h y-v y))=0 := by
  classical
  let w : V → ℝ := fun y => if (activeGraph S h).Reachable x y then 1 else 0
  have hw : ∀ p∈S.pins,w p=0 := by intro p hp;exact ite_eq_right (hpin p hp)
  have he (e : E) (he : h (S.left e)-h (S.right e)=S.cost e) : w (S.left e)=w (S.right e) := by
    have hr := active_edge_reachable S h e he
    have hi : (activeGraph S h).Reachable x (S.left e) ↔ (activeGraph S h).Reachable x (S.right e) :=
      ⟨fun hx => hx.trans hr,fun hx => hx.trans hr.symm⟩
    simp only [w,hi]
  have hbal := tangent_balance S b v h w hp hw he
  calc
    (∑ y ∈ activeComponent S h x, (h y-v y)) = ∑ y ∈ activeComponent S h x, (h y-v y)*w y := by
      apply Finset.sum_congr rfl
      intro y hy
      simp only [w,ite_eq_left ((mem_activeComponent S h x y).mp hy),mul_one]
    _ = ∑ y, (h y-v y)*w y := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro y hy hn
      have hn' : ¬(activeGraph S h).Reachable x y := by simpa only [mem_activeComponent] using hn
      simp only [w,ite_eq_right hn',mul_zero]
    _ = 0 := hbal

omit [Fintype V] [Fintype E] in
lemma active_graph_eq (S : System V E) (h k : V → ℝ)
    (he : ∀ e,h (S.left e)-h (S.right e)=S.cost e ↔ k (S.left e)-k (S.right e)=S.cost e) :
    activeGraph S h=activeGraph S k := by
  ext x y
  simp only [activeGraph,he]

omit [Fintype V] [Fintype E] in
lemma active_difference_constant (S : System V E) (h k : V → ℝ)
    (he : ∀ e,h (S.left e)-h (S.right e)=S.cost e → k (S.left e)-k (S.right e)=S.cost e)
    (x y : V) (hxy : (activeGraph S h).Reachable x y) : h x-k x=h y-k y := by
  obtain ⟨p⟩ := hxy
  induction p with
  | nil => rfl
  | @cons x z y hxz p ih =>
    rcases hxz with ⟨_,e,heh,hor⟩
    have hek := he e heh
    have hxz : h x-k x=h z-k z := by
      rcases hor with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> linarith
    exact hxz.trans ih

omit [Fintype E] in
lemma grounded_component_difference (S : System V E) (b₁ b₂ v₁ v₂ h₁ h₂ : V → ℝ)
    (hp₁ : IsProjection S b₁ v₁ h₁) (hp₂ : IsProjection S b₂ v₂ h₂)
    (hface : ∀ e,h₁ (S.left e)-h₁ (S.right e)=S.cost e → h₂ (S.left e)-h₂ (S.right e)=S.cost e)
    (x p : V) (hpin : p∈S.pins) (hxp : (activeGraph S h₁).Reachable x p) :
    h₁ x-h₂ x=b₁ p-b₂ p := by
  rw [active_difference_constant S h₁ h₂ hface x p hxp,hp₁.1.2 p hpin,hp₂.1.2 p hpin]

end ProjectionComparison

namespace ProjectionComparison

open Set

variable {V E : Type*} [Fintype V] [Fintype E]

theorem component_averaging (S : System V E) (b₁ b₂ v₁ v₂ h₁ h₂ : V → ℝ)
    (hp₁ : IsProjection S b₁ v₁ h₁) (hp₂ : IsProjection S b₂ v₂ h₂)
    (hface : ∀ e,h₁ (S.left e)-h₁ (S.right e)=S.cost e ↔ h₂ (S.left e)-h₂ (S.right e)=S.cost e)
    (x : V) :
    (∀ p∈S.pins,¬(activeGraph S h₁).Reachable x p) →
    h₁ x-h₂ x=(∑ y ∈ activeComponent S h₁ x, (v₁ y-v₂ y))/(activeComponent S h₁ x).card := by
  intro hpin
  classical
  have hg := active_graph_eq S h₁ h₂ hface
  have hcomp : activeComponent S h₁ x=activeComponent S h₂ x := by ext y;simp only [mem_activeComponent,hg]
  have hc₁ := component_balance S b₁ v₁ h₁ hp₁ x hpin
  have hc₂ := component_balance S b₂ v₂ h₂ hp₂ x (by simpa only [← hg] using hpin)
  rw [← hcomp] at hc₂
  have hsum : (∑ y ∈ activeComponent S h₁ x, (h₁ y-h₂ y))=∑ y ∈ activeComponent S h₁ x, (v₁ y-v₂ y) := by
    simp only [Finset.sum_sub_distrib] at hc₁ hc₂ ⊢
    linarith
  have hconst : (∑ y ∈ activeComponent S h₁ x, (h₁ y-h₂ y))=(activeComponent S h₁ x).card*(h₁ x-h₂ x) := by
    trans ∑ _y ∈ activeComponent S h₁ x, (h₁ x-h₂ x)
    · apply Finset.sum_congr rfl
      intro y hy
      have hxy : (activeGraph S h₁).Reachable x y := (mem_activeComponent S h₁ x y).mp hy
      exact (active_difference_constant S h₁ h₂ (fun e he => (hface e).mp he) x y hxy).symm
    · simp only [Finset.sum_const,nsmul_eq_mul]
  have hx : x∈activeComponent S h₁ x := (mem_activeComponent S h₁ x x).mpr (SimpleGraph.Reachable.refl _)
  have hcard : (0:ℝ)<(activeComponent S h₁ x).card := Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨x,hx⟩)
  apply (eq_div_iff hcard.ne').mpr
  rw [← hsum,hconst,mul_comm]

end ProjectionComparison

end OAI
