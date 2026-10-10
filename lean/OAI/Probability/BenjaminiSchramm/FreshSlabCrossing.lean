import OAI.Probability.BenjaminiSchramm.SelectedLayerVertex
import OAI.Probability.UnimodularPercolation.Deformation.ClusterProducts

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma conn_internalEdges_end_mem (ω : Set E) (D : Set V) {x y : V}
    (hx : x ∈ D) (hconn : Conn G (ω ∩ internalEdges G D) x y) : y ∈ D := by
  induction hconn with
  | refl => exact hx
  | @tail z y _ hy _ =>
    obtain ⟨e,he,heq⟩ := hy
    exact he.2 y (by rw [heq]; simp)

def lowerCrossingBlock (f : V → ℝ) (a b R : ℝ) : Set E :=
  internalEdges G {v | a ≤ f v ∧ f v ≤ b+R} ∩ (internalEdges G {v | b ≤ f v})ᶜ

lemma lowerCrossingBlock_disjoint_upper (f : V → ℝ) (a b R : ℝ) :
    Disjoint (lowerCrossingBlock G f a b R) (internalEdges G {v | b ≤ f v}) := by
  exact Set.disjoint_left.mpr fun _ h₁ h₂ => h₁.2 h₂

lemma first_height_crossing_unexposed (f : V → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hjump : ∀ e u v, u ∈ G e → v ∈ G e → |f v-f u| ≤ R)
    (ω : Set E) {x y : V} (p : (openSimpleGraph G ω).Walk x y) (a b : ℝ) :
    a ≤ f x → f x < b → b ≤ f y → (∀ z ∈ p.support, a ≤ f z) →
      ∃ z, b ≤ f z ∧ f z ≤ b+R ∧
        Conn G (ω ∩ lowerCrossingBlock G f a b R) x z := by
  induction p with
  | @nil u =>
    intro _ hu hv _
    exact (not_lt_of_ge hv hu).elim
  | @cons x v y huv p ih =>
    intro ha hb hend hlow
    have hav : a ≤ f v := hlow v (by simp)
    obtain ⟨e,he,heq⟩ := huv.2
    have hxe : x ∈ G e := by rw [heq]; simp
    have hve : v ∈ G e := by rw [heq]; simp
    have hj := (abs_le.mp (hjump e x v hxe hve)).2
    by_cases hv : b ≤ f v
    · have hvR : f v ≤ b+R := by linarith
      refine ⟨v,hv,hvR,Relation.ReflTransGen.single ⟨e,⟨he,?_,?_⟩,heq⟩⟩
      · rw [mem_internalEdges_of_ends G _ e x v heq]
        exact ⟨⟨ha,by linarith⟩,hav,hvR⟩
      · intro he'
        exact (not_le_of_gt hb) (he' x hxe)
    · obtain ⟨z,hz,hzR,hconn⟩ := ih hav (lt_of_not_ge hv) hend
        (fun w hw => hlow w (List.mem_cons_of_mem _ hw))
      refine ⟨z,hz,hzR,(Relation.ReflTransGen.single ⟨e,⟨he,?_,?_⟩,heq⟩).trans hconn⟩
      · rw [mem_internalEdges_of_ends G _ e x v heq]
        exact ⟨⟨ha,by linarith⟩,hav,by linarith⟩
      · intro he'
        exact (not_le_of_gt hb) (he' x hxe)

theorem conn_above_lower_first_crossing (f : V → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hjump : ∀ e u v, u ∈ G e → v ∈ G e → |f v-f u| ≤ R)
    (ω : Set E) (x y : V) (a b : ℝ) (hx : a ≤ f x) (hxb : f x < b)
    (hy : b ≤ f y) (hc : Conn G (ω ∩ internalEdges G {v | a ≤ f v}) x y) :
    ∃ z, b ≤ f z ∧ f z ≤ b+R ∧
      Conn G (ω ∩ lowerCrossingBlock G f a b R) x z := by
  obtain ⟨p⟩ := (conn_iff_reachable G _ x y).mp hc
  have hlow : ∀ z ∈ p.support, a ≤ f z := by
    intro z hz
    have hconn : Conn G (ω ∩ internalEdges G {v | a ≤ f v}) x z :=
      (conn_iff_reachable G _ x z).mpr ⟨p.takeUntil z hz⟩
    exact conn_internalEdges_end_mem G ω _ hx hconn
  obtain ⟨z,hz,hzR,hconn⟩ := first_height_crossing_unexposed G f R hR hjump
    (ω ∩ internalEdges G {v | a ≤ f v}) p a b hx hxb hy hlow
  refine ⟨z,hz,hzR,conn_mono G ?_ hconn⟩
  intro e he
  exact ⟨he.1.1,he.2⟩

end Percolation.BenjaminiSchramm

end

end OAI
