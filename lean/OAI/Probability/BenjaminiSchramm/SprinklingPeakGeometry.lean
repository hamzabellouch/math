import OAI.Probability.BenjaminiSchramm.PeakSurgeryGeometry
import OAI.Probability.BenjaminiSchramm.LayerFrontierGeometry
import OAI.Probability.UnimodularPercolation.Kernel.Sprinkling

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma conn_last_exit_off_internal (ω : Set E) (S : Set V) {x y : V}
    (hx : x ∈ S) (hy : y ∉ S) (hc : Conn G ω x y) :
    ∃ u ∈ S, Conn G (ω \ internalEdges G S) u y := by
  obtain ⟨z,⟨hz,u,hu,e,he,heq⟩,hzy⟩ := conn_last_exit_frontier G ω S hx hy hc
  have heI : e ∉ internalEdges G S := fun h => hz (h z (by rw [heq]; simp))
  have huz : Conn G (ω \ internalEdges G S) u z :=
    Relation.ReflTransGen.single ⟨e,⟨he,heI⟩,heq⟩
  refine ⟨u,hu,huz.trans (conn_mono G ?_ hzy)⟩
  intro b hb
  refine ⟨hb.1,fun hI => hb.2 ?_⟩
  exact ⟨(G b).out.1,hI _ (Sym2.out_fst_mem _),Sym2.out_fst_mem _⟩

lemma union_strict_peak_of_exterior_avoidance (white blue : Set E) (f : V → ℝ) (x : V)
    (hpeak : ∀ y, Conn G white x y → y ≠ x → f y < f x)
    (havoid : ∀ u ∈ cluster G white x,
      ¬∃ y, y ≠ x ∧ f x ≤ f y ∧ y ∉ cluster G white x ∧
        Conn G ((white ∪ blue) \ internalEdges G (cluster G white x)) u y) :
    ∀ y, Conn G (white ∪ blue) x y → y ≠ x → f y < f x := by
  intro y hxy hyx
  by_contra! hle
  have hyS : y ∉ cluster G white x := fun hy => (hpeak y hy hyx).not_ge hle
  obtain ⟨u,hu,huy⟩ := conn_last_exit_off_internal G (white ∪ blue) (cluster G white x)
    (mem_cluster_self G white x) hyS hxy
  exact havoid u hu ⟨y,hyx,hle,hyS,huy⟩

lemma no_blue_incident_exterior_avoidance (white blue : Set E) (x u : V)
    (hu : u ∈ cluster G white x)
    (hblue : ∀ e, u ∈ G e → e ∉ blue) :
    ∀ y, y ∉ cluster G white x →
      ¬Conn G ((white ∪ blue) \ internalEdges G (cluster G white x)) u y := by
  have hnobond (v : V) :
      ¬∃ e ∈ ((white ∪ blue) \ internalEdges G (cluster G white x)), G e=s(u,v) := by
    rintro ⟨e,⟨he,heI⟩,heq⟩
    have hue : u ∈ G e := by rw [heq]; simp
    have hew : e ∈ white := he.resolve_right (hblue e hue)
    have hv : v ∈ cluster G white x := hu.trans (Relation.ReflTransGen.single ⟨e,hew,heq⟩)
    apply heI
    intro z hz
    rw [heq] at hz
    rcases Sym2.mem_iff.mp hz with hzu | hzv
    · rwa [hzu]
    · rwa [hzv]
  have hsame (y : V) (hy : Conn G ((white ∪ blue) \ internalEdges G (cluster G white x)) u y) : y=u := by
    induction hy with
    | refl => rfl
    | @tail a b _ hab ih =>
      subst a
      exact False.elim (hnobond b hab)
  intro y hy hconn
  exact hy (hsame y hconn ▸ hu)

end Percolation.BenjaminiSchramm

end

end OAI
