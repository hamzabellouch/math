import OAI.Probability.BenjaminiSchramm.ModularSlabs

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical

namespace Percolation.BenjaminiSchramm
variable {V : Type*} {H : SimpleGraph V}

lemma first_height_crossing_walk (f : V → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hjump : ∀ {u v}, H.Adj u v → |f v - f u| ≤ R)
    {x y : V} (p : H.Walk x y) (a b : ℝ) :
    a ≤ f x → f x ≤ b → b ≤ f y → (∀ z ∈ p.support, a ≤ f z) →
      ∃ z, ∃ q : H.Walk x z,
        b ≤ f z ∧ f z ≤ b+R ∧ q.support ⊆ p.support ∧
        ∀ w ∈ q.support, a ≤ f w ∧ f w ≤ b+R := by
  induction p with
  | @nil u =>
    intro ha hb hend _
    refine ⟨_,SimpleGraph.Walk.nil,hend,by linarith,?_,?_⟩
    · exact fun _ h => h
    · intro w hw
      have hw' : w = u := by simpa only [SimpleGraph.Walk.support_nil,List.mem_singleton] using hw
      subst w
      exact ⟨ha,by linarith⟩
  | @cons x v y huv p ih =>
    intro ha hb hend hlow
    by_cases hx : b ≤ f x
    · refine ⟨x,SimpleGraph.Walk.nil,hx,by linarith,?_,?_⟩
      · intro w hw
        have hw' : w = x := by simpa only [SimpleGraph.Walk.support_nil,List.mem_singleton] using hw
        subst w
        exact SimpleGraph.Walk.start_mem_support _
      · intro w hw
        have hw' : w = x := by simpa only [SimpleGraph.Walk.support_nil,List.mem_singleton] using hw
        subst w
        exact ⟨ha,by linarith⟩
    have hav : a ≤ f v := hlow v (by simp)
    by_cases hv : b ≤ f v
    · have hvu := (abs_le.mp (hjump huv)).2
      refine ⟨v,SimpleGraph.Walk.cons huv SimpleGraph.Walk.nil,hv,by linarith,?_,?_⟩
      · intro w hw
        simp only [SimpleGraph.Walk.support_cons,SimpleGraph.Walk.support_nil,List.mem_cons,
          List.not_mem_nil,or_false] at hw
        rcases hw with rfl | rfl
        · exact SimpleGraph.Walk.start_mem_support _
        · simp
      · intro w hw
        simp only [SimpleGraph.Walk.support_cons,SimpleGraph.Walk.support_nil,List.mem_cons,
          List.not_mem_nil,or_false] at hw
        rcases hw with rfl | rfl <;> exact ⟨by assumption,by linarith⟩
    · obtain ⟨z,q,hz,hz',hq,hbound⟩ := ih hav (le_of_not_ge hv) hend
        (fun w hw => hlow w (List.mem_cons_of_mem _ hw))
      refine ⟨z,q.cons huv,hz,hz',?_,?_⟩
      · intro w hw
        simp only [SimpleGraph.Walk.support_cons,List.mem_cons] at hw ⊢
        exact hw.imp id (hq ·)
      · intro w hw
        simp only [SimpleGraph.Walk.support_cons,List.mem_cons] at hw
        rcases hw with rfl | hw
        · exact ⟨ha,by linarith⟩
        · exact hbound w hw

end Percolation.BenjaminiSchramm

end

end OAI
