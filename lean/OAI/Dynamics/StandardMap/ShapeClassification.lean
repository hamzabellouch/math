import OAI.Dynamics.StandardMap.RealCancellation

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology Classical
namespace StandardMapEntropy
lemma localUnit_affineOn {d : ℝ → ℝ → ℝ} (hd : TreeLine d) {U : Set ℝ}
    (hU : IsPreconnected U) (hl : ∀x∈U,LocallyAffineAt d x 1) :
    ∀a∈U,∀b∈U,d a b=|b-a| := by
  intro a ha b hb
  rcases lt_trichotomy a b with hab|rfl|hab
  · rw [abs_of_pos (sub_pos.mpr hab)]
    simpa only [one_mul] using tree_affine_of_fixed_local_speed hd a b 1 hab (by norm_num)
      (fun y hy => hl y (hU.ordConnected.out ha hb hy))
  · simp only [hd.self,sub_self,abs_zero]
  · rw [hd.symm,abs_sub_comm,abs_of_pos (sub_pos.mpr hab)]
    simpa only [one_mul] using tree_affine_of_fixed_local_speed hd b a 1 hab (by norm_num)
      (fun y hy => hl y (hU.ordConnected.out hb ha hy))
lemma slowCore_left_unit {d : ℝ → ℝ → ℝ} (hd : TreeLine d)
    (hc : Continuous (Function.uncurry d)) (hb : BddBelow (slowCore d)) :
    ∀x≤ sInf (slowCore d),∀y≤ sInf (slowCore d),d x y=|y-x| := by
  have hl : ∀x∈Iio (sInf (slowCore d)),LocallyAffineAt d x 1 := by
    intro x hx
    by_contra hh
    have hh' : x∈slowCore d := hh
    exact (not_le_of_gt hx) (csInf_le hb hh')
  have ha := localUnit_affineOn hd isPreconnected_Iio hl
  have he := affineOn_closure hc (Iio (sInf (slowCore d))) 1 (by simpa only [one_mul] using ha)
  rw [closure_Iio] at he
  simpa only [one_mul, mem_Iic, mem_Ici] using he
lemma slowCore_right_unit {d : ℝ → ℝ → ℝ} (hd : TreeLine d)
    (hc : Continuous (Function.uncurry d)) (hb : BddAbove (slowCore d)) :
    ∀x≥ sSup (slowCore d),∀y≥ sSup (slowCore d),d x y=|y-x| := by
  have hl : ∀x∈Ioi (sSup (slowCore d)),LocallyAffineAt d x 1 := by
    intro x hx
    by_contra hh
    have hh' : x∈slowCore d := hh
    exact (not_le_of_gt hx) (le_csSup hb hh')
  have ha := localUnit_affineOn hd isPreconnected_Ioi hl
  have he := affineOn_closure hc (Ioi (sSup (slowCore d))) 1 (by simpa only [one_mul] using ha)
  rw [closure_Ioi] at he
  simpa only [one_mul, mem_Iic, mem_Ici] using he
lemma closed_ordConnected_bounded {U : Set ℝ} (hc : IsClosed U) (hU : OrdConnected U)
    (hne : U.Nonempty) (hlo : BddBelow U) (hhi : BddAbove U) : U=Icc (sInf U) (sSup U) := by
  have ha := hc.csInf_mem hne hlo
  have hb := hc.csSup_mem hne hhi
  ext x
  exact ⟨fun hx => ⟨csInf_le hlo hx,le_csSup hhi hx⟩,fun hx => hU.out ha hb hx⟩
lemma closed_ordConnected_left_bounded {U : Set ℝ} (hc : IsClosed U) (hU : OrdConnected U)
    (hne : U.Nonempty) (hlo : BddBelow U) (hhi : ¬BddAbove U) : U=Ici (sInf U) := by
  have ha := hc.csInf_mem hne hlo
  ext x; constructor
  · exact csInf_le hlo
  · intro hx
    obtain ⟨y,hy,hxy⟩ := not_bddAbove_iff.mp hhi x
    exact hU.out ha hy ⟨hx,hxy.le⟩
lemma closed_ordConnected_right_bounded {U : Set ℝ} (hc : IsClosed U) (hU : OrdConnected U)
    (hne : U.Nonempty) (hlo : ¬BddBelow U) (hhi : BddAbove U) : U=Iic (sSup U) := by
  have hb := hc.csSup_mem hne hhi
  ext x; constructor
  · exact le_csSup hhi
  · intro hx
    obtain ⟨y,hy,hyx⟩ := not_bddBelow_iff.mp hlo x
    exact hU.out hy hb ⟨hyx.le,hx⟩

def SlowShape (d : ℝ → ℝ → ℝ) (c : ℝ) : Prop :=
  (∀x y:ℝ,d x y≤ c*|y-x|) ∨
  (∃a:ℝ,(∀x≤ a,∀y≤ a,d x y=|y-x|) ∧ (∀x≥ a,∀y≥ a,d x y≤ c*|y-x|)) ∨
  (∃b:ℝ,(∀x≥ b,∀y≥ b,d x y=|y-x|) ∧ (∀x≤ b,∀y≤ b,d x y≤ c*|y-x|)) ∨
  (∃a b:ℝ,a< b ∧ ExteriorUnitRays d a b ∧ ∀x∈Icc a b,∀y∈Icc a b,d x y≤ c*|y-x|)
lemma slowShape_of_exclusions {d : ℝ → ℝ → ℝ} (hd : TreeLine d)
    (hc : Continuous (Function.uncurry d)) (hn : NonaffineLine d) {c δ : ℝ}
    (hp : SlowPair d c) (hc1 : c<1) (hδ : 0<δ) (hf : NoFastCancellation d δ) : SlowShape d c := by
  have hne := slowCore_nonempty hd hn
  have hcl := isClosed_slowCore d
  have hU := slowCore_ordConnected hd hc hn hp hc1
  by_cases hlo : BddBelow (slowCore d)
  · have hl := slowCore_left_unit hd hc hlo
    by_cases hhi : BddAbove (slowCore d)
    · have hr := slowCore_right_unit hd hc hhi
      have he := closed_ordConnected_bounded hcl hU hne hlo hhi
      have hab : sInf (slowCore d)≤ sSup (slowCore d) := csInf_le hlo (hcl.csSup_mem hne hhi)
      have hrays : ExteriorUnitRays d (sInf (slowCore d)) (sSup (slowCore d)) :=
        ⟨fun x y hx hy => hl x hx y hy,fun x y hx hy => hr x hx y hy⟩
      have hlt := exterior_rays_nondegenerate hd hab hδ hrays hf (fun h => hn ⟨1,by simpa only [one_mul] using h⟩)
      refine Or.inr (Or.inr (Or.inr ⟨_,_,hlt,hrays,?_⟩))
      intro x hx y hy
      exact slowCore_secant hd hc hn hp (by rwa [he]) (by rwa [he])
    · have he := closed_ordConnected_left_bounded hcl hU hne hlo hhi
      refine Or.inr (Or.inl ⟨_,hl,?_⟩)
      intro x hx y hy
      apply slowCore_secant hd hc hn hp <;> rwa [he]
  · by_cases hhi : BddAbove (slowCore d)
    · have hr := slowCore_right_unit hd hc hhi
      have he := closed_ordConnected_right_bounded hcl hU hne hlo hhi
      refine Or.inr (Or.inr (Or.inl ⟨_,hr,?_⟩))
      intro x hx y hy
      apply slowCore_secant hd hc hn hp <;> rwa [he]
    · have he := ordConnected_eq_univ_of_unbounded hU hlo hhi
      refine Or.inl (fun x y => slowCore_secant hd hc hn hp ?_ ?_) <;> rw [he] <;> trivial
lemma SlowShape.slow_interval {d : ℝ → ℝ → ℝ} {c : ℝ} (h : SlowShape d c) :
    ∃a b:ℝ,a< b ∧ ∀x∈Icc a b,∀y∈Icc a b,d x y≤ c*|y-x| := by
  rcases h with h|⟨a,_,ha⟩|⟨b,_,hb⟩|⟨a,b,hab,_,h⟩
  · exact ⟨0,1,by norm_num,fun x _ y _ => h x y⟩
  · exact ⟨a,a+1,by linarith,fun x hx y hy => ha x hx.1 y hy.1⟩
  · exact ⟨b-1,b,by linarith,fun x hx y hy => hb x hx.2 y hy.2⟩
  · exact ⟨a,b,hab,h⟩
end StandardMapEntropy

end OAI
