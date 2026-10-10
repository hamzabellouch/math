import Mathlib
import OAI.Probability.LatticeSurface.Dynamics.ProjectionFaces

namespace OAI

namespace ProjectionComparison

open Set

variable {V E : Type*} [Fintype V] [Fintype E]

omit [Fintype V] [Fintype E] in
lemma active_values_constant (S : System V E) (h d : V → ℝ)
    (he : ∀ e,h (S.left e)-h (S.right e)=S.cost e → d (S.left e)=d (S.right e))
    (x y : V) (hxy : (activeGraph S h).Reachable x y) : d x=d y := by
  obtain ⟨p⟩ := hxy
  induction p with
  | nil => rfl
  | @cons x z y hxz p ih =>
    rcases hxz with ⟨_,e,heh,hor⟩
    have hek := he e heh
    have hxz : d x=d z := by
      rcases hor with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hek
      · exact hek.symm
    exact hxz.trans ih

omit [Fintype V] in
lemma active_eventually_subset (S : System V E) (H : ℝ → V → ℝ) (t : ℝ)
    (hc : ∀ x,ContinuousAt (fun s => H s x) t) :
    ∀ᶠ s in nhds t,∀ e,H s (S.left e)-H s (S.right e)=S.cost e → H t (S.left e)-H t (S.right e)=S.cost e := by
  apply Filter.eventually_all.mpr
  intro e
  by_cases he : H t (S.left e)-H t (S.right e)=S.cost e
  · exact Filter.Eventually.of_forall (fun _ _ => he)
  · have hne := ((hc (S.left e)).sub (hc (S.right e))).eventually (isOpen_ne.mem_nhds he)
    filter_upwards [hne] with s hs
    exact fun h => (hs h).elim

end ProjectionComparison

namespace ProjectionComparison

open Set

variable {V E : Type*} [Fintype V] [Fintype E]

theorem projection_derivative (S : System V E) (B U H : ℝ → V → ℝ) (dB dU dH : V → ℝ) (t : ℝ)
    (hp : ∀ᶠ s in nhds t,IsProjection S (B s) (U s) (H s))
    (hb : ∀ x,HasDerivAt (fun s => B s x) (dB x) t)
    (hu : ∀ x,HasDerivAt (fun s => U s x) (dU x) t)
    (hh : ∀ x,HasDerivAt (fun s => H s x) (dH x) t) :
    (∀ x p,p∈S.pins → (activeGraph S (H t)).Reachable x p → dH x=dB p) ∧
    (∀ x,(∀ p∈S.pins,¬(activeGraph S (H t)).Reachable x p) →
      dH x=(∑ y∈activeComponent S (H t) x,dU y)/(activeComponent S (H t) x).card) := by
  classical
  have hed (e : E) (he : H t (S.left e)-H t (S.right e)=S.cost e) : dH (S.left e)=dH (S.right e) := by
    have hmax : IsLocalMax (fun s => H s (S.left e)-H s (S.right e)) t := by
      filter_upwards [hp] with s hs
      rw [he]
      exact hs.1.1 e
    exact sub_eq_zero.mp (hmax.hasDerivAt_eq_zero ((hh (S.left e)).sub (hh (S.right e))))
  have hpin (p : V) (hp' : p∈S.pins) : dH p=dB p := by
    have heq : (fun s => H s p)=ᶠ[nhds t](fun s => B s p) := hp.mono (fun s hs => hs.1.2 p hp')
    exact ((hh p).congr_of_eventuallyEq heq.symm).unique (hb p)
  constructor
  · intro x p hp' hxp
    exact (active_values_constant S (H t) dH hed x p hxp).trans (hpin p hp')
  · intro x hground
    let w : V → ℝ := fun y => if (activeGraph S (H t)).Reachable x y then 1 else 0
    have hw : ∀ p∈S.pins,w p=0 := by intro p hp';exact ite_eq_right (hground p hp')
    have hedge (e : E) (he : H t (S.left e)-H t (S.right e)=S.cost e) : w (S.left e)=w (S.right e) := by
      have hr := active_edge_reachable S (H t) e he
      have hi : (activeGraph S (H t)).Reachable x (S.left e) ↔ (activeGraph S (H t)).Reachable x (S.right e) :=
        ⟨fun hx => hx.trans hr,fun hx => hx.trans hr.symm⟩
      simp only [w,hi]
    have heq : (fun s => ∑ y,(H s y-U s y)*w y)=ᶠ[nhds t](fun _ => (0:ℝ)) := by
      filter_upwards [hp,active_eventually_subset S H t (fun x => (hh x).continuousAt)] with s hs ha
      exact tangent_balance S (B s) (U s) (H s) w hs hw (fun e he => hedge e (ha e he))
    have hd : HasDerivAt (fun s => ∑ y,(H s y-U s y)*w y) (∑ y,(dH y-dU y)*w y) t := by
      apply HasDerivAt.fun_sum
      intro y hy
      exact ((hh y).sub (hu y)).mul_const (w y)
    have hzero : (∑ y,(dH y-dU y)*w y)=0 := (hd.congr_of_eventuallyEq heq.symm).unique (hasDerivAt_const t 0)
    have hbal : (∑ y∈activeComponent S (H t) x,(dH y-dU y))=0 := by
      calc
        _ = ∑ y∈activeComponent S (H t) x,(dH y-dU y)*w y := by
          apply Finset.sum_congr rfl
          intro y hy
          simp only [w,ite_eq_left ((mem_activeComponent S (H t) x y).mp hy),mul_one]
        _ = ∑ y,(dH y-dU y)*w y := by
          apply Finset.sum_subset (Finset.subset_univ _)
          intro y hy hn
          have hn' : ¬(activeGraph S (H t)).Reachable x y := by simpa only [mem_activeComponent] using hn
          simp only [w,ite_eq_right hn',mul_zero]
        _ = 0 := hzero
    have hconst : (∑ y∈activeComponent S (H t) x,dH y)=(activeComponent S (H t) x).card*dH x := by
      trans ∑ _y∈activeComponent S (H t) x,dH x
      · apply Finset.sum_congr rfl
        intro y hy
        exact (active_values_constant S (H t) dH hed x y ((mem_activeComponent S (H t) x y).mp hy)).symm
      · simp only [Finset.sum_const,nsmul_eq_mul]
    have hx : x∈activeComponent S (H t) x := (mem_activeComponent S (H t) x x).mpr (.refl x)
    have hcard : (0:ℝ)<(activeComponent S (H t) x).card := Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨x,hx⟩)
    apply (eq_div_iff hcard.ne').mpr
    rw [Finset.sum_sub_distrib,hconst] at hbal
    linarith

end ProjectionComparison

end OAI
