import Mathlib
import OAI.Combinatorics.UniformKServer.PilotConcentration

namespace OAI

namespace UniformKServer.PilotCompact
noncomputable section
variable {X : Type*} [Fintype X] [MetricSpace X]
omit [MetricSpace X] in
theorem sum_trim_le (a : X → ℝ) (ha : ∀ t, 0 ≤ a t) (q : ℝ) (hq : 0 ≤ q) :
    (∑ t, max (a t-q) 0) ≤ max ((∑ t, a t)-q) 0 := by
  classical
  have hall : ∀ S : Finset X, (∑ t ∈ S, max (a t-q) 0) ≤ max ((∑ t ∈ S, a t)-q) 0 := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp [max_eq_right (neg_nonpos.mpr hq)]
    | @insert t S ht ih =>
      rw [Finset.sum_insert ht, Finset.sum_insert ht]
      exact (add_le_add_right ih _).trans (trim_add_le _ _ q (ha t)
        (Finset.sum_nonneg fun i hi => ha i) hq)
  exact hall Finset.univ

omit [MetricSpace X] in
theorem capacity_patch (a b : X → ℝ) (A A' q : ℝ)
    (ha : ∀ t, 0 ≤ a t) (hq : 0 ≤ q) (hcap : A+∑ t, a t ≤ 1)
    (hA' : A' ≤ 1) (hLip : A' ≤ A+q)
    (hmono : ∀ t, b t ≤ a t) (htrim : A < A' → ∀ t, b t ≤ max (a t-q) 0) :
    A'+∑ t, b t ≤ 1 := by
  by_cases hA : A' ≤ A
  · exact (add_le_add hA (Finset.sum_le_sum fun t _ => hmono t)).trans hcap
  · have hb : (∑ t, b t) ≤ max ((∑ t, a t)-q) 0 :=
      (Finset.sum_le_sum fun t _ => htrim (lt_of_not_ge hA) t).trans (sum_trim_le a ha q hq)
    apply le_trans (add_le_add_right hb _)
    by_cases hB : q ≤ ∑ t, a t
    · rw [max_eq_left (sub_nonneg.mpr hB)]
      linarith
    · rw [max_eq_right (by linarith : (∑ t, a t)-q≤0), add_zero]
      exact hA'

omit [MetricSpace X] in
theorem sum_split_pair [DecidableEq X] (f : X → ℝ) (s x : X) (hsx : s ≠ x) :
    (∑ t, f t) = f s+f x+∑ t, if t=s ∨ t=x then 0 else f t := by
  have he : ∀ t, f t = (if t=s then f s else 0)+(if t=x then f x else 0)+
      (if t=s ∨ t=x then 0 else f t) := by
    intro t
    by_cases hs : t=s <;> by_cases hx : t=x <;> simp_all
  calc
    _ = ∑ t, ((if t=s then f s else 0)+(if t=x then f x else 0)+
        (if t=s ∨ t=x then 0 else f t)) := Finset.sum_congr rfl (fun t _ => he t)
    _ = _ := by simp only [Finset.sum_add_distrib]; simp

theorem gate_positive_near (R v z : ℝ) (hR : 0 < R) (hz : z ≤ 1)
    (hp : 0 < max (z-gate R v) 0) : v < 20*R := by
  by_contra h
  rw [gate_one R v hR (le_of_not_gt h), max_eq_right (sub_nonpos.mpr hz)] at hp
  linarith

theorem zero_at_relocation_target (r σ R : ℝ) (_hr : 0 < r) (hR : 256 ≤ R)
    (z : X → ℝ) (hz : feasible r σ R z) (s x : X) (hsx : s ≠ x)
    (hother : ∀ t, t ≠ s → 0 < z t → R/2 < dist t x/r) : z x = 0 := by
  rcases (hz.1 x).eq_or_lt with he | hp
  · exact he.symm
  · have hh := hother x (Ne.symm hsx) hp
    simp only [dist_self, zero_div] at hh
    linarith

omit [Fintype X] in
theorem relocate_at_target [DecidableEq X] (r R : ℝ) (z : X → ℝ) (s x : X) :
    relocate r R z s x x = z s := by simp [relocate]

omit [Fintype X] in
theorem relocate_at_site [DecidableEq X] (r R : ℝ) (z : X → ℝ) (s x : X) (hsx : s ≠ x) :
    relocate r R z s x s = 0 := by simp [relocate, hsx]

omit [Fintype X] in
theorem relocate_nonneg [DecidableEq X] (r R : ℝ) (z : X → ℝ) (hz : ∀ t, 0 ≤ z t)
    (s x t : X) : 0 ≤ relocate r R z s x t := by
  unfold relocate
  split_ifs <;> first | exact hz _ | exact le_max_right _ _ | rfl

omit [Fintype X] in
theorem relocate_other_le [DecidableEq X] (r R : ℝ) (hr : 0 < r) (hR : 0 < R)
    (z : X → ℝ) (hz : ∀ t, 0 ≤ z t) (s x t : X) (htx : t ≠ x) :
    relocate r R z s x t ≤ z t := by
  unfold relocate
  rw [ite_eq_right htx]
  split_ifs
  · exact hz t
  · have hq : 0 ≤ (dist s x/r)/(10*R) := by positivity
    exact max_le (by linarith) (hz t)
  · rfl

theorem relocated_capacity [DecidableEq X] (r σ R : ℝ) (hr : 0 < r) (hR : 256 ≤ R)
    (z : X → ℝ) (hz : feasible r σ R z) (s x : X) (hsx : s ≠ x) (hzx : z x=0)
    (p : X) : (∑ t, max (relocate r R z s x t-gate R (dist t p/r)) 0) ≤ 1 := by
  let q := (dist s x/r)/(10*R)
  let A := max (z s-gate R (dist s p/r)) 0
  let A' := max (z s-gate R (dist x p/r)) 0
  let a : X → ℝ := fun t => if t=s ∨ t=x then 0 else max (z t-gate R (dist t p/r)) 0
  let b : X → ℝ := fun t => if t=s ∨ t=x then 0 else max (relocate r R z s x t-gate R (dist t p/r)) 0
  have hRpos : 0 < R := by linarith
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hnegative : ∀ t : X, max (0-gate R (dist t p/r)) 0 = 0 := by
    intro t
    exact max_eq_right (by linarith [gate_nonneg R (dist t p/r)])
  have hold : (∑ t, max (z t-gate R (dist t p/r)) 0) = A+∑ t, a t := by
    rw [sum_split_pair _ s x hsx, hzx, hnegative]
    simp only [add_zero]
    rfl
  have hnew : (∑ t, max (relocate r R z s x t-gate R (dist t p/r)) 0) = A'+∑ t, b t := by
    rw [sum_split_pair _ s x hsx, relocate_at_site r R z s x hsx, hnegative, relocate_at_target]
    simp only [zero_add]
    rfl
  rw [hnew]
  apply capacity_patch a b A A' q
  · intro t
    dsimp [a]
    split_ifs <;> first | rfl | exact le_max_right _ _
  · exact hq
  · rw [← hold]
    exact hz.2.1 p
  · dsimp [A']
    exact max_le (by linarith [feasible_upper r σ R z hz s, gate_nonneg R (dist x p/r)]) (by norm_num)
  · have hg := gate_lipschitz R (dist s p/r) (dist x p/r) hRpos
    have hdist : |dist s p/r-dist x p/r| ≤ dist s x/r := by
      rw [← sub_div, abs_div, abs_of_pos hr]
      exact div_le_div_of_nonneg_right (abs_dist_sub_le s x p) hr.le
    have hgp : |gate R (dist s p/r)-gate R (dist x p/r)| ≤ q :=
      hg.trans (div_le_div_of_nonneg_right hdist (by positivity))
    have hm := abs_max_sub_max_le_abs (z s-gate R (dist x p/r)) (z s-gate R (dist s p/r)) 0
    have he : (z s-gate R (dist x p/r))-(z s-gate R (dist s p/r)) =
        gate R (dist s p/r)-gate R (dist x p/r) := by ring
    rw [he] at hm
    have hi : A'-A ≤ q := (le_abs_self _).trans (hm.trans hgp)
    linarith
  · intro t
    dsimp [a, b]
    split_ifs with ht
    · rfl
    · exact max_le_max (sub_le_sub_right
        (relocate_other_le r R hr hRpos z hz.1 s x t (fun h => ht (Or.inr h))) _) le_rfl
  · intro hA t
    by_cases hts : t=s ∨ t=x
    · simp [a, b, hts]
    have hts' : t ≠ s := fun h => hts (Or.inl h)
    have htx : t ≠ x := fun h => hts (Or.inr h)
    dsimp [a, b]
    rw [ite_eq_right hts, ite_eq_right hts]
    by_cases hc : dist t x ≤ (50*R)*r
    · simp only [relocate, ite_eq_right htx, ite_eq_right hts', ite_eq_left hc]
      exact le_of_eq (trim_contribution _ _ _ (gate_nonneg _ _) hq)
    · have hAp : 0 < A' := (le_max_right _ _).trans_lt hA
      have hxp : dist x p/r < 20*R :=
        gate_positive_near R _ _ hRpos (feasible_upper r σ R z hz s) hAp
      have hat : max (z t-gate R (dist t p/r)) 0 = 0 := by
        apply le_antisymm _ (le_max_right _ _)
        by_contra hn
        have htp := gate_positive_near R _ _ hRpos (feasible_upper r σ R z hz t) (lt_of_not_ge hn)
        have htri := normalized_triangle r hr t p x
        rw [dist_comm p x] at htri
        have hfar : 50*R < dist t x/r := (lt_div_iff₀ hr).mpr (lt_of_not_ge hc)
        linarith
      simp only [relocate, ite_eq_right htx, ite_eq_right hts', ite_eq_right hc, hat]
      exact le_max_right _ _

theorem relocate_feasible [DecidableEq X] (r σ R : ℝ)
    (hr : 0 < r) (_hσ : 0 < σ) (hσ1 : σ ≤ 1) (hR : 256 ≤ R)
    (z : X → ℝ) (hz : feasible r σ R z) (s x : X)
    (hsx : s ≠ x) (_hs : 0 < z s) (_hnear : dist s x/r < σ/4)
    (hother : ∀ t, t ≠ s → 0 < z t → R/2 < dist t x/r) :
    feasible r σ R (relocate r R z s x) := by
  have hRpos : 0 < R := by linarith
  have hzx := zero_at_relocation_target r σ R hr hR z hz s x hsx hother
  refine ⟨relocate_nonneg r R z hz.1 s x, relocated_capacity r σ R hr hR z hz s x hsx hzx, ?_⟩
  intro u v huv hu hv
  have hne : ∀ t, 0 < relocate r R z s x t → t ≠ s := by
    intro t ht he
    subst t
    rw [relocate_at_site r R z s x hsx] at ht
    linarith
  have hfar : ∀ t, t ≠ x → 0 < relocate r R z s x t → 5*σ*r ≤ dist t x := by
    intro t htx ht
    have htz : 0 < z t := ht.trans_le (relocate_other_le r R hr hRpos z hz.1 s x t htx)
    have hf := hother t (hne t ht) htz
    have hh : 5*σ ≤ dist t x/r := by linarith
    exact (le_div_iff₀ hr).mp hh
  by_cases hux : u=x
  · subst u
    rw [dist_comm]
    exact hfar v huv.symm hv
  by_cases hvx : v=x
  · subst v
    exact hfar u hux hu
  exact hz.2.2 u v huv
    (hu.trans_le (relocate_other_le r R hr hRpos z hz.1 s x u hux))
    (hv.trans_le (relocate_other_le r R hr hRpos z hz.1 s x v hvx))

theorem integrand_affine (r σ R : ℝ) (g z : X → ℝ) (p : X) :
    integrand r σ R g z p = 1+g p+∑ t, z t*coefficient r σ R g t p := by
  unfold integrand coefficient
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [Finset.mul_sum, Finset.mul_sum]
  have ha : (∑ t, z t*(256*(1+g t)*bumpA σ R (dist t p/r))) =
      ∑ t, 256*(z t*(1+g t)*bumpA σ R (dist t p/r)) := by
    apply Finset.sum_congr rfl
    intro t ht
    ring
  have hb : (∑ t, z t*((1+g p)*bumpB σ (dist t p/r))) =
      ∑ t, (1+g p)*(z t*bumpB σ (dist t p/r)) := by
    apply Finset.sum_congr rfl
    intro t ht
    ring
  rw [ha, hb]
  ring

theorem integrand_relocate [DecidableEq X] (r σ R : ℝ) (g z : X → ℝ) (s x p : X)
    (hsx : s ≠ x) (hzx : z x=0) :
    integrand r σ R g (relocate r R z s x) p-integrand r σ R g z p =
      z s*(coefficient r σ R g x p-coefficient r σ R g s p) +
      ∑ t, if t=s ∨ t=x then 0 else
        (relocate r R z s x t-z t)*coefficient r σ R g t p := by
  rw [integrand_affine, integrand_affine]
  have he : (∑ t, relocate r R z s x t*coefficient r σ R g t p) -
      (∑ t, z t*coefficient r σ R g t p) =
      ∑ t, (relocate r R z s x t-z t)*coefficient r σ R g t p := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    ring
  rw [show (1+g p+∑ t, relocate r R z s x t*coefficient r σ R g t p)-
        (1+g p+∑ t, z t*coefficient r σ R g t p) =
        (∑ t, relocate r R z s x t*coefficient r σ R g t p)-
        (∑ t, z t*coefficient r σ R g t p) by ring, he]
  rw [sum_split_pair _ s x hsx, relocate_at_site r R z s x hsx, relocate_at_target, hzx]
  ring

theorem positive_bump_unique (r σ R : ℝ) (hr : 0 < r) (hσ : 0 < σ)
    (z : X → ℝ) (hz : feasible r σ R z) (p u v : X)
    (hu : 0 < z u*bumpB σ (dist u p/r)) (hv : 0 < z v*bumpB σ (dist v p/r)) : u=v := by
  have hup := (mul_pos_iff.mp hu).resolve_right (fun h => (not_lt_of_ge (hz.1 u)) h.1)
  have hvp := (mul_pos_iff.mp hv).resolve_right (fun h => (not_lt_of_ge (hz.1 v)) h.1)
  have hdist : ∀ t, 0 < bumpB σ (dist t p/r) → dist t p/r < 2*σ := by
    intro t ht
    by_contra h
    rw [bumpB_zero σ _ hσ (le_of_not_gt h)] at ht
    linarith
  by_contra hne
  have hsep : 5*σ ≤ dist u v/r := (le_div_iff₀ hr).mpr (hz.2.2 u v hne hup.1 hvp.1)
  have htri := normalized_triangle r hr u p v
  rw [dist_comm p v] at htri
  linarith [hdist u hup.2, hdist v hvp.2]

omit [MetricSpace X] in
theorem sum_le_unique (f : X → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (hbound : ∀ t, f t ≤ q) (huniq : ∀ u v, 0 < f u → 0 < f v → u=v) :
    (∑ t, f t) ≤ q := by
  classical
  by_cases hp : ∃ t, 0 < f t
  · obtain ⟨t, ht⟩ := hp
    have hh : ∀ u, f u ≤ if u=t then q else 0 := by
      intro u
      by_cases he : u=t
      · simpa [he] using hbound t
      · rw [ite_eq_right he]
        by_contra h
        exact he (huniq u t (lt_of_not_ge h) ht)
    have hh' := Finset.sum_le_sum (s := Finset.univ) (fun u _ => hh u)
    simpa using hh'
  · have hh : ∀ t, f t ≤ 0 := fun t => le_of_not_gt (fun h => hp ⟨t,h⟩)
    exact (Finset.sum_nonpos fun t ht => hh t).trans hq

omit [Fintype X] in
theorem relocate_reduction [DecidableEq X] (r R : ℝ) (hr : 0 < r) (hR : 0 < R)
    (z : X → ℝ) (hz : ∀ t, 0 ≤ z t) (s x t : X) (hts : t ≠ s) (htx : t ≠ x) :
    z t-relocate r R z s x t ∈ Set.Icc (0:ℝ) ((dist s x/r)/(10*R)) := by
  have hq : 0 ≤ (dist s x/r)/(10*R) := by positivity
  refine ⟨sub_nonneg.mpr (relocate_other_le r R hr hR z hz s x t htx), ?_⟩
  unfold relocate
  rw [ite_eq_right htx, ite_eq_right hts]
  split_ifs
  · linarith [le_max_left (z t-dist s x/r/(10*R)) 0]
  · simpa using hq

theorem other_reduction_loss [DecidableEq X] (r σ R : ℝ)
    (hr : 0 < r) (hσ : 0 < σ) (hR : 256 ≤ R)
    (g z : X → ℝ) (hg : ∀ p, g p ∈ Set.Icc (0:ℝ) 1) (hz : feasible r σ R z)
    (s x p : X) :
    (∑ t, if t=s ∨ t=x then 0 else
      (relocate r R z s x t-z t)*coefficient r σ R g t p) ≤ 2*((dist s x/r)/(10*R)) := by
  let f : X → ℝ := fun t => if t=s ∨ t=x then 0 else
    (z t-relocate r R z s x t)*bumpB σ (dist t p/r)
  have hRpos : 0 < R := by linarith
  have hq : 0 ≤ (dist s x/r)/(10*R) := by positivity
  have hf : ∀ t, f t ≤ (dist s x/r)/(10*R) := by
    intro t
    dsimp [f]
    split_ifs with ht
    · exact hq
    · have hh := relocate_reduction r R hr hRpos z hz.1 s x t
        (fun h => ht (Or.inl h)) (fun h => ht (Or.inr h))
      exact (mul_le_mul_of_nonneg_left (bumpB_bounds σ _).2 hh.1).trans (by simpa using hh.2)
  have huni : ∀ u v, 0 < f u → 0 < f v → u=v := by
    intro u v hu hv
    have hh : ∀ t, 0 < f t → 0 < z t*bumpB σ (dist t p/r) := by
      intro t ht
      dsimp [f] at ht
      split_ifs at ht with hcase
      · linarith
      · have hc : z t-relocate r R z s x t ≤ z t := by
          linarith [relocate_nonneg r R z hz.1 s x t]
        exact ht.trans_le (mul_le_mul_of_nonneg_right hc (bumpB_bounds σ _).1)
    exact positive_bump_unique r σ R hr hσ z hz p u v (hh u hu) (hh v hv)
  have hsum := sum_le_unique f _ hq hf huni
  have hterm : ∀ t, (if t=s ∨ t=x then 0 else
      (relocate r R z s x t-z t)*coefficient r σ R g t p) ≤ 2*f t := by
    intro t
    dsimp [f]
    split_ifs with ht
    · norm_num
    · have hh := relocate_reduction r R hr hRpos z hz.1 s x t
        (fun h => ht (Or.inl h)) (fun h => ht (Or.inr h))
      have hA := (bumpA_bounds σ R (dist t p/r) hRpos).1
      have hB := (bumpB_bounds σ (dist t p/r)).1
      have hgs := (hg t).1
      have hgp := (hg p).2
      have hac : 0 ≤ (1+g t)*bumpA σ R (dist t p/r) := mul_nonneg (by linarith) hA
      have hbc : 0 ≤ (1-g p)*bumpB σ (dist t p/r) := mul_nonneg (by linarith) hB
      have ha := mul_nonneg hh.1 hac
      have hb := mul_nonneg hh.1 hbc
      unfold coefficient
      nlinarith only [ha,hb]
  calc
    _ ≤ ∑ t, 2*f t := Finset.sum_le_sum fun t _ => hterm t
    _ = 2*∑ t, f t := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by norm_num)

omit [Fintype X] in
theorem normalized_dist_difference (r : ℝ) (hr : 0 < r) (s x p : X) :
    |dist s p/r-dist x p/r| ≤ dist s x/r := by
  rw [← sub_div, abs_div, abs_of_pos hr]
  exact div_le_div_of_nonneg_right (abs_dist_sub_le s x p) hr.le


end
end UniformKServer.PilotCompact

end OAI
