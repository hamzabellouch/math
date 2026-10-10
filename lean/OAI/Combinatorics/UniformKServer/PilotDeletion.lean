import Mathlib
import OAI.Combinatorics.UniformKServer.PilotCompact

namespace OAI

namespace UniformKServer.PilotCompact
noncomputable section
variable {X : Type*} [Fintype X] [MetricSpace X]
theorem objective_erase [DecidableEq X] (r σ R : ℝ) (μ g z : X → ℝ) (s : X) :
    objective r σ R μ g z - objective r σ R μ g (Function.update z s 0) =
      r*z s*∑ p, μ p*coefficient r σ R g s p := by
  unfold objective
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  simp_rw [← mul_sub, integrand_erase]
  have he : (∑ p, μ p*(z s*coefficient r σ R g s p)) =
      z s*∑ p, μ p*coefficient r σ R g s p := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  rw [he]
  ring

omit [Fintype X] in
theorem normalized_triangle (r : ℝ) (hr : 0 < r) (s x p : X) :
    dist s p/r ≤ dist s x/r + dist x p/r := by
  rw [← add_div]
  exact div_le_div_of_nonneg_right (dist_triangle s x p) hr.le

omit [Fintype X] in
theorem bumpA_inner_lower (r σ R γ : ℝ) (hr : 0 < r) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hR : 256 ≤ R) (hγσ : γ ≤ σ/64)
    (x s p : X) (hnear : σ/4 ≤ dist s x/r) (hfar : dist s x/r ≤ R/2)
    (hp : dist x p ≤ γ*r) : (225:ℝ)/4096 ≤ bumpA σ R (dist s p/r) := by
  have hv : dist x p/r ≤ γ := (div_le_iff₀ hr).mpr hp
  have ht := normalized_triangle r hr s x p
  have ht' := normalized_triangle r hr s p x
  rw [dist_comm p x] at ht'
  have hu : dist s p/r ≤ R := by linarith
  have hl : (15:ℝ)/64*σ ≤ dist s p/r := by linarith
  have hnon : 0 ≤ dist s p/r := div_nonneg dist_nonneg hr.le
  have hsq : (225:ℝ)/4096 ≤ (dist s p/r)^2/σ^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hσ)).mpr
    nlinarith [sq_nonneg (dist s p/r-(15:ℝ)/64*σ)]
  unfold bumpA
  rw [ite_eq_left hu]
  exact le_min hsq (by norm_num)

omit [Fintype X] in
theorem bumpB_outer_bound (r σ R : ℝ) (hr : 0 < r) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hR : 256 ≤ R) (x s p : X) (hfar : dist s x/r ≤ R/2) :
    bumpB σ (dist s p/r) ≤ if dist x p ≤ (100*R)*r then 1 else 0 := by
  split_ifs with hp
  · exact (bumpB_bounds _ _).2
  · have ht := normalized_triangle r hr x s p
    rw [dist_comm x s] at ht
    have hv : 100*R < dist x p/r := (lt_div_iff₀ hr).mpr (lt_of_not_ge hp)
    have hu : 2*σ ≤ dist s p/r := by linarith
    rw [bumpB_zero σ _ hσ hu]

omit [Fintype X] in
theorem coefficient_lower (r σ R γ : ℝ) (hr : 0 < r) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hR : 256 ≤ R) (hγσ : γ ≤ σ/64)
    (g : X → ℝ) (hg : ∀ p, g p ∈ Set.Icc (0:ℝ) 1)
    (x s p : X) (hnear : σ/4 ≤ dist s x/r) (hfar : dist s x/r ≤ R/2) :
    (225:ℝ)/16*(if dist x p ≤ γ*r then 1 else 0) -
        2*(if dist x p ≤ (100*R)*r then 1 else 0) ≤ coefficient r σ R g s p := by
  have ha := bumpA_bounds σ R (dist s p/r) (show 0<R by linarith)
  have hb := bumpB_bounds σ (dist s p/r)
  have hlo : (225:ℝ)/4096*(if dist x p ≤ γ*r then 1 else 0) ≤ bumpA σ R (dist s p/r) := by
    split_ifs with hp
    · simpa using bumpA_inner_lower r σ R γ hr hσ hσ1 hR hγσ x s p hnear hfar hp
    · simpa using ha.1
  have hhi := bumpB_outer_bound r σ R hr hσ hσ1 hR x s p hfar
  have hterm : 256*bumpA σ R (dist s p/r)-2*bumpB σ (dist s p/r) ≤
      coefficient r σ R g s p := by
    unfold coefficient
    nlinarith [mul_nonneg (hg s).1 ha.1,
      mul_nonneg (show 0 ≤ 1-g p by linarith [(hg p).2]) hb.1]
  linarith

theorem middle_site_zero [DecidableEq X] (r σ R γ δ : ℝ)
    (hr : 0 < r) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hR : 256 ≤ R)
    (_hγ : 0 < γ) (hγσ : γ ≤ σ/64) (hδ : 0 < δ) (hδbound : δ ≤ 1/4112)
    (μ g z : X → ℝ) (hμ : ∀ p, 0 ≤ μ p) (hg : ∀ p, g p ∈ Set.Icc (0:ℝ) 1)
    (x : X) (hM : 0 < ballMass r γ μ x)
    (hconc : ballMass r (100*R) μ x ≤ (1+δ)*ballMass r γ μ x)
    (hz : feasible r σ R z)
    (hmin : objective r σ R μ g z = value r σ R μ g)
    (s : X) (hnear : σ/4 ≤ dist s x/r) (hfar : dist s x/r ≤ R/2) :
    z s = 0 := by
  have hc : (225:ℝ)/16 * ballMass r γ μ x - 2*ballMass r (100*R) μ x ≤
      ∑ p, μ p*coefficient r σ R g s p := by
    have he : (225:ℝ)/16 * ballMass r γ μ x - 2*ballMass r (100*R) μ x =
        ∑ p, μ p*((225:ℝ)/16*(if dist x p ≤ γ*r then 1 else 0) -
          2*(if dist x p ≤ (100*R)*r then 1 else 0)) := by
      unfold ballMass
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      split_ifs <;> ring
    rw [he]
    exact Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_left
      (coefficient_lower r σ R γ hr hσ hσ1 hR hγσ g hg x s p hnear hfar) (hμ p)
  have hδle : δ ≤ 1 := by linarith
  have hout : ballMass r (100*R) μ x ≤ 2*ballMass r γ μ x := by
    exact hconc.trans (by nlinarith [mul_nonneg (show 0≤1-δ by linarith) hM.le])
  have hpos : 0 < ∑ p, μ p*coefficient r σ R g s p := by linarith
  have hdel := value_le r σ R μ g (Function.update z s 0) (erase_feasible r σ R z hz s)
  rw [← hmin] at hdel
  have he := objective_erase r σ R μ g z s
  rcases (hz.1 s).eq_or_lt with hzero | hposz
  · exact hzero.symm
  · have hprod := mul_pos (mul_pos hr hposz) hpos
    linarith

def innerMoment (r γ : ℝ) (μ : X → ℝ) (x : X) : ℝ :=
  ∑ p, if dist x p ≤ γ*r then μ p*(dist x p/r) else 0

def insertUnit [DecidableEq X] (r R : ℝ) (z : X → ℝ) (x s : X) : ℝ :=
  if s=x then 1 else if dist s x ≤ (50*R)*r then 0 else z s


theorem gate_one (R v : ℝ) (hR : 0 < R) (hv : 20*R ≤ v) : gate R v = 1 := by
  have hd : 2 ≤ v/(10*R) := (le_div_iff₀ (by positivity : 0<10*R)).mpr (by linarith)
  unfold gate
  rw [min_eq_left (by linarith), max_eq_right (by norm_num)]

omit [Fintype X] in
theorem insertUnit_at [DecidableEq X] (r R : ℝ) (z : X → ℝ) (x : X) :
    insertUnit r R z x x = 1 := by simp [insertUnit]

omit [Fintype X] in
theorem insertUnit_nonneg [DecidableEq X] (r R : ℝ) (z : X → ℝ)
    (hz : ∀ s, 0 ≤ z s) (x s : X) : 0 ≤ insertUnit r R z x s := by
  unfold insertUnit
  split_ifs <;> first | positivity | exact hz s

omit [Fintype X] in
theorem insertUnit_le [DecidableEq X] (r R : ℝ) (z : X → ℝ)
    (hz : ∀ s, 0 ≤ z s) (x s : X) (hne : s ≠ x) : insertUnit r R z x s ≤ z s := by
  unfold insertUnit
  rw [ite_eq_right hne]
  split_ifs <;> first | exact hz s | rfl

omit [Fintype X] in
theorem insertUnit_positive [DecidableEq X] (r R : ℝ) (z : X → ℝ)
    (x s : X) (hne : s ≠ x) (hp : 0 < insertUnit r R z x s) :
    (50*R)*r < dist s x ∧ 0 < z s := by
  unfold insertUnit at hp
  rw [ite_eq_right hne] at hp
  split_ifs at hp with h
  · linarith
  · exact ⟨lt_of_not_ge h, hp⟩

theorem insertUnit_feasible [DecidableEq X] (r σ R : ℝ)
    (hr : 0 < r) (_hσ : 0 < σ) (hσ1 : σ ≤ 1) (hR : 256 ≤ R)
    (z : X → ℝ) (hz : feasible r σ R z) (x : X) :
    feasible r σ R (insertUnit r R z x) := by
  refine ⟨insertUnit_nonneg r R z hz.1 x, ?_, ?_⟩
  · intro p
    by_cases hfar : 20*R ≤ dist x p/r
    · have hg := gate_one R (dist x p/r) (by linarith) hfar
      apply le_trans (Finset.sum_le_sum ?_) (hz.2.1 p)
      intro s hs
      by_cases heq : s=x
      · subst s
        rw [insertUnit_at, hg]
        norm_num
      · exact max_le_max (sub_le_sub_right (insertUnit_le r R z hz.1 x s heq) _) le_rfl
    · have hother : ∀ s : X, s ≠ x →
          max (insertUnit r R z x s-gate R (dist s p/r)) 0 = 0 := by
        intro s hne
        by_cases hcut : dist s x ≤ (50*R)*r
        · simp only [insertUnit, ite_eq_right hne, ite_eq_left hcut]
          exact max_eq_right (by linarith [gate_nonneg R (dist s p/r)])
        · have hsx : 50*R < dist s x/r := (lt_div_iff₀ hr).mpr (lt_of_not_ge hcut)
          have ht := normalized_triangle r hr s p x
          rw [dist_comm p x] at ht
          have hsp : 20*R ≤ dist s p/r := by linarith
          rw [gate_one R _ (by linarith) hsp]
          apply max_eq_right
          exact sub_nonpos.mpr ((insertUnit_le r R z hz.1 x s hne).trans (feasible_upper r σ R z hz s))
      have he : (∑ s, max (insertUnit r R z x s-gate R (dist s p/r)) 0) =
          max (1-gate R (dist x p/r)) 0 := by
        rw [Finset.sum_eq_single x]
        · rw [insertUnit_at]
        · intro s hs hne
          exact hother s hne
        · simp
      rw [he]
      exact max_le (by linarith [gate_nonneg R (dist x p/r)]) (by norm_num)
  · intro s s' hne hs hs'
    have hsep : 5*σ*r ≤ 50*R*r := by nlinarith
    by_cases hx : s=x
    · subst s
      have hp := insertUnit_positive r R z x s' (Ne.symm hne) hs'
      rw [dist_comm]
      exact hsep.trans hp.1.le
    by_cases hx' : s'=x
    · subst s'
      exact hsep.trans (insertUnit_positive r R z x s hx hs).1.le
    exact hz.2.2 s s' hne (insertUnit_positive r R z x s hx hs).2
      (insertUnit_positive r R z x s' hx' hs').2

theorem bumpB_one (σ v : ℝ) (hσ : 0 < σ) (hv : v ≤ σ) : bumpB σ v = 1 := by
  have hd : v/σ ≤ 1 := (div_le_iff₀ hσ).mpr (by simpa using hv)
  unfold bumpB
  rw [min_eq_left (by linarith), max_eq_right (by norm_num)]

def nearWeight (r σ : ℝ) (z : X → ℝ) (x : X) : ℝ :=
  ∑ s, if dist s x/r < σ/4 then z s else 0

theorem inner_bump_sum (r σ R γ : ℝ) (hr : 0 < r) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hR : 256 ≤ R) (hγσ : γ ≤ σ/64)
    (z : X → ℝ) (x p : X) (hp : dist x p ≤ γ*r)
    (hmid : ∀ s, σ/4 ≤ dist s x/r → dist s x/r ≤ R/2 → z s = 0) :
    (∑ s, z s*bumpB σ (dist s p/r)) = nearWeight r σ z x := by
  unfold nearWeight
  apply Finset.sum_congr rfl
  intro s hs
  have hv : dist x p/r ≤ γ := (div_le_iff₀ hr).mpr hp
  split_ifs with hn
  · have ht := normalized_triangle r hr s x p
    rw [bumpB_one σ _ hσ (by linarith), mul_one]
  · by_cases hf : dist s x/r ≤ R/2
    · rw [hmid s (le_of_not_gt hn) hf, zero_mul]
    · have ht := normalized_triangle r hr s p x
      rw [dist_comm p x] at ht
      rw [bumpB_zero σ _ hσ (by linarith), mul_zero]

theorem nearWeight_bounds (r σ R γ : ℝ) (hr : 0 < r) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hR : 256 ≤ R) (hγ : 0 < γ) (hγσ : γ ≤ σ/64)
    (z : X → ℝ) (hz : feasible r σ R z) (x : X)
    (hmid : ∀ s, σ/4 ≤ dist s x/r → dist s x/r ≤ R/2 → z s = 0) :
    nearWeight r σ z x ∈ Set.Icc (0:ℝ) 1 := by
  have he := inner_bump_sum r σ R γ hr hσ hσ1 hR hγσ z x x
    (by simp; positivity) hmid
  rw [← he]
  exact weighted_bumpB_sum r σ R hσ hσ1 hR z hz x

theorem old_inner_lower (r σ R γ : ℝ) (hr : 0 < r) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hR : 256 ≤ R) (hγ : 0 < γ) (hγσ : γ ≤ σ/64)
    (g z : X → ℝ) (hg : ∀ p, g p ∈ Set.Icc (0:ℝ) 1) (hz : feasible r σ R z)
    (x p : X) (hp : dist x p ≤ γ*r)
    (hmid : ∀ s, σ/4 ≤ dist s x/r → dist s x/r ≤ R/2 → z s = 0) :
    1-nearWeight r σ z x ≤ integrand r σ R g z p := by
  have hB := nearWeight_bounds r σ R γ hr hσ hσ1 hR hγ hγσ z hz x hmid
  have hA := surcharge_sum r σ R (show 0<R by linarith) g z hg hz p
  unfold integrand
  rw [inner_bump_sum r σ R γ hr hσ hσ1 hR hγσ z x p hp hmid]
  nlinarith [mul_nonneg (hg p).1 (show 0≤1-nearWeight r σ z x by linarith [hB.2]), hA.1]

theorem new_inner_upper [DecidableEq X] (r σ R γ : ℝ) (hr : 0 < r) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hR : 256 ≤ R) (hγσ : γ ≤ σ/64)
    (g z : X → ℝ) (hg : ∀ p, g p ∈ Set.Icc (0:ℝ) 1)
    (x p : X) (hp : dist x p ≤ γ*r) :
    integrand r σ R g (insertUnit r R z x) p ≤ 512/σ^2*(dist x p/r)^2 := by
  have hv : dist x p/r ≤ γ := (div_le_iff₀ hr).mpr hp
  have hzero : ∀ s : X, s ≠ x →
      insertUnit r R z x s*bumpB σ (dist s p/r) = 0 ∧
      insertUnit r R z x s*(1+g s)*bumpA σ R (dist s p/r) = 0 := by
    intro s hne
    by_cases hc : dist s x ≤ (50*R)*r
    · simp [insertUnit, hne, hc]
    · have hsx : 50*R < dist s x/r := (lt_div_iff₀ hr).mpr (lt_of_not_ge hc)
      have ht := normalized_triangle r hr s p x
      rw [dist_comm p x] at ht
      rw [bumpB_zero σ _ hσ (by linarith), bumpA_zero σ R _ (by linarith) (by linarith)]
      simp
  have hB : (∑ s, insertUnit r R z x s*bumpB σ (dist s p/r)) = 1 := by
    rw [Finset.sum_eq_single x]
    · rw [insertUnit_at, one_mul, bumpB_one σ _ hσ (by linarith)]
    · intro s hs hne
      exact (hzero s hne).1
    · simp
  have hA : (∑ s, insertUnit r R z x s*(1+g s)*bumpA σ R (dist s p/r)) =
      (1+g x)*bumpA σ R (dist x p/r) := by
    rw [Finset.sum_eq_single x]
    · rw [insertUnit_at, one_mul]
    · intro s hs hne
      exact (hzero s hne).2
    · simp
  have ha : bumpA σ R (dist x p/r) ≤ (dist x p/r)^2/σ^2 := by
    unfold bumpA
    rw [ite_eq_left (by linarith : dist x p/r ≤ R)]
    exact min_le_left _ _
  have haa := (bumpA_bounds σ R (dist x p/r) (show 0<R by linarith)).1
  unfold integrand
  rw [hB, hA]
  have hh := mul_le_mul_of_nonneg_right (show 1+g x ≤ 2 by linarith [(hg x).2]) haa
  have he : 512/σ^2*(dist x p/r)^2 = 512*((dist x p/r)^2/σ^2) := by ring
  rw [he]
  nlinarith

theorem unchanged_outside [DecidableEq X] (r σ R : ℝ) (hr : 0 < r) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hR : 256 ≤ R) (g z : X → ℝ) (x p : X)
    (hp : (100*R)*r < dist x p) :
    integrand r σ R g (insertUnit r R z x) p = integrand r σ R g z p := by
  have hv : 100*R < dist x p/r := (lt_div_iff₀ hr).mpr hp
  have hterm : ∀ s : X,
      insertUnit r R z x s*bumpB σ (dist s p/r) = z s*bumpB σ (dist s p/r) ∧
      insertUnit r R z x s*(1+g s)*bumpA σ R (dist s p/r) =
        z s*(1+g s)*bumpA σ R (dist s p/r) := by
    intro s
    by_cases hc : dist s x ≤ (50*R)*r
    · have hsx : dist s x/r ≤ 50*R := (div_le_iff₀ hr).mpr hc
      have ht := normalized_triangle r hr x s p
      rw [dist_comm x s] at ht
      rw [bumpB_zero σ _ hσ (by linarith), bumpA_zero σ R _ (by linarith) (by linarith)]
      simp
    · have hne : s ≠ x := by
        intro he
        subst s
        simp only [dist_self, not_le] at hc
        have : 0 ≤ 50*R*r := by positivity
        linarith
      simp [insertUnit, hne, hc]
  have hB := Finset.sum_congr rfl (fun s (_ : s ∈ Finset.univ) => (hterm s).1)
  have hA := Finset.sum_congr rfl (fun s (_ : s ∈ Finset.univ) => (hterm s).2)
  unfold integrand
  rw [hB, hA]

theorem innerMoment_bounds (r γ : ℝ) (hr : 0 < r) (μ : X → ℝ) (hμ : ∀ p, 0 ≤ μ p) (x : X) :
    0 ≤ innerMoment r γ μ x ∧ innerMoment r γ μ x ≤ γ*ballMass r γ μ x := by
  constructor
  · apply Finset.sum_nonneg
    intro p hp
    split_ifs
    · exact mul_nonneg (hμ p) (div_nonneg dist_nonneg hr.le)
    · rfl
  · unfold innerMoment ballMass
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    split_ifs with hd
    · have hv := (div_le_iff₀ hr).mpr hd
      nlinarith [mul_le_mul_of_nonneg_left hv (hμ p)]
    · simp


end
end UniformKServer.PilotCompact

end OAI
