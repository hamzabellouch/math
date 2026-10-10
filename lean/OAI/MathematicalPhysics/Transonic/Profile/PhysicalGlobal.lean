import OAI.MathematicalPhysics.Transonic.Profile.ClampedUniqueness
import OAI.MathematicalPhysics.Transonic.Profile.FiniteSourceProfile
import OAI.MathematicalPhysics.Transonic.Profile.ExteriorCoordinates

namespace OAI

section
noncomputable section
namespace SepticProfile.PhysicalExterior
open Set Filter
open scoped Topology

lemma solution_unique {q beta a b m : ℝ}
    (hq : 1 < q) (ha : 0 < a) (hm : -1 < m ∧ m < 1)
    (hfirst : 1-q*a+(q-a)*m < 0) (hsecond : 0 < 1+q*a-(a+q)*m)
    {u v : ℝ → ℝ}
    (hu : ∀ y∈Icc a b, HasDerivWithinAt u (field (q^2) beta (y,u y)) (Icc a b) y)
    (hv : ∀ y∈Icc a b, HasDerivWithinAt v (field (q^2) beta (y,v y)) (Icc a b) y)
    (hub : ∀ y∈Icc a b, u y∈Icc (-1) m)
    (hvb : ∀ y∈Icc a b, v y∈Icc (-1) m)
    (hinit : u a=v a) : EqOn u v (Icc a b) := by
  refine RegularContinuation.clamped_unique (f:=field (q^2) beta) hm.1.le
    (field_smooth_on hq ha hm hfirst hsecond) ?_ ?_ hinit
  · intro y hy
    simpa only [RegularContinuation.clamp_eq (hub y hy)] using hu y hy
  · intro y hy
    simpa only [RegularContinuation.clamp_eq (hvb y hy)] using hv y hy

lemma global_continuation {q beta a m v0 : ℝ}
    (hq : 1 < q) (hbeta : 0 < beta) (ha : 0 < a)
    (hm : -1 < m ∧ m < 1)
    (hfirst : 1-q*a+(q-a)*m < 0) (hsecond : 0 < 1+q*a-(a+q)*m)
    (hcrit : 0 < beta*q^2*(1-m^2)*a-3*m*(1-a*m))
    (hstart : -1 < v0 ∧ v0 ≤ m) :
    ∃ v : ℝ → ℝ, v a=v0 ∧
      (∀ y∈Ici a, -1 < v y ∧ v y ≤ m) ∧
      ∀ y∈Ici a, HasDerivWithinAt v (field (q^2) beta (y,v y)) (Ici a) y := by
  classical
  let endpt : ℕ → ℝ := fun n => a+(n:ℝ)+1
  have hab (n:ℕ) : a ≤ endpt n := by dsimp [endpt];have := Nat.cast_nonneg (α:=ℝ) n;linarith
  choose u hu huc hb hd using fun n : ℕ =>
    finite_continuation hq hbeta ha (hab n) hm hfirst hsecond hcrit hstart
  have hcompat (n k : ℕ) {y:ℝ} (hy:Icc a (min (endpt n) (endpt k)) y) : u n y=u k y := by
    apply solution_unique hq ha hm hfirst hsecond
      (fun t ht => (hd n t ⟨ht.1,ht.2.trans (min_le_left _ _)⟩).mono
        (Icc_subset_Icc_right (min_le_left _ _)))
      (fun t ht => (hd k t ⟨ht.1,ht.2.trans (min_le_right _ _)⟩).mono
        (Icc_subset_Icc_right (min_le_right _ _)))
      (fun t ht => ⟨(hb n t ⟨ht.1,ht.2.trans (min_le_left _ _)⟩).1.le,
        (hb n t ⟨ht.1,ht.2.trans (min_le_left _ _)⟩).2⟩)
      (fun t ht => ⟨(hb k t ⟨ht.1,ht.2.trans (min_le_right _ _)⟩).1.le,
        (hb k t ⟨ht.1,ht.2.trans (min_le_right _ _)⟩).2⟩)
      ((hu n).trans (hu k).symm) hy
  have hex (y:ℝ) : ∃ n:ℕ, y < endpt n := by
    obtain ⟨n,hn⟩ := exists_nat_gt (y-a)
    exact ⟨n,by dsimp [endpt];linarith⟩
  let idx : ℝ → ℕ := fun y => Classical.choose (hex y)
  have hidx (y:ℝ) : y < endpt (idx y) := Classical.choose_spec (hex y)
  let v : ℝ → ℝ := fun y => u (idx y) y
  have heq (n:ℕ) {y:ℝ} (hy:y∈Icc a (endpt n)) : v y=u n y :=
    hcompat (idx y) n ⟨hy.1,le_min (hidx y).le hy.2⟩
  refine ⟨v,?_,?_,?_⟩
  · rw [heq 0 ⟨le_rfl,hab 0⟩,hu]
  · intro y hy
    exact hb (idx y) y ⟨hy,(hidx y).le⟩
  · intro y hy
    have hevent : v =ᶠ[𝓝[Ici a] y] u (idx y) := by
      filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (hidx y))] with t ht ht1
      exact heq (idx y) ⟨ht,ht1.le⟩
    have hder' : HasDerivWithinAt (u (idx y)) (field (q^2) beta (y,u (idx y) y)) (Ici a) y := by
      apply (hd (idx y) y ⟨hy,(hidx y).le⟩).mono_of_mem_nhdsWithin
      filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (hidx y))] with t ht ht1
      exact ⟨ht,ht1.le⟩
    convert hder'.congr_of_eventuallyEq hevent (heq (idx y) ⟨hy,(hidx y).le⟩) using 1

end SepticProfile.PhysicalExterior

end
end

end OAI
