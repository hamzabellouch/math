import OAI.MeasureTheory.Falconer.Estimates.ScalarDilationBound

namespace OAI

/-! A separated family of scalar parameters cannot have many nearly
vanishing affine values. This controls projection-collision fibers. -/
namespace Falconer

theorem scalar_affine_fiber_diameter {δ u v c d : ℝ}
    (hc : |u+c*v| ≤ δ) (hd : |u+d*v| ≤ δ) : |c-d| * |v| ≤ 2*δ := by
  have he : (c-d)*v = (u+c*v)-(u+d*v) := by ring
  rw [← abs_mul,he]
  have hh := abs_add_le (u+c*v) (-(u+d*v))
  rw [abs_neg] at hh
  have hs : |(u+c*v)-(u+d*v)| ≤ |u+c*v|+|u+d*v| := by
    simpa only [sub_eq_add_neg] using hh
  linarith

theorem scalar_affine_fiber_card {η r δ u v : ℝ} (hη : 0 < η) (hr : 0 < r)
    (hv : r ≤ |v|) (A : Finset ℝ)
    (hsep : ∀ c ∈ A, ∀ d ∈ A, c ≠ d → η ≤ |c-d|)
    (hval : ∀ c ∈ A, |u+c*v| ≤ δ) (k : ℕ) (hscale : 2*δ ≤ (k : ℝ)*η*r) :
    A.card ≤ 2*k+3 := by
  classical
  by_cases hA : A.Nonempty
  · obtain ⟨c,hc⟩ := hA
    have hcover : ∀ d ∈ A, ∃ e ∈ ({c} : Finset ℝ), |d-e| ≤ (k : ℝ)*η := by
      intro d hd
      refine ⟨c,Finset.mem_singleton_self _,?_⟩
      have hbound := scalar_affine_fiber_diameter (hval d hd) (hval c hc)
      have hmul : |d-c| * r ≤ ((k : ℝ)*η)*r :=
        (mul_le_mul_of_nonneg_left hv (abs_nonneg _)).trans (hbound.trans hscale)
      exact (mul_le_mul_iff_left₀ hr).1 hmul
    have hn := scalarCells_near_card_nat hη A {c} k hcover
    have hAc : (scalarCells η A).card = A.card :=
      Finset.card_image_of_injOn (scalarCells_injective hη hsep)
    rw [hAc] at hn
    simpa only [scalarCells,Finset.image_singleton,Finset.card_singleton,Nat.mul_one] using hn
  · have he : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    simp [he]

theorem scalar_projection_collision_parameter_card {δ η r : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hr : 0 < r) (p q : ℝ × ℝ)
    (hpq : r ≤ |p.2-q.2|) (A : Finset ℝ)
    (hsep : ∀ c ∈ A, ∀ d ∈ A, c ≠ d → η ≤ |c-d|)
    (k : ℕ) (hscale : 2*δ ≤ (k : ℝ)*η*r) :
    (A.filter fun c => ⌊(p.1+c*p.2)/δ⌋ = ⌊(q.1+c*q.2)/δ⌋).card ≤ 2*k+3 := by
  classical
  apply scalar_affine_fiber_card hη hr hpq
  · intro c hc d hd hne
    exact hsep c (Finset.mem_filter.mp hc).1 d (Finset.mem_filter.mp hd).1 hne
  · intro c hc
    have hh := (same_scalar_cell_dist_lt hδ (Finset.mem_filter.mp hc).2).le
    have he : (p.1-q.1)+c*(p.2-q.2) = (p.1+c*p.2)-(q.1+c*q.2) := by ring
    rwa [he]
  · exact hscale

theorem scalar_projection_collision_parameter_bound {δ η r : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hr : 0 < r) (p q : ℝ × ℝ)
    (hpq : r ≤ |p.2-q.2|) (A : Finset ℝ)
    (hsep : ∀ c ∈ A, ∀ d ∈ A, c ≠ d → η ≤ |c-d|) :
    ((A.filter fun c => ⌊(p.1+c*p.2)/δ⌋ = ⌊(q.1+c*q.2)/δ⌋).card : ℝ) ≤
      5+4*δ/(η*r) := by
  let t : ℝ := 2*δ/(η*r)
  let k := ⌈t⌉₊
  have ht : 0 ≤ t := div_nonneg (by positivity) (mul_pos hη hr).le
  have hscale : 2*δ ≤ (k : ℝ)*η*r := by
    have hh := (div_le_iff₀ (mul_pos hη hr)).1 (Nat.le_ceil t)
    simpa only [mul_assoc] using hh
  have hn := scalar_projection_collision_parameter_card hδ hη hr p q hpq A hsep k hscale
  have hnR : ((A.filter fun c => ⌊(p.1+c*p.2)/δ⌋ = ⌊(q.1+c*q.2)/δ⌋).card : ℝ) ≤
      2*(k : ℝ)+3 := by exact_mod_cast hn
  have hk : (k : ℝ) < t+1 := Nat.ceil_lt_add_one ht
  have he : 2*t = 4*δ/(η*r) := by dsimp [t]; ring
  linarith

end Falconer

end OAI
