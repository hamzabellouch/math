import OAI.MeasureTheory.Falconer.Radial.HeavyPlateCells

namespace OAI

/-! # Passing a finite plate cover to the actual dyadic cell exclusions -/

namespace Falconer
open Set MeasureTheory Metric
open scoped ENNReal
variable {d : ℕ}

theorem affine_slab_point_transport {w x y : Space d} {a r D : ℝ}
    (hw : ‖w‖ = 1) (hy : |inner ℝ w y-a| ≤ r) (hxy : dist x y ≤ D) :
    |inner ℝ w x-a| ≤ r+D := by
  have he : inner ℝ w x-a = inner ℝ w (x-y)+(inner ℝ w y-a) := by
    rw [inner_sub_right]; ring
  rw [he]
  apply (abs_add_le _ _).trans
  have hi : |inner ℝ w (x-y)| ≤ D := by
    have hn := abs_real_inner_le_norm w (x-y)
    rw [hw,one_mul,← dist_eq_norm] at hn
    exact hn.trans hxy
  linarith only [hi,hy]

theorem heavyPlateCellPairs_finite_cover (ρ : Measure (Space d)) (Q : DyadicCube d)
    (j : ℕ) (S : Finset (Space d × ℝ)) {r m R D : ℝ}
    (hunit : ∀ p ∈ S, ‖p.1‖ = 1)
    (hdiam : ∀ p ∈ cubePaths d j, ∀ x ∈ (Q.descendant p).carrier,
      ∀ y ∈ (Q.descendant p).carrier, dist x y ≤ D)
    (hcover : ∀ w : Space d, ‖w‖ = 1 → ∀ a : ℝ,
      ENNReal.ofReal m ≤ ρ {x | |inner ℝ w x-a| ≤ r} →
      ∃ p ∈ S, ∀ x ∈ Q.carrier, |inner ℝ w x-a| ≤ r → |inner ℝ p.1 x-p.2| ≤ R) :
    heavyPlateCellPairs ρ Q j r m ⊆
      ⋃ p ∈ S, {x | |inner ℝ p.1 x-p.2| ≤ R+D} ×ˢ
        {y | |inner ℝ p.1 y-p.2| ≤ R+D} := by
  rintro ⟨x,y⟩ h
  obtain ⟨P,hP,T,hT,⟨w,hw,a,hm,⟨x',hx',hxw⟩,⟨y',hy',hyw⟩⟩,hx,hy⟩ :=
    (mem_heavyPlateCellPairs_iff ρ Q j r m x y).mp h
  obtain ⟨p,hp,hpc⟩ := hcover w hw a hm
  refine mem_iUnion₂.mpr ⟨p,hp,?_,?_⟩
  · exact affine_slab_point_transport (hunit p hp)
      (hpc x' (Q.descendant_subset P hx') hxw) (hdiam P hP x hx x' hx')
  · exact affine_slab_point_transport (hunit p hp)
      (hpc y' (Q.descendant_subset T hy') hyw) (hdiam T hT y hy y' hy')

end Falconer

end OAI
