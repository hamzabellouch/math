import OAI.Geometry.NodalSets.Elliptic.UniformJets

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Metric Filter
open scoped ContDiff Topology
noncomputable section

lemma norm_sub_le_on_closedBall {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Coord → E) (y : Coord) (r C : ℝ) (hC : 0 ≤ C)
    (hs : ∀ z, ‖z-y‖ ≤ r → DifferentiableAt ℝ f z)
    (hb : ∀ z, ‖z-y‖ ≤ r → ‖fderiv ℝ f z‖ ≤ C)
    (hr : 0 ≤ r) (x : Coord) (hx : ‖x-y‖ ≤ r) : ‖f x-f y‖ ≤ C*‖x-y‖ := by
  let c : NNReal := ⟨C,hC⟩
  have hl : LipschitzOnWith c f (closedBall y r) := by
    apply (convex_closedBall y r).lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
    · intro z hz; exact hs z (by simpa [mem_closedBall,dist_eq_norm] using hz)
    · intro z hz; exact hb z (by simpa [mem_closedBall,dist_eq_norm] using hz)
  have h := hl.dist_le_mul x
    (by simpa [mem_closedBall,dist_eq_norm] using hx) y (by simpa using hr)
  change dist (f x) (f y) ≤ C*dist x y at h
  simpa only [dist_eq_norm] using h

lemma complex_ne_zero_of_near_one (a : ℂ) (h : ‖a-1‖ ≤ (1/2:ℝ)) :
    (1/2:ℝ) ≤ ‖a‖ ∧ ‖a‖ ≤ 3/2 ∧ a ≠ 0 := by
  have hl := norm_add_le (1-a) a
  have hu := norm_add_le (a-1) (1:ℂ)
  rw [norm_sub_rev] at hl
  norm_num at hl hu
  constructor
  · linarith
  constructor
  · linarith
  · intro hz; simp [hz] at h; norm_num at h

variable {T : Type*} [TopologicalSpace T] [CompactSpace T]
variable {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w S : Coord → ℝ}
variable {y : T → Coord} {d : SourceFrameTriple g S y} {m J K k0 : ℕ}
namespace TripleSourceWaveData
variable (b : TripleSourceWaveData g w S y d m J K k0)

theorem uniform_amplitude_bounds (hg : ContDiff ℝ ∞ g)
    (hpos : ∀ x v, v ≠ 0 → 0 < g x v v) (hy : Continuous y) :
    ∃ delta > 0, ∃ C > 0, ∃ D : ℝ, 1 ≤ D ∧ ∀ t x,
      ‖x-y t.1‖ ≤ delta → x ∈ (b.F t).target ∧
      ‖(b.F t).symm x‖ ≤ D*‖x-y t.1‖ ∧
      ContDiffAt ℝ ∞ ((b.F t).symm : Coord → Coord) x ∧
      ∀ N, 1 ≤ N → ContDiffAt ℝ ∞ (b.amplitude N t) x ∧
        ‖b.amplitude N t x-1‖ ≤ C*‖x-y t.1‖ ∧
        (1/2:ℝ) ≤ ‖b.amplitude N t x‖ ∧ ‖b.amplitude N t x‖ ≤ 3/2 ∧
        b.amplitude N t x ≠ 0 ∧ ‖fderiv ℝ (b.amplitude N t) x‖ ≤ C := by
  obtain ⟨delta,hd,C,hC,D,hD,hb⟩ := b.uniform_spatial_bounds hg hpos hy 1
  let r := min delta (1/(2*C))
  have hr : 0 < r := lt_min hd (by positivity)
  have hh (t : T × Fin 3) (x : Coord) (hx : ‖x-y t.1‖ ≤ r) :=
    hb t x (hx.trans (min_le_left _ _))
  refine ⟨r,hr,C,hC,D,hD,?_⟩
  intro t x hx
  have h := hh t x hx
  have hInv := norm_sub_le_on_closedBall ((b.F t).symm : Coord → Coord) (y t.1) r D
    (by linarith) (fun z hz ↦ (hh t z hz).2.2.2.2.2.1.differentiableAt (by simp))
    (fun z hz ↦ (hh t z hz).2.2.2.2.2.2) hr.le x hx
  rw [b.inverse_center,sub_zero] at hInv
  refine ⟨h.1,hInv,h.2.2.2.2.2.1,?_⟩
  intro N hN
  have hAmpDer (z : Coord) (hz : ‖z-y t.1‖ ≤ r) : ‖fderiv ℝ (b.amplitude N t) z‖ ≤ C := by
    simpa only [norm_iteratedFDeriv_one] using (hh t z hz).2.2.2.2.1 N hN 1 le_rfl
  have hAmp := norm_sub_le_on_closedBall (b.amplitude N t) (y t.1) r C hC.le
    (fun z hz ↦ ((hh t z hz).2.2.1 N).differentiableAt (by simp)) hAmpDer hr.le x hx
  rw [b.amplitude_center] at hAmp
  have hsmall : C*‖x-y t.1‖ ≤ 1/2 := by
    have he := hx.trans (min_le_right delta (1/(2*C)))
    have he' := (le_div_iff₀ (by positivity : 0 < 2*C)).mp he
    nlinarith
  obtain ⟨hl,hu,hn⟩ := complex_ne_zero_of_near_one _ (hAmp.trans hsmall)
  exact ⟨h.2.2.1 N,hAmp,hl,hu,hn,hAmpDer x hx⟩

end TripleSourceWaveData

end
end Yau.Geometry

end OAI
