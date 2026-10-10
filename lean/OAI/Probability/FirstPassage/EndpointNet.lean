import OAI.Probability.FirstPassage.AttachmentGeometry

namespace OAI

namespace PlanarFPP
open Set Filter Metric
open scoped Topology

theorem finite_ball_net (D γ : ℝ) (hγ : 0 < γ) :
    ∃ S : Finset {v : Plane // ‖v‖ ≤ D},
      ∀ v : Plane, ‖v‖ ≤ D → ∃ u ∈ S, ‖v-u.val‖ < γ := by
  classical
  have hc : closedBall (0 : Plane) D ⊆
      ⋃ u : {v : Plane // ‖v‖ ≤ D}, ball u.val γ := by
    intro v hv
    have hv' : ‖v‖ ≤ D := by simpa using hv
    exact mem_iUnion.mpr ⟨⟨v,hv'⟩,by simpa using hγ⟩
  obtain ⟨S,hS⟩ := (isCompact_closedBall (0 : Plane) D).elim_finite_subcover
    (fun u : {v : Plane // ‖v‖ ≤ D} => ball u.val γ) (fun _ => isOpen_ball) hc
  refine ⟨S,?_⟩
  intro v hv
  obtain ⟨u,hu,hvu⟩ := mem_iUnion₂.mp (hS (by simpa using hv))
  exact ⟨u,hu,hvu⟩

theorem lattice_mem_box_of_norm (p : Vertex) (n : ℕ)
    (hp : ‖latticeEmbed p‖ ≤ (n : ℝ)) : p ∈ latticeBox n := by
  have h0 := (plane_coordinate_le_norm (latticeEmbed p) 0).trans hp
  have h1 := (plane_coordinate_le_norm (latticeEmbed p) 1).trans hp
  simp only [latticeEmbed,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at h0 h1
  have hh0 : -(n : ℤ) ≤ p.1 ∧ p.1 ≤ n := by exact_mod_cast abs_le.mp h0
  have hh1 : -(n : ℤ) ≤ p.2 ∧ p.2 ≤ n := by exact_mod_cast abs_le.mp h1
  simpa only [latticeBox,Finset.mem_product,Finset.mem_Icc] using And.intro hh0 hh1

theorem scaled_net_norm (D : ℝ) (u : {v : Plane // ‖v‖ ≤ D}) (n : ℕ) :
    ‖latticeEmbed (latticeFloor ((n : ℝ) • u.val))‖ ≤ D*n+2 := by
  have ht := norm_add_le
    (latticeEmbed (latticeFloor ((n : ℝ) • u.val))-(n : ℝ) • u.val)
    ((n : ℝ) • u.val)
  rw [sub_add_cancel,norm_smul,Real.norm_natCast] at ht
  have hu := mul_le_mul_of_nonneg_left u.property (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  linarith [latticeFloor_error ((n : ℝ) • u.val)]

theorem scaled_net_approximates (D γ : ℝ)
    (S : Finset {v : Plane // ‖v‖ ≤ D})
    (hS : ∀ v : Plane, ‖v‖ ≤ D → ∃ u ∈ S, ‖v-u.val‖ < γ)
    (n : ℕ) (hn : 0 < n) (p : Vertex) (hp : ‖latticeEmbed p‖ ≤ D*n) :
    ∃ u ∈ S, ‖latticeEmbed (latticeFloor ((n : ℝ) • u.val)-p)‖ ≤ γ*n+2 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  let v := (1/(n : ℝ)) • latticeEmbed p
  have hv : ‖v‖ ≤ D := by
    dsimp [v]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr hn')]
    rw [one_div_mul_eq_div]
    exact (div_le_iff₀ hn').mpr (by nlinarith)
  obtain ⟨u,hu,hvu⟩ := hS v hv
  refine ⟨u,hu,?_⟩
  have he : (n : ℝ) • v = latticeEmbed p := by
    dsimp [v]; rw [smul_smul]; simp [hn'.ne']
  have hd : ‖(n : ℝ) • u.val-latticeEmbed p‖ ≤ γ*n := by
    rw [← he,← smul_sub,norm_smul,Real.norm_natCast,norm_sub_rev]
    nlinarith
  have ht := norm_add_le
    (latticeEmbed (latticeFloor ((n : ℝ) • u.val))-(n : ℝ) • u.val)
    ((n : ℝ) • u.val-latticeEmbed p)
  rw [sub_add_sub_cancel,← latticeEmbed_sub] at ht
  linarith [latticeFloor_error ((n : ℝ) • u.val)]

end PlanarFPP

end OAI
