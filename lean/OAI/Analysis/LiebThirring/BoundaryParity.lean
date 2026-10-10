import OAI.Analysis.LiebThirring.FreeLocus

namespace OAI

universe u136 u137 u138 u139 u140 u141 u142

noncomputable section
open Finset
noncomputable section
open Finset
noncomputable section
open Finset


namespace SharpLiebThirring.CubeFlags
open Finset SharpLiebThirring.PLParity

lemma bottom_hit_unique {d : ℕ} (H : Subgroup (Signs (d + 1)))
    (hHt : ∀ s : H, s.val.val (Fin.last d) = false)
    (D : SubMulAction H (Flag (d + 1)))
    {V : Type u136} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (ρ : H →* (V ≃ₗ[ℝ] V)) (L : (Fin d → ℝ) ≃ₗ[ℝ] V)
    (p q : Fin d → ℝ) (R h : ℝ) (hR : 0 < R) (hh : 0 < h) (hhr : h ≤ R / 2)
    (hsep : ∀ g k : H, g ≠ k → 8 * R < dist (g • embedSpatial p) (k • embedSpatial p))
    (a : vertices H D → V)
    (haf : ∀ F : D, ∀ k, gridPoint h (F.val.vertex k) (Fin.last d) = 0 →
      gridPoint h (F.val.vertex k) ∈ orbitBall (G := H) (embedSpatial p) R →
      a (flagVertex H D F k) = affineOrbitModel H ρ L (embedSpatial p) R q (gridPoint h (F.val.vertex k)))
    (w₀ : Fin (d + 2) → ℝ) (hw₀ : ∀ k, 0 ≤ w₀ k)
    (hwp : ∀ k, k ≠ Fin.last (d + 1) → 0 < w₀ k) (hs₀ : ∑ k, w₀ k = 1)
    (he₀ : (bottomSeed h p).combination h w₀ = embedSpatial q)
    (F : D) (ht : (F.val.order.symm (Fin.last d)).val = d)
    (hb : F.val.base (Fin.last d) = 0) (hc : F.val.corner (Fin.last d) = false)
    (w : Fin (d + 2) → ℝ) (hw : ∀ k, 0 ≤ w k) (hs : ∑ k, w k = 1)
    (hj : w (Fin.last (d + 1)) = 0) (hz : ∑ k, w k • a (flagVertex H D F k) = 0)
    (hx : F.val.combination h w ∈ orbitBall (G := H) (embedSpatial p) (R / 2)) :
    ∃ s : H, F.val = s • bottomSeed h p := by
  obtain ⟨s,hxs⟩ := hx
  have hdist (k : Fin (d + 2)) : dist (gridPoint h (F.val.vertex k)) (s • embedSpatial p) < R := by
    calc
      _ ≤ dist (gridPoint h (F.val.vertex k)) (F.val.combination h w) +
          dist (F.val.combination h w) (s • embedSpatial p) := dist_triangle _ _ _
      _ < h + R / 2 := add_lt_add_of_le_of_lt
        (by rw [dist_comm]; exact F.val.dist_combination_gridPoint h hh.le w hw hs k) hxs
      _ ≤ R := by linarith
  have htime (k : Fin (d + 2)) (hk : k ≠ Fin.last (d + 1)) :
      gridPoint h (F.val.vertex k) (Fin.last d) = 0 := by
    rw [gridPoint_vertex]
    change h * F.val.point k (Fin.last d) = 0
    rw [F.val.point_time_boundary (Fin.last d) (by simpa using ht) k hk, hb, hc]
    simp
  have hlabel (k : Fin (d + 2)) :
      ballLabel (G := H) (embedSpatial p) R (gridPoint h (F.val.vertex k)) = s :=
    ballLabel_eq (embedSpatial p) R hR hsep (hdist k)
  have hval (k : Fin (d + 2)) (hk : k ≠ Fin.last (d + 1)) :
      a (flagVertex H D F k) = ρ s (L (spatial (s⁻¹ • gridPoint h (F.val.vertex k)) - q)) := by
    rw [haf F k (htime k hk) ⟨s,hdist k⟩]
    simp only [affineOrbitModel, hlabel]
  have hxt : F.val.combination h w (Fin.last d) = 0 := by
    rw [F.val.combination_time_boundary h (Fin.last d) (by simpa using ht) w hs hj, hb, hc]
    simp
  have hxq := mesh_affine_zero_point H ρ L F.val _ h s q w hs hj
    (fun k ↦ a (flagVertex H D F k)) hz hval hxt
  exact ⟨s, bottom_facet_unique h hh.ne' p q s.val (hHt s) F.val hb hc
    w₀ w hw₀ hwp hw hs₀ hs he₀ hxq⟩

/-- Finite equivariant parity rules out a bounded approximating cylinder whose
only boundary hits lie in the one initial root orbit. -/
lemma mesh_parity_contradiction {d : ℕ} (H : Subgroup (Signs (d + 1)))
    (hHt : ∀ s : H, s.val.val (Fin.last d) = false)
    (D : SubMulAction H (Flag (d + 1))) [Fintype D]
    {V : Type u137} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (ρ : H →* (V ≃ₗ[ℝ] V)) (L : (Fin d → ℝ) ≃ₗ[ℝ] V)
    (p q : Fin d → ℝ) (R h : ℝ) (hR : 0 < R) (hh : 0 < h) (hhr : 2*h < R)
    (hsep : ∀ g k : H, g ≠ k → 8 * R < dist (g • embedSpatial p) (k • embedSpatial p))
    (a : vertices H D → V) (ha : ∀ s : H, ∀ z, a (s • z) = ρ s (a z))
    (haug : ∀ F : D, ∀ j : Fin (d + 2), LinearIndependent ℝ
      (fun k : {k // k ≠ j} ↦ ((1 : ℝ), a (flagVertex H D F k))))
    (hvec : ∀ F : D, ∀ i j : Fin (d + 2), i ≠ j → LinearIndependent ℝ
      (fun k : {k // k ≠ i ∧ k ≠ j} ↦ a (flagVertex H D F k)))
    (hfree : ∀ z : vertices H D, ∀ s : H, s • gridPoint h z.val = gridPoint h z.val → s = 1)
    (haf : ∀ F : D, ∀ k, gridPoint h (F.val.vertex k) (Fin.last d) = 0 →
      gridPoint h (F.val.vertex k) ∈ orbitBall (G := H) (embedSpatial p) R →
      a (flagVertex H D F k) = affineOrbitModel H ρ L (embedSpatial p) R q (gridPoint h (F.val.vertex k)))
    (F₀ : D) (hF₀ : F₀.val = bottomSeed h p)
    (hout₀ : F₀.val.neighbor (Fin.last (d + 1)) ∉ D)
    (w₀ : Fin (d + 2) → ℝ) (hw₀ : ∀ k, 0 ≤ w₀ k)
    (hwp : ∀ k, k ≠ Fin.last (d + 1) → 0 < w₀ k) (hs₀ : ∑ k, w₀ k = 1)
    (hj₀ : w₀ (Fin.last (d + 1)) = 0)
    (he₀ : (bottomSeed h p).combination h w₀ = embedSpatial q)
    (hbdy : ∀ F : D, ∀ j : Fin (d + 2), F.val.neighbor j ∉ D →
      ∀ w : Fin (d + 2) → ℝ, (∀ k, 0 ≤ w k) → ∑ k, w k = 1 → w j = 0 →
      ∑ k, w k • a (flagVertex H D F k) = 0 →
      j = Fin.last (d + 1) ∧ (F.val.order.symm (Fin.last d)).val = d ∧
      F.val.base (Fin.last d) = 0 ∧ F.val.corner (Fin.last d) = false ∧
      F.val.combination h w ∈ orbitBall (G := H) (embedSpatial p) (R / 2)) : False := by
  have hseed : cellHit H D a F₀.val (Fin.last (d + 1)) := by
    apply model_seed_hit H D ρ L p q R h hR hh hhr hsep F₀ hF₀ a
      (fun k hk ↦ haf F₀ k ?_ ?_) w₀ hw₀ hs₀ hj₀
    · rw [hF₀, ← Flag.combination_eq_sum_gridPoint]
      exact he₀
    · rw [hF₀, gridPoint_vertex]
      change h * (bottomSeed h p).point k (Fin.last d) = 0
      rw [bottomSeed_time h p k hk, mul_zero]
    · refine ⟨1,?_⟩
      rw [one_smul, hF₀, gridPoint_vertex]
      exact (bottomSeed_dist_point h hh p k).trans_lt hhr
  let p₀ : FinitePairing.selected D (cellHit H D a) (cellHit_equivariant H D ρ a ha) :=
    ⟨⟨F₀, Fin.last (d + 1)⟩, hseed⟩
  have hdim : d + 1 = Module.finrank ℝ V + 1 := by
    have he := L.finrank_eq
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using congrArg (· + 1) he
  obtain ⟨b,hb,hborb⟩ := another_boundary H D ρ a ha hdim haug hvec h hfree p₀ hout₀
  obtain ⟨w,hw,hs,hj,hz⟩ := cellHit_weights H D a b.val.cell b.val.facet b.prop
  obtain ⟨hjl,ht,hbase,hcorner,hx⟩ := hbdy b.val.cell b.val.facet hb w hw hs hj hz
  have hj' : w (Fin.last (d + 1)) = 0 := hjl ▸ hj
  obtain ⟨s,hF⟩ := bottom_hit_unique H hHt D ρ L p q R h hR hh (by linarith) hsep
    a haf w₀ hw₀ hwp hs₀ he₀ b.val.cell ht hbase hcorner w hw hs hj' hz hx
  apply hborb
  apply MulAction.orbitRel_apply.mpr
  apply MulAction.mem_orbit_iff.mpr
  refine ⟨s,?_⟩
  apply Subtype.ext
  apply FinitePairing.CellFacet.ext
  · apply Subtype.ext
    change s • F₀.val = b.val.cell.val
    rw [hF₀, hF]
  · exact hjl.symm

end SharpLiebThirring.CubeFlags

namespace SharpLiebThirring.CubeFlags
open Finset SharpLiebThirring.PLParity
attribute [local instance] Classical.propDecidable

lemma fixed_initial_vectors {d : ℕ}
    (H : Subgroup (Signs (d + 1))) (D : SubMulAction H (Flag (d + 1)))
    {V : Type u138} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (ρ : H →* (V ≃ₗ[ℝ] V)) (L : (Fin d → ℝ) ≃ₗ[ℝ] V)
    (p : Fin (d + 1) → ℝ) (R h : ℝ) (hR : 0 < R) (hh : 0 < h) (hhr : h ≤ R)
    (hsep : ∀ g k : H, g ≠ k → 8 * R < dist (g • p) (k • p))
    (P : vertices H D → Prop)
    (hb : ∀ z : vertices H D, P z → gridPoint h z.val ∈ orbitBall (G := H) p R)
    (q : Fin d → ℝ) (F : D) (i j : Fin (d + 2))
    (hq : ∀ s : H, LinearIndependent ℝ
      (fun k : {k : {k : Fin (d + 2) // k ≠ i ∧ k ≠ j} // P (flagVertex H D F k.val)} ↦
        spatial (s⁻¹ • gridPoint h (F.val.vertex k.val.val)) - q)) :
    LinearIndependent ℝ (fun k : {k : {k : Fin (d + 2) // k ≠ i ∧ k ≠ j} //
        P (flagVertex H D F k.val)} ↦
      affineOrbitModel H ρ L p R q (gridPoint h (F.val.vertex k.val.val))) := by
  obtain ⟨s,hs⟩ := common_flag_label H p R h hR hh hhr hsep F.val
    (fun k ↦ P (flagVertex H D F k)) (fun k hk ↦ hb (flagVertex H D F k) hk)
  exact affineOrbitModel_independent H ρ L p R q
    (fun k : {k : {k : Fin (d + 2) // k ≠ i ∧ k ≠ j} // P (flagVertex H D F k.val)} ↦
      gridPoint h (F.val.vertex k.val.val)) s (fun k ↦ hs k.val.val k.prop) (hq s)

lemma generic_initial_approximation {d : ℕ}
    (H : Subgroup (Signs (d + 1))) (D : SubMulAction H (Flag (d + 1)))
    [Fintype D] [IsCancelSMul H (vertices H D)]
    {V : Type u139} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (ρ : H →* (V ≃ₗ[ℝ] V)) (L : (Fin d → ℝ) ≃ₗ[ℝ] V)
    (hρ : ∀ s : H, ∀ v : V, ‖ρ s v‖ = ‖v‖)
    (p : Fin d → ℝ) (R h η : ℝ) (hR : 0 < R) (hh : 0 < h) (hhr : h ≤ R) (hη : 0 < η)
    (hsep : ∀ g k : H, g ≠ k → 8 * R < dist (g • embedSpatial p) (k • embedSpatial p))
    (hbnd : ∀ q, dist (embedSpatial q) (embedSpatial p) ≤ 2*h → dist (L q) (L p) < η)
    (f : (Fin (d + 1) → ℝ) → V) (hf : ∀ s : H, ∀ x, f (s • x) = ρ s (f x))
    (hmodel : ∀ x, x (Fin.last d) = 0 → x ∈ orbitBall (G := H) (embedSpatial p) R →
      f x = affineOrbitModel H ρ L (embedSpatial p) R p x) :
    ∃ (q : Fin d → ℝ) (w : Fin (d + 2) → ℝ) (a : vertices H D → V),
      (∀ k, 0 ≤ w k) ∧ (∀ k, k ≠ Fin.last (d + 1) → 0 < w k) ∧
      ∑ k, w k = 1 ∧ w (Fin.last (d + 1)) = 0 ∧
      (bottomSeed h p).combination h w = embedSpatial q ∧
      (∀ s : H, ∀ z, a (s • z) = ρ s (a z)) ∧
      (∀ z, dist (a z) (f (gridPoint h z.val)) < 2*η) ∧
      (∀ z, gridPoint h z.val (Fin.last d) = 0 →
        gridPoint h z.val ∈ orbitBall (G := H) (embedSpatial p) R →
        a z = affineOrbitModel H ρ L (embedSpatial p) R q (gridPoint h z.val)) ∧
      (∀ F : D, ∀ j : Fin (d + 2), LinearIndependent ℝ
        (fun k : {k // k ≠ j} ↦ ((1 : ℝ), a (flagVertex H D F k)))) ∧
      (∀ F : D, ∀ i j : Fin (d + 2), i ≠ j → LinearIndependent ℝ
        (fun k : {k // k ≠ i ∧ k ≠ j} ↦ a (flagVertex H D F k))) := by
  classical
  let P : vertices H D → Prop := fun z ↦ gridPoint h z.val (Fin.last d) = 0 ∧
    gridPoint h z.val ∈ orbitBall (G := H) (embedSpatial p) R
  have hP : ∀ s : H, ∀ z, P (s • z) ↔ P z := by
    intro s z
    suffices hs : ∀ s : H, ∀ z, P z → P (s • z) from
      ⟨fun hz ↦ by simpa only [inv_smul_smul] using hs s⁻¹ (s • z) hz, hs s z⟩
    intro s z hz
    change gridPoint h (s.val • z.val) (Fin.last d) = 0 ∧
      gridPoint h (s.val • z.val) ∈ orbitBall (G := H) (embedSpatial p) R
    rw [gridPoint_smul]
    exact ⟨s.val.smul_time_zero _ hz.1, orbitBall_smul (embedSpatial p) R s hz.2⟩
  obtain ⟨U,hU,hUn,hUw⟩ := bottomSeed_open_roots h hh p
  obtain ⟨q,hq,hqg⟩ := exists_generic_initial_root H D h hh.ne' P (fun _ hz ↦ hz.1) U hU hUn
  obtain ⟨w,hw,hwp,hs,hj,he,hd⟩ := hUw q hq
  let b : vertices H D → V := fun z ↦ if P z then
    affineOrbitModel H ρ L (embedSpatial p) R q (gridPoint h z.val) else f (gridPoint h z.val)
  have hb : ∀ s : H, ∀ z, b (s • z) = ρ s (b z) := by
    intro s z
    dsimp only [b]
    by_cases hz : P z
    · rw [ite_eq_left hz, ite_eq_left ((hP s z).mpr hz)]
      change affineOrbitModel H ρ L (embedSpatial p) R q (gridPoint h (s.val • z.val)) = _
      rw [gridPoint_smul]
      exact affineOrbitModel_smul H ρ L (embedSpatial p) R hR hsep q s hz.2
    · rw [ite_eq_right hz, ite_eq_right (fun hs ↦ hz ((hP s z).mp hs))]
      change f (gridPoint h (s.val • z.val)) = _
      rw [gridPoint_smul]
      exact hf s _
  have hbfix (z : vertices H D) (hz : P z) : b z =
      affineOrbitModel H ρ L (embedSpatial p) R q (gridPoint h z.val) := ite_eq_left hz
  have haug : ∀ F : D, ∀ j : Fin (d + 2), LinearIndependent ℝ
      (fun k : {k : {k : Fin (d + 2) // k ≠ j} // P (flagVertex H D F k.val)} ↦
        ((1 : ℝ), b (flagVertex H D F k.val.val))) := by
    intro F j
    convert fixed_initial_augmented H D ρ L (embedSpatial p) R h hR hh hhr hsep P
      (fun _ hz ↦ hz.1) (fun _ hz ↦ hz.2) q F j using 1
    funext k
    rw [hbfix _ k.prop]
    rfl
  have hvec : ∀ F : D, ∀ i j : Fin (d + 2), i ≠ j → LinearIndependent ℝ
      (fun k : {k : {k : Fin (d + 2) // k ≠ i ∧ k ≠ j} // P (flagVertex H D F k.val)} ↦
        b (flagVertex H D F k.val.val)) := by
    intro F i j hij
    convert fixed_initial_vectors H D ρ L (embedSpatial p) R h hR hh hhr hsep P
      (fun _ hz ↦ hz.2) q F i j (hqg F i j hij) using 1
    funext k
    rw [hbfix _ k.prop]
    rfl
  have hdim : d + 1 = Module.finrank ℝ V + 1 := by
    have hdim := L.finrank_eq
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using congrArg (· + 1) hdim
  obtain ⟨a,ha,hab,haf,hag,hvg⟩ := generic_on_complex H D ρ hdim P hP b hb haug hvec η hη
  refine ⟨q,w,a,hw,hwp,hs,hj,?_,ha,?_,?_,hag,hvg⟩
  · rw [Flag.combination_eq_sum_gridPoint]
    exact he
  · intro z
    have hbf : dist (b z) (f (gridPoint h z.val)) < η := by
      by_cases hz : P z
      · rw [hbfix z hz, hmodel _ hz.1 hz.2, affineOrbitModel_dist H ρ L _ _ hρ]
        exact hbnd q hd
      · simp only [b, ite_eq_right hz, dist_self]
        exact hη
    have ht := dist_triangle (a z) (b z) (f (gridPoint h z.val))
    linarith [hab z]
  · intro z ht hz
    exact (haf z ⟨ht,hz⟩).trans (hbfix z ⟨ht,hz⟩)

end SharpLiebThirring.CubeFlags

namespace SharpLiebThirring.CubeFlags
open Finset SharpLiebThirring.PLParity

lemma mesh_boundary_bottom {d : ℕ}
    (K : Set (Fin (d + 1) → ℝ)) (h r : ℝ) (hh : 0 < h) (hhr : h < r)
    (m : ℕ) (hm : h * m = 1) (F : Flag (d + 1))
    (hF : F ∈ nearCylinder K h r (Fin.last d) m) (j : Fin (d + 2))
    (hout : F.neighbor j ∉ nearCylinder K h r (Fin.last d) m)
    (w : Fin (d + 2) → ℝ) (hw : ∀ k, 0 ≤ w k) (hs : ∑ k, w k = 1) (hj : w j = 0)
    (hx : F.combination h w ∈ Metric.thickening (r/2) K)
    (htop : F.combination h w (Fin.last d) < 1) :
    j = Fin.last (d + 1) ∧ (F.order.symm (Fin.last d)).val = d ∧
      F.base (Fin.last d) = 0 ∧ F.corner (Fin.last d) = false := by
  have hn := neighbor_near_centers_of_combination K h r hh.le hhr F j w hw hs hj
    (Metric.mem_thickening_iff.mp hx)
  have hnt : ¬ (0 ≤ (F.neighbor j).base (Fin.last d) ∧
      (F.neighbor j).base (Fin.last d) < (m : ℤ)) :=
    fun ht ↦ hout ⟨hn,ht⟩
  obtain ⟨hjl,ht,hbc⟩ := F.neighbor_outside_time j (Fin.last d) m hF.2.1 hF.2.2 hnt
  refine ⟨hjl,by simpa using ht,?_⟩
  rcases hbc with hbot | htop'
  · exact hbot
  · have hj' : w (Fin.last (d + 1)) = 0 := hjl ▸ hj
    have he := F.combination_time_boundary h (Fin.last d) ht w hs hj'
    simp only [htop'.1, htop'.2, ↓reduceIte, Int.cast_sub, Int.cast_natCast,
      Int.cast_one, sub_add_cancel, hm] at he
    linarith

lemma isOpen_orbitBall {G : Type u140} {E : Type u141} [Group G] [MulAction G E] [MetricSpace E]
    (p : E) (R : ℝ) : IsOpen (orbitBall (G := G) p R) := by
  have he : orbitBall (G := G) p R = ⋃ s : G, Metric.ball (s • p) R := by
    ext x
    simp only [orbitBall, Set.mem_ofPred_eq, Set.mem_iUnion, Metric.mem_ball]
  rw [he]
  exact isOpen_iUnion (fun _ ↦ Metric.isOpen_ball)

lemma dist_spatial_le {d : ℕ} (x y : Fin (d + 1) → ℝ) :
    dist (spatial x) (spatial y) ≤ dist x y := by
  rw [dist_pi_le_iff dist_nonneg]
  intro i
  exact dist_le_pi_dist x y i.castSucc

lemma exists_positive_mesh (δ : ℝ) (hδ : 0 < δ) :
    ∃ m : ℕ, ∃ h : ℝ, 0 < m ∧ 0 < h ∧ h < δ ∧ h * m = 1 := by
  obtain ⟨n,hn⟩ := exists_nat_one_div_lt hδ
  refine ⟨n+1,1 / ((n : ℝ)+1), Nat.succ_pos _, by positivity,hn,?_⟩
  push_cast
  exact div_mul_cancel₀ 1 (by positivity)

lemma bottomSeed_mem_nearCylinder {d : ℕ} (K : Set (Fin (d + 1) → ℝ))
    (p : Fin d → ℝ) (hp : embedSpatial p ∈ K) (h r : ℝ) (hh : 0 < h) (hhr : h < r)
    (m : ℕ) (hm : 0 < m) : bottomSeed h p ∈ nearCylinder K h r (Fin.last d) m := by
  refine ⟨⟨embedSpatial p,hp,(bottomSeed_dist_center h hh p).trans_lt hhr⟩,?_,?_⟩
  · simp [bottomSeed]
  · simpa only [bottomSeed,Fin.snoc_last] using (Int.natCast_pos.mpr hm)

lemma bottomSeed_neighbor_not_mem {d : ℕ} (K : Set (Fin (d + 1) → ℝ))
    (p : Fin d → ℝ) (h r : ℝ) (m : ℕ) :
    (bottomSeed h p).neighbor (Fin.last (d + 1)) ∉ nearCylinder K h r (Fin.last d) m := by
  intro hb
  have hn : ((bottomSeed h p).neighbor (Fin.last (d + 1))).base (Fin.last d) = -1 := by
    simp only [Flag.neighbor, Fin.val_last, Nat.add_eq_zero_iff, Nat.one_ne_zero,
      and_false, dite_eq_left, bottomSeed, Flag.cross, Equiv.refl_apply,
      Bool.false_eq_true, ↓reduceIte]
    change Function.update _ (Fin.last d) _ (Fin.last d) = -1
    simp only [Function.update_self]
    have hi : (⟨d + 1 - 1, by omega⟩ : Fin (d + 1)) = Fin.last d := Fin.ext (by simp only [Fin.val_last]; omega)
    rw [hi, Fin.snoc_last, zero_add]
  have hneg := hb.2.1
  rw [hn] at hneg
  exact (by norm_num : ¬ (0 : ℤ) ≤ -1) hneg

end SharpLiebThirring.CubeFlags

namespace SharpLiebThirring.CubeFlags
open Finset SharpLiebThirring.PLParity

/-- The exact continuation principle needed below, first for an affine initial
model in disjoint neighborhoods of its one free zero orbit. The proof uses
finite equivariant PL perturbation and mod-two boundary pairing. -/
theorem exists_terminal_zero_affine {d : ℕ}
    (H : Subgroup (Signs (d + 1))) (hHt : ∀ s : H, s.val.val (Fin.last d) = false)
    {V : Type u142} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (ρ : H →* (V ≃ₗ[ℝ] V)) (L : (Fin d → ℝ) ≃ₗ[ℝ] V)
    (hρ : ∀ s : H, ∀ v : V, ‖ρ s v‖ = ‖v‖)
    (p : Fin d → ℝ) (R : ℝ) (hR : 0 < R)
    (hsep : ∀ g k : H, g ≠ k → 8 * R < dist (g • embedSpatial p) (k • embedSpatial p))
    (f : (Fin (d + 1) → ℝ) → V)
    (hf : ContinuousOn f {x | x (Fin.last d) ∈ Set.Icc (0 : ℝ) 1})
    (hfe : ∀ s : H, ∀ x, f (s • x) = ρ s (f x))
    (hmodel : ∀ x, x (Fin.last d) = 0 → x ∈ orbitBall (G := H) (embedSpatial p) R →
      f x = affineOrbitModel H ρ L (embedSpatial p) R p x)
    (hz0 : ∀ x, x (Fin.last d) = 0 → f x = 0 → ∃ s : H, s • embedSpatial p = x)
    (hK : IsCompact {x | x (Fin.last d) ∈ Set.Icc (0 : ℝ) 1 ∧ f x = 0})
    (hfree : ∀ x, x (Fin.last d) ∈ Set.Icc (0 : ℝ) 1 → f x = 0 →
      ∀ s : H, s • x = x → s = 1) :
    ∃ x : Fin (d + 1) → ℝ, x (Fin.last d) = 1 ∧ f x = 0 := by
  classical
  by_contra hterm
  let K := {x : Fin (d + 1) → ℝ | x (Fin.last d) ∈ Set.Icc (0 : ℝ) 1 ∧ f x = 0}
  have hp0 : (embedSpatial p) (Fin.last d) = 0 := by
    change Fin.snoc (α := fun _ : Fin (d + 1) ↦ ℝ) p 0 (Fin.last d) = 0
    simp only [Fin.snoc_last]
  have fp0 : f (embedSpatial p) = 0 := by
    rw [hmodel _ hp0 ⟨1,by simpa using hR⟩]
    have hl : ballLabel (G := H) (embedSpatial p) R (embedSpatial p) = 1 :=
      ballLabel_eq _ _ hR hsep (by simpa using hR)
    simp only [affineOrbitModel,hl,inv_one,one_smul,spatial_embed,sub_self,map_zero]
  have hpK : embedSpatial p ∈ K := ⟨by rw [hp0]; exact ⟨le_refl _,zero_le_one⟩,fp0⟩
  have hKfree : K ⊆ freeLocus (G := H) := fun x hx ↦ hfree x hx.1 hx.2
  obtain ⟨r₀,hr₀,hrt⟩ := compact_free_tube (G := H) hK hKfree
  let r := r₀ / 4
  have hr : 0 < r := by dsimp [r]; positivity
  let C := Metric.cthickening r₀ K ∩ {x | x (Fin.last d) ∈ Set.Icc (0 : ℝ) 1}
  have hC : IsCompact C := hK.cthickening.inter_right
    (isClosed_Icc.preimage (continuous_apply (Fin.last d)))
  let U := Metric.thickening (r/2) K ∩ {x | x (Fin.last d) < 1} ∩
    ({x | x (Fin.last d) ≠ 0} ∪ orbitBall (G := H) (embedSpatial p) (R/2))
  have hU : IsOpen U := (Metric.isOpen_thickening.inter
    (isOpen_lt (continuous_apply _) continuous_const)).inter
      ((isOpen_ne_fun (continuous_apply _) continuous_const).union (isOpen_orbitBall _ _))
  have hCU : ∀ x ∈ C, f x = 0 → x ∈ U := by
    intro x hx hfx
    have hxK : x ∈ K := ⟨hx.2,hfx⟩
    refine ⟨⟨Metric.mem_thickening_iff.mpr ⟨x,hxK,by simp; positivity⟩,?_⟩,?_⟩
    · exact lt_of_le_of_ne hx.2.2 (fun he ↦ hterm ⟨x,he,hfx⟩)
    · by_cases ht : x (Fin.last d) = 0
      · obtain ⟨s,rfl⟩ := hz0 x ht hfx
        exact Or.inr ⟨s,by simp; positivity⟩
      · exact Or.inl ht
  obtain ⟨ε,hε,hsmall⟩ := small_norm_near_zeros hC hU f (hf.mono Set.inter_subset_right) hCU
  obtain ⟨δ,hδ,hδf⟩ := Metric.uniformContinuousOn_iff.mp
    (hC.uniformContinuousOn_of_continuous (hf.mono Set.inter_subset_right)) (ε/4) (by positivity)
  have hLc : ContinuousAt (fun x : Fin (d + 1) → ℝ ↦ L (spatial x)) (embedSpatial p) :=
    (L.toContinuousLinearEquiv.continuous.comp spatial.continuous_of_finiteDimensional).continuousAt
  obtain ⟨δL,hδL,hδLf⟩ := Metric.continuousAt_iff.mp hLc (ε/8) (by positivity)
  obtain ⟨m,h,hm,hh,hbound,hhm⟩ := exists_positive_mesh
    (min (r/4) (min (R/4) (min δ (δL/4)))) (by positivity)
  have hhr : h < r/4 := (lt_min_iff.mp hbound).1
  have hhR : h < R/4 := (lt_min_iff.mp (lt_min_iff.mp hbound).2).1
  have hhδ : h < δ := (lt_min_iff.mp (lt_min_iff.mp (lt_min_iff.mp hbound).2).2).1
  have hhδL : h < δL/4 := (lt_min_iff.mp (lt_min_iff.mp (lt_min_iff.mp hbound).2).2).2
  have hsize : r + h/2 ≤ r₀ := by dsimp [r] at *; linarith
  have hKs : ∀ s : H, ∀ x ∈ K, s • x ∈ K := by
    intro s x hx
    constructor
    · change (if s.val.val (Fin.last d) then -x (Fin.last d) else x (Fin.last d)) ∈ _
      simpa only [hHt s,Bool.false_eq_true,↓reduceIte] using hx.1
    · rw [hfe,hx.2,map_zero]
  let D : SubMulAction H (Flag (d + 1)) :=
    ⟨nearCylinder K h r (Fin.last d) m,
      fun s _ hF ↦ nearCylinder_smul K h r (Fin.last d) m s.val (hHt s) (hKs s) hF⟩
  let : Fintype D := (finite_nearCylinder hK.isBounded h r hh (Fin.last d) m).fintype
  have hpoint : ∀ F : D, ∀ k, gridPoint h (F.val.vertex k) ∈ C := by
    intro F k
    rw [gridPoint_vertex]
    exact ⟨Metric.cthickening_mono hsize K
      (nearCylinder_point_cthickening K h r hh.le (Fin.last d) m F.prop k),
      nearCylinder_point_time K h r hh.le (Fin.last d) m hhm F.prop k⟩
  have hvfree : ∀ z : vertices H D, ∀ s : H, s • gridPoint h z.val = gridPoint h z.val → s = 1 := by
    intro z s hs
    obtain ⟨F,k,hFk⟩ := z.prop
    have hmem : gridPoint h z.val ∈ Metric.cthickening r₀ K := by
      rw [← hFk]
      exact (hpoint F k).1
    exact hrt hmem s hs
  let : IsCancelSMul H (vertices H D) := verticesIsCancel H D h hvfree
  obtain ⟨q,w₀,a,hw₀,hwp,hs₀,hj₀,he₀,ha,hap,haf,haug,hvec⟩ :=
    generic_initial_approximation H D ρ L hρ p R h (ε/8) hR hh (by linarith) (by positivity)
      hsep (fun q hqp ↦ by
        have hdq : dist (embedSpatial q) (embedSpatial p) < δL := by linarith
        simpa only [spatial_embed] using hδLf hdq) f hfe hmodel
  let F₀ : D := ⟨bottomSeed h p, bottomSeed_mem_nearCylinder K p hpK h r hh (by linarith) m hm⟩
  apply mesh_parity_contradiction H hHt D ρ L p q R h hR hh (by linarith) hsep
    a ha haug hvec hvfree (fun F k ht hb ↦ haf (flagVertex H D F k) ht hb)
    F₀ rfl (bottomSeed_neighbor_not_mem K p h r m) w₀ hw₀ hwp hs₀ hj₀ he₀
  intro F j hout w hw hs hj hz
  have hxC : F.val.combination h w ∈ C :=
    ⟨Metric.cthickening_mono hsize K
      (nearCylinder_combination_cthickening K h r hh.le (Fin.last d) m F.prop w hw hs),
      nearCylinder_combination_time K h r hh.le (Fin.last d) m hhm F.prop w hw hs⟩
  have hn := norm_at_mesh_zero H D a f h (ε/4) (ε/4) hh.le C
    (fun z ↦ by have hz := hap z; linarith)
    (fun x hx y hy hxy ↦ (hδf x hx y hy (hxy.trans_lt hhδ)).le)
    F w hw hs hz hxC (hpoint F)
  have hxU := hsmall _ hxC (by linarith : ‖f (F.val.combination h w)‖ < ε)
  obtain ⟨hjl,ht,hbase,hcorner⟩ := mesh_boundary_bottom K h r hh (by linarith) m hhm
    F.val F.prop j hout w hw hs hj hxU.1.1 hxU.1.2
  refine ⟨hjl,ht,hbase,hcorner,?_⟩
  have htime : F.val.combination h w (Fin.last d) = 0 := by
    rw [F.val.combination_time_boundary h (Fin.last d) (by simpa using ht) w hs (hjl ▸ hj)]
    simp only [hbase,hcorner,Int.cast_zero,Bool.false_eq_true,↓reduceIte,add_zero,mul_zero]
  exact hxU.2.resolve_left (fun hne ↦ hne htime)

end SharpLiebThirring.CubeFlags

end
end
end

end OAI
