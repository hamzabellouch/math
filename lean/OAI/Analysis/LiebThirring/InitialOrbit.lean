import OAI.Analysis.LiebThirring.EquivariantFlags

namespace OAI

universe u103 u104 u105 u106 u107 u108 u109 u110 u111 u112 u113 u114 u115

noncomputable section
open Finset
noncomputable section
open Finset
noncomputable section
open Finset
section
open Set Finset Filter


/-! Disjoint equivariant coordinate balls for the unique initial zero orbit. -/

open Set Finset
namespace SharpLiebThirring.PLParity
section OrbitBalls
attribute [local instance] Classical.propDecidable
variable {G : Type u103} {E : Type u104} [Group G] [MetricSpace E] [MulAction G E]
  [IsIsometricSMul G E]

omit [IsIsometricSMul G E] in
lemma orbit_separation [Fintype G] (p : E) (hp : ∀ g : G, g • p = p → g = 1) :
    ∃ R > 0, ∀ g k : G, g ≠ k → 8 * R < dist (g • p) (k • p) := by
  classical
  let d : G × G → ℝ := fun q ↦ if q.1 = q.2 then 1 else dist (q.1 • p) (q.2 • p)
  have hd (q : G × G) : 0 < d q := by
    dsimp [d]
    split_ifs with he
    · norm_num
    · apply dist_pos.mpr
      intro hh
      have hx : (q.2⁻¹ * q.1) • p = p := by rw [mul_smul, hh, inv_smul_smul]
      exact he (inv_mul_eq_one.mp (hp _ hx)).symm
  have hn : (Finset.univ : Finset (G × G)).Nonempty := ⟨(1,1), Finset.mem_univ _⟩
  let b := Finset.univ.inf' hn d
  have hb : 0 < b := (Finset.lt_inf'_iff _).mpr (fun q _ ↦ hd q)
  refine ⟨b / 16, by positivity, ?_⟩
  intro g k hgk
  have hle : b ≤ d (g,k) := Finset.inf'_le _ (Finset.mem_univ _)
  dsimp [d] at hle
  rw [ite_eq_right hgk] at hle
  linarith

variable (p : E) (R : ℝ)

def orbitBall : Set E := {x | ∃ g : G, dist x (g • p) < R}

noncomputable def ballLabel (x : E) : G :=
  if hx : x ∈ orbitBall (G := G) p R then hx.choose else 1

omit [IsIsometricSMul G E] in
lemma ballLabel_dist {x : E} (hx : x ∈ orbitBall (G := G) p R) :
    dist x (ballLabel (G := G) p R x • p) < R := by
  simp only [ballLabel, dite_eq_left hx]
  exact hx.choose_spec

lemma orbitBall_smul (g : G) {x : E} (hx : x ∈ orbitBall (G := G) p R) :
    g • x ∈ orbitBall (G := G) p R := by
  obtain ⟨k,hk⟩ := hx
  refine ⟨g*k, ?_⟩
  rw [mul_smul, dist_smul]
  exact hk

lemma mem_orbitBall_smul_iff (g : G) (x : E) :
    g • x ∈ orbitBall (G := G) p R ↔ x ∈ orbitBall (G := G) p R := by
  constructor
  · intro hx
    simpa only [inv_smul_smul] using orbitBall_smul p R g⁻¹ hx
  · exact orbitBall_smul p R g

variable (hR : 0 < R) (hsep : ∀ g k : G, g ≠ k → 8 * R < dist (g • p) (k • p))

include hR hsep in
omit [IsIsometricSMul G E] in
lemma ballLabel_eq {x : E} {g : G} (hx : dist x (g • p) < R) :
    ballLabel (G := G) p R x = g := by
  by_contra hn
  have hl := ballLabel_dist p R (show x ∈ orbitBall (G := G) p R from ⟨g,hx⟩)
  have hd := dist_triangle (ballLabel (G := G) p R x • p) x (g • p)
  rw [dist_comm (ballLabel (G := G) p R x • p) x] at hd
  have hs := hsep _ _ hn
  linarith

include hR hsep in
lemma ballLabel_smul (g : G) {x : E} (hx : x ∈ orbitBall (G := G) p R) :
    ballLabel (G := G) p R (g • x) = g * ballLabel (G := G) p R x := by
  apply ballLabel_eq p R hR hsep
  rw [mul_smul, dist_smul]
  exact ballLabel_dist p R hx

include hR hsep in
omit [IsIsometricSMul G E] in
lemma ballLabel_eq_of_dist {x y : E} (hx : x ∈ orbitBall (G := G) p R)
    (hy : y ∈ orbitBall (G := G) p R) (hxy : dist x y ≤ R) :
    ballLabel (G := G) p R x = ballLabel (G := G) p R y := by
  by_contra hn
  have hlx := ballLabel_dist p R hx
  have hly := ballLabel_dist p R hy
  have hd := dist_triangle4 (ballLabel (G := G) p R x • p) x y (ballLabel (G := G) p R y • p)
  rw [dist_comm (ballLabel (G := G) p R x • p) x] at hd
  have hs := hsep _ _ hn
  linarith

include hR hsep in
omit [IsIsometricSMul G E] in
lemma exists_common_ballLabel {ι : Type u105} (v : ι → E) (P : ι → Prop)
    (hv : ∀ i, P i → v i ∈ orbitBall (G := G) p R)
    (hd : ∀ i j, dist (v i) (v j) ≤ R) :
    ∃ g : G, ∀ i, P i → ballLabel (G := G) p R (v i) = g := by
  by_cases hn : ∃ i, P i
  · obtain ⟨j,hj⟩ := hn
    refine ⟨ballLabel (G := G) p R (v j), ?_⟩
    intro i hi
    exact ballLabel_eq_of_dist p R hR hsep (hv i hi) (hv j hj) (hd i j)
  · exact ⟨1, fun i hi ↦ False.elim (hn ⟨i,hi⟩)⟩

end OrbitBalls
end SharpLiebThirring.PLParity

namespace SharpLiebThirring.CubeFlags
open Finset SharpLiebThirring.PLParity
section Translate
variable {V : Type u106} {W : Type u107} {ι : Type u108} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
lemma augmented_translate_independent (v : ι → V) (p : V)
    (hv : LinearIndependent ℝ (fun i ↦ ((1 : ℝ), v i))) :
    LinearIndependent ℝ (fun i ↦ ((1 : ℝ), v i - p)) := by
  let fst : (ℝ × V) →ₗ[ℝ] ℝ := LinearMap.fst ℝ ℝ V
  let snd : (ℝ × V) →ₗ[ℝ] V := LinearMap.snd ℝ ℝ V
  let T : (ℝ × V) →ₗ[ℝ] (ℝ × V) := fst.prod (snd - fst.smulRight p)
  have hT : Function.Injective T := by
    rintro ⟨a,x⟩ ⟨b,y⟩ he
    have hab : a = b := congrArg Prod.fst he
    have hxy : x - a • p = y - b • p := congrArg Prod.snd he
    rw [← hab] at hxy
    exact Prod.ext hab (sub_left_inj.mp hxy)
  have hh := hv.map' T (LinearMap.ker_eq_bot.mpr hT)
  change LinearIndependent ℝ (fun i ↦ T ((1 : ℝ), v i)) at hh
  have he : (fun i ↦ T ((1 : ℝ), v i)) = (fun i ↦ ((1 : ℝ), v i - p)) := by
    funext i
    change ((1 : ℝ), v i - (1 : ℝ) • p) = (1, v i - p)
    rw [one_smul]
  rwa [he] at hh

lemma augmented_equiv_independent (v : ι → V) (L : V ≃ₗ[ℝ] W)
    (hv : LinearIndependent ℝ (fun i ↦ ((1 : ℝ), v i))) :
    LinearIndependent ℝ (fun i ↦ ((1 : ℝ), L (v i))) :=
  hv.map' ((LinearEquiv.refl ℝ ℝ).prodCongr L).toLinearMap
    (LinearMap.ker_eq_bot.mpr (LinearEquiv.injective _))
end Translate

lemma Signs.smul_time_zero {d : ℕ} (s : Signs (d + 1)) (x : Fin (d + 1) → ℝ)
    (hx : x (Fin.last d) = 0) : (s • x) (Fin.last d) = 0 := by
  simp only [Signs.smul_real, hx, neg_zero, ite_self]

lemma Flag.augmented_spatial_scaled {d : ℕ} {ι : Type u109} (F : Flag (d + 1))
    (v : ι → Fin (d + 2)) (hv : Function.Injective v) {h : ℝ} (hh : h ≠ 0)
    (s : Signs (d + 1)) (ht : ∀ i, (h • F.point (v i)) (Fin.last d) = 0) :
    LinearIndependent ℝ (fun i ↦ ((1 : ℝ), spatial (s • (h • F.point (v i))))) := by
  have hu := augmented_scale_independent (fun i ↦ F.point (v i))
    (F.augmented_linearIndependent.comp v hv) hh
  have hr := augmented_equiv_independent (fun i ↦ h • F.point (v i))
    s.linearIsometry.toLinearEquiv hu
  exact augmented_spatial_independent _ hr (fun i ↦ s.smul_time_zero _ (ht i))

instance signsSubgroupIsIsometric {n : ℕ} (H : Subgroup (Signs n)) :
    IsIsometricSMul H (Fin n → ℝ) where
  isometry_smul s := s.val.linearIsometry.isometry

section Model
variable {d : ℕ} (H : Subgroup (Signs (d + 1)))
variable {V : Type u110} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable (ρ : H →* (V ≃ₗ[ℝ] V)) (L : (Fin d → ℝ) ≃ₗ[ℝ] V)
variable (p : Fin (d + 1) → ℝ) (R : ℝ)

def affineOrbitModel (q : Fin d → ℝ) (x : Fin (d + 1) → ℝ) : V :=
  let s := ballLabel (G := H) p R x
  ρ s (L (spatial (s⁻¹ • x) - q))

lemma affineOrbitModel_smul (hR : 0 < R)
    (hsep : ∀ g k : H, g ≠ k → 8 * R < dist (g • p) (k • p))
    (q : Fin d → ℝ) (s : H) {x : Fin (d + 1) → ℝ} (hx : x ∈ orbitBall (G := H) p R) :
    affineOrbitModel H ρ L p R q (s • x) = ρ s (affineOrbitModel H ρ L p R q x) := by
  simp only [affineOrbitModel, ballLabel_smul p R hR hsep s hx, mul_inv_rev,
    mul_smul, inv_smul_smul, map_mul, LinearEquiv.mul_apply]

lemma affineOrbitModel_dist (hρ : ∀ s : H, ∀ v : V, ‖ρ s v‖ = ‖v‖)
    (q q' : Fin d → ℝ) (x : Fin (d + 1) → ℝ) :
    dist (affineOrbitModel H ρ L p R q x) (affineOrbitModel H ρ L p R q' x) = dist (L q) (L q') := by
  let s := ballLabel (G := H) p R x
  simp only [dist_eq_norm, affineOrbitModel, ← map_sub, hρ]
  have he : spatial (s⁻¹ • x) - q - (spatial (s⁻¹ • x) - q') = q' - q := by abel
  change ‖L (spatial (s⁻¹ • x) - q - (spatial (s⁻¹ • x) - q'))‖ = ‖L (q - q')‖
  rw [he, map_sub, map_sub, norm_sub_rev]

lemma affineOrbitModel_augmented {ι : Type u111} (q : Fin d → ℝ)
    (x : ι → Fin (d + 1) → ℝ) (s : H)
    (hs : ∀ i, ballLabel (G := H) p R (x i) = s)
    (hi : LinearIndependent ℝ (fun i ↦ ((1 : ℝ), spatial (s⁻¹ • x i)))) :
    LinearIndependent ℝ (fun i ↦ ((1 : ℝ), affineOrbitModel H ρ L p R q (x i))) := by
  simp only [affineOrbitModel, hs]
  exact augmented_equiv_independent _ (L.trans (ρ s)) (augmented_translate_independent _ q hi)

lemma affineOrbitModel_independent {ι : Type u112} (q : Fin d → ℝ)
    (x : ι → Fin (d + 1) → ℝ) (s : H)
    (hs : ∀ i, ballLabel (G := H) p R (x i) = s)
    (hi : LinearIndependent ℝ (fun i ↦ spatial (s⁻¹ • x i) - q)) :
    LinearIndependent ℝ (fun i ↦ affineOrbitModel H ρ L p R q (x i)) := by
  simp only [affineOrbitModel, hs]
  exact hi.map' (L.trans (ρ s)).toLinearMap (LinearMap.ker_eq_bot.mpr (LinearEquiv.injective _))

end Model
end SharpLiebThirring.CubeFlags

namespace SharpLiebThirring.CubeFlags
open Finset SharpLiebThirring.PLParity
attribute [local instance] Classical.propDecidable

lemma Flag.dist_gridPoint_gridPoint {n : ℕ} (F : Flag n) (h : ℝ) (hh : 0 ≤ h)
    (j k : Fin (n + 1)) : dist (gridPoint h (F.vertex j)) (gridPoint h (F.vertex k)) ≤ h := by
  rw [gridPoint_vertex, gridPoint_vertex]
  calc
    _ ≤ dist (h • F.point j) (h • F.center) + dist (h • F.center) (h • F.point k) := dist_triangle _ _ _
    _ ≤ h / 2 + h / 2 := by
      apply add_le_add (F.dist_scaled_point_center h hh j)
      rw [dist_comm]
      exact F.dist_scaled_point_center h hh k
    _ = h := by ring

lemma exists_generic_initial_root {d : ℕ}
    (H : Subgroup (Signs (d + 1))) (D : SubMulAction H (Flag (d + 1))) [Fintype D]
    (h : ℝ) (hh : h ≠ 0) (P : vertices H D → Prop)
    (hP : ∀ z : vertices H D, P z → gridPoint h z.val (Fin.last d) = 0)
    (U : Set (Fin d → ℝ)) (hU : IsOpen U) (hUn : U.Nonempty) :
    ∃ q ∈ U, ∀ F : D, ∀ i j : Fin (d + 2), i ≠ j → ∀ s : H,
      LinearIndependent ℝ (fun k : {k : {k : Fin (d + 2) // k ≠ i ∧ k ≠ j} //
          P (flagVertex H D F k.val)} ↦
        spatial (s⁻¹ • gridPoint h (F.val.vertex k.val.val)) - q) := by
  classical
  let T := (D × {p : Fin (d + 2) × Fin (d + 2) // p.1 ≠ p.2}) × H
  let J (t : T) := {k : {k : Fin (d + 2) // k ≠ t.1.2.val.1 ∧ k ≠ t.1.2.val.2} //
    P (flagVertex H D t.1.1 k.val)}
  let v (t : T) (k : J t) := spatial (t.2⁻¹ • gridPoint h (t.1.1.val.vertex k.val.val))
  have hv (t : T) : LinearIndependent ℝ (fun k ↦ ((1 : ℝ), v t k)) := by
    have hh' := t.1.1.val.augmented_spatial_scaled (fun k : J t ↦ k.val.val)
      (fun _ _ he ↦ Subtype.ext (Subtype.ext he)) hh t.2⁻¹.val (fun k ↦ by
        rw [← gridPoint_vertex]
        exact hP (flagVertex H D t.1.1 k.val.val) k.prop)
    simpa only [v, gridPoint_vertex, Subgroup.smul_def] using hh'
  have hc (t : T) : Fintype.card (J t) ≤ Module.finrank ℝ (Fin d → ℝ) := by
    have h₁ := Fintype.card_subtype_le (fun k : {k : Fin (d + 2) // k ≠ t.1.2.val.1 ∧ k ≠ t.1.2.val.2} ↦
      P (flagVertex H D t.1.1 k.val))
    have h₂ := card_omit_two_le t.1.2.val.1 t.1.2.val.2 t.1.2.prop
    change Fintype.card (J t) ≤ _ at h₁
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    exact h₁.trans (Nat.le_of_succ_le_succ h₂)
  have hd := dense_finite_conditions (fun t : T ↦ fun q : Fin d → ℝ ↦
      LinearIndependent ℝ (fun k ↦ v t k - q))
    (fun t ↦ isOpen_independent_shift (v t)) (fun t ↦ dense_independent_shift (v t) (hv t) (hc t))
  obtain ⟨q,hqu,hq⟩ := hd.inter_open_nonempty U hU hUn
  exact ⟨q,hqu,fun F i j hij s ↦ hq ((F,⟨(i,j),hij⟩),s)⟩

lemma common_flag_label {d : ℕ} (H : Subgroup (Signs (d + 1)))
    (p : Fin (d + 1) → ℝ) (R h : ℝ) (hR : 0 < R) (hh : 0 < h) (hhr : h ≤ R)
    (hsep : ∀ g k : H, g ≠ k → 8 * R < dist (g • p) (k • p))
    (F : Flag (d + 1)) (P : Fin (d + 2) → Prop)
    (hb : ∀ k, P k → gridPoint h (F.vertex k) ∈ orbitBall (G := H) p R) :
    ∃ s : H, ∀ k, P k → ballLabel (G := H) p R (gridPoint h (F.vertex k)) = s := by
  have hd : ∀ i j : Fin (d + 2),
      dist (gridPoint h (F.vertex i)) (gridPoint h (F.vertex j)) ≤ R :=
    fun i j ↦ (F.dist_gridPoint_gridPoint h hh.le i j).trans hhr
  exact exists_common_ballLabel (G := H) p R hR hsep
    (fun k : Fin (d + 2) ↦ gridPoint h (F.vertex k)) P hb hd

lemma fixed_initial_augmented {d : ℕ}
    (H : Subgroup (Signs (d + 1))) (D : SubMulAction H (Flag (d + 1)))
    {V : Type u113} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (ρ : H →* (V ≃ₗ[ℝ] V)) (L : (Fin d → ℝ) ≃ₗ[ℝ] V)
    (p : Fin (d + 1) → ℝ) (R h : ℝ) (hR : 0 < R) (hh : 0 < h) (hhr : h ≤ R)
    (hsep : ∀ g k : H, g ≠ k → 8 * R < dist (g • p) (k • p))
    (P : vertices H D → Prop)
    (ht : ∀ z : vertices H D, P z → gridPoint h z.val (Fin.last d) = 0)
    (hb : ∀ z : vertices H D, P z → gridPoint h z.val ∈ orbitBall (G := H) p R)
    (q : Fin d → ℝ) (F : D) (j : Fin (d + 2)) :
    LinearIndependent ℝ (fun k : {k : {k : Fin (d + 2) // k ≠ j} // P (flagVertex H D F k.val)} ↦
      ((1 : ℝ), affineOrbitModel H ρ L p R q (gridPoint h (F.val.vertex k.val.val)))) := by
  obtain ⟨s,hs⟩ := common_flag_label H p R h hR hh hhr hsep
    F.val (fun k ↦ P (flagVertex H D F k)) (fun k hk ↦ hb (flagVertex H D F k) hk)
  apply affineOrbitModel_augmented H ρ L p R q
    (fun k : {k : {k : Fin (d + 2) // k ≠ j} // P (flagVertex H D F k.val)} ↦
      gridPoint h (F.val.vertex k.val.val)) s (fun k ↦ hs k.val.val k.prop)
  have hu := F.val.augmented_spatial_scaled
    (fun k : {k : {k : Fin (d + 2) // k ≠ j} // P (flagVertex H D F k.val)} ↦ k.val.val)
    (fun _ _ he ↦ Subtype.ext (Subtype.ext he)) hh.ne' s⁻¹.val (fun k ↦ by
      rw [← gridPoint_vertex]
      exact ht (flagVertex H D F k.val.val) k.prop)
  simpa only [gridPoint_vertex, Subgroup.smul_def] using hu

end SharpLiebThirring.CubeFlags

namespace SharpLiebThirring.CubeFlags
open Finset SharpLiebThirring.PLParity

lemma dist_convex_sum_le {ι : Type u114} {E : Type u115} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) (x : ι → E) (p : E) (r : ℝ)
    (hx : ∀ i, dist (x i) p ≤ r) : dist (∑ i, w i • x i) p ≤ r := by
  have he : (∑ i, w i • x i) - p = ∑ i, w i • (x i - p) := by
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hs, one_smul]
  rw [dist_eq_norm, he]
  calc
    _ ≤ ∑ i, ‖w i • (x i - p)‖ := norm_sum_le _ _
    _ ≤ ∑ i, w i * r := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw i)]
      exact mul_le_mul_of_nonneg_left (by simpa only [dist_eq_norm] using hx i) (hw i)
    _ = r := by rw [← Finset.sum_mul, hs, one_mul]

/-- The bottom cube has a nonempty open family of roots with strictly positive
facet barycentric coordinates. A generic root can be chosen in this family. -/
lemma bottomSeed_open_roots {d : ℕ} (h : ℝ) (hh : 0 < h) (p : Fin d → ℝ) :
    ∃ U : Set (Fin d → ℝ), IsOpen U ∧ U.Nonempty ∧
      ∀ q ∈ U, ∃ w : Fin (d + 2) → ℝ,
        (∀ k, 0 ≤ w k) ∧ (∀ k, k ≠ Fin.last (d + 1) → 0 < w k) ∧
        ∑ k, w k = 1 ∧ w (Fin.last (d + 1)) = 0 ∧
        ∑ k, w k • gridPoint h ((bottomSeed h p).vertex k) = embedSpatial q ∧
        dist (embedSpatial q) (embedSpatial p) ≤ 2 * h := by
  classical
  let F := bottomSeed h p
  let v : Fin (d + 1) → Fin d → ℝ := fun k ↦ spatial (h • F.point k.castSucc)
  have hv : LinearIndependent ℝ (fun k ↦ ((1 : ℝ), v k)) := by
    have hi := F.augmented_spatial_scaled Fin.castSucc (Fin.castSucc_injective _) hh.ne' 1
      (fun k ↦ by
        change h * F.point k.castSucc (Fin.last d) = 0
        rw [bottomSeed_time h p _ (Fin.castSucc_ne_last k), mul_zero])
    simpa only [one_smul] using hi
  let w₀ : Fin (d + 1) → ℝ := fun _ ↦ (d + 1 : ℝ)⁻¹
  have hw₀ : ∀ k, 0 < w₀ k := fun _ ↦ by dsimp [w₀]; positivity
  have hs₀ : ∑ k, w₀ k = 1 := by
    simp only [w₀, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    exact mul_inv_cancel₀ (by positivity)
  obtain ⟨U,hU,hq₀,hpos⟩ := positive_barycentric_neighborhood v hv (by simp) w₀ hw₀ hs₀
  refine ⟨U,hU,⟨_,hq₀⟩,?_⟩
  intro q hq
  obtain ⟨z,hz,hzs,he⟩ := hpos q hq
  let w : Fin (d + 2) → ℝ := Fin.snoc z 0
  have hw : ∀ k, 0 ≤ w k := by
    intro k
    refine Fin.lastCases ?_ (fun j ↦ ?_) k
    · simp [w]
    · simpa only [w,Fin.snoc_castSucc] using (hz j).le
  have hp : ∀ k, k ≠ Fin.last (d + 1) → 0 < w k := by
    intro k
    refine Fin.lastCases ?_ (fun j ↦ ?_) k
    · exact fun hk ↦ False.elim (hk rfl)
    · intro _
      simpa only [w,Fin.snoc_castSucc] using hz j
  have hs : ∑ k, w k = 1 := by
    rw [Fin.sum_univ_castSucc]
    simpa only [w,Fin.snoc_castSucc,Fin.snoc_last,add_zero] using hzs
  have hlast : w (Fin.last (d + 1)) = 0 := Fin.snoc_last _ _
  have hgrid (k : Fin (d + 1)) : gridPoint h (F.vertex k.castSucc) = embedSpatial (v k) := by
    rw [gridPoint_vertex]
    apply (embed_spatial_of_time_zero _ ?_).symm
    change h * F.point k.castSucc (Fin.last d) = 0
    rw [bottomSeed_time h p _ (Fin.castSucc_ne_last k), mul_zero]
  have hsum : ∑ k, w k • gridPoint h (F.vertex k) = embedSpatial q := by
    rw [Fin.sum_univ_castSucc]
    simp only [w, Fin.snoc_castSucc, Fin.snoc_last, zero_smul, add_zero, hgrid]
    rw [← he, map_sum]
    exact Finset.sum_congr rfl (fun k _ ↦ (map_smul embedSpatial (z k) (v k)).symm)
  refine ⟨w,hw,hp,hs,hlast,hsum,?_⟩
  rw [← hsum]
  apply dist_convex_sum_le w hw hs _ _ _
  intro k
  rw [gridPoint_vertex]
  exact bottomSeed_dist_point h hh p k

end SharpLiebThirring.CubeFlags

end
end
end
end

end OAI
