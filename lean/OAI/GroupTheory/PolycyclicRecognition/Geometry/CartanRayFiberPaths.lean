import OAI.GroupTheory.PolycyclicRecognition.Algebra.RayIdealTemplates
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBoxPaths
import OAI.GroupTheory.PolycyclicRecognition.Analysis.NegativePathWords

namespace OAI

/-! # Actual paths between ideal-fiber representatives at negative height

A fixed ideal element enters the expanding mixed-word box. Its support path
can be based at the ray pivot even though the template does not contain zero.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Filter
open scoped Manifold Topology

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

include hunimod in
/-- Every fixed ray-ideal displacement can be realized at linearly negative
height by an actual path with linear coarse speed and logarithmic error.
The path constant is independent of the ideal displacement; the threshold
is allowed to depend on it. -/
theorem exists_negative_height_ideal_fiber_paths
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (π : G →* Multiplicative W)
    (hπ : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (α : W →L[ℝ] ℝ) (v₀ : W) (hα : α v₀ < 0) :
    let αH := α.toLinearMap.comp
      (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype))
    let h₀ := cartanHeightSection T H (eW.symm v₀)
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : M.coneWordIdeal (positiveWeightRay αH),
      ∀ᶠ n : ℕ in atTop,
        ∃ γ : Path (Exp ((n : ℝ) • (h₀ : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
          (F.inclusionN (F.ExpN (F.N.equiv (x : cartanRootIdeal H))) *
            Exp ((n : ℝ) • (h₀ : GroupLieAlgebra (𝓘(ℝ, EG)) G))),
          PathMetricBound γ (C * n) (C * (1 + Real.log (2 + n))) ∧
          ∀ t, α ((π (γ t)).toAdd) ≤ (n : ℝ) * α v₀ := by
  dsimp only
  let αH := α.toLinearMap.comp
    (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype))
  let h₀ := cartanHeightSection T H (eW.symm v₀)
  obtain ⟨E, hE, hconv, hv₀, hnegative, hpositive⟩ :=
    M.exists_negative_ray_ideal_template T hunimod eW α v₀ hα
  obtain ⟨β, hβ⟩ := exists_maximizing_wordBasis M.letter M.wordList b₀
    (M.boxCost T hunimod eW E)
  let A := ‖(finBasis ℝ H).equivFun h₀‖
  have hA : 0 ≤ A := norm_nonneg _
  obtain ⟨C, hC, hpaths⟩ := M.exists_cartan_box_path_bound T F hunimod eW hExp realize
    haarN haarD dynkinN dynkinD π hπ b₀ hE hconv hv₀ 1 hA 1
  refine ⟨C, hC, ?_⟩
  intro x
  have hsmall := M.fixed_ideal_polynomial_box_norm_tendsto_zero T hunimod eW
    (positiveWeightRay αH) E hpositive b₀ (fun _ => β) (fun _ => hβ) x 1 zero_le_one 0
  have hnsmall : ∀ᶠ n : ℕ in atTop,
      ‖(M.boxBasis T hunimod eW E β n).equivFun (x : cartanRootIdeal H)‖ ≤ 1 := by
    simpa only [pow_zero, mul_one, one_mul] using
      (hsmall.eventually (eventually_lt_nhds zero_lt_one)).mono (fun _ h => h.le)
  filter_upwards [hnsmall] with n hn
  have hnorm : ‖(finBasis ℝ H).equivFun ((n : ℝ) • h₀)‖ ≤ A * (1 + n) ^ 1 := by
    rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n)]
    change (n : ℝ) * A ≤ _
    nlinarith
  have hheight : (π (Exp (((n : ℝ) • h₀ : H) : GroupLieAlgebra (𝓘(ℝ, EG)) G))).toAdd =
      (n : ℝ) • v₀ := by
    rw [hπ]
    simp [h₀]
  obtain ⟨γ, hγ, hγheight⟩ := hpaths n (Nat.cast_nonneg n) ((n : ℝ) • h₀)
    hnorm hheight β hβ (F.ExpN (F.N.equiv (x : cartanRootIdeal H)))
    ⟨(x : cartanRootIdeal H), rfl, hn⟩
  refine ⟨γ, hγ, ?_⟩
  intro t
  obtain ⟨w, hw, he⟩ := hγheight t
  rw [he, map_smul, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (hnegative w hw) (Nat.cast_nonneg n)

include hunimod in
/-- Unit-step representatives of the actual ideal-fiber difference.
Every prefix retains a negative linear height margin, and remains in a
linear ball about the ray pivot. -/
theorem exists_negative_height_ideal_fiber_words
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (π : G →* Multiplicative W)
    (hπ : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
    {Kπ : ℝ} (hKπ : 0 ≤ Kπ)
    (hLip : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ Kπ * dist x y)
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (α : W →L[ℝ] ℝ) (v₀ : W) (hα : α v₀ < 0) :
    let αH := α.toLinearMap.comp
      (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype))
    let d := fun n : ℕ => Exp ((n : ℝ) •
      (cartanHeightSection T H (eW.symm v₀) : GroupLieAlgebra (𝓘(ℝ, EG)) G))
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x : M.coneWordIdeal (positiveWeightRay αH),
      ∀ᶠ n : ℕ in atTop, ∃ w : List G,
        (∀ g ∈ w, g ∈ Metric.closedBall (1 : G) 1) ∧
        w.prod = (d n)⁻¹ * (F.inclusionN (F.ExpN (F.N.equiv
          (x : cartanRootIdeal H))) * d n) ∧
        (w.length : ℝ) ≤ R * (1 + n) ^ 2 ∧ ∀ j : ℕ,
          α ((π (d n * (w.take j).prod)).toAdd) ≤ (α v₀ / 2) * n ∧
          dist (d n) (d n * (w.take j).prod) ≤ R * n := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  dsimp only
  obtain ⟨C, hC, hp⟩ := M.exists_negative_height_ideal_fiber_paths T F hunimod eW
    hExp realize haarN haarD dynkinN dynkinD π hπ b₀ α v₀ hα
  let R := 5 + (C + 1) * (3 * C + 2) + 7 * C
  have hR : 0 ≤ R := by dsimp [R]; positivity
  refine ⟨R, hR, ?_⟩
  intro x
  let d := fun n : ℕ => Exp ((n : ℝ) •
    (cartanHeightSection T H (eW.symm v₀) : GroupLieAlgebra (𝓘(ℝ, EG)) G))
  let target := fun n => F.inclusionN (F.ExpN (F.N.equiv
    (x : cartanRootIdeal H))) * d n
  have hscalar (a b : G) : |α ((π a).toAdd) - α ((π b).toAdd)| ≤
      (‖α‖ * Kπ) * dist a b := by
    calc
      _ = ‖α ((π a).toAdd - (π b).toAdd)‖ := by rw [map_sub, Real.norm_eq_abs]
      _ ≤ ‖α‖ * ‖(π a).toAdd - (π b).toAdd‖ := α.le_opNorm _
      _ ≤ ‖α‖ * (Kπ * dist a b) := mul_le_mul_of_nonneg_left (hLip a b) (norm_nonneg _)
      _ = _ := by ring
  have he := eventually_negative_path_unit_words hpath
    (fun g => α ((π g).toAdd)) (mul_nonneg (norm_nonneg _) hKπ) hC
    (by linarith : 0 < -α v₀) hscalar d target (by
      filter_upwards [hp x] with n hn
      obtain ⟨γ, hγ, hheight⟩ := hn
      exact ⟨γ, hγ, fun t => by have hh := hheight t; linarith⟩)
  filter_upwards [he] with n hn
  obtain ⟨w, hw, hprod, hlen, hprefix⟩ := hn
  refine ⟨w, hw, hprod, hlen.trans ?_, ?_⟩
  · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    dsimp [R]
    linarith
  · intro j
    refine ⟨?_, (hprefix j).2.trans ?_⟩
    · (convert (hprefix j).1 using 1; ring)
    · apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg n)
      dsimp [R]
      nlinarith

include hunimod in
/-- Actual chains for ideal-fiber independence, with an absolute linear
radius and the canonical negative-height margin. -/
theorem exists_negative_height_ideal_fiber_chains
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (π : G →* Multiplicative W)
    (hπ : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
    {Kπ : ℝ} (hKπ : 0 ≤ Kπ)
    (hLip : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ Kπ * dist x y)
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (α : W →L[ℝ] ℝ) (v₀ : W) (hα : α v₀ < 0) :
    let αH := α.toLinearMap.comp
      (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype))
    let d := fun n : ℕ => Exp ((n : ℝ) •
      (cartanHeightSection T H (eW.symm v₀) : GroupLieAlgebra (𝓘(ℝ, EG)) G))
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x : M.coneWordIdeal (positiveWeightRay αH),
      ∃ (m : ℕ → ℕ) (z : ℕ → ℕ → G),
        (∀ n, z n 0 = d n) ∧
        (∀ᶠ n in atTop, z n (m n) =
          F.inclusionN (F.ExpN (F.N.equiv (x : cartanRootIdeal H))) * d n) ∧
        (∀ᶠ n in atTop, (m n : ℝ) ≤ R * (1 + n) ^ 2) ∧
        (∀ᶠ n in atTop, ∀ i ≤ m n,
          α ((π (z n i)).toAdd) ≤ (α v₀ / 2) * n) ∧
        (∀ᶠ n in atTop, ∀ i ≤ m n, dist 1 (z n i) ≤ R * n) ∧
        ∀ᶠ n in atTop, ∀ i < m n, dist (z n i) (z n (i + 1)) ≤ 1 := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  dsimp only
  obtain ⟨C, hC, hwords⟩ := M.exists_negative_height_ideal_fiber_words T F hunimod eW
    hExp realize haarN haarD dynkinN dynkinD π hπ hKπ hLip hpath b₀ α v₀ hα
  let h₀ := (cartanHeightSection T H (eW.symm v₀) : GroupLieAlgebra (𝓘(ℝ, EG)) G)
  let d := fun n : ℕ => Exp ((n : ℝ) • h₀)
  let D := dist (1 : G) (Exp h₀)
  have hD : 0 ≤ D := dist_nonneg
  have hbase (n : ℕ) : dist 1 (d n) ≤ D * n := by
    have hh := one_parameter_nat_dist_le (fun t : ℝ => Exp (t • h₀))
      (by simpa only [zero_smul] using hExp.map_zero) (hExp.map_add_smul h₀) n
    simpa only [one_smul, mul_comm, d, D] using hh
  refine ⟨D + C, add_nonneg hD hC, ?_⟩
  intro x
  have hw := hwords x
  have hw' : ∀ᶠ n : ℕ in atTop, ∃ w : List G,
      (∀ g ∈ w, g ∈ Metric.closedBall (1 : G) 1) ∧
      w.prod = (d n)⁻¹ * (F.inclusionN (F.ExpN (F.N.equiv
        (x : cartanRootIdeal H))) * d n) ∧
      (w.length : ℝ) ≤ C * (1 + n) ^ 2 ∧ ∀ i : ℕ,
        α ((π (d n * (w.take i).prod)).toAdd) ≤ -(-α v₀ / 2) * n ∧
        dist (d n) (d n * (w.take i).prod) ≤ C * n := by
    filter_upwards [hw] with n hn
    obtain ⟨w, hu, hp, hl, hs⟩ := hn
    refine ⟨w, hu, hp, hl, ?_⟩
    intro i
    exact ⟨by have hh := (hs i).1; linarith, (hs i).2⟩
  obtain ⟨m, z, hz0, hzend, hlen, hheight, hball, hsteps⟩ :=
    exists_negative_word_prefix_chains (fun g => α ((π g).toAdd)) d
      (fun n => F.inclusionN (F.ExpN (F.N.equiv (x : cartanRootIdeal H))) * d n) hbase hw'
  refine ⟨m, z, hz0, hzend, ?_, ?_, hball, hsteps⟩
  · filter_upwards [hlen] with n hn
    exact hn.trans (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _))
  · filter_upwards [hheight] with n hn
    intro i hi
    have hh := hn i hi
    linarith

end PolycyclicRecognition.CartanWordModel

end

end OAI
