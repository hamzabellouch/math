import OAI.Probability.ContinuumTransition.ScaledLocalization

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

lemma three_group_persistence {F : Parameter → ℝ} (hF : ConvexOn ℝ pressureDomain F)
    {x g : Parameter} (hx : x ∈ pressureDomain) {r γ : ℝ} (hr : 0 < r) (hγ : 0 < γ)
    (hball : ball x r ⊆ pressureDomain)
    (hsl : closedBall g γ ⊆ subgradients pressureDomain F x)
    {K : Fin 3 → Set Parameter} (hc : ∀ i, Convex ℝ (K i))
    (hsep : ∀ i j, i ≠ j → Disjoint (Prod.snd '' K i) (Prod.snd '' K j))
    (hK : subgradients pressureDomain F x = convexHull ℝ (⋃ i, K i))
    {v : Fin 3 → Parameter} {b ε : ℝ} (hε : 0 < ε)
    (hKv : ∀ i, K i ⊆ closedBall (v i) b) (C D : ℝ) :
    ∃ S > 0, ∃ δ > 0, ∀ a : ℝ, 0 < a → a < δ → ∀ Q P : Parameter → ℝ,
      ConvexOn ℝ pressureDomain Q → IsMeanField Q a P →
      (∀ y ∈ pressureDomain, ∃ d, quadraticCost Q a y d=P y) →
      (∀ y ∈ ball x r, |Q y-F y| ≤ a^2) → P x ≤ Q x+C*a →
      (∀ y ∈ ball x r, ∀ w ∈ activeLifts Q a P y, |w.2| ≤ D) →
      ∃ z ∈ ball x (S*a), z ∈ ball x r ∧ SupportOn pressureDomain P z g ∧
        subgradients pressureDomain P z = convexHull ℝ (⋃ i, slopeGroups P z v (b+ε) i) := by
  let S : ℝ := (|C|+3)/γ
  have hS : 0 < S := div_pos (by positivity) hγ
  have hCS : C+2 < γ*S := by
    have he : γ*S=|C|+3 := by dsimp [S]; field_simp
    rw [he]
    linarith only [le_abs_self C]
  let U := ⋃ i, ball (v i) (b+ε)
  have hU : IsOpen U := isOpen_iUnion (fun i => isOpen_ball)
  have hKU : (⋃ i, K i) ⊆ U := by
    intro w hw
    obtain ⟨i,hi⟩ := mem_iUnion.mp hw
    exact mem_iUnion.mpr ⟨i,lt_of_le_of_lt (hKv i hi) (show b < b+ε by linarith)⟩
  obtain ⟨δ,hδ,hloc⟩ := scaled_localization hF hx hr hball K hc hsep hK hU hKU S D
  refine ⟨S,hS,min 1 (min (r/S) δ),lt_min zero_lt_one (lt_min (div_pos hr hS) hδ),?_⟩
  intro a ha had Q P hQ hP hatt happ hgain hD
  have ha1 := had.trans_le (min_le_left _ _)
  have haδ := had.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have har := had.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hSa : S*a < r := by nlinarith only [(lt_div_iff₀ hS).mp har]
  obtain ⟨z,hz,hg⟩ := nearby_center_support hF (meanField_convex hQ hP) hx hγ hS ha ha1 hCS hSa hball
    (fun w hw => hsl hw) happ (fun y hy => meanField_ge_base hP (hball hy)) hgain
  have hzr : z ∈ ball x r := hz.trans hSa
  let Ξ := a⁻¹ • (z-x)
  have hrep : x+a • Ξ=z := by
    dsimp [Ξ]
    rw [smul_smul,mul_inv_cancel₀ ha.ne',one_smul,add_sub_cancel]
  have hΞ : ‖Ξ‖ ≤ S := by
    dsimp [Ξ]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ha),← div_eq_inv_mul]
    apply (div_le_iff₀ ha).mpr
    have hzl : dist z x ≤ S*a := le_of_lt hz
    simpa only [← dist_eq_norm_sub] using hzl
  refine ⟨z,hz,hzr,hg,regroup_active ha hQ hP hatt (hball hzr) ?_⟩
  intro w hw
  have he := hloc a ha haδ Q P hQ hP happ Ξ hΞ (hrep.symm ▸ hball hzr) w (hrep.symm ▸ hw)
    (hD z hzr w hw)
  change w ∈ ⋃ i, ball (v i) (b+ε) at he
  obtain ⟨i,hi⟩ := mem_iUnion.mp he
  apply mem_iUnion.mpr
  refine ⟨i,?_⟩
  change dist w (v i) ≤ b+ε
  exact le_of_lt hi

end ContinuumTemperature
end
end

end OAI
