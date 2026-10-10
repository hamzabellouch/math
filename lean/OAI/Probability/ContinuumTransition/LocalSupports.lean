import OAI.Probability.ContinuumTransition.ActiveUniform

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

lemma supportOn_of_local {S : Set Parameter} {F : Parameter → ℝ}
    (hF : ConvexOn ℝ S F) {x v : Parameter} (hx : x ∈ S)
    (hl : ∀ᶠ y in 𝓝 x, F x+pDot v (y-x) ≤ F y) : SupportOn S F x v := by
  intro y hy
  let Z : ℝ → Parameter := fun c => (1-c) • x+c • y
  have hcont : Continuous Z := by dsimp [Z]; fun_prop
  have hZ : Tendsto Z (𝓝 (0:ℝ)) (𝓝 x) := by simpa [Z] using hcont.tendsto 0
  obtain ⟨c,hc,hc1,hcl⟩ : ∃ c : ℝ, 0 < c ∧ c < 1 ∧ F x+pDot v (Z c-x) ≤ F (Z c) := by
    have hmem : ∀ᶠ c in 𝓝[>] (0:ℝ), c ∈ Ioi 0 := self_mem_nhdsWithin
    have he : ∀ᶠ c in 𝓝[>] (0:ℝ),
        c ∈ Ioi 0 ∧ c < 1 ∧ F x+pDot v (Z c-x) ≤ F (Z c) :=
      hmem.and ((eventually_lt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds |>.and
        ((hZ.eventually hl).filter_mono nhdsWithin_le_nhds))
    exact he.exists
  have hc0 : 0 ≤ 1-c := by linarith
  have hh := hF.2 hx hy hc0 hc.le (show (1-c)+c=1 by ring)
  have he : pDot v (Z c-x) = c*pDot v (y-x) := by dsimp [Z,pDot]; ring
  rw [he] at hcl
  change F (Z c) ≤ (1-c)*F x+c*F y at hh
  have hh' : c*(F x+pDot v (y-x)) ≤ c*F y := by nlinarith only [hcl,hh]
  exact (mul_le_mul_iff_right₀ hc).mp (by simpa only [mul_comm] using hh')

lemma supportOn_of_ball {S : Set Parameter} {F : Parameter → ℝ}
    (hF : ConvexOn ℝ S F) {x v : Parameter} (hx : x ∈ S) {r : ℝ} (hr : 0 < r)
    (hl : SupportOn (ball x r) F x v) : SupportOn S F x v :=
  supportOn_of_local hF hx (mem_of_superset (ball_mem_nhds x hr) hl)

lemma support_of_interior_min {S : Set Parameter} {F : Parameter → ℝ}
    (hF : ConvexOn ℝ S F) {x g : Parameter} (hx : x ∈ S) {T : Set Parameter}
    (hT : T ∈ 𝓝 x) (hmin : ∀ y ∈ T, F x-pDot g x ≤ F y-pDot g y) :
    SupportOn S F x g := by
  apply supportOn_of_local hF hx
  filter_upwards [hT] with y hy
  have hh := hmin y hy
  dsimp [pDot] at *
  linarith only [hh]

end ContinuumTemperature
end
end

end OAI
