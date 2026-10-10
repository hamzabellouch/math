import OAI.Analysis.AncientFlat.Profile.RadialBilaplacian
import OAI.Analysis.AncientFlat.Profile.AnnularProfileCore

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff Laplacian Topology
namespace FlatRadial
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

def scalarF (h : ℝ → ℝ) (t y : ℝ) : ℝ := (Real.sqrt (-t))⁻¹*h (y/Real.sqrt (-t))
def originalB (G h : ℝ → ℝ) (t : ℝ) (x : V) : ℝ :=
  2*‖x‖^2*G (‖x‖^2/Real.sqrt (-t))*(Δ (Δ (lift (V := V) (scalarF h t))) x/16)
lemma positive_smooth {h : ℝ → ℝ} (hh : ContDiffOn ℝ ∞ h (Ici 0)) {y : ℝ} (hy : 0<y) :
    ContDiffAt ℝ ∞ h y := (hh y hy.le).contDiffAt (Ici_mem_nhds hy)
lemma G_deriv (G h : ℝ → ℝ) (_hG : ContDiffOn ℝ ∞ G (Ici 0))
    (hh : ContDiffOn ℝ ∞ h (Ici 0)) (hid : ∀ y : ℝ, 0<y → G y=1+y*h y)
    {y : ℝ} (hy : 0<y) : deriv G y=h y+y*deriv h y := by
  have he : G=ᶠ[𝓝 y] (fun z => 1+z*h z) := by
    filter_upwards [isOpen_Ioi.mem_nhds hy] with z hz
    exact hid z hz
  have hdh := ((positive_smooth hh hy).differentiableAt (by simp)).hasDerivAt
  have hd := (hasDerivAt_const y (1:ℝ)).add ((hasDerivAt_id y).mul hdh)
  change HasDerivAt (fun z : ℝ => 1+z*h z) _ y at hd
  have hs := he.deriv_eq
  rw [hs,hd.deriv]
  simp
lemma scalarF_spatial (h : ℝ → ℝ) (hh : ContDiffOn ℝ ∞ h (Ici 0))
    {t y : ℝ} (ht : t<0) (hy : 0<y) : ContDiffAt ℝ 4 (scalarF h t) y := by
  have hr : 0<Real.sqrt (-t) := Real.sqrt_pos.2 (neg_pos.mpr ht)
  have hc : ContDiffAt ℝ ∞ (fun z : ℝ => z/Real.sqrt (-t)) y := contDiffAt_id.div_const _
  have hf : ContDiffAt ℝ ∞ (scalarF h t) y := contDiffAt_const.mul ((positive_smooth hh (div_pos hy hr)).comp y hc)
  exact hf.of_le (show (4:ℕ∞ω)≤∞ from WithTop.coe_le_coe.mpr le_top)
lemma scalarF_time (G h : ℝ → ℝ) (hG : ContDiffOn ℝ ∞ G (Ici 0))
    (hh : ContDiffOn ℝ ∞ h (Ici 0)) (hid : ∀ y : ℝ, 0<y → G y=1+y*h y)
    {t y : ℝ} (ht : t<0) (hy : 0<y) :
    HasDerivAt (fun r => scalarF h r y)
      (deriv G (y/Real.sqrt (-t))/(2*(Real.sqrt (-t))^3)) t := by
  have hp : 0< -t := neg_pos.mpr ht
  have hr : 0<Real.sqrt (-t) := Real.sqrt_pos.2 hp
  have hn : Real.sqrt (-t)≠0 := ne_of_gt hr
  have hs := ((hasDerivAt_id t).neg).sqrt (ne_of_gt hp)
  have hq := (hasDerivAt_const t y).div hs hn
  have hd := ((positive_smooth hh (div_pos hy hr)).differentiableAt (by simp)).hasDerivAt.comp t hq
  have hf := (hs.inv hn).mul hd
  convert! hf using 1
  rw [G_deriv G h hG hh hid (div_pos hy hr)]
  dsimp
  field_simp
  ring
end FlatRadial

end

end OAI
