import Mathlib
import OAI.Analysis.SymmetricDomains.EventuallyImageBallNonzero
import OAI.Analysis.SymmetricDomains.HomeomorphInverse

namespace OAI

open Set Metric Complex
open scoped Topology
namespace Release061
open Set Filter Metric
open scoped Topology

theorem holomorphicOnSubset_of_analyticOnNhd_open {n m : ℕ}
    {S : Set (Affine n)} (hS : IsOpen S) {f : Affine n → Affine m}
    (hf : AnalyticOnNhd ℂ f S) : HolomorphicOnSubset S (fun x => f x) := by
  intro p
  exact ⟨S,hS,p.property,f,hf,fun _ _ => rfl⟩

theorem scaling_biholomorph_open_domain {n : ℕ}
    {S O : Set (Affine n)} {y₀ : Affine n} (hy₀ : y₀ ∈ O)
    (hS : IsOpen S) (hconn : IsPreconnected S) (hO : IsOpen O)
    {T : ℕ → Set (Affine n)}
    {f g : ℕ → Affine n → Affine n} {F G : Affine n → Affine n}
    (hf : TendstoLocallyUniformlyOn f F atTop S)
    (hg : TendstoLocallyUniformlyOn g G atTop (connectedComponentIn O y₀))
    (hfhol : ∀ x ∈ S, ∃ W ∈ 𝓝 x, ∀ᶠ j in atTop,
      AnalyticOnNhd ℂ (f j) W ∧ ∀ z ∈ W, (fderiv ℂ (f j) z).det ≠ 0)
    (hghol : ∀ y ∈ connectedComponentIn O y₀, ∃ W ∈ 𝓝 y,
      ∀ᶠ j in atTop, AnalyticOnNhd ℂ (g j) W)
    (hfmap : ∀ K : Set (Affine n), IsCompact K → K ⊆ S →
      ∀ᶠ j in atTop, MapsTo (f j) K (T j))
    (hGmap : MapsTo G (connectedComponentIn O y₀) S)
    (hgmap : ∀ y ∈ connectedComponentIn O y₀, ∀ᶠ j in atTop, g j y ∈ S)
    (hright : ∀ y ∈ connectedComponentIn O y₀, ∀ᶠ j in atTop, f j (g j y) = y)
    (hleft : ∀ x ∈ S, ∀ᶠ j in atTop, g j (f j x) = x)
    (hexcluded : ∀ y ∉ O, ∃ a : ℕ → Affine n,
      Tendsto a atTop (𝓝 y) ∧ ∀ᶠ j in atTop, a j ∉ T j) :
    Nonempty (Biholomorph S (connectedComponentIn O y₀)) := by
  have hD := hO.connectedComponentIn (x := y₀)
  have hfdiff : ∀ x ∈ S, ∃ W ∈ 𝓝 x, ∀ᶠ j in atTop, DifferentiableOn ℂ (f j) W := by
    intro x hx
    obtain ⟨W,hW,he⟩ := hfhol x hx
    exact ⟨W,hW,he.mono fun _ h => h.1.differentiableOn⟩
  have hgdiff : ∀ y ∈ connectedComponentIn O y₀, ∃ W ∈ 𝓝 y,
      ∀ᶠ j in atTop, DifferentiableOn ℂ (g j) W := by
    intro y hy
    obtain ⟨W,hW,he⟩ := hghol y hy
    exact ⟨W,hW,he.mono fun _ h => h.differentiableOn⟩
  have hFd := differentiableOn_of_locally_uniform_limit hS hf hfdiff
  have hGd := differentiableOn_of_locally_uniform_limit hD hg hgdiff
  have hFa := analyticOnNhd_of_differentiableOn_affine hS hFd
  have hGa := analyticOnNhd_of_differentiableOn_affine hD hGd
  have hri : ∀ y ∈ connectedComponentIn O y₀, F (G y) = y := by
    intro y hy
    have ht : Tendsto (fun j => g j y) atTop (𝓝[S] G y) :=
      tendsto_nhdsWithin_iff.mpr ⟨hg.tendsto_at hy,hgmap y hy⟩
    have hcomp := hf.tendsto_comp (hFa.continuousOn (G y) (hGmap hy)) (hGmap hy) ht
    exact tendsto_nhds_unique hcomp
      (tendsto_const_nhds.congr' ((hright y hy).mono fun _ h => h.symm))
  have hbase : y₀ ∈ connectedComponentIn O y₀ := mem_connectedComponentIn hy₀
  have hanchor := jacobian_ne_zero_of_right_inverse hS hD hFd hGd hGmap hri hbase
  have hfull := jacobian_nonzero_of_anchor hS hconn hf hfhol ⟨G y₀,hGmap hbase,hanchor⟩
  have hfh : ∀ x ∈ S, ∃ W ∈ 𝓝 x, ∀ᶠ j in atTop, AnalyticOnNhd ℂ (f j) W := by
    intro x hx
    obtain ⟨W,hW,he⟩ := hfhol x hx
    exact ⟨W,hW,he.mono fun _ h => h.1⟩
  have hstable : ∀ x ∈ S, ∃ r > 0, ∀ᶠ j in atTop, ball (F x) r ⊆ T j := by
    intro x hx
    obtain ⟨r,hr,R,hR,hRS,he⟩ :=
      eventually_image_ball_of_nonzero_jacobian hS hf hfh hx (hfull x hx)
    refine ⟨r,hr,?_⟩
    filter_upwards [he,hfmap (closedBall x R) (isCompact_closedBall x R) hRS] with j hj hm
    intro y hy
    obtain ⟨z,hz,rfl⟩ := hj hy
    exact hm hz
  have hmaps := mapsTo_of_stable_balls_and_excluded_points hstable hexcluded
  obtain ⟨hFm,hri',hli⟩ := inverse_limit_component hy₀ hconn hD hf hg
    hFa.continuousOn hGa.continuousOn hGmap hgmap hright hleft hmaps
  refine ⟨⟨homeomorphOfInverseOn hFa.continuousOn hGa.continuousOn hFm hGmap hli hri', ?_, ?_⟩⟩
  · exact holomorphicOnSubset_of_analyticOnNhd_open hS hFa
  · exact holomorphicOnSubset_of_analyticOnNhd_open hD hGa

end Release061

noncomputable section


end

end OAI
