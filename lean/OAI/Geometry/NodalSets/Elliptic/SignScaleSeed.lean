import OAI.Geometry.NodalSets.Elliptic.RescaledSeedDecay
import OAI.Geometry.NodalSets.Waves.LocalCovarianceGeometry

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

def sourceSignScale (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (S : Coord → ℝ)
    (x : Coord) : ℝ := Real.sqrt (g x (metricGradient g S x) (metricGradient g S x)+4)

lemma sourceSignScale_ge_two {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ}
    {S : Coord → ℝ} {x : Coord} (hp : 0 ≤ g x (metricGradient g S x) (metricGradient g S x)) :
    2 ≤ sourceSignScale g S x := by
  unfold sourceSignScale
  apply (Real.le_sqrt (by norm_num) (by linarith)).mpr
  nlinarith

variable {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w S : Coord → ℝ}
variable {D U : Set Coord} {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

include a in
lemma source_sign_scale_lower : ∀ x ∈ D, 2 ≤ sourceSignScale g S x := by
  obtain ⟨μ,hμ,B,hB,hgeom⟩ := a.original_covariance_geometry
  intro x hx
  exact sourceSignScale_ge_two ((by positivity : 0 ≤ μ*‖metricGradient g S x‖^2).trans
    ((hgeom x hx).2.2 _))

theorem sign_scale_seed_decay (hUD : U ⊆ D) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {Q : Set Coord} (hQ : IsCompact Q) (hQU : Q ⊆ U)
    (hS : ContDiff ℝ ∞ S) (S0 T0 : Coord → ℝ)
    (hS0 : ContDiff ℝ ∞ S0) (hT0 : ContDiff ℝ ∞ T0)
    (δ : ℝ) (hδ : 0 < δ) (hgap : ∀ x ∈ Q, S0 x+δ ≤ S x)
    (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n), letI := hfin
      ∀ x ∈ Q, ∀ v : Coord, sourceEuclideanNorm v ≤ 2 → ∀ k : Fin (d+1),
        ‖iteratedFDeriv ℝ k.val
          (rescaledSeed S0 T0 S n (sourceSignScale g S x) (a.latticeSigma hUD n x) x) v‖ ≤ ε := by
  have hall := Filter.eventually_all.mpr (fun k : Fin (d+1) ↦
    a.rescaled_seed_decay hUD hU hUb hQ hQU hS S0 T0 hS0 hT0 δ hδ hgap 2 (by norm_num) k.val ε hε)
  filter_upwards [hall] with n hn
  obtain ⟨hfin,_⟩ := hn ⟨0,by omega⟩
  let := hfin
  refine ⟨hfin,?_⟩
  intro x hx v hv k
  obtain ⟨hfin',hb⟩ := hn k
  have he : hfin' = hfin := Subsingleton.elim _ _
  subst hfin'
  exact hb x hx _ (by linarith [a.source_sign_scale_lower x (hUD (hQU hx))]) v
    ((norm_le_sourceEuclideanNorm v).trans hv)

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
