import Mathlib
import OAI.Geometry.SplitTangent.TensorVanishing
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.TwistedCurveTensor
import OAI.Geometry.SplitTangent.HolomorphicManifoldProduct
import OAI.Geometry.SplitTangent.ManifoldLeafJets
import OAI.Geometry.SplitTangent.ManifoldJetAnalytic

namespace OAI

/-! Leaf Jet Atlas. -/

noncomputable section
open Set Filter Topology Bundle
open scoped Manifold ContDiff
universe u
namespace SplitTangent

 
structure LeafJetAtlas {X : ComplexManifold.{u}} (S : TangentSplitting X) where
  chart : ∀x, AlignedProductChart S (S.FirstModel x) (S.SecondModel x)
  mem_source : ∀x,x∈(chart x).chart.source

def TangentSplitting.leafJetAtlas {X : ComplexManifold.{u}} (S : TangentSplitting X)
    (hI₁ : Integrable X S.first) (hI₂ : Integrable X S.second) : LeafJetAtlas S where
  chart x := (S.exists_aligned_product_chart hI₁ hI₂ x).choose
  mem_source x := (S.exists_aligned_product_chart hI₁ hI₂ x).choose_spec.1

namespace LeafJetAtlas
variable {X : ComplexManifold.{u}} {S : TangentSplitting X} (A : LeafJetAtlas S)

abbrev jet (f : X.Carrier → ℂ) (y : X.Carrier) (m : ℕ) : TangentTensor X m :=
  (A.chart y).jet f y m

lemma jet_add {f h : X.Carrier → ℂ} {y : X.Carrier}
    (hf : ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,ℂ) ω f y)
    (hh : ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,ℂ) ω h y) (m : ℕ) :
    A.jet (f+h) y m=A.jet f y m+A.jet h y m :=
  (A.chart y).jet_add (A.mem_source y) hf hh m

lemma jet_csmul {f : X.Carrier → ℂ} {y : X.Carrier}
    (hf : ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,ℂ) ω f y) (m : ℕ) (c : ℂ) :
    A.jet (c • f) y m=c • A.jet f y m :=
  (A.chart y).jet_csmul (A.mem_source y) hf m c

@[simp] lemma jet_zero (y : X.Carrier) (m : ℕ) : A.jet 0 y m=0 :=
  (A.chart y).jet_zero y m

lemma jet_smul {f v : X.Carrier → ℂ} {y : X.Carrier}
    (hf : ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,ℂ) ω f y)
    (hv : ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,ℂ) ω v y)
    (m : ℕ) (hz : ∀n,n < m → A.jet f y n=0) :
    A.jet (fun x => v x*f x) y m=v y • A.jet f y m :=
  (A.chart y).jet_smul (A.mem_source y) hf hv m hz

lemma jet_congr {f h : X.Carrier → ℂ} {y : X.Carrier}
    (he : f=ᶠ[𝓝 y] h) (m : ℕ) : A.jet f y m=A.jet h y m :=
  (A.chart y).jet_congr (A.mem_source y) he m

lemma parameter_slice {f : ℂ × X.Carrier → ℂ} {z : ℂ} {y : X.Carrier}
    (hf : ContMDiffAt (𝓘(ℂ,ℂ).prod (ModelWithCorners X)) 𝓘(ℂ,ℂ) ω f (z,y)) :
    ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,ℂ) ω (fun x => f (z,x)) y :=
  hf.comp y (contMDiffAt_const.prodMk contMDiffAt_id)

 

theorem leading_analytic {g : ℂ → X.Carrier} {f : ℂ × X.Carrier → ℂ}
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g)
    (hf : ∀z,ContMDiffAt (𝓘(ℂ,ℂ).prod (ModelWithCorners X)) 𝓘(ℂ,ℂ) ω f (z,g z))
    (m : ℕ) (hz : ∀z n,n < m → A.jet (fun x => f (z,x)) (g z) n=0) (z₀ : ℂ) :
    AnalyticAt ℂ (tangentTensorCoordinates g
      (fun z => A.jet (fun x => f (z,x)) (g z) m) z₀) z₀ := by
  let P := A.chart (g z₀)
  have hp := P.jet_parameter_analytic (hg z₀) (A.mem_source _) (hf z₀) m
  apply hp.congr
  filter_upwards [(hg z₀).continuousAt.preimage_mem_nhds
    (P.chart.open_source.mem_nhds (A.mem_source _))] with z hPz
  have he := P.jet_independent (A.chart (g z)) hPz (A.mem_source _)
    (parameter_slice (hf z)) m (hz z)
  exact congrArg (fun t : TangentTensor X m =>
    tangentTensorCoordinates g (fun _ => t) z₀ z) he

lemma jet_supported (f : X.Carrier → ℂ) (y : X.Carrier) (m : ℕ)
    (v : Fin m → Tangent X y) :
    A.jet f y m (fun i => S.projector y (v i))=A.jet f y m v :=
  (A.chart y).jet_supported f (A.mem_source _) m v

lemma jet_symmetric {f : X.Carrier → ℂ} {y : X.Carrier}
    (hf : ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,ℂ) ω f y)
    (m : ℕ) (v : Fin m → Tangent X y) (σ : Equiv.Perm (Fin m)) :
    A.jet f y m (v ∘ σ)=A.jet f y m v :=
  (A.chart y).jet_symmetric (A.mem_source _) hf m v σ

end LeafJetAtlas
end SplitTangent

end

end OAI
