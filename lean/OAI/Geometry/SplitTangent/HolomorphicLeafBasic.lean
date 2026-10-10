import Mathlib
import OAI.Geometry.SplitTangent.TensorVanishing
import OAI.Geometry.SplitTangent.LeafJetAtlas
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.LeafPlaques

namespace OAI

/-! Holomorphic Leaf Basic. -/

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff
universe u
namespace SplitTangent
namespace AlignedProductChart
variable {X Y : ComplexManifold.{u}} {S : TangentSplitting X}
  {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]
  [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
  (P : AlignedProductChart S A B) {f : X.Carrier → Y.Carrier}
  (hf : ContMDiff (ModelWithCorners X) (ModelWithCorners Y) ω f)
  (hz : ∀x v,v∈S.first x → mfderiv (ModelWithCorners X) (ModelWithCorners Y) f x v=0)

include hf hz in
omit [CompleteSpace A] [CompleteSpace B] in
lemma map_plaque_eventually_constant {a : A} {b : B} (ht : (a,b)∈P.chart.target) :
    ∀ᶠ c in 𝓝 a,f (P.chart.symm (c,b))=f (P.chart.symm (a,b)) := by
  let g : A × B → Y.Carrier := f ∘ P.chart.symm
  let y := g (a,b)
  let Q := chartAt (Model Y) y
  have hy : y∈Q.source := mem_chart_source (Model Y) y
  have hQa : Q∈IsManifold.maximalAtlas (ModelWithCorners Y) ω Y.Carrier :=
    IsManifold.chart_mem_maximalAtlas y
  have hgn : ∀ᶠ z in 𝓝 (a,b),z∈P.chart.target ∧ g z∈Q.source :=
    Filter.Eventually.and (P.chart.open_target.mem_nhds ht)
      (((hf _).continuousAt.comp (P.inverse_holomorphicAt ht).continuousAt).preimage_mem_nhds
        (Q.open_source.mem_nhds hy))
  have hd : ∀ᶠ z in 𝓝 (a,b),DifferentiableAt ℂ (Q ∘ g) z := by
    filter_upwards [hgn] with z hz
    exact (((contMDiffAt_of_mem_maximalAtlas hQa hz.2).comp z
      ((hf _).comp z (P.inverse_holomorphicAt hz.1))).contDiffAt).differentiableAt (by simp)
  have hd0 : ∀ᶠ z in 𝓝 (a,b),∀v,fderiv ℂ (Q ∘ g) z (v,0)=0 := by
    filter_upwards [hgn] with z hzg
    intro v
    have hP := (P.inverse_holomorphicAt hzg.1).mdifferentiableAt (by simp)
    have hfz := (hf (P.chart.symm z)).mdifferentiableAt (by simp)
    have hQ := (contMDiffAt_of_mem_maximalAtlas hQa hzg.2).mdifferentiableAt (by simp)
    have hchain := mfderiv_comp z hQ (hfz.comp z hP)
    rw [mfderiv_eq_fderiv] at hchain
    rw [hchain]
    change mfderiv (ModelWithCorners Y) 𝓘(ℂ,Model Y) Q (g z)
      (mfderiv 𝓘(ℂ,A × B) (ModelWithCorners Y) g z (v,0))=0
    change mfderiv _ _ Q (g z)
      (mfderiv _ _ (f ∘ P.chart.symm) z (v,0))=0
    rw [mfderiv_comp z hfz hP]
    change mfderiv _ _ Q (g z)
      (mfderiv _ _ f (P.chart.symm z) (mfderiv _ _ P.chart.symm z (v,0)))=0
    rw [hz _ _ (P.inverse_first hzg.1 v),map_zero]
  have he := ProductTransition.eventually_factors_snd hd hd0
  have hc : Tendsto (fun c : A => (c,b)) (𝓝 a) (𝓝 (a,b)) :=
    continuousAt_id.prodMk continuousAt_const
  filter_upwards [hc.eventually hgn,hc.eventually he] with c hcg hce
  apply Q.injOn hcg.2 hy
  exact hce

include hf hz in
omit [CompleteSpace A] [CompleteSpace B] in
lemma map_plaque_constant {U : Set A} {b : B}
    (hU : IsPreconnected U) (ht : ∀a∈U,(a,b)∈P.chart.target)
    {a c : A} (ha : a∈U) (hc : c∈U) :
    f (P.chart.symm (a,b))=f (P.chart.symm (c,b)) := by
  let : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hU
  have hlocal : IsLocallyConstant (fun a : U => f (P.chart.symm (a.val,b))) := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro a
    exact continuous_subtype_val.continuousAt.eventually
      (P.map_plaque_eventually_constant hf hz (ht a.val a.property))
  exact hlocal.apply_eq_of_preconnectedSpace ⟨a,ha⟩ ⟨c,hc⟩

end AlignedProductChart
namespace LeafJetAtlas
variable {X Y : ComplexManifold.{u}} {S : TangentSplitting X} (L : LeafJetAtlas S)

lemma holomorphic_map_eq_on_leaf {f : X.Carrier → Y.Carrier}
    (hf : ContMDiff (ModelWithCorners X) (ModelWithCorners Y) ω f)
    (hz : ∀x v,v∈S.first x → mfderiv (ModelWithCorners X) (ModelWithCorners Y) f x v=0)
    {x y : X.Carrier} (hy : y∈L.leaf x) : f x=f y := by
  induction hy with
  | refl => rfl
  | @tail y z _ h ih =>
    obtain ⟨i,b,U,hU,hT,a,ha,c,hc,rfl,rfl⟩ := h
    exact ih.trans ((L.chart i).map_plaque_constant hf hz hU hT ha hc)

end LeafJetAtlas
end SplitTangent

end

end OAI
