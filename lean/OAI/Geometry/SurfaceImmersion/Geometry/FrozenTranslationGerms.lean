import OAI.Geometry.SurfaceImmersion.Whitney.FixedSurfacePairPatch

namespace OAI

/-! Translation germs on frozen closed neighborhoods are retained by
finite compositions of the constructed scalar translation families. -/
noncomputable section
open Set Filter
open scoped Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M ι : Type*} [TopologicalSpace M]

def FrozenTranslationGerms (A : ι → Set M) (f g : M → ProjectionTarget 3) : Prop :=
  ∀ i, ∃ c : ProjectionTarget 3, g =ᶠ[𝓝ˢ (A i)] (fun x => f x+c)

lemma frozenTranslationGerms_refl (A : ι → Set M) (f : M → ProjectionTarget 3) :
    FrozenTranslationGerms A f f := by
  intro i
  exact ⟨0,Filter.Eventually.of_forall fun _ => (add_zero _).symm⟩

lemma FrozenTranslationGerms.trans {A : ι → Set M} {f g h : M → ProjectionTarget 3}
    (hfg : FrozenTranslationGerms A f g) (hgh : FrozenTranslationGerms A g h) :
    FrozenTranslationGerms A f h := by
  intro i
  obtain ⟨a,ha⟩ := hfg i
  obtain ⟨b,hb⟩ := hgh i
  refine ⟨a+b,?_⟩
  filter_upwards [ha,hb] with x hax hbx
  rw [hbx,hax,add_assoc]

lemma frozenTranslationGerms_translate {A : ι → Set M} {χ : M → ℝ}
    (hχ : ∀ i, (χ =ᶠ[𝓝ˢ (A i)] (fun _ => 0)) ∨ (χ =ᶠ[𝓝ˢ (A i)] (fun _ => 1)))
    (f : M → ProjectionTarget 3) (a : ProjectionTarget 3) :
    FrozenTranslationGerms A f (surfaceTranslation f χ a) := by
  intro i
  rcases hχ i with h0 | h1
  · refine ⟨0,?_⟩
    filter_upwards [h0] with x hx
    simp only [surfaceTranslation,hx,zero_smul]
  · refine ⟨a,?_⟩
    filter_upwards [h1] with x hx
    simp only [surfaceTranslation,hx,one_smul]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
