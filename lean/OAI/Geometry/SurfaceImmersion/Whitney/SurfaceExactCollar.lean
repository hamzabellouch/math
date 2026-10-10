import OAI.Geometry.SurfaceImmersion.Whitney.SupportedExactCollar
import OAI.Geometry.SurfaceImmersion.Atlas.CoordinateRegularReplacement

namespace OAI

/-! Transfer of the exact supported collar interpolation to the actual
surface, retaining its singular set and exterior germs. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [T2Space M]

theorem surface_exact_collar (c : OpenPartialHomeomorph M Base)
    (hcs : ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ c c.source)
    (hci : ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ c.symm c.target)
    {f : M → ProjectionTarget 3} (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    {φ ψ : Base → ProjectionTarget 3} {V : ℝ × ℝ → ProjectionTarget 3}
    (hφ : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ ψ) (hV : ContDiff ℝ ∞ V)
    (haxisValue : ∀ t, φ (crosscapAxis t) = ψ (crosscapAxis t))
    (hV0 : ∀ t, V (0,t) = axisTransverse φ t)
    (hV1 : ∀ t, V (1,t) = axisTransverse ψ t)
    {a b : ℝ} (hab : a ≤ b)
    (hI : ∀ s ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc a b,
      Function.Injective (homotopyCollarJet (axisValue φ) V s t 0 0))
    (hstation : ∀ x : Base, x 1 ∉ Ioo a b → ψ x = φ x ∧
      ∀ s ∈ Icc (0:ℝ) 1, V (s,x 1) = axisTransverse φ (x 1))
    {U : Set Base} (hU : IsOpen U) (hUt : U ⊆ c.target)
    (haxis : ∀ t ∈ Icc a b, crosscapAxis t ∈ U)
    (hmatch : EqOn φ (f ∘ c.symm) U) :
    ∃ (g : M → ProjectionTarget 3) (L : Set M),
      ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ g ∧ IsCompact L ∧
      L ⊆ c.symm '' U ∧
      (∀ x, Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) g x) ↔
        Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x)) ∧
      (∀ x ∉ L, g =ᶠ[𝓝 x] f) ∧
      ∀ t ∈ Icc a b, g =ᶠ[𝓝 (c.symm (crosscapAxis t))] ψ ∘ c := by
  obtain ⟨F,K,hF,hK,hKU,hreg,hout,hinner⟩ :=
    supported_exact_collar hφ hψ hV haxisValue hV0 hV1 hab hI hstation hU haxis
  let Q := F-φ
  have hQ : ContDiff ℝ ∞ Q := hF.sub hφ
  have hs : tsupport Q ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hn
    have he := (hout x hn).self_of_nhds
    exact hx (sub_eq_zero.mpr he)
  have hQc : HasCompactSupport Q := hK.of_isClosed_subset (isClosed_tsupport Q) hs
  have hsum : φ+Q = F := by
    funext x
    change φ x + (F x-φ x) = F x
    abel
  obtain ⟨g,hg,hgreg,hgout,hglocal⟩ := coordinate_regular_replacement c hcs hci hf hQ
    hQc hU hUt (hs.trans hKU) hmatch (fun x _ => by rw [hsum]; exact hreg x)
  let L := c.symm '' K
  have hKt : K ⊆ c.target := hKU.trans hUt
  have hL : IsCompact L := hK.image_of_continuousOn (c.symm.continuousOn.mono hKt)
  refine ⟨g,L,hg,hL,image_mono hKU,hgreg,?_,?_⟩
  · intro x hx
    apply hgout x
    exact fun hh => hx (image_mono hs hh)
  · intro t ht
    have hat := hUt (haxis t ht)
    have hps : c.symm (crosscapAxis t) ∈ c.source := c.map_target hat
    have hca : c (c.symm (crosscapAxis t)) = crosscapAxis t := c.right_inv hat
    have hlocal := hglocal (c.symm (crosscapAxis t)) hps (by rw [hca]; exact haxis t ht)
    rw [hsum] at hlocal
    have hct : Tendsto c (𝓝 (c.symm (crosscapAxis t))) (𝓝 (crosscapAxis t)) := by
      simpa only [hca] using (c.continuousAt hps).tendsto
    exact hlocal.trans ((hinner t).comp_tendsto hct)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
