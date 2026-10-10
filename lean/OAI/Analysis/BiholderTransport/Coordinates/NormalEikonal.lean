import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.ContactDifferential

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section NormalEikonal
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance (x : M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

def doubleNormalCost (x y : M)
    (z : TangentSpace 𝓘(ℝ,Model n) x × TangentSpace 𝓘(ℝ,Model n) y) : ℝ :=
  cost (riemannianExp x z.1) (riemannianExp y z.2)

lemma doubleNormalCost_contDiffAt {x y : M} {r : TangentSpace 𝓘(ℝ,Model n) y}
    (hr : r∈injectivityDomain y) (he : riemannianExp y r=x) :
    ContDiffAt ℝ ∞ (doubleNormalCost (n := n) x y) (0,0) := by
  let X := TangentSpace 𝓘(ℝ,Model n) x
  let Y := TangentSpace 𝓘(ℝ,Model n) y
  have hu : ContMDiffAt 𝓘(ℝ,X×Y) 𝓘(ℝ,Model n) ∞
      (fun z : X×Y => riemannianExp y z.2) (0,0) :=
    (contMDiff_riemannianExp_fiber y _).comp (0,0) contDiffAt_snd.contMDiffAt
  have hv : ContMDiffAt 𝓘(ℝ,X×Y) 𝓘(ℝ,Model n) ∞
      (fun z : X×Y => riemannianExp x z.1) (0,0) :=
    (contMDiff_riemannianExp_fiber x _).comp (0,0) contDiffAt_fst.contMDiffAt
  have hc := cost_contMDiffAt_of_injectivityDomain
    (⟨y,r⟩ : TangentBundle 𝓘(ℝ,Model n) M) hr
  have hc' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun q : M×M => cost q.1 q.2) (riemannianExp y (0:Y),riemannianExp x (0:X)) := by
    simpa only [riemannianExp_zero,he] using hc
  have H := (hc'.comp (0,0) (hu.prodMk hv)).contDiffAt
  convert! H using 1
  funext z
  exact congrArg (fun d : ℝ => d^2/2) (dist_comm _ _)

lemma exists_normal_eikonal_log {x y : M} {r : TangentSpace 𝓘(ℝ,Model n) y}
    (hr : r∈injectivityDomain y) (he : riemannianExp y r=x) :
    ∃ q : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) y,
      q 0=r ∧ ContDiffAt ℝ ∞ q 0 ∧
      (∀ᶠ a in 𝓝 0, riemannianExp y (q a)=riemannianExp x a) ∧
      (∀ᶠ a in 𝓝 0,
        doubleNormalCost x y (a,0)=‖q a‖^2/2 ∧
        fderiv ℝ (fun b => doubleNormalCost x y (a,b)) 0=innerSL ℝ (-q a)) := by
  let : Nonempty M := ⟨x⟩
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  let X := TangentSpace 𝓘(ℝ,Model n) x
  let Y := TangentSpace 𝓘(ℝ,Model n) y
  obtain ⟨κ,hκ0,hκ,hκright⟩ := exists_normal_local_inverse_at hr
  rw [he] at hκ0 hκ hκright
  let q : X → Y := κ ∘ riemannianExp (n := n) x
  have hq0 : q 0=r := by simp only [q,Function.comp_apply,riemannianExp_zero,hκ0]
  have hq : ContDiffAt ℝ ∞ q 0 := by
    apply ContMDiffAt.contDiffAt
    exact (show ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Y) ∞ κ (riemannianExp x (0:X)) from
      by simpa only [riemannianExp_zero] using hκ).comp 0 (contMDiff_riemannianExp_fiber x 0)
  have hqright : ∀ᶠ a in 𝓝 0, riemannianExp y (q a)=riemannianExp x a :=
    (show ContinuousAt (riemannianExp (n := n) x) (0:X) from
      (continuous_riemannianExp x).continuousAt).eventually
        (by simpa only [riemannianExp_zero] using hκright)
  have hqI : ∀ᶠ a in 𝓝 0, q a∈injectivityDomain y :=
    hq.continuousAt.preimage_mem_nhds ((isOpen_injectivityDomain y).mem_nhds (hq0.symm ▸ hr))
  refine ⟨q,hq0,hq,hqright,?_⟩
  filter_upwards [hqright,hqI] with a ha haI
  change riemannianExp y (q a)=riemannianExp x a at ha
  change q a∈injectivityDomain y at haI
  constructor
  · have hm := injectivityDomain_subset_minimizingVectors y haI
    change dist y (riemannianExp y (q a))=‖q a‖ at hm
    simp only [doubleNormalCost,riemannianExp_zero,cost,←ha,dist_comm _ y,hm]
  · have heq : (fun b => doubleNormalCost x y (a,b))=normalCost y (q a) := by
      funext b
      dsimp [doubleNormalCost,normalCost,cost]
      rw [←ha,dist_comm]
    rw [heq]
    exact (normalCost_hasFDerivAt_zero haI).fderiv

end NormalEikonal
end WeakMTWTransport

end

end

end

end OAI
