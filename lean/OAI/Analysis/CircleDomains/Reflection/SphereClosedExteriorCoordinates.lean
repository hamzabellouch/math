import OAI.Analysis.CircleDomains.Reflection.AnalyticSphereClosedExterior

namespace OAI

/-! The spherical and planar closed-exterior extensions are the same
at every finite point. The spherical image is the entire closed disk. -/
open Set Function Filter Metric
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma coe_mem_closed_jordan_exterior {H : ℂ ≃ₜ ℂ} {x : ℂ} :
    (x : Sphere)∈closure (closedTerminalCap H)ᶜ ↔
      x∈closure (closure (jordanInterior H))ᶜ := by
  simp only [closure_compl,interior_closedTerminalCap,interior_closure_jordanInterior,
    mem_compl_iff,OnePoint.coe_injective.mem_set_image]

lemma sphere_plane_closed_exterior_eq {H : ℂ ≃ₜ ℂ}
    (hH : IsAnalyticJordanCap H) {f : Sphere → Sphere} {d : ℂ} {s : ℝ}
    (hs : 0<s) (hf : IsConformalEquivalence f (closedTerminalCap H)ᶜ
      ((((↑) : ℂ → Sphere) '' closedBall d s)ᶜ))
    {x : ℂ} (hx : x∈closure (closure (jordanInterior H))ᶜ) :
    extendFrom (closedTerminalCap H)ᶜ (exteriorDiskNormalization d s hs ∘ f) (x : Sphere)=
      ((extendFrom (closure (jordanInterior H))ᶜ
        (fun z : ℂ => finiteCoord (exteriorDiskNormalization d s hs (f (z : Sphere)))) x : ℂ) : Sphere) := by
  let U := (closedTerminalCap H)ᶜ
  let A := (closure (jordanInterior H))ᶜ
  let F := exteriorDiskNormalization d s hs ∘ f
  let E := extendFrom U F
  let g := fun z : ℂ => finiteCoord (F (z : Sphere))
  let e := extendFrom A g
  obtain ⟨hEc,hEe⟩ := analytic_sphere_closed_exterior_extension hH hs hf
  obtain ⟨hec,hee⟩ := analytic_jordan_closed_exterior_extension hH hs hf
  change ContinuousOn E (closure U) at hEc
  change EqOn E F U at hEe
  change ContinuousOn e (closure A) at hec
  change EqOn e g A at hee
  have hco : MapsTo ((↑) : ℂ → Sphere) (closure A) (closure U) :=
    fun z hz => coe_mem_closed_jordan_exterior.mpr hz
  have h1c : ContinuousOn (fun z : ℂ => E (z : Sphere)) (closure A) :=
    hEc.comp OnePoint.continuous_coe.continuousOn hco
  have h2c : ContinuousOn (fun z : ℂ => (e z : Sphere)) (closure A) :=
    OnePoint.continuous_coe.comp_continuousOn hec
  have hsame : ∀z∈A,E (z : Sphere)=(e z : Sphere) := by
    intro z hz
    have hzU : (z : Sphere)∈U := by
      rintro ⟨w,hw,he⟩
      exact hz (OnePoint.coe_injective he ▸ hw)
    have hF := hf.trans (isConformalEquivalence_exteriorDiskNormalization d hs)
    have hfin : F (z : Sphere)≠∞ := by
      obtain ⟨w,_,hw⟩ := hF.2.1 hzU
      change (w : Sphere)=F (z : Sphere) at hw
      rw [←hw]
      exact OnePoint.coe_ne_infty w
    rw [hEe hzU,hee hz]
    exact (coe_finiteCoord hfin).symm
  have hclosed : IsClosed {z∈closure A | E (z : Sphere)=(e z : Sphere)} :=
    isClosed_closure.isClosed_eq h1c h2c
  have hsub : A⊆{z∈closure A | E (z : Sphere)=(e z : Sphere)} :=
    fun z hz => ⟨subset_closure hz,hsame z hz⟩
  exact (closure_minimal hsub hclosed hx).2

lemma analytic_sphere_closed_exterior_image {H : ℂ ≃ₜ ℂ}
    (hH : IsAnalyticJordanCap H) {f : Sphere → Sphere} {d : ℂ} {s : ℝ}
    (hs : 0<s) (hf : IsConformalEquivalence f (closedTerminalCap H)ᶜ
      ((((↑) : ℂ → Sphere) '' closedBall d s)ᶜ)) :
    extendFrom (closedTerminalCap H)ᶜ (exteriorDiskNormalization d s hs ∘ f) ''
      closure (closedTerminalCap H)ᶜ = ((↑) : ℂ → Sphere) '' closedBall 0 1 := by
  let U := (closedTerminalCap H)ᶜ
  let F := exteriorDiskNormalization d s hs ∘ f
  let E := extendFrom U F
  obtain ⟨hEc,hEe⟩ := analytic_sphere_closed_exterior_extension hH hs hf
  change ContinuousOn E (closure U) at hEc
  change EqOn E F U at hEe
  have himg : E '' U=((↑) : ℂ → Sphere) '' ball 0 1 := by
    rw [image_congr hEe]
    exact (hf.trans (isConformalEquivalence_exteriorDiskNormalization d hs)).bijOn.image_eq
  have hclosed : IsClosed (E '' closure U) :=
    ((isClosed_closure : IsClosed (closure U)).isCompact.image_of_continuousOn hEc).isClosed
  have heq : E '' closure U=closure (E '' U) := by
    apply Subset.antisymm hEc.image_closure
    exact closure_minimal (image_mono subset_closure) hclosed
  change E '' closure U= _
  rw [heq,himg]
  have hcl := closure_sphere_image_jordanInterior (roundJordanAt (0:ℂ) 1 zero_lt_one)
  rw [roundJordanAt_interior,closure_ball (0:ℂ) one_ne_zero] at hcl
  exact hcl

end CircleDomainRigidity

end

end OAI
