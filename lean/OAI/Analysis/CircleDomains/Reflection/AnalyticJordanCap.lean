import OAI.Analysis.CircleDomains.Reflection.AnalyticJordanBoundaryContinuation
import OAI.Analysis.CircleDomains.Uniformization.JordanCircularizationSequence

namespace OAI

/-! Analytic circle parametrizations of the actual compact Jordan holes.
The neighborhood and injectivity are retained so that a later
circularization has the proved local continuation. -/
open Set Function Metric
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

def IsAnalyticJordanCap (H : ℂ ≃ₜ ℂ) : Prop :=
  ∃ (S : Set ℂ) (α : ℂ → ℂ) (c : ℂ) (r : ℝ), IsOpen S ∧ 0<r ∧
    closedBall c r⊆S ∧ DifferentiableOn ℂ α S ∧ InjOn α S ∧
    α '' closedBall c r=closure (jordanInterior H)

lemma isAnalyticJordanCap_of_round {H : ℂ ≃ₜ ℂ} {c : ℂ} {r : ℝ}
    (hr : 0<r) (he : jordanInterior H=ball c r) : IsAnalyticJordanCap H := by
  refine ⟨univ,id,c,r,isOpen_univ,hr,subset_univ _,differentiableOn_id,injective_id.injOn,?_⟩
  rw [image_id,he,closure_ball _ hr.ne']

lemma IsAnalyticJordanCap.conformal_image {H K : ℂ ≃ₜ ℂ} (hH : IsAnalyticJordanCap H)
    {f : Sphere → Sphere} {U V : Set Sphere}
    (hf : IsConformalEquivalence f U V) (hU : IsOpen U)
    (hinf : ∞∈U) (hfix : f ∞=∞) (hHU : closedTerminalCap H⊆U)
    (himage : f '' closedTerminalCap H=closedTerminalCap K) : IsAnalyticJordanCap K := by
  obtain ⟨S,α,c,r,hS,hr,hDS,hα,hi,hαeq⟩ := hH
  let g : ℂ → ℂ := fun z => finiteCoord (f (z : Sphere))
  let P := ((↑) : ℂ → Sphere) ⁻¹' U
  have hP : IsOpen P := hU.preimage OnePoint.continuous_coe
  obtain ⟨hgd,_,hgi⟩ := hf.1.finite_open_embedding hU hf.bijOn.injOn hinf hfix
  let W := S ∩ α ⁻¹' P
  have hW : IsOpen W := hα.continuousOn.isOpen_inter_preimage hS hP
  have hDW : closedBall c r⊆W := by
    intro z hz
    refine ⟨hDS hz,?_⟩
    apply hHU
    refine ⟨α z,?_,rfl⟩
    rw [←hαeq]
    exact mem_image_of_mem α hz
  have hfin : ∀z∈closure (jordanInterior H),f (z : Sphere)≠∞ :=
    fun z hz => finite_image_of_fixes_infty hf.bijOn.injOn hinf hfix (hHU ⟨z,hz,rfl⟩)
  have hgimage : g '' closure (jordanInterior H)=closure (jordanInterior K) := by
    apply OnePoint.coe_injective.image_injective
    rw [finite_part_sphere_image hfin]
    exact himage
  refine ⟨W,g ∘ α,c,r,hW,hr,hDW,?_,?_,?_⟩
  · exact hgd.comp (hα.mono inter_subset_left) (fun _ hz => hz.2)
  · exact hgi.comp (hi.mono inter_subset_left) (fun _ hz => hz.2)
  · rw [image_comp,hαeq,hgimage]

namespace FiniteJordanConfiguration
variable {I : Type*} [Finite I] {C : FiniteJordanConfiguration I} {j : I}

omit [Finite I] in
lemma Step.analytic_selected (q : Step C j) : IsAnalyticJordanCap (q.target.hole j) :=
  isAnalyticJordanCap_of_round q.radius_pos q.selected

omit [Finite I] in
lemma Step.analytic_other (q : Step C j) {i : I} (hij : i≠j)
    (ha : IsAnalyticJordanCap (C.hole i)) : IsAnalyticJordanCap (q.target.hole i) := by
  let U := (closedTerminalCap (C.hole j))ᶜ
  have hU : IsOpen U := (isCompact_closedTerminalCap (C.hole j)).isClosed.isOpen_compl
  have hinf : ∞∈U := by
    rintro ⟨z,_,he⟩
    exact OnePoint.coe_ne_infty z he
  have hHU : closedTerminalCap (C.hole i)⊆U := by
    intro x hx hxj
    exact Set.disjoint_left.mp (disjoint_closedTerminalCaps C.hole C.disjoint hij) hx hxj
  exact ha.conformal_image q.exterior_conformal hU hinf q.principal.1 hHU (q.others i hij)

lemma iterate_analytic_of_visited (C : FiniteJordanConfiguration I) (schedule : ℕ → I)
    (n : ℕ) (i : I) (hv : ∃k<n,schedule k=i) :
    IsAnalyticJordanCap ((iterate C schedule n).hole i) := by
  induction n with
  | zero => obtain ⟨k,hk,_⟩ := hv;omega
  | succ n ih =>
    by_cases hi : i=schedule n
    · subst i
      exact (chosenStep (iterate C schedule n) (schedule n)).analytic_selected
    · apply (chosenStep (iterate C schedule n) (schedule n)).analytic_other hi
      apply ih
      obtain ⟨k,hk,hki⟩ := hv
      have hkn : k≠n := by
        intro he
        subst k
        exact hi hki.symm
      exact ⟨k,by omega,hki⟩

end FiniteJordanConfiguration
end CircleDomainRigidity

end

end OAI
