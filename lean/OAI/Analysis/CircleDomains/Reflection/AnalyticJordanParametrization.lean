import OAI.Analysis.CircleDomains.Reflection.AnalyticJordanCap

namespace OAI

/-! The analytic disk parametrizations retained by the iteration also
parametrize the entire actual Jordan boundary. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma holomorphic_injOn_isOpen_image {S : Set ℂ} {f : ℂ → ℂ}
    (hS : IsOpen S) (hf : DifferentiableOn ℂ f S) (hi : InjOn f S)
    {T : Set ℂ} (hT : IsOpen T) (hTS : T⊆S) : IsOpen (f '' T) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro _ ⟨z,hz,rfl⟩
  rw [←holomorphicInjOn_map_nhds hS hf hi (hTS hz)]
  exact image_mem_map (hT.mem_nhds hz)

lemma exists_analytic_jordan_parametrization {H : ℂ ≃ₜ ℂ} (hH : IsAnalyticJordanCap H) :
    ∃ (S : Set ℂ) (α : ℂ → ℂ) (c : ℂ) (r : ℝ), IsOpen S ∧ 0<r ∧
      closedBall c r⊆S ∧ DifferentiableOn ℂ α S ∧ InjOn α S ∧
      α '' closedBall c r=closure (jordanInterior H) ∧
      α '' sphere c r=frontier (jordanInterior H) := by
  obtain ⟨S,α,c,r,hS,hr,hDS,hα,hi,he⟩ := hH
  let J := roundJordanAt c r hr
  have hJcl : closure (jordanInterior J)=closedBall c r := roundJordanAt_closure c r hr
  have hJS : closure (jordanInterior J)⊆S := by rwa [hJcl]
  obtain ⟨K,_,hKcl,hKf⟩ := exists_jordan_image_disk planarSchoenflies hS hα.continuousOn
    (fun _ hT hTS => holomorphic_injOn_isOpen_image hS hα hi hT hTS) hi J hJS
  rw [hJcl,he] at hKcl
  have hKI : jordanInterior K=jordanInterior H := by
    calc
      jordanInterior K = interior (closure (jordanInterior K)) :=
        (interior_closure_jordanInterior K).symm
      _ = interior (closure (jordanInterior H)) := congrArg interior hKcl.symm
      _ = jordanInterior H := interior_closure_jordanInterior H
  have hJfront : frontier (jordanInterior J)=sphere c r := by
    rw [roundJordanAt_interior,frontier_ball _ hr.ne']
  refine ⟨S,α,c,r,hS,hr,hDS,hα,hi,he,?_⟩
  rw [←hJfront,←hKf,hKI]

end CircleDomainRigidity

end

end OAI
