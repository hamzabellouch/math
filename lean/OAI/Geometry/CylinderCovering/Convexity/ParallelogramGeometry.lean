import OAI.Geometry.CylinderCovering.Convexity.OpenParallelogramDefinitions

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Topology

namespace RuledApproximation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem parallelogram_coordinate_homeomorph (hd : Module.finrank ℝ E = 2)
    (c u v : E) (hli : LinearIndependent ℝ ![u, v]) :
    ∃ e : (Fin 2 → ℝ) ≃ₜ E, ∀ p, e p = c + p 0 • u + p 1 • v := by
  let b : Module.Basis (Fin 2) ℝ E :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp [hd])
  let e := b.equivFunL.symm.toHomeomorph.trans (Homeomorph.addLeft c)
  refine ⟨e, fun p => ?_⟩
  change c + b.equivFun.symm p = c + p 0 • u + p 1 • v
  rw [b.equivFun_symm_apply]
  simp [b, coe_basisOfLinearIndependentOfCardEqFinrank, Fin.sum_univ_two, add_assoc]

theorem parallelogram_coordinate_image (c u v : E) {e : (Fin 2 → ℝ) ≃ₜ E}
    (he : ∀ p, e p = c + p 0 • u + p 1 • v) (J : Set ℝ) :
    e '' Set.pi Set.univ (fun _ : Fin 2 => J) =
      {x | ∃ s ∈ J, ∃ t ∈ J, x = c + s • u + t • v} := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p 0, hp 0 (mem_univ 0), p 1, hp 1 (mem_univ 1), he p⟩
  · rintro ⟨s, hs, t, ht, rfl⟩
    refine ⟨![s,t], ?_, ?_⟩
    · intro i _
      fin_cases i
      · simpa using hs
      · simpa using ht
    · simpa using he ![s,t]

theorem parallelogram_interior (hd : Module.finrank ℝ E = 2)
    (c u v : E) (hli : LinearIndependent ℝ ![u, v]) :
    interior {x | ∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1,
      x = c + s • u + t • v} = openParallelogramSet c u v := by
  obtain ⟨e, he⟩ := parallelogram_coordinate_homeomorph hd c u v hli
  rw [← parallelogram_coordinate_image c u v he,
    ← e.image_interior, interior_pi_set (Set.toFinite Set.univ)]
  simp only [interior_Icc]
  exact parallelogram_coordinate_image c u v he (Ioo 0 1)

end RuledApproximation

namespace RuledApproximation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem IsParallelogram.compact {P : Set E} (hP : IsParallelogram P) : IsCompact P := by
  obtain ⟨c,u,v,_,rfl⟩ := hP
  have hi : IsCompact ((fun p : ℝ × ℝ => c + p.1 • u + p.2 • v) ''
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) :=
    (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  convert hi using 1
  ext x
  constructor
  · rintro ⟨s,hs,t,ht,rfl⟩
    exact ⟨(s,t), ⟨hs,ht⟩, rfl⟩
  · rintro ⟨⟨s,t⟩, ⟨hs,ht⟩,rfl⟩
    exact ⟨s,hs,t,ht,rfl⟩

theorem IsParallelogram.convex {P : Set E} (hP : IsParallelogram P) : Convex ℝ P := by
  obtain ⟨c,u,v,_,rfl⟩ := hP
  intro x hx y hy a b ha hb hab
  obtain ⟨s,hs,t,ht,rfl⟩ := hx
  obtain ⟨s',hs',t',ht',rfl⟩ := hy
  refine ⟨a*s+b*s', ?_, a*t+b*t', ?_, ?_⟩
  · exact (convex_Icc (0 : ℝ) 1) hs hs' ha hb hab
  · exact (convex_Icc (0 : ℝ) 1) ht ht' ha hb hab
  · calc
      a • (c + s • u + t • v) + b • (c + s' • u + t' • v) =
          (a+b) • c + (a*s+b*s') • u + (a*t+b*t') • v := by module
      _ = c + (a*s+b*s') • u + (a*t+b*t') • v := by rw [hab, one_smul]

theorem IsParallelogram.interior_nonempty (hd : Module.finrank ℝ E = 2)
    {P : Set E} (hP : IsParallelogram P) : (interior P).Nonempty := by
  obtain ⟨c,u,v,hli,rfl⟩ := hP
  rw [parallelogram_interior hd c u v hli]
  exact ⟨c + (1/2 : ℝ) • u + (1/2 : ℝ) • v,
    1/2, by norm_num, 1/2, by norm_num, rfl⟩

theorem IsParallelogram.isOpenParallelogram_interior (hd : Module.finrank ℝ E = 2)
    {P : Set E} (hP : IsParallelogram P) : IsOpenParallelogram (interior P) := by
  obtain ⟨c,u,v,hli,rfl⟩ := hP
  exact ⟨c,u,v,hli,parallelogram_interior hd c u v hli⟩

theorem IsParallelogram.homothety {P : Set E} (hP : IsParallelogram P)
    (o : E) {r : ℝ} (hr : r ≠ 0) :
    IsParallelogram (AffineMap.homothety o r '' P) := by
  obtain ⟨c,u,v,hli,rfl⟩ := hP
  refine ⟨AffineMap.homothety o r c, r • u, r • v, ?_, ?_⟩
  · convert hli.units_smul (fun _ => Units.mk0 r hr) using 1
    ext i
    fin_cases i <;> rfl
  · ext x
    constructor
    · rintro ⟨z,⟨s,hs,t,ht,rfl⟩,rfl⟩
      refine ⟨s,hs,t,ht,?_⟩
      simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
      module
    · rintro ⟨s,hs,t,ht,rfl⟩
      refine ⟨c + s • u + t • v, ⟨s,hs,t,ht,rfl⟩, ?_⟩
      simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
      module

end RuledApproximation

end

end OAI
