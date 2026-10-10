import Mathlib
import OAI.Geometry.WeakMTW.Potentials.PotentialGraphGlobal
import OAI.Geometry.WeakMTW.Potentials.LiftedSections
import OAI.Geometry.WeakMTW.Potentials.IntermediateDefinitions

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem hopfLax_le {u : M → ℝ} (hu : Continuous u) (t : ℝ) (x z : M) :
     hopfLax t u z ≤ u x+cost x z/t := by
   apply csInf_le _ (mem_range_self x)
   have hc : Continuous (fun x : M => u x+cost x z/t) :=
     hu.add ((cost_continuous.comp (continuous_id.prodMk continuous_const)).div_const t)
   simpa only [image_univ] using (isCompact_univ.image hc).bddBelow

 theorem hopfLax_attained {u : M → ℝ} (hu : Continuous u) (t : ℝ) (z : M) :
     ∃ x : M, hopfLax t u z = u x+cost x z/t := by
   let : Nonempty M := ⟨z⟩
   have hc : Continuous (fun x : M => u x+cost x z/t) :=
     hu.add ((cost_continuous.comp (continuous_id.prodMk continuous_const)).div_const t)
   obtain ⟨x,_,hmin⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hc.continuousOn
   refine ⟨x,le_antisymm (hopfLax_le hu t x z) ?_⟩
   exact le_csInf (range_nonempty _) (by rintro _ ⟨x',rfl⟩; exact hmin (mem_univ x'))

 theorem hopfLax_continuous {u : M → ℝ} (hu : Continuous u) (t : ℝ) : Continuous (hopfLax t u) := by
   have hc : Continuous (fun zx : M × M => u zx.2+cost zx.2 zx.1/t) :=
     (hu.comp continuous_snd).add ((cost_continuous.comp (continuous_snd.prodMk continuous_fst)).div_const t)
   have h := isCompact_univ.continuous_sInf (f := fun z x : M => u x+cost x z/t) hc
   change Continuous (fun z : M => sInf (range (fun x : M => u x+cost x z/t)))
   simpa only [image_univ] using h

 theorem global_support_contact {u v : M → ℝ} (huv : IsDualPair u v) {x y : M}
     (hs : ∀ z, u x+cost x y-cost z y ≤ u z) : u x+cost x y+v y = 0 := by
   let : Nonempty M := ⟨x⟩
   have hlo := cTransform_ge huv.1 y x
   rw [←huv.2.2.2,cost_comm] at hlo
   have hup : v y ≤ -u x-cost x y := by
     rw [huv.2.2.2]
     apply csSup_le (range_nonempty _) (by
       rintro _ ⟨z,rfl⟩
       change -cost y z-u z ≤ -u x-cost x y
       rw [cost_comm y z]
       linarith [hs z])
   linarith

 theorem minimizing_cost_split {x : M} {p : TangentSpace (model n) x}
     (hp : p ∈ minimizingDomain x) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
     cost x (exp x (t•p))/t+cost (exp x (t•p)) (exp x p)/(1-t) = cost x (exp x p) := by
   have hd := minimizing_shortened_dist hp ht.le ht1.le (le_refl 1)
   simp only [one_smul] at hd
   have hc : cost (exp x (t•p)) (exp x p) = (1-t)^2*‖p‖^2/2 := by
     unfold cost
     rw [hd,mul_pow]
   rw [minimizing_shortened_cost hp ht.le ht1.le,hc,minimizing_cost hp]
   field_simp [ht.ne',(sub_pos.mpr ht1).ne']
   ring

 theorem hopfLax_at_projected_pole (hMTW : HasWeakMTW (n := n) (M := M))
     {u : M → ℝ} (hu : IsPotential u) {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
     (q : potentialGraph (n := n) u) :
     hopfLax t u (potentialProjection u t q) = u q.val.1+cost q.val.1 (potentialProjection u t q)/t := by
   let : Nonempty M := ⟨q.val.1⟩
   apply le_antisymm (hopfLax_le (isPotential_continuous hu) t _ _)
   have hmin := ((globalSupportingProperty hMTW hu).2 t ht ht1).2 q
   exact le_csInf (range_nonempty _) (by rintro _ ⟨x',rfl⟩; exact (hmin.2 x').1)

 theorem hopfLax_duality (hMTW : HasWeakMTW (n := n) (M := M))
     {u v : M → ℝ} (huv : IsDualPair u v) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) (z : M) :
     hopfLax t u z = -hopfLax (1-t) v z := by
   obtain ⟨x₀,hx₀⟩ := hopfLax_attained huv.1 t z
   obtain ⟨y₀,hy₀⟩ := hopfLax_attained huv.2.1 (1-t) z
   have hge := cTransform_ge huv.2.1 x₀ y₀
   rw [←huv.2.2.1] at hge
   have htri := cost_triangle_split x₀ z y₀ ht (sub_pos.mpr ht1)
   rw [add_sub_cancel,div_one] at htri
   have hlo : 0 ≤ hopfLax t u z+hopfLax (1-t) v z := by
     rw [hx₀,hy₀,cost_comm y₀ z]
     linarith
   obtain ⟨q,hq⟩ := potentialProjection_surjective (n := n) huv.2.1 huv.2.2.1 ht z
   have hsup := (globalSupportingProperty hMTW ⟨v,huv.2.1,huv.2.2.1⟩).1 q.val.1 q.val.2 q.property
   have hcontact := global_support_contact huv hsup.2
   have hsplit := minimizing_cost_split hsup.1 ht ht1
   change cost q.val.1 (potentialProjection u t q)/t+
     cost (potentialProjection u t q) (exp q.val.1 q.val.2)/(1-t) = cost q.val.1 (exp q.val.1 q.val.2) at hsplit
   rw [hq] at hsplit
   have hup₀ := hopfLax_le huv.1 t q.val.1 z
   have hup₁ := hopfLax_le huv.2.1 (1-t) (exp q.val.1 q.val.2) z
   rw [cost_comm (exp q.val.1 q.val.2) z] at hup₁
   linarith

 theorem intermediate_two_sided_supports (hMTW : HasWeakMTW (n := n) (M := M))
     {u v : M → ℝ} (huv : IsDualPair u v) {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
     (q : potentialGraph (n := n) u) :
     (∀ z', -v (exp q.val.1 q.val.2)-cost z' (exp q.val.1 q.val.2)/(1-t) ≤ hopfLax t u z' ∧
       hopfLax t u z' ≤ u q.val.1+cost q.val.1 z'/t) ∧
     hopfLax t u (potentialProjection u t q) = u q.val.1+cost q.val.1 (potentialProjection u t q)/t ∧
     hopfLax t u (potentialProjection u t q) =
       -v (exp q.val.1 q.val.2)-cost (potentialProjection u t q) (exp q.val.1 q.val.2)/(1-t) := by
   have hupper := hopfLax_at_projected_pole hMTW ⟨v,huv.2.1,huv.2.2.1⟩ ht ht1 q
   refine ⟨fun z' => ⟨?_,hopfLax_le huv.1 t _ _⟩,hupper,?_⟩
   · rw [hopfLax_duality hMTW huv ht ht1]
     have hh := hopfLax_le huv.2.1 (1-t) (exp q.val.1 q.val.2) z'
     rw [cost_comm] at hh
     linarith
   · have hsup := (globalSupportingProperty hMTW ⟨v,huv.2.1,huv.2.2.1⟩).1 q.val.1 q.val.2 q.property
     have hcontact := global_support_contact huv hsup.2
     have hsplit := minimizing_cost_split hsup.1 ht ht1
     change cost q.val.1 (potentialProjection u t q)/t+
       cost (potentialProjection u t q) (exp q.val.1 q.val.2)/(1-t) = cost q.val.1 (exp q.val.1 q.val.2) at hsplit
     linarith
end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
