import OAI.Geometry.NodalSets.Elliptic.RealCompactL2Product
import OAI.Geometry.NodalSets.Elliptic.RealInteriorWeakProduct

namespace OAI

namespace Yau
open MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem real_local_weak_cutoff {n : ℕ} {K : Set (Coord n)} (hK : IsCompact K)
    (u g eta : Coord n → ℝ) (hu : MemLp u 2 (volume.restrict K))
    (hg : MemLp g 2 (volume.restrict K)) (he : ContDiff ℝ ∞ eta)
    (hs : tsupport eta ⊆ K) (i : Fin n)
    (hweak : ∀ phi : Coord n → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi → tsupport phi ⊆ K →
      (∫ x in K, u x*coordPartial phi x i)=-(∫ x in K, g x*phi x)) :
    MemLp (fun x ↦ eta x*u x) 2 volume ∧
    MemLp (fun x ↦ eta x*g x+coordPartial eta x i*u x) 2 volume ∧
    ∀ phi : Coord n → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      Integrable (fun x ↦ eta x*u x*coordPartial phi x i) ∧
      Integrable (fun x ↦ (eta x*g x+coordPartial eta x i*u x)*phi x) ∧
      (∫ x, eta x*u x*coordPartial phi x i) =
        -(∫ x, (eta x*g x+coordPartial eta x i*u x)*phi x) := by
  have hpart : tsupport (fun x ↦ coordPartial eta x i) ⊆ K :=
    (tsupport_fderiv_apply_subset ℝ (Pi.single i 1)).trans hs
  have hval := real_compact_localL2_product hK eta u he.continuous hs hu
  have h1 := real_compact_localL2_product hK eta g he.continuous hs hg
  have h2 := real_compact_localL2_product hK (fun x ↦ coordPartial eta x i) u
    (real_coordPartial_smooth eta he i).continuous hpart hu
  refine ⟨hval,h1.add h2,fun phi hp hc ↦ ?_⟩
  have hphi := real_compact_continuous_memLp phi hp.continuous hc
  have hi1 : Integrable (fun x ↦ eta x*g x*phi x) := h1.integrable_mul hphi
  have hi2 : Integrable (fun x ↦ coordPartial eta x i*u x*phi x) := h2.integrable_mul hphi
  have hi3 : Integrable (fun x ↦ eta x*u x*coordPartial phi x i) := hval.integrable_mul
    (real_compact_continuous_memLp _ (real_coordPartial_smooth phi hp i).continuous
      (hc.fderiv_apply ℝ (Pi.single i 1)))
  have hw := hweak (fun x ↦ eta x*phi x) (he.mul hp) hc.mul_left
    (tsupport_mul_subset_left.trans hs)
  have he1 : (fun x ↦ g x*(eta x*phi x)) = fun x ↦ eta x*g x*phi x := by funext x; ring
  have he2 : (fun x ↦ u x*coordPartial (fun y ↦ eta y*phi y) x i) =
      fun x ↦ coordPartial eta x i*u x*phi x+eta x*u x*coordPartial phi x i := by
    funext x
    rw [real_coordPartial_mul eta phi he hp]
    ring
  rw [he1,he2,integral_add hi2.integrableOn hi3.integrableOn] at hw
  have hz (x : Coord n) (hx : x ∉ K) : eta x=0 :=
    image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hs h))
  have hdz (x : Coord n) (hx : x ∉ K) : coordPartial eta x i=0 :=
    image_eq_zero_of_notMem_tsupport (f := fun y ↦ coordPartial eta y i) (fun h ↦ hx (hpart h))
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by rw [hdz x hx,zero_mul,zero_mul]),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by rw [hz x hx,zero_mul,zero_mul]),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by rw [hz x hx,zero_mul,zero_mul])] at hw
  have heG : (fun x ↦ (eta x*g x+coordPartial eta x i*u x)*phi x) =
      fun x ↦ eta x*g x*phi x+coordPartial eta x i*u x*phi x := by funext x; ring
  refine ⟨hi3,by rw [heG]; exact hi1.add hi2,?_⟩
  rw [heG,integral_add hi1 hi2]
  linarith only [hw]

end
end Yau

end OAI
