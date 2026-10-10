import OAI.Geometry.NodalSets.Elliptic.CompactSmoothExtension
import OAI.Geometry.NodalSets.Elliptic.RealLocalWeakCutoff

namespace OAI

namespace Yau
open MeasureTheory Set Filter
open scoped ContDiff Topology
noncomputable section

theorem real_supported_local_weak_global {Q K : Set Jets.Coord}
    (hQ : IsCompact Q) (hK : IsCompact K) (hKQ : K ⊆ interior Q)
    (u g : Jets.Coord → ℝ) (hu : MemLp u 2 (volume.restrict Q))
    (hg : MemLp g 2 (volume.restrict Q)) (hsu : tsupport u ⊆ K) (hsg : tsupport g ⊆ K)
    (i : Fin 4)
    (hw : ∀ psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
      (∫ x in Q, u x*coordPartial psi x i)=-(∫ x in Q, g x*psi x)) :
    MemLp u 2 volume ∧ MemLp g 2 volume ∧
    ∀ psi, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      Integrable (fun x ↦ u x*coordPartial psi x i) ∧ Integrable (fun x ↦ g x*psi x) ∧
      (∫ x, u x*coordPartial psi x i)=-(∫ x, g x*psi x) := by
  obtain ⟨eta,he,hc,hs,hb,h1⟩ := Geometry.compact_smooth_cutoff hK isOpen_interior hKQ
  have h := real_local_weak_cutoff hQ u g eta hu hg he (hs.trans interior_subset) i hw
  have hm (v : Jets.Coord → ℝ) (hv : tsupport v ⊆ K) : (fun x ↦ eta x*v x)=v := by
    funext x
    by_cases hx : x ∈ K
    · rw [(h1 x hx).self_of_nhds,one_mul]
    · rw [image_eq_zero_of_notMem_tsupport (fun ht ↦ hx (hv ht)),mul_zero]
  have hd : (fun x ↦ coordPartial eta x i*u x)=(fun _ ↦ (0:ℝ)) := by
    funext x
    by_cases hx : x ∈ K
    · have hd := (h1 x hx).fderiv_eq (𝕜 := ℝ)
      simp [coordPartial,hd]
    · rw [image_eq_zero_of_notMem_tsupport (fun ht ↦ hx (hsu ht)),mul_zero]
  have hcomb : (fun x ↦ eta x*g x+coordPartial eta x i*u x)=g := by
    funext x
    rw [congrFun (hm g hsg) x,congrFun hd x,add_zero]
  rw [hm u hsu,hcomb] at h
  simp_rw [show ∀ x, eta x*u x=u x from fun x ↦ congrFun (hm u hsu) x,
    show ∀ x, eta x*g x+coordPartial eta x i*u x=g x from fun x ↦ congrFun hcomb x] at h
  exact h

end
end Yau

end OAI
