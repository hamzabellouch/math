import OAI.Geometry.SurfaceImmersion.Geometry.RelativeDefectFilling

namespace OAI

/-! A smooth field specified near its compact modification extends by the
original field, with no change to the support. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

theorem compact_relative_field {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {D A : Base → E} (hD : ContDiff ℝ ∞ D) {V K : Set Base}
    (hV : IsOpen V) (hA : ContDiffOn ℝ ∞ A V) (hK : IsCompact K) (hKV : K ⊆ V)
    (he : ∀ x ∈ V, x ∉ K → A x = D x) :
    ∃ B : Base → E, ContDiff ℝ ∞ B ∧ tsupport (B-D) ⊆ K ∧
      EqOn B A V ∧ ∀ x ∉ K, B x = D x := by
  obtain ⟨χ,hχ,_hc,_hr,hχV,hχone⟩ := CollarVelocity.compact_cutoff hK hV hKV
  let B := fun x => D x+χ x • (A x-D x)
  have hB : ContDiff ℝ ∞ B := hD.add
    (CollarVelocity.supported_local_smul hV hχ (hA.sub hD.contDiffOn) hχV)
  have hext : ∀ x ∉ K, B x = D x := by
    intro x hx
    by_cases hxV : x ∈ V
    · simp [B,he x hxV hx]
    · have hz : χ x = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hxV (hχV ht))
      simp [B,hz]
  refine ⟨B,hB,?_,?_,hext⟩
  · apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hxK
    exact hx (by simp only [Pi.sub_apply,hext x hxK,sub_self])
  · intro x hx
    by_cases hxK : x ∈ K
    · simp only [B,hχone x hxK,one_smul,add_sub_cancel]
    · rw [hext x hxK,he x hx hxK]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
