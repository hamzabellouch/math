import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Excision.PureStateCarrier

namespace OAI

section

noncomputable section
namespace PureStateExcision
open scoped ComplexOrder InnerProductSpace ComplexStarModule

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

 theorem exists_pure_positive_state_norming [Nontrivial A] (a : A) (ha : 0≤a) :
    ∃ (f : A →ₚ[ℂ] ℂ) (hf : f 1=1),
      ofPositiveState f hf∈(realStateCarrier (A := A)).extremePoints ℝ ∧ f a=(‖a‖:ℂ) := by
  let a₀ : selfAdjoint A := ⟨a,IsSelfAdjoint.of_nonneg ha⟩
  let F : Set (WeakDual ℝ (selfAdjoint A)) := realStateCarrier∩{f | f a₀=‖a‖}
  have hcompact : IsCompact F := realStateCarrier_isCompact.inter_right
    (isClosed_eq (WeakDual.eval_continuous a₀) continuous_const)
  have hnonempty : F.Nonempty := by
    obtain ⟨f,hf,hfa⟩ := Pureness.exists_positiveState_norming a ha
    refine ⟨ofPositiveState f hf,ofPositiveState_mem f hf,?_⟩
    change (f a).re=‖a‖
    rw [hfa,Complex.ofReal_re]
  have hle (f : WeakDual ℝ (selfAdjoint A)) (hf : f∈realStateCarrier) : f a₀≤‖a‖ := by
    calc
      f a₀≤‖f a₀‖ := le_abs_self _
      _≤‖f.toStrongDual‖*‖a₀‖ := f.toStrongDual.le_opNorm a₀
      _≤1*‖a₀‖ := mul_le_mul_of_nonneg_right hf.2 (norm_nonneg _)
      _=‖a‖ := one_mul _
  have hextreme : IsExtreme ℝ realStateCarrier F := by
    refine ⟨Set.inter_subset_left,?_⟩
    intro x hx y hy z hz hseg
    refine ⟨hx,?_⟩
    rcases hseg with ⟨r,s,hr,hs,hrs,heq⟩
    have hv := congrArg (fun g : WeakDual ℝ (selfAdjoint A) => g a₀) heq
    change r*x a₀+s*y a₀=z a₀ at hv
    rw [hz.2] at hv
    have hx' := hle x hx
    have hy' := hle y hy
    have hnorm := congrArg (fun u : ℝ => u*‖a‖) hrs
    have hys := mul_nonneg hs.le (sub_nonneg.mpr hy')
    apply le_antisymm hx'
    by_contra! hlt
    have hpos := mul_pos hr (sub_pos.mpr hlt)
    nlinarith
  let : LocallyConvexSpace ℝ (WeakDual ℝ (selfAdjoint A)) := WeakBilin.locallyConvexSpace
  obtain ⟨g,hg⟩ := hcompact.extremePoints_nonempty hnonempty
  have hgs := hextreme.extremePoints_subset_extremePoints hg
  refine ⟨toPositiveState g hgs.1,toPositiveState_one g hgs.1,?_,?_⟩
  · rw [ofPositiveState_toPositiveState]; exact hgs
  · change toPositiveState g hgs.1 (a₀:A)=_
    rw [toPositiveState_apply,hg.1.2]

 def gnsOperatorNorm (f : A →ₚ[ℂ] ℂ) (a : A) : ℝ := ‖f.gnsStarAlgHom a‖

 theorem norm_le_of_pure_gns [Nontrivial A] (a : A) {R : ℝ} (hR : 0≤R)
    (h : ∀ (f : A →ₚ[ℂ] ℂ) (hf : f 1=1),
      ofPositiveState f hf∈(realStateCarrier (A := A)).extremePoints ℝ → gnsOperatorNorm f a≤R) :
    ‖a‖≤R := by
  obtain ⟨f,hf,hpure,hfa⟩ := exists_pure_positive_state_norming (star a*a) (star_mul_self_nonneg a)
  have hn := h f hf hpure
  change ‖f.gnsStarAlgHom a‖≤R at hn
  have hi : ‖star a*a‖≤‖f.gnsStarAlgHom a‖*‖f.gnsStarAlgHom a‖ := by
    have hi := norm_inner_le_norm (𝕜 := ℂ) (Pureness.stateGNSVector f)
      (f.gnsStarAlgHom (star a*a) (Pureness.stateGNSVector f))
    rw [Pureness.stateGNS_vector_value,hfa,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg _),
      Pureness.stateGNSVector_norm f hf,one_mul] at hi
    calc
      ‖star a*a‖≤‖f.gnsStarAlgHom (star a*a) (Pureness.stateGNSVector f)‖ := hi
      _≤‖f.gnsStarAlgHom (star a*a)‖*‖Pureness.stateGNSVector f‖ :=
        (f.gnsStarAlgHom (star a*a)).le_opNorm _
      _=‖f.gnsStarAlgHom a‖*‖f.gnsStarAlgHom a‖ := by
        rw [Pureness.stateGNSVector_norm f hf,mul_one,map_mul,map_star]
        exact CStarRing.norm_star_mul_self (x := f.gnsStarAlgHom a)
  rw [CStarRing.norm_star_mul_self] at hi
  exact nonneg_le_nonneg_of_sq_le_sq hR
    (hi.trans (mul_self_le_mul_self (norm_nonneg _) hn))

end PureStateExcision

end
end

end OAI
