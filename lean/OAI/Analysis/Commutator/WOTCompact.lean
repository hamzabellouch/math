import Mathlib
import OAI.Analysis.Commutator.WeakOperatorLimit

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace Pointwise

open Filter ContinuousLinearMapWOT

namespace Kadison.WOTDistance

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def normBall (C : ℝ) : Set (H →WOT[ℂ] H) := {T | ‖T.toCLM‖≤C}

lemma isCompact_normBall {C : ℝ} (hC : 0≤C) : IsCompact (normBall (H:=H) C) := by
  classical
  apply isCompact_iff_ultrafilter_le_nhds.mpr
  intro ω hω
  let T : (H →WOT[ℂ] H) → H →L[ℂ] H := fun U => if ‖U.toCLM‖≤C then U.toCLM else 0
  have hT : ∀ U, ‖T U‖≤C := by
    intro U
    dsimp [T]
    split_ifs with h
    · exact h
    · simpa using hC
  obtain ⟨V,hV,hlim⟩ := WeakOperatorLimit.exists_ultralimit ω T C hC hT
  refine ⟨ofCLM V,hV,?_⟩
  apply (tendsto_iff_forall_inner_apply_tendsto (f:=id)).mpr
  intro x y
  have hh : Tendsto (fun U => inner ℂ y (T U x)) (ω : Filter (H →WOT[ℂ] H))
      (𝓝 (inner ℂ y (V x))) := by
    simpa only [RCLike.star_def,inner_conj_symm] using (hlim x y).star
  apply hh.congr'
  filter_upwards [Filter.le_principal_iff.mp hω] with U hU
  change inner ℂ y (T U x)=inner ℂ y (U x)
  change ‖U.toCLM‖≤C at hU
  dsimp [T]
  rw [ite_eq_left hU]
  rfl

lemma isClosed_normBall {C : ℝ} (hC : 0≤C) : IsClosed (normBall (H:=H) C) :=
  (isCompact_normBall hC).isClosed

omit [CompleteSpace H] in
lemma convex_normBall (C : ℝ) : Convex ℝ (normBall (H:=H) C) := by
  intro x hx y hy a b ha hb hab
  change ‖a • x.toCLM+b • y.toCLM‖≤C
  calc
    _ ≤ ‖a • x.toCLM‖+‖b • y.toCLM‖ := norm_add_le _ _
    _ = a*‖x.toCLM‖+b*‖y.toCLM‖ := by simp [norm_smul,abs_of_nonneg ha,abs_of_nonneg hb]
    _ ≤ a*C+b*C := add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
    _ = C := by rw [←add_mul,hab,one_mul]

def commutant (S : Set (H →L[ℂ] H)) : Submodule ℂ (H →WOT[ℂ] H) where
  carrier := {T | ∀ a∈S, ofCLM a*T=T*ofCLM a}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy a ha; simp [mul_add,add_mul,hx a ha,hy a ha]
  smul_mem' := by
    intro z x hx a ha
    apply toCLM_injective
    change a*(z • x.toCLM)=(z • x.toCLM)*a
    have hh : a*x.toCLM=x.toCLM*a := congrArg toCLM (hx a ha)
    rw [mul_smul_comm,smul_mul_assoc,hh]

omit [CompleteSpace H] in
lemma isClosed_commutant (S : Set (H →L[ℂ] H)) :
    IsClosed (commutant S : Set (H →WOT[ℂ] H)) := by
  change IsClosed {T | ∀ a∈S, ofCLM a*T=T*ofCLM a}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro a
  apply isClosed_iInter
  intro _
  exact isClosed_eq (continuous_const_mul _) (continuous_mul_const _)

lemma isClosed_commutant_add_ball (S : Set (H →L[ℂ] H)) {C : ℝ} (hC : 0≤C) :
    IsClosed ((commutant S : Set (H →WOT[ℂ] H))+normBall C) := by
  exact (isClosed_commutant S).add_right_of_isCompact (isCompact_normBall hC)

end Kadison.WOTDistance

end

end
end

end OAI
