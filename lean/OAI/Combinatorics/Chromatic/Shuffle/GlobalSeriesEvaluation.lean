import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.GlobalPrimitiveLog

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped DirectSum
open WithConv
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]
variable {A : Type*} [Ring A] [Algebra ℚ A]

lemma convSeries_eventually_finite
    {f : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A)}
    (hf : convVanishes a c η hc θ 1 f) (p : PowerSeries ℚ)
    (x : UnitalShuffle a c η hc θ) :
    ∃ N : ℕ, ∀ n, N ≤ n → (convSeries a c η hc θ f p).ofConv x=
      ∑ r ∈ Finset.range n,PowerSeries.coeff r p • (f^r).ofConv x := by
  induction x using DirectSum.induction_on with
  | zero => exact ⟨0,fun n _=>by simp⟩
  | add x y hx hy =>
    obtain ⟨N,hN⟩ := hx
    obtain ⟨M,hM⟩ := hy
    refine ⟨max N M,fun n hn=>?_⟩
    rw [map_add,hN n (le_trans (le_max_left _ _) hn),hM n (le_trans (le_max_right _ _) hn)]
    simp only [map_add,smul_add,Finset.sum_add_distrib]
  | of k x =>
    refine ⟨dimensionSize k.1.val+1,fun n hn=>?_⟩
    change (convSeries a c η hc θ f p).ofConv
      (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x)=
      ∑ r ∈ Finset.range n,PowerSeries.coeff r p •
        (f^r).ofConv (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x)
    rw [convSeries_lof]
    apply Finset.sum_subset (Finset.range_mono hn)
    intro r hr hsmall
    rw [Finset.mem_range,not_lt] at hsmall
    rw [convVanishes_pow a c η hc θ hf r k (by omega) x,smul_zero]

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open WithConv
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]

noncomputable def globalPrimitives : Submodule ℚ (UnitalShuffle a c η hc θ) :=
  LinearMap.ker (globalCoproduct a c η hc θ -
    ((TensorProduct.mk ℚ (UnitalShuffle a c η hc θ) (UnitalShuffle a c η hc θ)).flip
      (globalUnit a c η hc θ) +
      TensorProduct.mk ℚ (UnitalShuffle a c η hc θ) (UnitalShuffle a c η hc θ)
        (globalUnit a c η hc θ)))

lemma mem_globalPrimitives (x : UnitalShuffle a c η hc θ) :
    x ∈ globalPrimitives a c η hc θ ↔ globalCoproduct a c η hc θ x=
      x⊗ₜ[ℚ]globalUnit a c η hc θ+globalUnit a c η hc θ⊗ₜ[ℚ]x := by
  change globalCoproduct a c η hc θ x -
    (x⊗ₜ[ℚ]globalUnit a c η hc θ+globalUnit a c η hc θ⊗ₜ[ℚ]x)=0 ↔ _
  exact sub_eq_zero

lemma globalPrimitive_counit {x : UnitalShuffle a c η hc θ}
    (hx : x ∈ globalPrimitives a c η hc θ) : globalCounit a c η hc θ x=0 := by
  have h := globalCoproduct_counit_left a c η hc θ x
  rw [(mem_globalPrimitives a c η hc θ x).mp hx,map_add,
    TensorProduct.map_tmul,TensorProduct.map_tmul,globalCounit_unit,
    LinearMap.id_apply,LinearMap.id_apply] at h
  have he := congrArg (fun t=>globalCounit a c η hc θ
    (TensorProduct.lid ℚ (UnitalShuffle a c η hc θ) t)) h
  simp only [map_add,TensorProduct.lid_tmul,map_smul,globalCounit_unit,smul_eq_mul,
    mul_one,one_mul] at he
  exact add_eq_right.mp he

omit [Fact (SlopeEulerSymmetric a c η θ)] in
lemma convVanishes_unit {A : Type*} [Ring A] [Algebra ℚ A]
    {f : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A)}
    (hf : convVanishes a c η hc θ 1 f) : f.ofConv (globalUnit a c η hc θ)=0 :=
  hf (0,0) (by simp [dimensionSize]) (unitalGradeOne a c η hc θ)

lemma convolution_mul_primitive {A : Type*} [Ring A] [Algebra ℚ A]
    (f g : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A))
    {x : UnitalShuffle a c η hc θ} (hx : x ∈ globalPrimitives a c η hc θ) :
    (f*g).ofConv x=f.ofConv x*g.ofConv (globalUnit a c η hc θ)+
      f.ofConv (globalUnit a c η hc θ)*g.ofConv x := by
  rw [LinearMap.convMul_apply]
  change LinearMap.mul' ℚ A (TensorProduct.map f.ofConv g.ofConv
    (globalCoproduct a c η hc θ x))=_
  rw [(mem_globalPrimitives a c η hc θ x).mp hx,map_add,map_add]
  simp only [TensorProduct.map_tmul,LinearMap.mul'_apply]

lemma convolution_pow_primitive {A : Type*} [Ring A] [Algebra ℚ A]
    {f : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A)}
    (hf : convVanishes a c η hc θ 1 f)
    {x : UnitalShuffle a c η hc θ} (hx : x ∈ globalPrimitives a c η hc θ)
    (r : ℕ) (hr : 2 ≤ r) : (f^r).ofConv x=0 := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hr
  rw [show 2+r=(1+r)+1 by omega,pow_succ,convolution_mul_primitive a c η hc θ _ _ hx,
    convVanishes_unit a c η hc θ hf]
  have hp := convVanishes_mono a c η hc θ (by omega : 1 ≤ 1+r)
    (convVanishes_pow a c η hc θ hf (1+r))
  rw [convVanishes_unit a c η hc θ hp,mul_zero,zero_mul,add_zero]

lemma convolutionJ_primitive {x : UnitalShuffle a c η hc θ}
    (hx : x ∈ globalPrimitives a c η hc θ) :
    (convolutionJ a c η hc θ).ofConv x=x := by
  change x-algebraMap ℚ (UnitalShuffle a c η hc θ) (globalCounit a c η hc θ x)=x
  rw [globalPrimitive_counit a c η hc θ hx,map_zero,sub_zero]

lemma globalPrimitiveLog_homogeneous_primitive (k : SlopeWeight c η hc θ)
    (x : unitalComponent a c η hc θ k)
    (hx : DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x ∈ globalPrimitives a c η hc θ) :
    globalPrimitiveLog a c η hc θ (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x)=
      DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x := by
  change (convSeries a c η hc θ (convolutionJ a c η hc θ) (PowerSeries.log ℚ)).ofConv _=_
  rw [convSeries_lof]
  by_cases hd : dimensionSize k.1.val=0
  · have hz := zeroDimension_lof_scalar a c η hc θ k ((dimensionSize_eq_zero _).mp hd) x
    rw [globalPrimitive_counit a c η hc θ hx,zero_smul] at hz
    simp only [hd,zero_add,Finset.sum_range_one,PowerSeries.coeff_zero_eq_constantCoeff,
      PowerSeries.constantCoeff_log,zero_smul,hz]
  · rw [Finset.sum_eq_single 1]
    · rw [pow_one,convolutionJ_primitive a c η hc θ hx]
      simp
    · intro r hr hr1
      by_cases hr0 : r=0
      · subst r
        simp
      · rw [convolution_pow_primitive a c η hc θ (convolutionJ_vanishes a c η hc θ) hx r
          (by omega),smul_zero]
    · intro h
      exact False.elim (h (Finset.mem_range.mpr (by omega)))

theorem globalPrimitiveLog_on_primitive {x : UnitalShuffle a c η hc θ}
    (hx : x ∈ globalPrimitives a c η hc θ) : globalPrimitiveLog a c η hc θ x=x := by
  obtain ⟨N,hN⟩ := convSeries_eventually_finite a c η hc θ
    (convolutionJ_vanishes a c η hc θ) (PowerSeries.log ℚ) x
  change (convSeries a c η hc θ (convolutionJ a c η hc θ) (PowerSeries.log ℚ)).ofConv x=x
  rw [hN (max N 2) (le_max_left _ _),Finset.sum_eq_single 1]
  · rw [pow_one,convolutionJ_primitive a c η hc θ hx]
    simp
  · intro r hr hr1
    by_cases hr0 : r=0
    · subst r; simp
    · rw [convolution_pow_primitive a c η hc θ (convolutionJ_vanishes a c η hc θ) hx r
        (by omega),smul_zero]
  · intro h
    exact False.elim (h (Finset.mem_range.mpr (lt_of_lt_of_le (by omega) (le_max_right _ _))))

theorem globalPrimitiveLog_range : LinearMap.range (globalPrimitiveLog a c η hc θ)=
    globalPrimitives a c η hc θ := by
  apply le_antisymm
  · rintro y ⟨x,rfl⟩
    exact (mem_globalPrimitives a c η hc θ _).mpr (globalPrimitiveLog_primitive a c η hc θ x)
  · intro x hx
    exact ⟨x,globalPrimitiveLog_on_primitive a c η hc θ hx⟩

theorem globalPrimitiveLog_idempotent :
    (globalPrimitiveLog a c η hc θ).comp (globalPrimitiveLog a c η hc θ)=globalPrimitiveLog a c η hc θ := by
  apply LinearMap.ext
  intro x
  exact globalPrimitiveLog_on_primitive a c η hc θ
    ((mem_globalPrimitives a c η hc θ _).mpr (globalPrimitiveLog_primitive a c η hc θ x))

end ElementaryPositivity.RawShuffle

end

end OAI
