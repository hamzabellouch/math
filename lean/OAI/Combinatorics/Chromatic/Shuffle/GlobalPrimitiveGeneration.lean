import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.GlobalPrimitiveLog
import OAI.Combinatorics.Chromatic.GradedAlgebra.NilpotentSeriesInverse

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open WithConv ElementaryPositivity.FiniteLog
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]
variable {A : Type*} [Ring A] [Algebra ℚ A]

lemma convSeries_exp_log {f : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A)}
    (hf : convVanishes a c η hc θ 1 f) :
    convSeries a c η hc θ (convSeries a c η hc θ f (PowerSeries.log ℚ)) (PowerSeries.exp ℚ)=1+f := by
  apply convolutionProjection_jointly_injective a c η hc θ
  intro n
  rw [convolutionProjection_series a c η hc θ n
    (convSeries_order_one a c η hc θ (PowerSeries.log ℚ) (PowerSeries.constantCoeff_log (A := ℚ))),
    convolutionProjection_series a c η hc θ n hf,map_add,map_one]
  exact nilEval_exp_log ⟨n,convolutionProjection_nilpotent a c η hc θ n hf⟩

theorem globalPrimitiveLog_exponential :
    convSeries a c η hc θ (toConv (globalPrimitiveLog a c η hc θ)) (PowerSeries.exp ℚ)=
      toConv (LinearMap.id : UnitalShuffle a c η hc θ →ₗ[ℚ] UnitalShuffle a c η hc θ) := by
  have h := convSeries_exp_log a c η hc θ (convolutionJ_vanishes a c η hc θ)
  change convSeries a c η hc θ (toConv (globalPrimitiveLog a c η hc θ)) (PowerSeries.exp ℚ)=_ at h
  rw [convolutionJ] at h
  convert h using 1; abel

lemma convolution_mapsTo_mul (S : Subalgebra ℚ A)
    {f g : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A)}
    (hf : ∀ x,f.ofConv x ∈ S) (hg : ∀ x,g.ofConv x ∈ S) :
    ∀ x,(f*g).ofConv x ∈ S := by
  intro x
  rw [LinearMap.convMul_apply]
  generalize Coalgebra.comul (R := ℚ) x=t
  induction t using TensorProduct.inductionOn with
  | add t u ht hu => simpa only [map_add] using S.add_mem ht hu
  | tmul x y =>
    rw [TensorProduct.map_tmul,LinearMap.mul'_apply]
    exact S.mul_mem (hf x) (hg y)

lemma convolution_mapsTo_pow (S : Subalgebra ℚ A)
    {f : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A)}
    (hf : ∀ x,f.ofConv x ∈ S) (n : ℕ) : ∀ x,(f^n).ofConv x ∈ S := by
  induction n with
  | zero => intro x; exact S.algebraMap_mem _
  | succ n ih =>
    rw [pow_succ]
    exact convolution_mapsTo_mul a c η hc θ S ih hf

theorem globalPrimitiveLog_adjoin :
    Algebra.adjoin ℚ (Set.range (globalPrimitiveLog a c η hc θ))=⊤ := by
  apply top_unique
  intro x hx
  clear hx
  induction x using DirectSum.induction_on with
  | zero => exact Subalgebra.zero_mem _
  | add x y hx hy => exact Subalgebra.add_mem _ hx hy
  | of k x =>
    let S := Algebra.adjoin ℚ (Set.range (globalPrimitiveLog a c η hc θ))
    have h := congrArg (fun f=>f.ofConv (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x))
      (globalPrimitiveLog_exponential a c η hc θ)
    rw [convSeries_lof] at h
    simp only [LinearMap.id_apply] at h
    change DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x ∈ S
    rw [←h]
    apply Subalgebra.sum_mem
    intro r hr
    exact S.smul_mem (convolution_mapsTo_pow a c η hc θ S
      (fun x=>Algebra.subset_adjoin ⟨x,rfl⟩) r _) _

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open WithConv DimensionSplit
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]

noncomputable def globalHomogeneous (k : SlopeWeight c η hc θ) : Submodule ℚ (UnitalShuffle a c η hc θ) :=
  LinearMap.range (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k)

def convPreservesWeight (f : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] UnitalShuffle a c η hc θ)) : Prop :=
  ∀ k (x : unitalComponent a c η hc θ k),
    f.ofConv (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x) ∈ globalHomogeneous a c η hc θ k

lemma globalHomogeneous_mul {k l : SlopeWeight c η hc θ} {x y : UnitalShuffle a c η hc θ}
    (hx : x ∈ globalHomogeneous a c η hc θ k) (hy : y ∈ globalHomogeneous a c η hc θ l) :
    x*y ∈ globalHomogeneous a c η hc θ (k+l) := by
  obtain ⟨x,rfl⟩ := hx
  obtain ⟨y,rfl⟩ := hy
  exact ⟨GradedMonoid.GMul.mul x y,(globalLof_mul a c η hc θ k l x y).symm⟩

lemma convPreservesWeight_one : convPreservesWeight a c η hc θ 1 := by
  intro k x
  change algebraMap ℚ (UnitalShuffle a c η hc θ)
    (globalCounit a c η hc θ (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x)) ∈ _
  by_cases hk : k=0
  · subst k
    rw [Algebra.algebraMap_eq_smul_one]
    apply Submodule.smul_mem
    exact ⟨unitalGradeOne a c η hc θ,rfl⟩
  · rw [globalCounit_lof_ne a c η hc θ k hk,map_zero]
    exact Submodule.zero_mem _

omit [Fact (SlopeEulerSymmetric a c η θ)] in
lemma convPreservesWeight_id : convPreservesWeight a c η hc θ (toConv LinearMap.id) :=
  fun _ x=>⟨x,rfl⟩

omit [Fact (SlopeEulerSymmetric a c η θ)] in
lemma convPreservesWeight_sub
    {f g : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] UnitalShuffle a c η hc θ)}
    (hf : convPreservesWeight a c η hc θ f) (hg : convPreservesWeight a c η hc θ g) :
    convPreservesWeight a c η hc θ (f-g) :=
  fun k x=>(globalHomogeneous a c η hc θ k).sub_mem (hf k x) (hg k x)

lemma globalTensorGrade_map_homogeneous (d e : slopeDimensions c η hc θ) (W : ℤ)
    (f g : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] UnitalShuffle a c η hc θ))
    (hf : convPreservesWeight a c η hc θ f) (hg : convPreservesWeight a c η hc θ g)
    (x : UnitalSourceTensorGrade a c η hc θ d.val e.val W) :
    LinearMap.mul' ℚ (UnitalShuffle a c η hc θ)
      (TensorProduct.map f.ofConv g.ofConv (globalTensorGradeInclusion a c η hc θ d e W x)) ∈
        globalHomogeneous a c η hc θ (d+e,W) := by
  induction x using unitalTensorGrade_induction a c η hc θ d.val e.val W with
  | hz => simpa only [map_zero] using (globalHomogeneous a c η hc θ (d+e,W)).zero_mem
  | ha x y hx hy => simpa only [map_add] using (globalHomogeneous a c η hc θ (d+e,W)).add_mem hx hy
  | ht u x y =>
    rw [globalTensorGradeInclusion_part,TensorProduct.map_tmul,LinearMap.mul'_apply]
    have h := globalHomogeneous_mul a c η hc θ (hf (d,u) x) (hg (e,W-u) y)
    have heq : (d,u)+(e,W-u)=(d+e,W) := by ext <;> simp
    rwa [heq] at h

lemma convPreservesWeight_mul
    {f g : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] UnitalShuffle a c η hc θ)}
    (hf : convPreservesWeight a c η hc θ f) (hg : convPreservesWeight a c η hc θ g) :
    convPreservesWeight a c η hc θ (f*g) := by
  intro k x
  rw [LinearMap.convMul_apply]
  change LinearMap.mul' ℚ (UnitalShuffle a c η hc θ) (TensorProduct.map f.ofConv g.ofConv
    (globalCoproduct a c η hc θ (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x))) ∈ _
  rw [globalCoproduct_lof]
  simp only [map_sum]
  apply Submodule.sum_mem
  intro s hs
  have h := globalTensorGrade_map_homogeneous a c η hc θ
    ⟨left s.val,s.property.1⟩ ⟨right s.val,s.property.2⟩ k.2 f g hf hg
    (unitalGradeCoproduct a c η hc θ (left s.val) (right s.val)
      (s.property.1.compatible s.property.2) k.2
      (unitalGradeCast a c η hc θ (left_add_right s.val).symm rfl x))
  have heq : (⟨left s.val,s.property.1⟩+⟨right s.val,s.property.2⟩ : slopeDimensions c η hc θ)=k.1 :=
    Subtype.ext (left_add_right s.val)
  rw [heq] at h
  exact h

lemma convPreservesWeight_pow
    {f : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] UnitalShuffle a c η hc θ)}
    (hf : convPreservesWeight a c η hc θ f) (n : ℕ) :
    convPreservesWeight a c η hc θ (f^n) := by
  induction n with
  | zero => exact convPreservesWeight_one a c η hc θ
  | succ n ih => rw [pow_succ]; exact convPreservesWeight_mul a c η hc θ ih hf

lemma globalPrimitiveLog_homogeneous :
    convPreservesWeight a c η hc θ (toConv (globalPrimitiveLog a c η hc θ)) := by
  intro k x
  change (convSeries a c η hc θ (convolutionJ a c η hc θ) (PowerSeries.log ℚ)).ofConv _ ∈ _
  rw [convSeries_lof]
  apply Submodule.sum_mem
  intro r hr
  exact Submodule.smul_mem _ _ (convPreservesWeight_pow a c η hc θ
    (convPreservesWeight_sub a c η hc θ (convPreservesWeight_id a c η hc θ)
      (convPreservesWeight_one a c η hc θ)) r k x)

end ElementaryPositivity.RawShuffle

end

end OAI
