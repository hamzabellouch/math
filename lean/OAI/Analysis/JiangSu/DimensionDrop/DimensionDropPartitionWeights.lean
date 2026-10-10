import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.DimensionDrop.DimensionDropFiberSections
import OAI.Analysis.JiangSu.TensorProducts.TensorCStarWeights
import OAI.Analysis.JiangSu.CStarAlgebras.EndpointPartition

namespace OAI

noncomputable section
namespace JiangSuConstruction

section
open Pureness
open scoped CStarAlgebra TensorProduct ComplexOrder

variable {p q : ℕ} {B : Type*} [CStarAlgebra B]
variable {J : Type*} [Fintype J]

def realScalarDrop (g : C(Interval,ℝ)) : DimensionDrop p q :=
  ⟨scalarMatrix g 1,by
    constructor
    · refine ⟨(g leftEndpoint:ℂ) • (1:Mat p),?_⟩
      change (leftAmplification p q) ((g leftEndpoint:ℂ) • (1:Mat p))=scalarMatrix g 1 leftEndpoint
      rw [map_smul,map_one,scalarMatrix_apply_complex]
    · refine ⟨(g rightEndpoint:ℂ) • (1:Mat q),?_⟩
      change (rightAmplification p q) ((g rightEndpoint:ℂ) • (1:Mat q))=scalarMatrix g 1 rightEndpoint
      rw [map_smul,map_one,scalarMatrix_apply_complex]⟩

lemma realScalarDrop_commute (g : C(Interval,ℝ)) (f : DimensionDrop p q) :
    Commute (realScalarDrop g) f := by
  show realScalarDrop g*f=f*realScalarDrop g
  apply Subtype.ext; apply ContinuousMap.ext; intro x
  change (g x • (1:TensorMat p q))*f.val x=f.val x*(g x • 1)
  rw [smul_mul_assoc,mul_smul_comm,one_mul,mul_one]

lemma realScalarDrop_selfAdjoint (g : C(Interval,ℝ)) :
    IsSelfAdjoint (realScalarDrop (p:=p) (q:=q) g) := by
  show star (realScalarDrop g)=realScalarDrop g
  apply Subtype.ext; apply ContinuousMap.ext; intro x
  change star (g x • (1:TensorMat p q))=g x • (1:TensorMat p q)
  simp

lemma realScalarDrop_sum (g : J → C(Interval,ℝ)) (hg : ∀ x,∑ j,g j x=1) :
    (∑ j,realScalarDrop (p:=p) (q:=q) (g j))=1 := by
  classical
  apply Subtype.ext; apply ContinuousMap.ext; intro x
  let ev := (evalHom p q x).comp (dimensionDrop p q).subtype
  change ev (∑ j,realScalarDrop (g j))=1
  rw [map_sum]
  change (∑ j,g j x • (1:TensorMat p q))=1
  rw [←Finset.sum_smul,hg,one_smul]

def realSqrtMap (g : C(Interval,ℝ)) : C(Interval,ℝ) :=
  ⟨fun x => Real.sqrt (g x),by fun_prop⟩

lemma realScalarDrop_sqrt_sq (g : C(Interval,ℝ)) (hg : ∀ x,0≤g x) :
    realScalarDrop (p:=p) (q:=q) (realSqrtMap g)*realScalarDrop (realSqrtMap g)=
      realScalarDrop g := by
  apply Subtype.ext; apply ContinuousMap.ext; intro x
  change (Real.sqrt (g x) • (1:TensorMat p q))*(Real.sqrt (g x) • 1)=g x • 1
  rw [smul_mul_assoc,mul_smul_comm,mul_one,smul_smul,Real.mul_self_sqrt (hg x)]

lemma realScalarDrop_tensor_commute (g : C(Interval,ℝ))
    (z : DimensionDrop p q ⊗[ℂ] B) : Commute (realScalarDrop g ⊗ₜ[ℂ] (1:B)) z := by
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    show (realScalarDrop g ⊗ₜ[ℂ] (1:B))*(a ⊗ₜ[ℂ] b)=
      (a ⊗ₜ[ℂ] b)*(realScalarDrop g ⊗ₜ[ℂ] (1:B))
    simp only [Algebra.TensorProduct.tmul_mul_tmul,one_mul,mul_one]
    rw [(realScalarDrop_commute g a).eq]
  | add x y hx hy => exact hx.add_right hy

lemma tensor_cstar_one_le (s : CStarAlgebraNorm (DimensionDrop p q ⊗[ℂ] B)) :
    s.toAlgebraNorm 1≤1 := by
  have h := s.cstar (1 : DimensionDrop p q ⊗[ℂ] B)
  simp only [star_one,one_mul] at h
  nlinarith [apply_nonneg s.toAlgebraNorm (1 : DimensionDrop p q ⊗[ℂ] B)]

lemma partition_tensor_bound (s : CStarAlgebraNorm (DimensionDrop p q ⊗[ℂ] B))
    (ρ : J → C(Interval,ℝ)) (hρ : ∀ j x,0≤ρ j x) (hsum : ∀ x,∑ j,ρ j x=1)
    (y : J → DimensionDrop p q ⊗[ℂ] B) {C : ℝ} (hC : 0≤C)
    (hy : ∀ j,s.toAlgebraNorm (y j)≤C) :
    s.toAlgebraNorm (∑ j,(realScalarDrop (p:=p) (q:=q) (ρ j) ⊗ₜ[ℂ] (1:B))*y j)≤C := by
  let v : J → DimensionDrop p q ⊗[ℂ] B :=
    fun j => realScalarDrop (p:=p) (q:=q) (realSqrtMap (ρ j)) ⊗ₜ[ℂ] 1
  have hv (j : J) : v j*v j=realScalarDrop (p:=p) (q:=q) (ρ j) ⊗ₜ[ℂ] (1:B) := by
    simp only [v,Algebra.TensorProduct.tmul_mul_tmul,one_mul,
      realScalarDrop_sqrt_sq _ (hρ j)]
  simp only [←hv]
  apply s.central_weighted_bound v y hC _ _ _ hy
  · intro j
    show star (v j)=v j
    simp only [v,TensorProduct.star_tmul,star_one,(realScalarDrop_selfAdjoint _).star_eq]
  · intro j
    exact realScalarDrop_tensor_commute _ _
  · simp only [hv,←TensorProduct.sum_tmul,realScalarDrop_sum ρ hsum,
      ←Algebra.TensorProduct.one_def]
    exact tensor_cstar_one_le s

end

section
open Pureness
open scoped CStarAlgebra TensorProduct ComplexOrder

variable {p q : ℕ} {J : Type*} [Fintype J]

abbrev dropEvaluation (p q : ℕ) (x : Interval) : DimensionDrop p q →⋆ₐ[ℂ] TensorMat p q :=
  (evalHom p q x).comp (dimensionDrop p q).subtype

def partitionInterpolate (t : J → Interval) (ρ g : J → C(Interval,ℝ))
    (h0 : ∀ j,t j≠leftEndpoint → g j leftEndpoint=0)
    (h1 : ∀ j,t j≠rightEndpoint → g j rightEndpoint=0)
    (f : DimensionDrop p q) : DimensionDrop p q :=
  ∑ j,realScalarDrop (ρ j)*fiberSection (t j) (g j) (h0 j) (h1 j) f

lemma partitionInterpolate_apply (t : J → Interval) (ρ g : J → C(Interval,ℝ)) (h0 h1)
    (f : DimensionDrop p q) (x : Interval) :
    (partitionInterpolate t ρ g h0 h1 f).val x=∑ j,ρ j x • (g j x • f.val (t j)) := by
  change dropEvaluation p q x (∑ j,_) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  change (ρ j x • (1:TensorMat p q))*(g j x • f.val (t j))=ρ j x • (g j x • f.val (t j))
  rw [smul_mul_assoc,one_mul]

lemma partitionInterpolate_error (t : J → Interval) (ρ g : J → C(Interval,ℝ)) (h0 h1)
    (hρ : ∀ j x,0≤ρ j x) (hsum : ∀ x,∑ j,ρ j x=1)
    (hg : ∀ j x,ρ j x≠0 → g j x=1) (f : DimensionDrop p q) {δ : ℝ} (hδ : 0≤δ)
    (hf : ∀ j x,ρ j x≠0 → ‖f.val x-f.val (t j)‖≤δ) :
    ‖partitionInterpolate t ρ g h0 h1 f-f‖≤δ := by
  classical
  apply (ContinuousMap.norm_le _ hδ).mpr
  intro x
  change ‖(partitionInterpolate t ρ g h0 h1 f).val x-f.val x‖≤δ
  rw [partitionInterpolate_apply]
  have he : (∑ j,ρ j x • (g j x • f.val (t j)))-f.val x=
      ∑ j,ρ j x • (g j x • f.val (t j)-f.val x) := by
    simp only [smul_sub,Finset.sum_sub_distrib]
    rw [←Finset.sum_smul,hsum,one_smul]
  rw [he]
  calc
    _ ≤ ∑ j,‖ρ j x • (g j x • f.val (t j)-f.val x)‖ := norm_sum_le _ _
    _ ≤ ∑ j,ρ j x*δ := by
      apply Finset.sum_le_sum
      intro j _
      rw [←complex_smul_real,norm_smul,Complex.norm_real,Real.norm_of_nonneg (hρ j x)]
      by_cases hj : ρ j x=0
      · simp [hj]
      · rw [hg j x hj,one_smul,norm_sub_rev]
        exact mul_le_mul_of_nonneg_left (hf j x hj) (hρ j x)
    _ = δ := by rw [←Finset.sum_mul,hsum,one_mul]

variable {B : Type*} [CStarAlgebra B] {ι : Type*} [Fintype ι]
lemma partitionInterpolate_tensor (t : J → Interval) (ρ g : J → C(Interval,ℝ)) (h0 h1)
    (f : ι → DimensionDrop p q) (b : ι → B) :
    (∑ l,partitionInterpolate t ρ g h0 h1 (f l) ⊗ₜ[ℂ] b l)=
      ∑ j,(realScalarDrop (p:=p) (q:=q) (ρ j) ⊗ₜ[ℂ] (1:B))*
        (∑ l,fiberSection (t j) (g j) (h0 j) (h1 j) (f l) ⊗ₜ[ℂ] b l) := by
  simp only [partitionInterpolate,TensorProduct.sum_tmul,Finset.mul_sum,
    Algebra.TensorProduct.tmul_mul_tmul,one_mul]
  rw [Finset.sum_comm]

end

open Pureness
open scoped CStarAlgebra TensorProduct ComplexOrder

universe v
variable {p q : ℕ} [NeZero p] [NeZero q]
variable {B : Type v} [CStarAlgebra B] {ι : Type*} [Fintype ι]

lemma dimensionDrop_tensor_bound_sum
    (r s : CStarAlgebraNorm (DimensionDrop p q ⊗[ℂ] B))
    (f : ι → DimensionDrop p q) (b : ι → B) :
    s.toAlgebraNorm (∑ l,f l ⊗ₜ[ℂ] b l) ≤
      fiberBound p q*r.toAlgebraNorm (∑ l,f l ⊗ₜ[ℂ] b l) := by
  classical
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := ε/(1+∑ l,‖b l‖)
  have hS : 0≤∑ l,‖b l‖ := Finset.sum_nonneg (fun l _ => norm_nonneg _)
  have hden : 0<1+∑ l,‖b l‖ := by linarith
  have hδ : 0<δ := div_pos hε hden
  obtain ⟨T,ρ,g,hρ,hsum,hg,h0,h1,hg1,hf⟩ :=
    EndpointPartition.exists_partition leftEndpoint rightEndpoint (fun l => (f l).val) hδ
  let F : ι → DimensionDrop p q := fun l =>
    partitionInterpolate (fun j:T => j.val) ρ g h0 h1 (f l)
  let z := ∑ l,f l ⊗ₜ[ℂ] b l
  let w := ∑ l,F l ⊗ₜ[ℂ] b l
  have hF (l : ι) : ‖f l-F l‖≤δ := by
    rw [norm_sub_rev]
    exact partitionInterpolate_error _ ρ g h0 h1 (fun j x => (hρ j x).1) hsum hg1 (f l)
      hδ.le (fun j x hx => (hf j x hx l).le)
  have herr : s.toAlgebraNorm (z-w)≤ε := by
    have he : z-w=∑ l,(f l-F l) ⊗ₜ[ℂ] b l := by
      simp only [z,w,TensorProduct.sub_tmul,Finset.sum_sub_distrib]
    rw [he]
    calc
      _ ≤ ∑ l,‖f l-F l‖*‖b l‖ := tensor_norm_sum_le s _ b
      _ ≤ ∑ l,δ*‖b l‖ := by gcongr with l; exact hF l
      _ = δ*(∑ l,‖b l‖) := by rw [Finset.mul_sum]
      _ ≤ ε := by
        dsimp [δ]
        rw [div_mul_eq_mul_div]
        apply (div_le_iff₀ hden).mpr
        nlinarith
  have hw : s.toAlgebraNorm w≤fiberBound p q*r.toAlgebraNorm z := by
    change s.toAlgebraNorm (∑ l,partitionInterpolate _ ρ g h0 h1 (f l) ⊗ₜ[ℂ] b l)≤_
    rw [partitionInterpolate_tensor]
    apply partition_tensor_bound s ρ (fun j x => (hρ j x).1) hsum _
      (mul_nonneg (fiberBound_nonneg p q) (apply_nonneg _ _))
    intro j
    exact fiberSection_tensor_bound r s f b j.val (g j) (h0 j) (h1 j)
      (fun x => by rw [abs_of_nonneg (hg j x).1]; exact (hg j x).2)
  have hn : s.toAlgebraNorm z ≤ s.toAlgebraNorm (z-w)+s.toAlgebraNorm w := by
    simpa only [sub_add_cancel] using map_add_le_add s.toAlgebraNorm (z-w) w
  exact hn.trans (by linarith)

lemma dimensionDrop_tensor_bound (r s : CStarAlgebraNorm (DimensionDrop p q ⊗[ℂ] B))
    (z : DimensionDrop p q ⊗[ℂ] B) :
    s.toAlgebraNorm z≤fiberBound p q*r.toAlgebraNorm z := by
  obtain ⟨n,f,b,rfl⟩ := TensorProduct.exists_sum_tmul_eq z
  exact dimensionDrop_tensor_bound_sum r s f b

theorem dimensionDrop_nuclear : IsNuclear.{0,v} (DimensionDrop p q) := by
  intro B _
  refine ⟨fun r s => CStarAlgebraNorm.eq_of_mutual_bound r s ?_ ?_⟩
  · exact ⟨fiberBound p q,dimensionDrop_tensor_bound s r⟩
  · exact ⟨fiberBound p q,dimensionDrop_tensor_bound r s⟩

end JiangSuConstruction
end

end OAI
