import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.TensorProducts.FaithfulTensorCrossNorm
import OAI.Analysis.JiangSu.Nuclearity.CompletelyPositiveOperations
import OAI.Analysis.JiangSu.Nonunital.Regularization
import OAI.Analysis.JiangSu.DimensionDrop.DimensionDrop

namespace OAI

noncomputable section


namespace JiangSuConstruction
open Pureness ConcreteMatrixUnits
open scoped TensorProduct CStarAlgebra ComplexOrder

variable {p q : ℕ} {B : Type*} [CStarAlgebra B]
local notation "I" => Fin p × Fin q
variable {ι : Type*} [Fintype ι]

lemma tensor_norm_sum_le (r : CStarAlgebraNorm (DimensionDrop p q ⊗[ℂ] B))
    (f : ι → DimensionDrop p q) (b : ι → B) :
    r.toAlgebraNorm (∑ l,f l ⊗ₜ[ℂ] b l) ≤ ∑ l,‖f l‖*‖b l‖ := by
  rw [←r.completionMap_norm,map_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro l _
  rw [r.completionMap_norm,NuclearUnitization.cstar_norm_tmul]

lemma tensor_norm_compress_le (r : CStarAlgebraNorm (DimensionDrop p q ⊗[ℂ] B))
    (a c : DimensionDrop p q) (ha : ‖a‖≤1) (hc : ‖c‖≤1)
    (z : DimensionDrop p q ⊗[ℂ] B) :
    r.toAlgebraNorm ((a ⊗ₜ[ℂ] (1:B))*z*(c ⊗ₜ[ℂ] (1:B))) ≤ r.toAlgebraNorm z := by
  have hOne : ‖(1 : B)‖ ≤ 1 := by
    have h : ‖star (1 : B) * (1 : B)‖ = ‖(1 : B)‖ * ‖(1 : B)‖ :=
      CStarRing.norm_star_mul_self
    simp only [star_one, one_mul] at h
    nlinarith [norm_nonneg (1 : B)]
  have h1 : r.toAlgebraNorm (a ⊗ₜ[ℂ] (1:B))≤1 := by
    rw [NuclearUnitization.cstar_norm_tmul]
    exact (mul_le_mul ha hOne (norm_nonneg _) (by norm_num)).trans (by norm_num)
  have h2 : r.toAlgebraNorm (c ⊗ₜ[ℂ] (1:B))≤1 := by
    rw [NuclearUnitization.cstar_norm_tmul]
    exact (mul_le_mul hc hOne (norm_nonneg _) (by norm_num)).trans (by norm_num)
  have h0 := apply_nonneg r.toAlgebraNorm z
  calc
    _ ≤ (r.toAlgebraNorm (a ⊗ₜ[ℂ] (1:B))*r.toAlgebraNorm z)*
        r.toAlgebraNorm (c ⊗ₜ[ℂ] (1:B)) :=
      (map_mul_le_mul r.toAlgebraNorm _ _).trans (mul_le_mul_of_nonneg_right
        (map_mul_le_mul r.toAlgebraNorm _ _) (apply_nonneg r.toAlgebraNorm _))
    _ ≤ (1*r.toAlgebraNorm z)*1 := by gcongr
    _ = r.toAlgebraNorm z := by ring

lemma interior_tensor_coefficient_le (r : CStarAlgebraNorm (DimensionDrop p q ⊗[ℂ] B))
    (f : ι → DimensionDrop p q) (b : ι → B) (t : Interval)
    (ht0 : t≠leftEndpoint) (ht1 : t≠rightEndpoint) (i j : I) :
    ‖∑ l,(f l).val t i j • b l‖ ≤ r.toAlgebraNorm (∑ l,f l ⊗ₜ[ℂ] b l) := by
  classical
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := ε/(1+∑ l,‖b l‖)
  have hS : 0 ≤ ∑ l,‖b l‖ := Finset.sum_nonneg (fun l _ => norm_nonneg _)
  have hden : 0<1+∑ l,‖b l‖ := by linarith
  have hδ : 0<δ := div_pos hε hden
  let V : Set Interval := {x | ∀ l,‖(f l).val x-(f l).val t‖<δ}
  have hV : IsOpen V := by
    dsimp only [V]
    rw [Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro l
    exact isOpen_lt (by fun_prop) continuous_const
  have htV : t∈V := by intro l; simpa using hδ
  obtain ⟨g,hgt,hg0,hg1,hg,hgV⟩ := exists_interior_bump t ht0 ht1 V hV htV
  have hga (x : Interval) : |g x|≤1 := by rw [abs_of_nonneg (hg x).1]; exact (hg x).2
  let a := interiorMatrix g hg0 hg1 (unit i i)
  let c := interiorMatrix g hg0 hg1 (unit j i)
  let d := interiorMatrix (g*g) (by simp [hg0]) (by simp [hg1]) (unit i i)
  have ha : ‖a‖≤1 := (interiorMatrix_norm_le _ _ _ _ hga).trans (unit_norm_le_one _ _)
  have hc : ‖c‖≤1 := (interiorMatrix_norm_le _ _ _ _ hga).trans (unit_norm_le_one _ _)
  have hd : ‖d‖=1 := by
    rw [interiorMatrix_norm_eq _ _ _ _ (fun x => ?_) t (by simp [hgt]),matrix_unit_norm]
    simpa only [ContinuousMap.mul_apply,abs_mul] using
      (mul_le_of_le_one_left (abs_nonneg _) (hga x)).trans (hga x)
  let β := ∑ l,(f l).val t i j • b l
  let z := ∑ l,f l ⊗ₜ[ℂ] b l
  let w := (a ⊗ₜ[ℂ] (1:B))*z*(c ⊗ₜ[ℂ] (1:B))
  have hw : r.toAlgebraNorm w≤r.toAlgebraNorm z := tensor_norm_compress_le r a c ha hc z
  have he : w - d ⊗ₜ[ℂ] β =
      ∑ l,(a*f l*c-(f l).val t i j • d) ⊗ₜ[ℂ] b l := by
    simp only [w,z,β,Finset.mul_sum,Finset.sum_mul,TensorProduct.tmul_sum,
      TensorProduct.sub_tmul,Finset.sum_sub_distrib,Algebra.TensorProduct.tmul_mul_tmul,
      one_mul,mul_one,TensorProduct.smul_tmul,TensorProduct.tmul_smul]
  have herr : r.toAlgebraNorm (w-d ⊗ₜ[ℂ] β)≤ε := by
    rw [he]
    calc
      _ ≤ ∑ l,‖a*f l*c-(f l).val t i j • d‖*‖b l‖ := tensor_norm_sum_le r _ _
      _ ≤ ∑ l,δ*‖b l‖ := by
        apply Finset.sum_le_sum
        intro l _
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact interior_compression_error g hg0 hg1 hga t i i j (f l) hδ.le
          (fun x hx => (hgV x hx l).le)
      _ = δ*(∑ l,‖b l‖) := by rw [Finset.mul_sum]
      _ ≤ ε := by dsimp [δ]; rw [div_mul_eq_mul_div]; apply (div_le_iff₀ hden).mpr; nlinarith
  have hn : r.toAlgebraNorm (d ⊗ₜ[ℂ] β) ≤ r.toAlgebraNorm w+r.toAlgebraNorm (w-d ⊗ₜ[ℂ] β) := by
    have hh := map_sub_le_add r.toAlgebraNorm w (w-d ⊗ₜ[ℂ] β)
    simpa only [sub_sub_cancel] using hh
  rw [NuclearUnitization.cstar_norm_tmul,hd,one_mul] at hn
  exact hn.trans (add_le_add hw herr)

lemma tensor_coefficient_le (r : CStarAlgebraNorm (DimensionDrop p q ⊗[ℂ] B))
    (f : ι → DimensionDrop p q) (b : ι → B) (t : Interval) (i j : I) :
    ‖∑ l,(f l).val t i j • b l‖ ≤ r.toAlgebraNorm (∑ l,f l ⊗ₜ[ℂ] b l) := by
  classical
  have hc : IsClosed {x : Interval | ‖∑ l,(f l).val x i j • b l‖ ≤
      r.toAlgebraNorm (∑ l,f l ⊗ₜ[ℂ] b l)} := isClosed_le (by fun_prop) continuous_const
  have hsub : Set.Ioo leftEndpoint rightEndpoint ⊆ {x : Interval |
      ‖∑ l,(f l).val x i j • b l‖ ≤ r.toAlgebraNorm (∑ l,f l ⊗ₜ[ℂ] b l)} := by
    intro x hx
    exact interior_tensor_coefficient_le r f b x (ne_of_gt hx.1) (ne_of_lt hx.2) i j
  apply closure_minimal hsub hc
  rw [closure_Ioo (show leftEndpoint≠rightEndpoint by
    intro h; have := congrArg Subtype.val h; norm_num [leftEndpoint,rightEndpoint] at this)]
  exact t.property

end JiangSuConstruction


namespace JiangSuConstruction
open Pureness ConcreteMatrixUnits CompletelyPositiveOperations
open scoped TensorProduct CStarAlgebra ComplexOrder

variable {p q : ℕ} {B : Type*} [CStarAlgebra B]
variable {ι J : Type*} [Fintype ι] [Fintype J] [DecidableEq J]

lemma matrix_unit_expansion (x : CStarMatrix J J ℂ) :
    x=∑ i,∑ j,x i j • unit i j := by
  ext a b
  simp [matrix_sum_apply,unit,CStarMatrix.ofMatrix_apply,Matrix.single_apply,ite_and]

lemma scalarMatrix_norm_le (g : C(Interval,ℝ)) (x : TensorMat p q)
    (hg : ∀ t,|g t|≤1) : ‖scalarMatrix g x‖≤‖x‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg x)).mpr
  intro t
  rw [scalarMatrix_apply_complex,norm_smul,Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _) (hg t)

def cutoffAmplification (g : C(Interval,ℝ))
    (T : CStarMatrix J J ℂ →⋆ₐ[ℂ] TensorMat p q)
    (h0 : g leftEndpoint≠0 → ∀ x,T x∈(leftAmplification p q).range)
    (h1 : g rightEndpoint≠0 → ∀ x,T x∈(rightAmplification p q).range) :
    CStarMatrix J J ℂ →ₗ[ℂ] DimensionDrop p q where
  toFun x := ⟨scalarMatrix g (T x),by
    constructor
    · change scalarMatrix g (T x) leftEndpoint∈(leftAmplification p q).range
      rw [scalarMatrix_apply_complex]
      by_cases h : g leftEndpoint=0
      · simp [h]
      · exact (leftAmplification p q).range.smul_mem (h0 h x) _
    · change scalarMatrix g (T x) rightEndpoint∈(rightAmplification p q).range
      rw [scalarMatrix_apply_complex]
      by_cases h : g rightEndpoint=0
      · simp [h]
      · exact (rightAmplification p q).range.smul_mem (h1 h x) _⟩
  map_add' x y := by
    apply Subtype.ext; ext t i j
    simp only [scalarMatrix_apply_complex,map_add,smul_add]
    rfl
  map_smul' z x := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro t
    change g t • T (z • x) = z • (g t • T x)
    rw [map_smul,smul_comm]

lemma cutoffAmplification_norm_le (g : C(Interval,ℝ))
    (T : CStarMatrix J J ℂ →⋆ₐ[ℂ] TensorMat p q) (h0 h1) (x : CStarMatrix J J ℂ)
    (hg : ∀ t,|g t|≤1) : ‖cutoffAmplification g T h0 h1 x‖≤‖x‖ :=
  (scalarMatrix_norm_le g (T x) hg).trans (NonUnitalStarAlgHom.norm_apply_le T x)

lemma tensor_basis_bound (s : CStarAlgebraNorm (DimensionDrop p q ⊗[ℂ] B))
    (L : CStarMatrix J J ℂ →ₗ[ℂ] DimensionDrop p q)
    (hL : ∀ i j,‖L (unit i j)‖≤1) (x : ι → CStarMatrix J J ℂ) (b : ι → B)
    {C : ℝ} (hC : 0≤C) (hx : ∀ i j,‖∑ l,x l i j • b l‖≤C) :
    s.toAlgebraNorm (∑ l,L (x l) ⊗ₜ[ℂ] b l) ≤ (Fintype.card J : ℝ)^2*C := by
  classical
  have he : (∑ l,L (x l) ⊗ₜ[ℂ] b l) =
      ∑ i,∑ j,L (unit i j) ⊗ₜ[ℂ] (∑ l,x l i j • b l) := by
    conv_lhs => arg 2; intro l; rw [matrix_unit_expansion (x l)]
    simp only [map_sum,map_smul,TensorProduct.sum_tmul,TensorProduct.smul_tmul,
      TensorProduct.tmul_sum,TensorProduct.tmul_smul]
    rw [Finset.sum_comm]
    congr 1
    funext i
    rw [Finset.sum_comm]
  rw [he,←s.completionMap_norm,map_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ i : J,∑ j : J,C := by
      apply Finset.sum_le_sum
      intro i _
      rw [map_sum]
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j _
      rw [s.completionMap_norm,NuclearUnitization.cstar_norm_tmul]
      exact (mul_le_mul_of_nonneg_left (hx i j) (norm_nonneg _)).trans
        (mul_le_of_le_one_left hC (hL i j))
    _ = (Fintype.card J : ℝ)^2*C := by simp; ring

lemma tensor_cutoff_bound (s : CStarAlgebraNorm (DimensionDrop p q ⊗[ℂ] B))
    (g : C(Interval,ℝ)) (T : CStarMatrix J J ℂ →⋆ₐ[ℂ] TensorMat p q)
    (h0 h1) (hg : ∀ t,|g t|≤1) (x : ι → CStarMatrix J J ℂ) (b : ι → B)
    {C : ℝ} (hC : 0≤C) (hx : ∀ i j,‖∑ l,x l i j • b l‖≤C) :
    s.toAlgebraNorm (∑ l,cutoffAmplification g T h0 h1 (x l) ⊗ₜ[ℂ] b l) ≤
      (Fintype.card J : ℝ)^2*C := by
  apply tensor_basis_bound s _ _ x b hC hx
  intro i j
  exact (cutoffAmplification_norm_le g T h0 h1 _ hg).trans (unit_norm_le_one _ _)

end JiangSuConstruction

end

end OAI
