import OAI.Analysis.CharacterCriterion.Definitions
import OAI.Analysis.CharacterCriterion.MinimalFunctoriality

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped CStarAlgebra ComplexOrder
open scoped TensorProduct InnerProductSpace
open UniformSpace

namespace KirchbergRordam.PrimeProjectionless
open scoped CStarAlgebra Matrix
open MatrixDiagonalPath MatrixTensor DropMatrixRepresentations
variable {ι κ : Type*} [Fintype ι] [instDecidableEqι : DecidableEq ι] [Fintype κ] [DecidableEq κ]
def tr (a : CStarMatrix ι ι ℂ) : ℂ := ∑ i, a i i
omit instDecidableEqι in
lemma tr_continuous.{contextLevel1}
    {ι : Type contextLevel1}
    [Fintype ι]
    [DecidableEq ι]
    : Continuous (tr : CStarMatrix ι ι ℂ → ℂ) := by
  apply continuous_finsetSum
  intro i hi
  exact (continuous_apply i).comp (continuous_apply i)
lemma tr_nat (a : CStarMatrix ι ι ℂ) (ha : IsIdempotentElem a) :
    ∃ k : ℕ, k≤Fintype.card ι ∧ tr a=(k:ℂ) := by
  let e : CStarMatrix ι ι ℂ ≃ₐ[ℂ] ((ι → ℂ) →ₗ[ℂ] (ι → ℂ)) :=
    CStarMatrix.ofMatrixStarAlgEquiv.symm.toAlgEquiv.trans Matrix.toLinAlgEquiv'
  have h : IsIdempotentElem (e a) := by
    change e a*e a=e a
    rw [←map_mul,ha.eq]
  refine ⟨Module.finrank ℂ (LinearMap.range (e a)), ?_, ?_⟩
  · simpa using (LinearMap.range (e a)).finrank_le
  · have ht := (LinearMap.IsIdempotentElem.isProj_range (e a) h).trace
    change LinearMap.trace ℂ (ι → ℂ) (Matrix.toLin' (CStarMatrix.ofMatrixStarAlgEquiv.symm a)) = _ at ht
    rw [Matrix.trace_toLin'_eq] at ht
    exact ht
lemma tr_zero (a : CStarMatrix ι ι ℂ) (ha : IsIdempotentElem a) (ht : tr a=0) : a=0 := by
  let e : CStarMatrix ι ι ℂ ≃ₐ[ℂ] ((ι → ℂ) →ₗ[ℂ] (ι → ℂ)) :=
    CStarMatrix.ofMatrixStarAlgEquiv.symm.toAlgEquiv.trans Matrix.toLinAlgEquiv'
  have h : IsIdempotentElem (e a) := by
    change e a*e a=e a
    rw [←map_mul,ha.eq]
  apply e.injective
  rw [map_zero]
  apply LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero h
  change LinearMap.trace ℂ (ι → ℂ) (Matrix.toLin' (CStarMatrix.ofMatrixStarAlgEquiv.symm a)) = 0
  rw [Matrix.trace_toLin'_eq]
  exact ht
lemma tr_left (a : CStarMatrix ι ι ℂ) :
    tr (MatrixTensor.leftMatrix (κ:=κ) a)=(Fintype.card κ:ℂ)*tr a := by
  simp only [tr,Fintype.sum_prod_type,MatrixBlockReindex.left_apply,ite_true]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Finset.mul_sum,mul_one]
lemma tr_right (a : CStarMatrix κ κ ℂ) :
    tr (MatrixTensor.rightMatrix (ι:=ι) a)=(Fintype.card ι:ℂ)*tr a := by
  simp only [tr,Fintype.sum_prod_type,MatrixBlockReindex.right_apply,ite_true]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,one_mul]
lemma tr_constant {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (f : X → CStarMatrix ι ι ℂ) (hf : Continuous f) (hp : ∀ x, IsIdempotentElem (f x))
    (x y : X) : tr (f x)=tr (f y) := by
  let g : X → ℂ := fun x => tr (f x)
  have hc : Continuous g := tr_continuous.comp hf
  have hfin : (Set.range g).Finite := by
    apply ((Finset.range (Fintype.card ι+1)).finite_toSet.image (fun n : ℕ => (n:ℂ))).subset
    rintro _ ⟨x,rfl⟩
    obtain ⟨k,hk,he⟩ := tr_nat (f x) (hp x)
    exact ⟨k,Finset.mem_range.mpr (by omega),he.symm⟩
  by_contra hn
  exact hfin.not_infinite ((isPreconnected_range hc).infinite_of_nontrivial
    ⟨g x,⟨x,rfl⟩,g y,⟨y,rfl⟩,hn⟩)
lemma tr_one_sub (a : CStarMatrix ι ι ℂ) : tr (1-a)=(Fintype.card ι:ℂ)-tr a := by
  simp only [tr]
  simp
lemma prime_idempotent (p q : ℕ) [NeZero p] [NeZero q] (hpq : p.Coprime q)
    (e : PrimeDimensionDrop.Algebra p q) (he : IsIdempotentElem e) : e=0 ∨ e=1 := by
  have heval (t : unitInterval) : IsIdempotentElem (e.val t) := by
    have h := congrArg (fun f : PrimeDimensionDrop.Algebra p q => f.val t) he.eq
    exact h
  have hl : IsIdempotentElem (leftEvaluation p q e) := by
    change leftEvaluation p q e * leftEvaluation p q e = _
    rw [←map_mul,he.eq]
  have hr : IsIdempotentElem (rightEvaluation p q e) := by
    change rightEvaluation p q e * rightEvaluation p q e = _
    rw [←map_mul,he.eq]
  obtain ⟨k,hk,hke⟩ := tr_nat _ hl
  obtain ⟨l,hl,hle⟩ := tr_nat _ hr
  simp only [Fintype.card_fin] at hk hl
  have ht (t : unitInterval) : tr (e.val t) = tr (e.val 0) :=
    tr_constant e.val e.val.continuous heval t 0
  have hzero : tr (e.val 0)=(q:ℂ)*(k:ℂ) := by
    rw [←leftValue_spec p q e,tr_left,Fintype.card_fin]
    change (q:ℂ)*tr (leftEvaluation p q e) = _
    rw [hke]
  have hone : tr (e.val 1)=(p:ℂ)*(l:ℂ) := by
    rw [←rightValue_spec p q e,tr_right,Fintype.card_fin]
    change (p:ℂ)*tr (rightEvaluation p q e) = _
    rw [hle]
  have hkl : q*k=p*l := by
    have h := ht 1
    rw [hzero,hone] at h
    exact_mod_cast h.symm
  have hpk : p ∣ k := hpq.dvd_of_dvd_mul_left (hkl.symm ▸ dvd_mul_right p l)
  have hkeq : k=0 ∨ k=p := by
    by_cases h : k=0
    · exact Or.inl h
    · exact Or.inr (le_antisymm hk (Nat.le_of_dvd (Nat.pos_of_ne_zero h) hpk))
  rcases hkeq with rfl|rfl
  · left
    apply Subtype.ext
    apply ContinuousMap.ext
    intro t
    exact tr_zero (e.val t) (heval t) (by rw [ht t,hzero]; simp)
  · right
    have hz : 1-e=0 := by
      apply Subtype.ext
      apply ContinuousMap.ext
      intro t
      apply tr_zero (1-e.val t) (heval t).one_sub
      rw [tr_one_sub,ht t,hzero]
      simp only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul]
      ring
    exact (sub_eq_zero.mp hz).symm

end KirchbergRordam.PrimeProjectionless
namespace KirchbergRordam.ProjectionRounding
open scoped CStarAlgebra

def cut (t : ℝ) : ℝ := max 0 (min 1 (2*t-1/2))
lemma cut_continuous : Continuous cut := by unfold cut; fun_prop
lemma cut_low {t : ℝ} (h : t≤1/4) : cut t=0 := by
  unfold cut
  rw [max_eq_left]
  exact (min_le_right _ _).trans (by linarith)
lemma cut_high {t : ℝ} (h : 3/4≤t) : cut t=1 := by
  unfold cut
  rw [min_eq_left (by linarith),max_eq_right (by norm_num)]
lemma scalar_round {t : ℝ} (h : |t*t-t|<3/16) :
    (cut t=0 ∨ cut t=1) ∧ |t-cut t|≤1/4 := by
  have h' := abs_lt.mp h
  have hlo : -(1/4:ℝ)<t := by
    by_contra hn
    have := sq_nonneg (t+1/4)
    nlinarith
  have hhi : t<(5/4:ℝ) := by
    by_contra hn
    have := sq_nonneg (t-5/4)
    nlinarith
  have hg : t<1/4 ∨ 3/4<t := by
    by_contra hn
    push Not at hn
    have := mul_nonneg (show 0≤t-1/4 by linarith) (show 0≤3/4-t by linarith)
    nlinarith
  rcases hg with h|h
  · rw [cut_low h.le]
    exact ⟨Or.inl rfl,abs_le.mpr ⟨by linarith,by linarith⟩⟩
  · rw [cut_high h.le]
    exact ⟨Or.inr rfl,abs_le.mpr ⟨by linarith,by linarith⟩⟩
variable {A : Type*} [CStarAlgebra A]
lemma polynomial_cfc (a : A) (ha : IsSelfAdjoint a) :
    cfc (fun t : ℝ => t*t-t) a=a*a-a := by
  rw [cfc_sub (fun t : ℝ => t*t) (fun t => t) a (by fun_prop) (by fun_prop),
    cfc_mul (fun t : ℝ => t) (fun t => t) a (by fun_prop) (by fun_prop),cfc_id' ℝ a ha]
lemma spectrum_small_defect {a : A} (ha : IsSelfAdjoint a) (h : ‖a*a-a‖<3/16)
    {t : ℝ} (ht : t∈spectrum ℝ a) : |t*t-t|<3/16 := by
  have hn := norm_apply_le_norm_cfc (fun t : ℝ => t*t-t) a ht (by fun_prop) ha
  rw [polynomial_cfc a ha,Real.norm_eq_abs] at hn
  exact hn.trans_lt h
lemma cut_idempotent {a : A} (ha : IsSelfAdjoint a) (h : ‖a*a-a‖<3/16) :
    IsIdempotentElem (cfc cut a) := by
  change cfc cut a*cfc cut a=cfc cut a
  rw [←cfc_mul cut cut a cut_continuous.continuousOn cut_continuous.continuousOn]
  apply cfc_congr
  intro t ht
  rcases (scalar_round (spectrum_small_defect ha h ht)).1 with h|h <;> simp only [h,mul_zero,mul_one]
lemma cut_close {a : A} (ha : IsSelfAdjoint a) (h : ‖a*a-a‖<3/16) :
    ‖a-cfc cut a‖≤1/4 := by
  calc
    ‖a-cfc cut a‖ = ‖cfc (fun t : ℝ => t-cut t) a‖ := by
      rw [cfc_sub (fun t : ℝ => t) cut a (by fun_prop) cut_continuous.continuousOn,cfc_id' ℝ a ha]
    _ ≤ 1/4 := norm_cfc_le (by norm_num) (fun t ht =>
      (scalar_round (spectrum_small_defect ha h ht)).2)
end KirchbergRordam.ProjectionRounding
namespace KirchbergRordam.ProjectionRounding
open scoped CStarAlgebra
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
def part (a : A) : A := (1/2:ℂ) • (a+star a)
lemma part_selfAdjoint (a : A) : IsSelfAdjoint (part a) := by
  change star (part a)=part a
  simp only [part,star_smul,star_add,star_star]
  simp [add_comm]
lemma part_sub (a b : A) : part (a-b)=part a-part b := by
  simp only [part,star_sub,sub_add_sub_comm,smul_sub]
lemma part_fixed {a : A} (ha : IsSelfAdjoint a) : part a=a := by
  simp only [part,ha.star_eq,←two_smul ℂ a,smul_smul]
  norm_num
lemma part_map (φ : A →⋆ₐ[ℂ] B) (a : A) : φ (part a)=part (φ a) := by
  simp only [part,map_smul,map_add,map_star]
lemma norm_part_le (a : A) : ‖part a‖≤‖a‖ := by
  calc
    ‖part a‖ = (1/2:ℝ)*‖a+star a‖ := by rw [part,norm_smul]; simp
    _ ≤ (1/2:ℝ)*(‖a‖+‖star a‖) := mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ = ‖a‖ := by rw [norm_star]; ring
lemma norm_part_sub_le (a p : A) (hp : IsSelfAdjoint p) : ‖part a-p‖≤‖a-p‖ := by
  calc
    ‖part a-p‖=‖part (a-p)‖ := by rw [part_sub,part_fixed hp]
    _ ≤ _ := norm_part_le _
lemma idempotent_eq_zero_of_norm_lt_one {p : A} (hp : IsIdempotentElem p) (h : ‖p‖<1) : p=0 := by
  apply norm_eq_zero.mp
  have hn := norm_mul_le p p
  rw [hp.eq] at hn
  have hn0 := norm_nonneg p
  nlinarith
lemma small_defect_of_near (a p : A) (hp : IsStarProjection p) (h : ‖a-p‖<1/100) :
    ‖a*a-a‖<3/16 := by
  have hp1 := hp.norm_le p
  have ha2 : ‖a‖<2 := by
    have hn : ‖a‖≤‖a-p‖+‖p‖ := by
      simpa only [sub_add_cancel] using norm_add_le (a-p) p
    linarith
  have he : a*a-a=(a-p)*a+p*(a-p)-(a-p) := by
    have hpp := hp.isIdempotentElem.eq
    noncomm_ring [hpp]
  have hn : ‖a*a-a‖≤‖a-p‖*‖a‖+‖p‖*‖a-p‖+‖a-p‖ := by
    rw [he]
    exact (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))) le_rfl)
  have ha0 := norm_nonneg (a-p)
  have hn' := mul_le_mul_of_nonneg_left ha2.le ha0
  have hn'' := mul_le_mul_of_nonneg_right hp1 ha0
  nlinarith
lemma projection_trivial_from_approximation (φ : A →⋆ₐ[ℂ] B) (hφ : Isometry φ)
    (hA : ∀ a : A, IsIdempotentElem a → a=0 ∨ a=1)
    (a : A) (p : B) (hp : IsStarProjection p) (h : ‖φ a-p‖<1/100) : p=0 ∨ p=1 := by
  let b := part a
  have hb : IsSelfAdjoint b := part_selfAdjoint a
  have hclose : ‖φ b-p‖<1/100 := by
    rw [part_map]
    exact (norm_part_sub_le _ _ hp.isSelfAdjoint).trans_lt h
  have hnorm (x : A) : ‖φ x‖=‖x‖ := hφ.norm_map_of_map_zero (map_zero φ) x
  have hdefect : ‖b*b-b‖<3/16 := by
    rw [←hnorm (b*b-b),map_sub,map_mul]
    exact small_defect_of_near (φ b) p hp hclose
  have hq := cut_idempotent hb hdefect
  have hdist : ‖p-φ (cfc cut b)‖<1 := by
    calc
      ‖p-φ (cfc cut b)‖ ≤ ‖p-φ b‖+‖φ b-φ (cfc cut b)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ = ‖φ b-p‖+‖b-cfc cut b‖ := by rw [norm_sub_rev p,←map_sub,hnorm]
      _ < 1 := by have := cut_close hb hdefect; linarith
  rcases hA _ hq with hz|ho
  · left
    rw [hz,map_zero,sub_zero] at hdist
    exact idempotent_eq_zero_of_norm_lt_one hp.isIdempotentElem hdist
  · right
    rw [ho,map_one,norm_sub_rev] at hdist
    exact (sub_eq_zero.mp (idempotent_eq_zero_of_norm_lt_one hp.isIdempotentElem.one_sub hdist)).symm
end KirchbergRordam.ProjectionRounding
namespace KirchbergRordam.BalancedDropLimit
open scoped CStarAlgebra


theorem projectionless (p : Algebra) (hp : IsStarProjection p) : p=0 ∨ p=1 := by
  obtain ⟨v,hv⟩ := denseRange_inclusion.exists_dist_lt p (show (0:ℝ)<1/100 by norm_num)
  have h : ‖inclusion v.1 v.2-p‖<1/100 := by
    simpa only [dist_eq_norm,norm_sub_rev] using hv
  exact ProjectionRounding.projection_trivial_from_approximation
    (inclusion v.1) (inclusion_isometry v.1)
    (fun e he => PrimeProjectionless.prime_idempotent
      (BalancedDropMultiplicity.stage v.1) (BalancedDropMultiplicity.stage v.1+1)
      (BalancedDropMultiplicity.stage_coprime v.1) e he) v.2 p hp h
end KirchbergRordam.BalancedDropLimit
namespace KirchbergRordam


end KirchbergRordam
end

end OAI
