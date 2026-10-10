import OAI.Analysis.InterpolatedFactors.Cyclic

namespace OAI

noncomputable section

universe u_1 u_2 u_3

namespace FreeGroupFactorMain.WeightedFock

section
open FreeFock
variable {ι : Type u_1} [DecidableEq ι]

def vertexOld (u v : ℝ) (r : Bool) : oldAlgebra u v (∅ : Set ι) :=
  ⟨vertex r,by cases r;exact sub_mem (one_mem _) (P_mem_old u v ∅);exact P_mem_old u v ∅⟩

theorem vertex_mul_vertex (r s : Bool) : (vertex r : Operator ι)*vertex s=if r=s then vertex r else 0 := by
  cases r <;> cases s <;> simp only [vertex_false,vertex_true,Bool.false_eq_true,Bool.true_eq_false,
    ite_true,ite_false,mul_sub,sub_mul,one_mul,mul_one,projection_P.isIdempotentElem.eq]
  all_goals abel

theorem vertex_commute_empty (u v : ℝ) (r : Bool) (T : oldAlgebra u v (∅ : Set ι)) :
    Commute (vertex r : Operator ι) (T:Operator ι) := by
  have hp : P∈StarSubalgebra.centralizer ℂ (insert (P : Operator ι) (S u v '' (∅ : Set ι))) := by
    rw [StarSubalgebra.mem_centralizer_iff]
    intro y hy
    rcases hy with rfl | ⟨_,h,_⟩
    · exact ⟨rfl,by rw [projection_P.isSelfAdjoint.star_eq]⟩
    · exact False.elim h
  have hc := ((StarSubalgebra.mem_centralizer_iff ℂ).mp T.property P hp).1
  cases r
  · exact (Commute.one_left _).sub_left hc
  · exact hc

theorem vertex_empty_vertex (u v : ℝ) (r s : Bool) (T : oldAlgebra u v (∅ : Set ι)) :
    (vertex r : Operator ι)*(T:Operator ι)*vertex s=if r=s then (T:Operator ι)*vertex r else 0 := by
  rw [(vertex_commute_empty u v r T).eq,mul_assoc,vertex_mul_vertex]
  split_ifs <;> simp only [mul_zero]

def ambientRect (u v : ℝ) (i : ι) (r s : Bool) : Operator ι := vertex r*C u v i*vertex s

theorem ambientRect_covariance (u v : ℝ) (i j : ι) (r s t q : Bool)
    (T : oldAlgebra u v (∅ : Set ι)) :
    star (ambientRect u v i r s)*(T:Operator ι)*ambientRect u v j t q=
      if i=j ∧ r=t ∧ s=q then vacuumTrace u v ((T:Operator ι)*vertex r) • vertex s else 0 := by
  have hc := fresh_C_contraction u v ∅ i j (by simp) (by simp)
    (vertexOld u v r*T*vertexOld u v t)
  change star (C u v i)*(vertex r*(T:Operator ι)*vertex t)*C u v j=_ at hc
  have hh : star (ambientRect u v i r s)*(T:Operator ι)*ambientRect u v j t q=
      if i=j then vacuumTrace u v (vertex r*(T:Operator ι)*vertex t) • (vertex s*vertex q) else 0 := by
    calc
      _ = vertex s*(star (C u v i)*(vertex r*(T:Operator ι)*vertex t)*C u v j)*vertex q := by
        simp only [ambientRect,star_mul,vertex_star,mul_assoc]
      _ = _ := by
        rw [hc]
        split_ifs <;> simp only [mul_smul_comm,smul_mul_assoc,mul_one,mul_zero,zero_mul]
        rfl
  rw [vertex_empty_vertex,vertex_mul_vertex] at hh
  rw [hh]
  have hz : vacuumTrace u v (0:Operator ι)=0 := by simp only [vacuumTrace,zero_apply,inner_zero_right]
  by_cases hij : i=j <;> by_cases hrt : r=t <;> by_cases hsq : s=q <;>
    simp [hij,hrt,hsq,hz,smul_zero (M := ℂ) (A := Operator ι),zero_smul ℂ (A := Operator ι)]

theorem ambientRect_annihilate (u v : ℝ) (i : ι) (r s : Bool)
    (T : oldAlgebra u v (∅ : Set ι)) :
    star (ambientRect u v i r s) ((T:Operator ι) (vacuum u v))=0 := by
  have hh := fresh_C_annihilates_old_vacuum u v ∅ i (by simp) (vertexOld u v r*T)
  simp only [ambientRect,star_mul,vertex_star,mul_apply_eq_comp]
  change star (C u v i) (vertex r ((T:Operator ι) (vacuum u v)))=0 at hh
  rw [hh,map_zero]

variable (u v : ℝ) (i : ι)
def diagonalCreate : Operator ι := ambientRect u v i true true+ambientRect u v i false false

def diagonalCovariance (T : oldAlgebra u v (∅ : Set ι)) : oldAlgebra u v (∅ : Set ι) :=
  vacuumTrace u v ((T:Operator ι)*vertex true) • vertexOld u v true+
    vacuumTrace u v ((T:Operator ι)*vertex false) • vertexOld u v false

theorem diagonalCreate_covariance (T : oldAlgebra u v (∅ : Set ι)) :
    star (diagonalCreate u v i)*(T:Operator ι)*diagonalCreate u v i=
      (diagonalCovariance u v T : Operator ι) := by
  simp only [diagonalCreate,star_add (R := Operator ι),add_mul,mul_add,ambientRect_covariance,
    Bool.true_eq_false,Bool.false_eq_true,and_self,and_false,ite_true,ite_false,add_zero,zero_add]
  rfl

theorem diagonalCreate_annihilate (T : oldAlgebra u v (∅ : Set ι)) :
    star (diagonalCreate u v i) ((T:Operator ι) (vacuum u v))=0 := by
  simp only [diagonalCreate,star_add (R := Operator ι),add_apply,ambientRect_annihilate,add_zero]

theorem ambientRect_diagonal_orthogonal (r : Bool) (T : oldAlgebra u v (∅ : Set ι)) :
    star (ambientRect u v i r (!r))*(T:Operator ι)*diagonalCreate u v i=0 := by
  cases r <;> simp only [diagonalCreate,mul_add,ambientRect_covariance,Bool.not_false,Bool.not_true,
    Bool.false_eq_true,Bool.true_eq_false,and_false,and_true,ite_false,add_zero]

def diagonalBase : StarSubalgebra ℂ (Operator ι) :=
  Bicommutant.algebra (insert (diagonalCreate u v i+star (diagonalCreate u v i))
    (oldAlgebra u v (∅ : Set ι) : Set (Operator ι)))

theorem diagonal_base_annihilate (r : Bool) (T : diagonalBase u v i) :
    star (ambientRect u v i r (!r)) ((T:Operator ι) (vacuum u v))=0 :=
  GaussianExtension.annihilation_extension (oldAlgebra u v ∅) (diagonalCreate u v i)
    (diagonalCovariance u v) (diagonalCreate_covariance u v i)
    (ambientRect u v i r (!r)) (vacuum u v) (diagonalCreate_annihilate u v i)
    (fun a => ambientRect_annihilate u v i r (!r) a)
    (ambientRect_diagonal_orthogonal u v i r) T T.property

theorem diagonal_vertex_annihilate (r : Bool) (T : oldAlgebra u v (∅ : Set ι)) :
    star (diagonalCreate u v i) ((T:Operator ι) (vertex r (vacuum u v)))=0 := by
  have hh := diagonalCreate_annihilate u v i (T*vertexOld u v r)
  change star (diagonalCreate u v i) (((T:Operator ι)*vertex r : Operator ι) (vacuum u v))=0 at hh
  exact hh

theorem diagonal_residual_covariance (r : Bool) (T : diagonalBase u v i) :
    star (ambientRect u v i r (!r))*(T:Operator ι)*ambientRect u v i r (!r)=
      inner ℂ (vertex r (vacuum u v)) ((T:Operator ι) (vertex r (vacuum u v))) • vertex (!r) := by
  apply GaussianExtension.covariance_extension (oldAlgebra u v ∅) (diagonalCreate u v i)
    (diagonalCovariance u v) (diagonalCreate_covariance u v i)
    (ambientRect u v i r (!r)) (ambientRect u v i r (!r)) (vertex (!r))
    (vertex r (vacuum u v)) (vertex r (vacuum u v))
    (diagonal_vertex_annihilate u v i r) (diagonal_vertex_annihilate u v i r)
    (ambientRect_diagonal_orthogonal u v i r)
    (GaussianOrthogonal.symm (ambientRect_diagonal_orthogonal u v i r)) ?_ T T.property
  intro a
  rw [ambientRect_covariance,ite_eq_left ⟨rfl,rfl,rfl⟩]
  congr 1
  rw [← ContinuousLinearMap.adjoint_inner_right (vertex r)]
  change inner ℂ (vacuum u v) (((a:Operator ι)*vertex r : Operator ι) (vacuum u v))=
    inner ℂ (vacuum u v) ((star (vertex r)*((a:Operator ι)*vertex r) : Operator ι) (vacuum u v))
  rw [vertex_star,← mul_assoc,vertex_empty_vertex,ite_eq_left rfl]
end

section
open FreeFock
variable {ι : Type u_2} [DecidableEq ι]

theorem vertex_projection (r : Bool) : IsStarProjection (vertex r : Operator ι) := by
  rw [vertex_eq_proj]
  exact CoordinateProjection.projection _

theorem ambientRect_left (u v : ℝ) (i : ι) (r s : Bool) :
    vertex r*ambientRect u v i r s=ambientRect u v i r s := by
  rw [ambientRect,← mul_assoc,← mul_assoc,vertex_mul_vertex,ite_eq_left rfl]

theorem ambientRect_right (u v : ℝ) (i : ι) (r s : Bool) :
    ambientRect u v i r s*vertex s=ambientRect u v i r s := by
  rw [ambientRect,mul_assoc,vertex_mul_vertex,ite_eq_left rfl]

def diagonalLeg (u v : ℝ) (i : ι) (r : Bool) : Operator ι :=
  ambientRect u v i r r+star (ambientRect u v i r r)

theorem diagonalLeg_selfAdjoint (u v : ℝ) (i : ι) (r : Bool) :
    IsSelfAdjoint (diagonalLeg u v i r) := IsSelfAdjoint.add_star_self (ambientRect u v i r r)

theorem diagonalLeg_left (u v : ℝ) (i : ι) (r : Bool) :
    vertex r*diagonalLeg u v i r=diagonalLeg u v i r := by
  have hs := congrArg star (ambientRect_right u v i r r)
  simp only [star_mul,vertex_star] at hs
  rw [diagonalLeg,mul_add,ambientRect_left,hs]

theorem diagonalLeg_right (u v : ℝ) (i : ι) (r : Bool) :
    diagonalLeg u v i r*vertex r=diagonalLeg u v i r := by
  simpa only [star_mul,vertex_star,(diagonalLeg_selfAdjoint u v i r).star_eq] using
    congrArg star (diagonalLeg_left u v i r)

theorem vertexRoot_inner (u v : ℝ) (r : Bool) :
    inner ℂ (vertex r (vacuum u v : H ι)) (vertex r (vacuum u v))=vacuumTrace u v (vertex r : Operator ι) := by
  rw [← ContinuousLinearMap.adjoint_inner_right (vertex r : Operator ι)]
  change inner ℂ (vacuum u v) ((star (vertex r)*vertex r : Operator ι) (vacuum u v))=_
  rw [vertex_star,vertex_mul_vertex,ite_eq_left rfl]
  rfl

theorem vertexRoot_ne_zero (u v : ℝ) (hu : u≠0) (hv : v≠0) (r : Bool) :
    vertex r (vacuum u v : H ι)≠0 := by
  intro hz
  have hh := congrArg (fun ξ : H ι => ξ ([],r)) hz
  cases r
  · apply hv
    simpa only [weight,vertex_vacuum,Bool.false_eq_true,ite_false,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,
      lp.single_apply,Pi.single_eq_same,mul_one,lp.coeFn_zero,Pi.zero_apply,Complex.ofReal_eq_zero] using hh
  · apply hu
    simpa only [weight,vertex_vacuum,ite_true,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,
      lp.single_apply,Pi.single_eq_same,mul_one,lp.coeFn_zero,Pi.zero_apply,Complex.ofReal_eq_zero] using hh

theorem diagonalLeg_eigen_root_zero (u v : ℝ) (hu : u≠0) (hv : v≠0) (i : ι)
    (r : Bool) (z : ℂ) (η : H ι) (he : diagonalLeg u v i r η=z • η) :
    inner ℂ (vertex r (vacuum u v)) η=0 := by
  apply SupportedSemicircle.unnormalized_eigen_root_zero
    (vertex r) (ambientRect u v i r r) (vertex_projection r)
    (ambientRect_left u v i r r) (ambientRect_right u v i r r)
    _ (vertexRoot_ne_zero u v hu hv r) _ _ _ z η he
  · exact DFunLike.congr_fun (vertex_projection (ι := ι) r).isIdempotentElem.eq _
  · rw [vertexRoot_inner]
    have hh := ambientRect_covariance u v i i r r r r (1:oldAlgebra u v ∅)
    simpa only [OneMemClass.coe_one,mul_one,one_mul,ite_true,and_self] using hh
  · exact ambientRect_annihilate u v i r r (vertexOld u v r)

def diagonalSelf (u v : ℝ) (i : ι) : Operator ι := diagonalLeg u v i true+diagonalLeg u v i false

theorem diagonalSelf_eq (u v : ℝ) (i : ι) :
    diagonalSelf u v i=diagonalCreate u v i+star (diagonalCreate u v i) := by
  simp only [diagonalSelf,diagonalLeg,diagonalCreate,star_add (R := Operator ι)]
  abel

def diagonalShift (u v : ℝ) (i : ι) : ℝ := 2*‖diagonalSelf u v i‖+1

def diagonalGenerator (u v : ℝ) (i : ι) : Operator ι := diagonalSelf u v i+(diagonalShift u v i:ℂ) • P

theorem diagonalSelf_selfAdjoint (u v : ℝ) (i : ι) : IsSelfAdjoint (diagonalSelf u v i) := by
  rw [diagonalSelf_eq]
  exact IsSelfAdjoint.add_star_self (diagonalCreate u v i)

theorem diagonalGenerator_selfAdjoint (u v : ℝ) (i : ι) : IsSelfAdjoint (diagonalGenerator u v i) := by
  change star (_+_)=_+_
  simp only [star_add (R := Operator ι),(diagonalSelf_selfAdjoint u v i).star_eq,star_smul,Complex.star_def,
    Complex.conj_ofReal,projection_P.isSelfAdjoint.star_eq]

theorem diagonalGenerator_eigen_root_zero (u v : ℝ) (hu : u≠0) (hv : v≠0) (i : ι)
    (z : ℂ) (η : H ι) (he : diagonalGenerator u v i η=z • η) : inner ℂ (vacuum u v) η=0 := by
  have hh := OrthogonalSpectralSum.eigen_root_zero (vertex true) (vertex false)
    (diagonalLeg u v i true) (diagonalLeg u v i false) (vertex_projection true) (vertex_projection false)
    (by rw [vertex_mul_vertex];rfl) (diagonalLeg_left u v i true) (diagonalLeg_right u v i true)
    (diagonalLeg_left u v i false) (diagonalLeg_right u v i false) (vacuum u v)
    (diagonalLeg_eigen_root_zero u v hu hv i true) (diagonalLeg_eigen_root_zero u v hu hv i false)
    (diagonalShift u v i) z η he
  simpa only [vertex_true,vertex_false,add_sub_cancel,one_apply_eq_self] using hh

theorem P_mem_diagonalBase (u v : ℝ) (i : ι) : P∈diagonalBase u v i :=
  Bicommutant.subset _ (Set.mem_insert_of_mem _ (P_mem_old u v ∅))

theorem diagonalSelf_mem (u v : ℝ) (i : ι) : diagonalSelf u v i∈diagonalBase u v i := by
  rw [diagonalSelf_eq]
  exact Bicommutant.subset _ (Set.mem_insert _ _)

theorem diagonalGenerator_mem (u v : ℝ) (i : ι) : diagonalGenerator u v i∈diagonalBase u v i :=
  add_mem (diagonalSelf_mem u v i) ((diagonalBase u v i).smul_mem (P_mem_diagonalBase u v i) _)

theorem P_commute_diagonalSelf (u v : ℝ) (i : ι) : Commute P (diagonalSelf u v i) := by
  have hf : Commute P (diagonalLeg u v i true) :=
    (diagonalLeg_left u v i true).trans (diagonalLeg_right u v i true).symm
  have hq : Commute (1-P) (diagonalLeg u v i false) :=
    (diagonalLeg_left u v i false).trans (diagonalLeg_right u v i false).symm
  have hp := (Commute.one_left (diagonalLeg u v i false)).sub_left hq
  rw [sub_sub_cancel] at hp
  exact hf.add_right hp

theorem diagonalBase_eq_generated (u v : ℝ) (i : ι) :
    diagonalBase u v i=Bicommutant.algebra {diagonalGenerator u v i} := by
  apply le_antisymm
  · have hp : P∈Bicommutant.algebra {diagonalGenerator u v i} :=
      SpectralSeparation.separated_projection_mem projection_P (diagonalSelf_selfAdjoint u v i)
        (P_commute_diagonalSelf u v i) (diagonalShift u v i) (by dsimp [diagonalShift];linarith)
    apply Bicommutant.generated_le
    rintro T (rfl|hT)
    · rw [← diagonalSelf_eq]
      have he : diagonalSelf u v i=diagonalGenerator u v i-(diagonalShift u v i:ℂ) • P := by
        rw [diagonalGenerator,add_sub_cancel_right]
      rw [he]
      exact sub_mem (Bicommutant.subset _ (Set.mem_singleton _)) ((Bicommutant.algebra _).smul_mem hp _)
    · apply Bicommutant.generated_le {diagonalGenerator u v i}
        (insert (P:Operator ι) (S u v '' (∅:Set ι))) ?_ hT
      rintro a (rfl|⟨_,h,_⟩)
      · exact hp
      · exact False.elim h
  · apply Bicommutant.generated_le
    rintro T rfl
    exact diagonalGenerator_mem u v i
end

section
open FreeFock GaussianOrthogonal
variable {ι : Type u_3} [DecidableEq ι]

theorem diagonalBase_vertex_commute (u v : ℝ) (i : ι) (r : Bool) (T : diagonalBase u v i) :
    Commute (vertex r : Operator ι) (T:Operator ι) := by
  have hp : P∈StarSubalgebra.centralizer ℂ {diagonalGenerator u v i} := by
    rw [StarSubalgebra.mem_centralizer_iff]
    rintro a rfl
    have hc : Commute P (diagonalGenerator u v i) :=
      (P_commute_diagonalSelf u v i).add_right ((Commute.refl P).smul_right _)
    exact ⟨hc.eq.symm,by rw [(diagonalGenerator_selfAdjoint u v i).star_eq];exact hc.eq.symm⟩
  have hh : (T:Operator ι)∈Bicommutant.algebra {diagonalGenerator u v i} :=
    (diagonalBase_eq_generated u v i).le T.property
  have hc := ((StarSubalgebra.mem_centralizer_iff ℂ).mp hh P hp).1
  cases r
  · exact (Commute.one_left _).sub_left hc
  · exact hc

theorem diagonal_residual_trace (u v : ℝ) (i : ι) (r : Bool) (T : diagonalBase u v i) :
    star (ambientRect u v i r (!r))*(T:Operator ι)*ambientRect u v i r (!r)=
      vacuumTrace u v ((T:Operator ι)*vertex r) • vertex (!r) := by
  rw [diagonal_residual_covariance]
  congr 1
  rw [← ContinuousLinearMap.adjoint_inner_right (vertex r : Operator ι)]
  change inner ℂ (vacuum u v) ((star (vertex r)*((T:Operator ι)*vertex r) : Operator ι) (vacuum u v))=_
  rw [vertex_star,← mul_assoc,(diagonalBase_vertex_commute u v i r T).eq,mul_assoc,
    vertex_mul_vertex,ite_eq_left rfl]
  rfl

theorem diagonal_residual_orthogonal (u v : ℝ) (i : ι) (r s : Bool) (hrs : r≠s)
    (T : diagonalBase u v i) :
    star (ambientRect u v i r (!r))*(T:Operator ι)*ambientRect u v i s (!s)=0 := by
  apply GaussianExtension.orthogonality_extension (oldAlgebra u v ∅) (diagonalCreate u v i)
    (diagonalCovariance u v) (diagonalCreate_covariance u v i)
    (ambientRect u v i r (!r)) (ambientRect u v i s (!s))
    (ambientRect_diagonal_orthogonal u v i r)
    (GaussianOrthogonal.symm (ambientRect_diagonal_orthogonal u v i s)) ?_ T T.property
  intro a
  rw [ambientRect_covariance,ite_eq_right (by simp only [hrs,and_false,false_and,not_false_eq_true])]

theorem rect_paired_eq (u v : ℝ) (i : ι) (r s : Bool) :
    ambientRect u v i r s+star (ambientRect u v i s r)=vertex r*S u v i*vertex s := by
  change _=vertex r*(C u v i+star (C u v i))*vertex s
  simp only [ambientRect,star_mul,vertex_star,mul_add,add_mul,mul_assoc]

theorem vertex_mem_old (u v : ℝ) (J : Set ι) (r : Bool) : (vertex r : Operator ι)∈oldAlgebra u v J := by
  cases r
  · exact sub_mem (one_mem _) (P_mem_old u v J)
  · exact P_mem_old u v J

theorem oldAlgebra_mono (u v : ℝ) {J K : Set ι} (h : J⊆K) : oldAlgebra u v J≤oldAlgebra u v K := by
  apply StarSubalgebra.centralizer_le
  apply StarSubalgebra.centralizer_le
  exact Set.insert_subset_insert (Set.image_mono h)

theorem diagonalBase_le_singleton (u v : ℝ) (i : ι) : diagonalBase u v i≤oldAlgebra u v {i} := by
  apply Bicommutant.generated_le
  rintro T (rfl|hT)
  · rw [← diagonalSelf_eq,diagonalSelf,diagonalLeg,diagonalLeg,rect_paired_eq,rect_paired_eq]
    exact add_mem (mul_mem (mul_mem (vertex_mem_old u v _ _) (S_mem_old u v _ i rfl)) (vertex_mem_old u v _ _))
      (mul_mem (mul_mem (vertex_mem_old u v _ _) (S_mem_old u v _ i rfl)) (vertex_mem_old u v _ _))
  · exact oldAlgebra_mono u v (Set.empty_subset {i}) hT

theorem diagonalBase_le_ambient (u v : ℝ) (i : ι) : diagonalBase u v i≤ambientAlgebra u v :=
  (diagonalBase_le_singleton u v i).trans (by
    apply StarSubalgebra.centralizer_le
    apply StarSubalgebra.centralizer_le
    exact Set.insert_subset_insert (by rintro _ ⟨j,_,rfl⟩;exact Set.mem_range_self j))

theorem ambient_C_rect_empty (u v : ℝ) (i n : ι) (hn : n≠i) (r s : Bool)
    (T : oldAlgebra u v (∅:Set ι)) : star (C u v n)*(T:Operator ι)*ambientRect u v i r s=0 := by
  have hh := fresh_C_contraction u v ∅ n i (by simp) (by simp) (T*vertexOld u v r)
  rw [ite_eq_right hn] at hh
  change star (C u v n)*((T:Operator ι)*vertex r)*C u v i=0 at hh
  calc
    _ = (star (C u v n)*((T:Operator ι)*vertex r)*C u v i)*vertex s := by simp only [ambientRect,mul_assoc]
    _ = 0 := by rw [hh,zero_mul]

theorem ambient_C_diagonal_empty (u v : ℝ) (i n : ι) (hn : n≠i)
    (T : oldAlgebra u v (∅:Set ι)) : star (C u v n)*(T:Operator ι)*diagonalCreate u v i=0 := by
  rw [diagonalCreate,mul_add,ambient_C_rect_empty u v i n hn,ambient_C_rect_empty u v i n hn,add_zero]

theorem ambient_C_residual (u v : ℝ) (i n : ι) (hn : n≠i) (r : Bool)
    (T : diagonalBase u v i) : star (C u v n)*(T:Operator ι)*ambientRect u v i r (!r)=0 := by
  exact GaussianExtension.orthogonality_extension (oldAlgebra u v ∅) (diagonalCreate u v i)
    (diagonalCovariance u v) (diagonalCreate_covariance u v i) (C u v n) (ambientRect u v i r (!r))
    (ambient_C_diagonal_empty u v i n hn)
    (GaussianOrthogonal.symm (ambientRect_diagonal_orthogonal u v i r))
    (ambient_C_rect_empty u v i n hn r (!r)) T T.property
end

open FreeFock WeightedCornerIndex

def residualIndex (b : Bool) : WeightedCornerIndex.Index := .inr (.inl 0,b)
def residualSlot : WeightedCornerIndex.Index → Option Bool
  | .inr (.inl 0,b) => some b
  | _ => none

theorem residualSlot_some (i : WeightedCornerIndex.Index) (b : Bool) : residualSlot i=some b ↔ i=residualIndex b := by
  rcases i with i|⟨(n|k),c⟩
  · simp [residualSlot,residualIndex]
  · cases n <;> simp [residualSlot,residualIndex]
  · simp [residualSlot,residualIndex]

theorem residualSlot_flip (i : WeightedCornerIndex.Index) :
    residualSlot (CircularRotation.flip i)=(residualSlot i).map Bool.not := by
  rcases i with i|⟨(n|k),c⟩
  · rfl
  · cases n <;> rfl
  · rfl

def diagonalVertex (u v : ℝ) (b : Bool) : diagonalBase u v (0:ℕ) :=
  ⟨vertex b,by cases b;exact sub_mem (one_mem _) (P_mem_diagonalBase u v 0);exact P_mem_diagonalBase u v 0⟩

def ambientLeft (u v : ℝ) (i : WeightedCornerIndex.Index) : diagonalBase u v (0:ℕ) :=
  (residualSlot i).elim 0 (diagonalVertex u v)
def ambientRight (u v : ℝ) (i : WeightedCornerIndex.Index) : diagonalBase u v (0:ℕ) :=
  (residualSlot i).elim 0 (fun b => diagonalVertex u v (!b))
def ambientExtra (u v : ℝ) (i : WeightedCornerIndex.Index) : Operator ℕ :=
  (residualSlot i).elim 0 (fun b => ambientRect u v 0 b (!b))

theorem diagonalVertex_projection (u v : ℝ) (b : Bool) : IsStarProjection (diagonalVertex u v b) := by
  constructor
  · apply Subtype.ext;exact (vertex_projection b).isIdempotentElem.eq
  · apply Subtype.ext;exact vertex_star b

theorem ambientLeft_projection (u v : ℝ) (i : WeightedCornerIndex.Index) : IsStarProjection (ambientLeft u v i) := by
  unfold ambientLeft
  cases residualSlot i
  · exact IsStarProjection.zero _
  · exact diagonalVertex_projection u v _

theorem ambientRight_projection (u v : ℝ) (i : WeightedCornerIndex.Index) : IsStarProjection (ambientRight u v i) := by
  unfold ambientRight
  cases residualSlot i
  · exact IsStarProjection.zero _
  · exact diagonalVertex_projection u v _

theorem ambientLeft_flip (u v : ℝ) (i : WeightedCornerIndex.Index) :
    ambientLeft u v (CircularRotation.flip i)=ambientRight u v i := by
  simp only [ambientLeft,ambientRight,residualSlot_flip]
  cases residualSlot i <;> rfl

theorem ambientRight_flip (u v : ℝ) (i : WeightedCornerIndex.Index) :
    ambientRight u v (CircularRotation.flip i)=ambientLeft u v i := by
  simp only [ambientLeft,ambientRight,residualSlot_flip]
  cases residualSlot i with
  | none => rfl
  | some b => cases b <;> rfl

theorem ambientExtra_supported (u v : ℝ) (i : WeightedCornerIndex.Index) :
    (ambientLeft u v i:Operator ℕ)*ambientExtra u v i*(ambientRight u v i:Operator ℕ)=ambientExtra u v i := by
  unfold ambientLeft ambientRight ambientExtra
  cases residualSlot i with
  | none => simp
  | some b =>
    change vertex b*ambientRect u v 0 b (!b)*vertex (!b)=_
    rw [ambientRect_left,ambientRect_right]
    rfl

def diagonalTrace (u v : ℝ) : diagonalBase u v (0:ℕ) →ₗ[ℂ] ℂ where
  toFun a := vacuumTrace u v (a:Operator ℕ)
  map_add' a b := by simp only [vacuumTrace,AddMemClass.coe_add,add_apply,inner_add_right]
  map_smul' c a := by simp only [vacuumTrace,SetLike.val_smul,smul_apply,inner_smul_right,RingHom.id_apply,smul_eq_mul]

theorem diagonalTrace_tracial (u v : ℝ) (hu : u≠0) (hv : v≠0) (a b : diagonalBase u v (0:ℕ)) :
    diagonalTrace u v (a*b)=diagonalTrace u v (b*a) :=
  ambient_trace_mul u v hu hv ⟨(a:Operator ℕ),diagonalBase_le_ambient u v 0 a.property⟩ ⟨(b:Operator ℕ),diagonalBase_le_ambient u v 0 b.property⟩

theorem ambientExtra_covariance (u v : ℝ) (i j : WeightedCornerIndex.Index) (a : diagonalBase u v (0:ℕ)) :
    star (ambientExtra u v i)*(a:Operator ℕ)*ambientExtra u v j=
      if i=j then diagonalTrace u v (a*ambientLeft u v i) • (ambientRight u v i:Operator ℕ) else 0 := by
  cases hi : residualSlot i with
  | none => simp [ambientExtra,ambientLeft,ambientRight,hi,star_zero (R := Operator ℕ),
      zero_smul ℂ (A := Operator ℕ)]
  | some b =>
    cases hj : residualSlot j with
    | none =>
      have hij : i≠j := by intro h;subst j;rw [hi] at hj;cases hj
      simp [ambientExtra,hj,hij]
    | some c =>
      have hei := (residualSlot_some i b).mp hi
      have hej := (residualSlot_some j c).mp hj
      have he : i=j ↔ b=c := by rw [hei,hej];simp [residualIndex]
      simp only [ambientExtra,ambientLeft,ambientRight,hi,hj,Option.elim_some,he]
      by_cases hbc : b=c
      · subst c
        rw [ite_eq_left rfl,diagonal_residual_trace]
        rfl
      · rw [ite_eq_right hbc]
        exact diagonal_residual_orthogonal u v 0 b c hbc a

def ambientRaw (u v : ℝ) (i : WeightedCornerIndex.Index) (n : ℕ) : Operator ℕ := C u v (reservoirCode (i,n)+1)

theorem ambientRaw_covariance (u v : ℝ) (i j : WeightedCornerIndex.Index) (n m : ℕ)
    (a : diagonalBase u v (0:ℕ)) :
    star (ambientRaw u v i n)*(a:Operator ℕ)*ambientRaw u v j m=
      if i=j ∧ n=m then diagonalTrace u v a • (1:Operator ℕ) else 0 := by
  have hh := fresh_C_contraction u v {0} (reservoirCode (i,n)+1) (reservoirCode (j,m)+1)
    (by simp) (by simp) ⟨a,diagonalBase_le_singleton u v 0 a.property⟩
  change star (C u v (reservoirCode (i,n)+1))*(a:Operator ℕ)*C u v (reservoirCode (j,m)+1)=
    if i=j ∧ n=m then vacuumTrace u v (a:Operator ℕ) • (1:Operator ℕ) else 0
  simpa only [Nat.add_right_cancel_iff,reservoirCode.injective.eq_iff,Prod.mk.injEq] using hh

theorem ambientRaw_extra (u v : ℝ) (i j : WeightedCornerIndex.Index) (n : ℕ)
    (a : diagonalBase u v (0:ℕ)) : star (ambientRaw u v i n)*(a:Operator ℕ)*ambientExtra u v j=0 := by
  unfold ambientExtra
  cases residualSlot j with
  | none => exact mul_zero _
  | some b => exact ambient_C_residual u v 0 _ (by omega) b a

def ambientAbsorption (u v : ℝ) (hu : u≠0) (hv : v≠0) :
    PairedAbsorption.Input (diagonalBase u v (0:ℕ)) SelfIndex PairIndex where
  τ := diagonalTrace u v
  tracial := diagonalTrace_tracial u v hu hv
  p := ambientLeft u v
  q := ambientRight u v
  projection := ambientLeft_projection u v
  projectionq := ambientRight_projection u v
  pq := ambientLeft_flip u v
  qp := ambientRight_flip u v
  raw := ambientRaw u v
  extra := ambientExtra u v
  supported := ambientExtra_supported u v
  raw_cov := ambientRaw_covariance u v
  extra_cov := ambientExtra_covariance u v
  raw_extra := ambientRaw_extra u v
end FreeGroupFactorMain.WeightedFock

end

end OAI
