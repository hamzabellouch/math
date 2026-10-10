import OAI.Geometry.HarmonicGrowth.ComplexHarmonics

namespace OAI

noncomputable section
open Matrix
open scoped BigOperators
open scoped Topology
open Filter
open Matrix
open scoped BigOperators
open Matrix MvPolynomial
open Matrix
open scoped BigOperators
open scoped BigOperators

namespace HarmonicCounterexample.Control
open Matrix
attribute [local instance 100] LieRing.ofAssociativeRing
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def skewUnit (i j : ι) : Matrix ι ι ℂ := single i j 1-single j i 1

def symmetricUnit (i j : ι) : Matrix ι ι ℂ := single i j 1+single j i 1

def diagonalDifference (i j : ι) : Matrix ι ι ℂ := single i i 1-single j j 1

def nullRank (i j : ι) : Matrix ι ι ℂ := diagonalDifference i j+Complex.I • symmetricUnit i j

lemma single_bracket (i j k m : ι) :
    ⁅single i j (1:ℂ),single k m (1:ℂ)⁆ =
      (if j=k then single i m 1 else 0)-(if m=i then single k j 1 else 0) := by
  rw [Ring.lie_def]
  by_cases h : j=k <;> by_cases h' : m=i
  · subst k; subst m; simp [single_mul_single_same]
  · subst k; simp [h',single_mul_single_same,single_mul_single_of_ne (1:ℂ) j m i h' (1:ℂ)]
  · subst m; simp [h,single_mul_single_same,single_mul_single_of_ne (1:ℂ) i j k h (1:ℂ)]
  · simp [h,h',single_mul_single_of_ne (1:ℂ) i j k h (1:ℂ),
      single_mul_single_of_ne (1:ℂ) k m i h' (1:ℂ)]

lemma skew_symmetric_bracket (i j : ι) :
    ⁅skewUnit i j,symmetricUnit i j⁆ = (2:ℂ) • diagonalDifference i j := by
  simp [skewUnit,symmetricUnit,diagonalDifference,lie_add,sub_lie,single_bracket]
  module

lemma skew_path_bracket (i a j : ι) (hia : i ≠ a) (hij : i ≠ j) (haj : a ≠ j) :
    ⁅skewUnit i a,symmetricUnit a j⁆ = symmetricUnit i j := by
  simp [skewUnit,symmetricUnit,lie_add,sub_lie,single_bracket,hia,hia.symm,hij,hij.symm,
    haj,haj.symm]

lemma skew_diagonal_bracket (i j : ι) (d : ι → ℂ) :
    ⁅skewUnit i j,diagonal d⁆ = (d j-d i) • symmetricUnit i j := by
  ext a b
  simp only [Ring.lie_def,Matrix.sub_apply,Matrix.mul_diagonal,Matrix.diagonal_mul,
    skewUnit,symmetricUnit,Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    single_apply]
  by_cases h : i=a ∧ j=b
  · obtain ⟨rfl,rfl⟩ := h
    simp only [true_and,ite_true]
    by_cases h' : i=j
    · subst j; simp only [and_self,ite_true]; ring
    · simp only [h',and_false,ite_false]; ring
  · by_cases h' : j=a ∧ i=b
    · obtain ⟨rfl,rfl⟩ := h'
      simp only [h,ite_false,and_self,ite_true]; ring
    · simp only [h,h',ite_false]; ring

omit [Fintype ι] in
lemma diagonalDifference_eq_diagonal (i j : ι) :
    diagonalDifference i j = diagonal (fun k => (if i=k then 1 else 0)-(if j=k then 1 else 0)) := by
  ext a b
  simp [diagonalDifference,single_apply,diagonal_apply]
  split_ifs <;> aesop

lemma double_skew_null_difference (a b c : ι) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ⁅skewUnit a c,⁅skewUnit a c,nullRank a b⁆⁆-
      ⁅skewUnit b c,⁅skewUnit b c,nullRank a b⁆⁆ =
      (-2:ℂ) • (diagonalDifference a c+diagonalDifference b c) := by
  simp only [skewUnit,nullRank,diagonalDifference,symmetricUnit,lie_add,lie_sub,sub_lie,
    lie_smul,single_bracket]
  simp only [hab,hac,hbc,hab.symm,hac.symm,hbc.symm,ite_false,ite_true,
    lie_zero,sub_zero,zero_sub,smul_sub,smul_add,smul_neg]
  simp only [single_bracket,hab,hac,hbc,hab.symm,hac.symm,hbc.symm,ite_false,ite_true]
  module

lemma diagonal_two_mem (L : LieSubalgebra ℂ (Matrix ι ι ℂ))
    (a b c : ι) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hskew : ∀ i j,skewUnit i j ∈ L) (hn : nullRank a b ∈ L) :
    diagonalDifference a c+diagonalDifference b c ∈ L := by
  have he := L.sub_mem (L.lie_mem (hskew a c) (L.lie_mem (hskew a c) hn))
    (L.lie_mem (hskew b c) (L.lie_mem (hskew b c) hn))
  rw [double_skew_null_difference a b c hab hac hbc] at he
  have h := L.smul_mem ((-2:ℂ)⁻¹) he
  norm_num only [smul_smul,inv_mul_cancel₀ (by norm_num : (-2:ℂ) ≠ 0),one_smul] at h
  exact h

/-- Off-diagonal units and diagonal differences span the actual trace-zero
matrices, with no dimension or simplicity assumption. -/
theorem tracefree_mem_of_units (L : LieSubalgebra ℂ (Matrix ι ι ℂ)) (a : ι)
    (hoff : ∀ i j,i ≠ j → single i j (1:ℂ) ∈ L)
    (hdiag : ∀ i,diagonalDifference i a ∈ L) {X : Matrix ι ι ℂ} (hX : trace X=0) : X ∈ L := by
  have hm : (∑ i : ι,∑ j : ι,
      (single i j (X i j)-(if i=j then single a a (X i i) else 0))) ∈ L := by
    apply L.sum_mem; intro i _
    apply L.sum_mem; intro j _
    change (single i j (X i j)-(if i=j then single a a (X i i) else 0)) ∈ L
    by_cases hij : i=j
    · subst j
      simpa only [ite_true,diagonalDifference,smul_sub,smul_single,smul_eq_mul,mul_one]
        using L.smul_mem (X i i) (hdiag i)
    · simpa only [hij,ite_false,sub_zero,smul_single,smul_eq_mul,mul_one]
        using L.smul_mem (X i j) (hoff i j hij)
  have he : (∑ i : ι,∑ j : ι,
      (single i j (X i j)-(if i=j then single a a (X i i) else 0))) = X := by
    simp only [Finset.sum_sub_distrib,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
    rw [← Matrix.matrix_eq_sum_single X]
    have hz : (∑ i : ι,single a a (X i i)) = 0 := by
      have hr (i : ι) : single a a (X i i) = X i i • single a a (1:ℂ) := by simp
      simp only [hr,← Finset.sum_smul]
      change trace X • single a a (1:ℂ) = 0
      rw [hX,zero_smul]
    rw [hz,sub_zero]
  exact he ▸ hm


lemma unsmul_mem {L : LieSubalgebra ℂ (Matrix ι ι ℂ)} {c : ℂ} (hc : c ≠ 0)
    {X : Matrix ι ι ℂ} (h : c • X ∈ L) : X ∈ L := by
  have he := L.smul_mem c⁻¹ h
  simpa only [smul_smul,inv_mul_cancel₀ hc,one_smul] using he

/-- The full trace-free algebra already follows by brackets from all skew
operators and one null rank-one operator. This is a direct algebraic replacement
for the manuscript's second use of special-orthogonal exponentials. -/
theorem tracefree_mem_of_skews_and_null (L : LieSubalgebra ℂ (Matrix ι ι ℂ))
    (a b c : ι) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hskew : ∀ i j,skewUnit i j ∈ L) (hn : nullRank a b ∈ L)
    {X : Matrix ι ι ℂ} (hX : trace X=0) : X ∈ L := by
  let d : ι → ℂ := fun i => (if a=i then 1 else 0)+(if b=i then 1 else 0)-
    2*(if c=i then 1 else 0)
  have he : diagonalDifference a c+diagonalDifference b c = diagonal d := by
    rw [diagonalDifference_eq_diagonal,diagonalDifference_eq_diagonal,diagonal_add]
    congr 1
    funext i
    dsimp [d]
    ring
  have hd : diagonal d ∈ L := he ▸ diagonal_two_mem L a b c hab hac hbc hskew hn
  have hdc : d c = -2 := by simp [d,hac,hbc]
  have hstar (i : ι) (hic : i ≠ c) : symmetricUnit c i ∈ L := by
    have hm := L.lie_mem (hskew c i) hd
    rw [skew_diagonal_bracket,hdc] at hm
    apply unsmul_mem (X := symmetricUnit c i) (h := hm)
    by_cases hai : a=i
    · subst i; norm_num [d,hab,hab.symm,hac,hac.symm]
    by_cases hbi : b=i
    · subst i; norm_num [d,hab,hab.symm,hbc,hbc.symm]
    · norm_num [d,hai,hbi,hic.symm]
  have hsymm (i j : ι) : symmetricUnit i j = symmetricUnit j i := add_comm _ _
  have hdiag (i : ι) : diagonalDifference i c ∈ L := by
    by_cases hic : i=c
    · subst i; simpa only [diagonalDifference,sub_self] using L.zero_mem
    have hm := L.lie_mem (hskew i c) (show symmetricUnit i c ∈ L from hsymm c i ▸ hstar i hic)
    rw [skew_symmetric_bracket] at hm
    exact unsmul_mem (by norm_num) hm
  have hoff (i j : ι) (hij : i ≠ j) : single i j (1:ℂ) ∈ L := by
    have hs : symmetricUnit i j ∈ L := by
      by_cases hic : i=c
      · subst i; exact hstar j hij.symm
      by_cases hjc : j=c
      · subst j; exact hsymm c i ▸ hstar i hic
      have hm := L.lie_mem (hskew i c) (hstar j hjc)
      rw [skew_path_bracket i c j hic hij (Ne.symm hjc)] at hm
      exact hm
    have hm := L.smul_mem (1/2:ℂ) (L.add_mem hs (hskew i j))
    have he' : (1/2:ℂ) • (symmetricUnit i j+skewUnit i j) = single i j (1:ℂ) := by
      unfold symmetricUnit skewUnit
      module
    exact he' ▸ hm
  exact tracefree_mem_of_units L c hoff hdiag hX

end HarmonicCounterexample.Control

end

noncomputable section
open Matrix
open scoped BigOperators
open scoped Topology
open Filter
open Matrix
open scoped BigOperators
open Matrix MvPolynomial
open Matrix
open scoped BigOperators
open scoped BigOperators

namespace HarmonicCounterexample.Control
open Module Matrix
open scoped BigOperators
attribute [local instance 100] LieRing.ofAssociativeRing
variable {W ι : Type*} [AddCommGroup W] [Module ℂ W] [Fintype ι] [DecidableEq ι]

lemma outer_bilinear_matrix (B : W →ₗ[ℂ] W →ₗ[ℂ] ℂ) (b : Basis ι ℂ W)
    (hb : ∀ i j,B (b i) (b j) = if i=j then 1 else 0) (u v : W) :
    LinearMap.toMatrixAlgEquiv b (outer B u v) = Matrix.vecMulVec (b.repr u) (b.repr v) := by
  change LinearMap.toMatrix b b ((B v).smulRight u) = _
  rw [LinearMap.toMatrix_smulRight]
  congr 1
  funext j
  exact bilin_basis_repr B b hb v j

lemma wedge_basis_matrix (B : W →ₗ[ℂ] W →ₗ[ℂ] ℂ) (b : Basis ι ℂ W)
    (hb : ∀ i j,B (b i) (b j) = if i=j then 1 else 0) (i j : ι) :
    LinearMap.toMatrixAlgEquiv b (wedgeLeft B (b i) (b j)) = skewUnit i j := by
  rw [wedgeLeft_apply,map_sub,outer_bilinear_matrix B b hb,outer_bilinear_matrix B b hb]
  ext a c
  simp only [Basis.repr_self,Matrix.vecMulVec_apply,Finsupp.single_apply,skewUnit,
    Matrix.sub_apply,Matrix.single_apply]
  by_cases hia : i=a <;> by_cases hjc : j=c <;> by_cases hja : j=a <;> by_cases hic : i=c <;>
    simp_all

lemma outer_null_basis_matrix (B : W →ₗ[ℂ] W →ₗ[ℂ] ℂ) (b : Basis ι ℂ W)
    (hb : ∀ i j,B (b i) (b j) = if i=j then 1 else 0) (i j : ι) (r : ℂ) :
    LinearMap.toMatrixAlgEquiv b
      (outer B (r • (b i+Complex.I • b j)) (r • (b i+Complex.I • b j))) =
      (r*r) • nullRank i j := by
  rw [outer_bilinear_matrix B b hb]
  ext a c
  simp only [map_smul,map_add,Basis.repr_self,Finsupp.add_apply,Finsupp.smul_apply,
    Matrix.vecMulVec_apply,smul_eq_mul,Finsupp.single_apply,nullRank,diagonalDifference,
    symmetricUnit,Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,Matrix.single_apply]
  by_cases hia : i=a <;> by_cases hjc : j=c <;> by_cases hja : j=a <;> by_cases hic : i=c
  all_goals simp_all <;> ring_nf <;> simp only [Complex.I_sq] <;> ring


end HarmonicCounterexample.Control

end

noncomputable section
open Matrix
open scoped BigOperators
open scoped Topology
open Filter
open Matrix
open scoped BigOperators
open Matrix MvPolynomial
open Matrix
open scoped BigOperators
open scoped BigOperators

namespace HarmonicCounterexample.Control
open Module Matrix
attribute [local instance 100] LieRing.ofAssociativeRing
variable {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

/-- Full complex special-linear saturation from all actual bilinear wedges and
one nonzero null rank one. All coordinate changes and brackets are proved. -/
theorem tracefree_mem_of_bilinear_wedges_null
    (L : LieSubalgebra ℂ (Module.End ℂ W))
    (B : W →ₗ[ℂ] W →ₗ[ℂ] ℂ) (hB : ∀ x y,B x y = B y x)
    (hinj : Function.Injective B) (hdim : 3 ≤ finrank ℂ W)
    (hskew : ∀ u v,wedgeLeft B u v ∈ L)
    (u : W) (hu : B u u=0) (hn : u ≠ 0) (hU : outer B u u ∈ L)
    {X : Module.End ℂ W} (hX : LinearMap.trace ℂ W X = 0) : X ∈ L := by
  classical
  obtain ⟨b,hb⟩ := exists_bilinear_orthonormal_basis B hB hinj
  let i : Fin (finrank ℂ W) := ⟨0,by omega⟩
  let j : Fin (finrank ℂ W) := ⟨1,by omega⟩
  let k : Fin (finrank ℂ W) := ⟨2,by omega⟩
  have hij : i ≠ j := by intro h; have := congrArg Fin.val h; simp [i,j] at this
  have hik : i ≠ k := by intro h; have := congrArg Fin.val h; simp [i,k] at this
  have hjk : j ≠ k := by intro h; have := congrArg Fin.val h; simp [j,k] at this
  obtain ⟨b',r,hr,hb',hur⟩ := exists_bilinear_null_basis B b hb i j hij u hu hn
  let e := LinearMap.toMatrixAlgEquiv b'
  let LM := LieSubalgebra.map e.toAlgHom.toLieHom L
  have hs (a c) : skewUnit a c ∈ LM := by
    have he := wedge_basis_matrix B b' hb' a c
    exact ⟨wedgeLeft B (b' a) (b' c),hskew _ _,he⟩
  have hn' : nullRank i j ∈ LM := by
    have h : ((r:ℂ)*(r:ℂ)) • nullRank i j ∈ LM := by
      refine ⟨outer B u u,hU,?_⟩
      rw [hur]
      exact outer_null_basis_matrix B b' hb' i j r
    apply unsmul_mem _ h
    exact mul_ne_zero (by exact_mod_cast ne_of_gt hr) (by exact_mod_cast ne_of_gt hr)
  have htr : Matrix.trace (e X)=0 := by
    change Matrix.trace (LinearMap.toMatrix b' b' X)=0
    rw [← LinearMap.trace_eq_matrix_trace ℂ b' X]
    exact hX
  have hm := tracefree_mem_of_skews_and_null LM i j k hij hik hjk hs hn' htr
  obtain ⟨Y,hY,he⟩ := hm
  have hy : Y=X := e.injective he
  exact hy ▸ hY

end HarmonicCounterexample.Control

end

noncomputable section
open Matrix
open scoped BigOperators
open scoped Topology
open Filter
open Matrix
open scoped BigOperators
open Matrix MvPolynomial
open Matrix
open scoped BigOperators
open scoped BigOperators

namespace HarmonicCounterexample.ComplexAngular
open MvPolynomial Module
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma linearForm_single_coordinate (i : ι ⊕ ι) :
    linearForm (Pi.single i (1:ℂ)) = X i := by
  simp [linearForm,Pi.single_apply]

lemma quadric_eval_single_inl (i : ι) :
    MvPolynomial.eval (Pi.single (.inl i) (1:ℂ)) (quadric ι) = 0 := by
  simp [quadric,Pi.single_apply]

def coordinatePower (l : ℕ) (i : ι) : harmonicSpace ι l :=
  isotropicPower l ⟨Pi.single (.inl i) 1,quadric_eval_single_inl i⟩

lemma coordinatePower_val (l : ℕ) (i : ι) :
    (coordinatePower l i : SplitPolynomial ι) = X (.inl i)^l := by
  change linearForm (Pi.single (Sum.inl i : ι⊕ι) (1:ℂ))^l = _
  rw [linearForm_single_coordinate]

lemma eval_coordinatePower (l : ℕ) (hl : 0 < l) (i j : ι) :
    MvPolynomial.eval (Pi.single (.inl j) (1:ℂ)) (coordinatePower l i : SplitPolynomial ι) =
      if i=j then 1 else 0 := by
  rw [coordinatePower_val,map_pow,eval_X]
  by_cases h : i=j <;> simp [h,hl.ne']

lemma coordinatePowers_independent (l : ℕ) (hl : 0 < l) :
    LinearIndependent ℂ (coordinatePower (ι := ι) l) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have h := congrArg (fun P : harmonicSpace ι l =>
    MvPolynomial.eval (Pi.single (.inl j) (1:ℂ)) P.1) hc
  simp only [Submodule.coe_sum,Submodule.coe_smul,Submodule.coe_zero,map_sum,
    MvPolynomial.smul_eval,eval_coordinatePower l hl,map_zero] at h
  simpa using h

lemma harmonicSpace_finrank_lower (l : ℕ) (hl : 0 < l) :
    Fintype.card ι ≤ finrank ℂ (harmonicSpace ι l) :=
  (coordinatePowers_independent l hl).fintype_card_le_finrank

end HarmonicCounterexample.ComplexAngular

end

noncomputable section
open Matrix
open scoped BigOperators
open scoped Topology
open Filter
open Matrix
open scoped BigOperators
open Matrix MvPolynomial
open Matrix
open scoped BigOperators
open scoped BigOperators

namespace HarmonicCounterexample.Control
open Module MvPolynomial HarmonicCounterexample.ComplexAngular
attribute [local instance 100] LieRing.ofAssociativeRing

/-- One-block complex Lie saturation on the genuine harmonic polynomials in
sixteen Cartesian dimensions, for every degree l>=2. No abstract-irreducibility,
orbit-spanning, or desired Lie-equality assumption is used. -/
theorem harmonicAngularLie_has_specialLinear (l : ℕ) (hl : 2 ≤ l)
    {X : Module.End ℂ (harmonicSpace (Fin 8) l)}
    (hX : LinearMap.trace ℂ (harmonicSpace (Fin 8) l) X=0) :
    X ∈ harmonicAngularLie l := by
  have hl0 : 0 < l := by omega
  have hd := harmonicSpace_finrank_lower (ι := Fin 8) l hl0
  have hd' : 3 ≤ finrank ℂ (harmonicSpace (Fin 8) l) := by
    simp only [Fintype.card_fin] at hd
    omega
  let a : {a : (Fin 8⊕Fin 8) → ℂ | MvPolynomial.eval a (quadric (Fin 8))=0} :=
    ⟨Pi.single (.inl 0) 1,quadric_eval_single_inl 0⟩
  have hn : isotropicPower l a ≠ 0 := by
    exact (coordinatePowers_independent (ι := Fin 8) l hl0).ne_zero 0
  exact tracefree_mem_of_bilinear_wedges_null (harmonicAngularLie l)
    (roundPairing l) (roundPairing_symm l) (roundPairing_injective l) hd'
    (harmonicAngularLie_wedges l hl) (isotropicPower l a)
    (roundPairing_isotropicPower l hl0 a) hn (harmonicAngularLie_rankones l hl a) hX

end HarmonicCounterexample.Control

end

noncomputable section
open Matrix
open scoped BigOperators
open scoped Topology
open Filter
open Matrix
open scoped BigOperators
open Matrix MvPolynomial
open Matrix
open scoped BigOperators
open scoped BigOperators

namespace HarmonicCounterexample.Control
variable {A : Type*} [Ring A] [Algebra ℂ A] [Algebra ℝ A] [IsScalarTower ℝ ℂ A]
attribute [local instance 100] LieRing.ofAssociativeRing

lemma complex_smul_real_parts (c : ℂ) (x : A) :
    c • x = c.re • x + Complex.I • (c.im • x) := by
  rw [← IsScalarTower.algebraMap_smul ℂ c.re x,← IsScalarTower.algebraMap_smul ℂ c.im x]
  rw [smul_smul,← add_smul]
  congr 1
  change c=(c.re:ℂ)+Complex.I*(c.im:ℂ)
  simpa only [mul_comm] using (Complex.re_add_im c).symm

/-- The complex scalar envelope of an actual real Lie algebra, with explicit
real and imaginary witnesses. -/
def complexLieEnvelope (L : LieSubalgebra ℝ A) : LieSubalgebra ℂ A where
  carrier := {x | ∃ a ∈ L,∃ b ∈ L,x=a+Complex.I • b}
  zero_mem' := ⟨0,L.zero_mem,0,L.zero_mem,by simp⟩
  add_mem' := by
    rintro x y ⟨a,ha,b,hb,rfl⟩ ⟨c,hc,d,hd,rfl⟩
    exact ⟨a+c,L.add_mem ha hc,b+d,L.add_mem hb hd,by simp only [smul_add]; abel⟩
  smul_mem' := by
    rintro z x ⟨a,ha,b,hb,rfl⟩
    refine ⟨z.re • a-z.im • b,L.sub_mem (L.smul_mem _ ha) (L.smul_mem _ hb),
      z.im • a+z.re • b,L.add_mem (L.smul_mem _ ha) (L.smul_mem _ hb),?_⟩
    rw [complex_smul_real_parts z]
    simp only [smul_add]
    rw [show (z.re:ℝ) • (Complex.I • b) = Complex.I • (z.re • b) by module,
      show Complex.I • ((z.im:ℝ) • (Complex.I • b)) = -(z.im • b) by
        rw [smul_comm (z.im:ℝ) Complex.I,smul_smul,Complex.I_mul_I,neg_one_smul]]
    abel
  lie_mem' := by
    rintro x y ⟨a,ha,b,hb,rfl⟩ ⟨c,hc,d,hd,rfl⟩
    refine ⟨⁅a,c⁆-⁅b,d⁆,L.sub_mem (L.lie_mem ha hc) (L.lie_mem hb hd),
      ⁅a,d⁆+⁅b,c⁆,L.add_mem (L.lie_mem ha hd) (L.lie_mem hb hc),?_⟩
    simp only [add_lie,lie_add,smul_lie,lie_smul,smul_add,smul_smul,Complex.I_mul_I,neg_one_smul]
    abel

lemma subset_complexLieEnvelope (L : LieSubalgebra ℝ A) {x : A} (hx : x ∈ L) :
    x ∈ complexLieEnvelope L := ⟨x,hx,0,L.zero_mem,by simp⟩

lemma lieSpan_complex_decomposition (s : Set A) {x : A}
    (hx : x ∈ LieSubalgebra.lieSpan ℂ A s) :
    ∃ a ∈ LieSubalgebra.lieSpan ℝ A s,∃ b ∈ LieSubalgebra.lieSpan ℝ A s,
      x=a+Complex.I • b := by
  apply (LieSubalgebra.lieSpan_le.2 (show s ⊆ complexLieEnvelope (LieSubalgebra.lieSpan ℝ A s) from ?_)) hx
  intro y hy
  exact subset_complexLieEnvelope _ (LieSubalgebra.subset_lieSpan hy)

/-- Faithful real descent. A conjugation-fixed element of a complex generated
Lie algebra is already in the real generated algebra, provided all generators
are fixed by the same actual algebra conjugation. -/
theorem real_lieSpan_of_complex (s : Set A)
    (τ : A →ₗ[ℝ] A)
    (hτI : ∀ x,τ (Complex.I • x) = -Complex.I • τ x)
    (hτlie : ∀ x y,τ ⁅x,y⁆ = ⁅τ x,τ y⁆)
    (hs : ∀ x ∈ s,τ x=x) {x : A}
    (hx : x ∈ LieSubalgebra.lieSpan ℂ A s) (hτx : τ x=x) :
    x ∈ LieSubalgebra.lieSpan ℝ A s := by
  let F : LieSubalgebra ℝ A :=
    { (LinearMap.ker (τ-LinearMap.id)) with
      lie_mem' := by
        intro u v hu hv
        have hu' : τ u=u := sub_eq_zero.1 hu
        have hv' : τ v=v := sub_eq_zero.1 hv
        change τ ⁅u,v⁆-⁅u,v⁆=0
        rw [hτlie,hu',hv',sub_self] }
  have hF : LieSubalgebra.lieSpan ℝ A s ≤ F := by
    apply LieSubalgebra.lieSpan_le.2
    intro y hy
    change τ y-y=0
    rw [hs y hy,sub_self]
  obtain ⟨a,ha,b,hb,he⟩ := lieSpan_complex_decomposition s hx
  have hτa : τ a=a := sub_eq_zero.1 (hF ha)
  have hτb : τ b=b := sub_eq_zero.1 (hF hb)
  have he' := congrArg τ he
  rw [map_add,hτI,hτa,hτb,hτx] at he'
  have hz : Complex.I • b = 0 := by
    have hh : (2:ℝ) • (Complex.I • b)=0 := by
      rw [two_smul]
      rw [neg_smul] at he'
      exact eq_neg_iff_add_eq_zero.1 (add_left_cancel (he.symm.trans he'))
    exact (smul_eq_zero.mp hh).resolve_left (by norm_num)
  rw [hz,add_zero] at he
  exact he ▸ ha

end HarmonicCounterexample.Control

end

noncomputable section
open Matrix
open scoped BigOperators
open scoped Topology
open Filter
open Matrix
open scoped BigOperators
open Matrix MvPolynomial
open Matrix
open scoped BigOperators
open scoped BigOperators

namespace HarmonicCounterexample.Control
open Module
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable {ι : Type*}

def conjugatedBasis (b : Basis ι ℂ V) (e : V ≃ₗ⋆[ℂ] V) : Basis ι ℂ V :=
  Basis.ofRepr ((e.symm.trans b.repr).trans (Finsupp.mapRange.linearEquiv (starLinearEquiv ℂ)))

lemma conjugatedBasis_repr (b : Basis ι ℂ V) (e : V ≃ₗ⋆[ℂ] V) (v : V) (i : ι) :
    (conjugatedBasis b e).repr v i = star (b.repr (e.symm v) i) := rfl

lemma conjugatedBasis_apply (b : Basis ι ℂ V) (e : V ≃ₗ⋆[ℂ] V) (i : ι) :
    conjugatedBasis b e i = e (b i) := by
  classical
  apply (conjugatedBasis b e).repr.injective
  ext j
  rw [Basis.repr_self,conjugatedBasis_repr,e.symm_apply_apply,Basis.repr_self]
  simp [Finsupp.single_apply]

lemma trace_conj_semilinear [FiniteDimensional ℂ V] (e : V ≃ₗ⋆[ℂ] V) (X : Module.End ℂ V) :
    LinearMap.trace ℂ V (e.conj X) = star (LinearMap.trace ℂ V X) := by
  let b := Module.finBasis ℂ V
  rw [LinearMap.trace_eq_matrix_trace ℂ (conjugatedBasis b e),
    LinearMap.trace_eq_matrix_trace ℂ b]
  simp only [Matrix.trace,Matrix.diag,LinearMap.toMatrix_apply,star_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [conjugatedBasis_repr,conjugatedBasis_apply,LinearEquiv.conj_apply_apply,
    e.symm_apply_apply,e.symm_apply_apply]

variable [Module ℝ V] [IsScalarTower ℝ ℂ V]
attribute [local instance 100] LieRing.ofAssociativeRing

def realEndConjugation (e : V ≃ₗ⋆[ℂ] V) : Module.End ℂ V →ₗ[ℝ] Module.End ℂ V where
  toFun := e.conj
  map_add' := e.conj.map_add
  map_smul' r X := by
    change e.conj (r • X) = r • e.conj X
    rw [← IsScalarTower.algebraMap_smul ℂ r X, map_smulₛₗ]
    simpa using IsScalarTower.algebraMap_smul ℂ r (e.conj X)

lemma realEndConjugation_I (e : V ≃ₗ⋆[ℂ] V) (X : Module.End ℂ V) :
    realEndConjugation e (Complex.I • X) = -Complex.I • realEndConjugation e X := by
  change e.conj (Complex.I • X) = _
  rw [map_smulₛₗ]
  simp [realEndConjugation]

lemma realEndConjugation_lie (e : V ≃ₗ⋆[ℂ] V) (X Y : Module.End ℂ V) :
    realEndConjugation e ⁅X,Y⁆ = ⁅realEndConjugation e X,realEndConjugation e Y⁆ := by
  change e.conjRingEquiv (X*Y-Y*X) = _
  rw [map_sub,map_mul,map_mul]
  rfl

end HarmonicCounterexample.Control

end

noncomputable section
open Matrix
open scoped BigOperators
open scoped Topology
open Filter
open Matrix
open scoped BigOperators
open Matrix MvPolynomial
open Matrix
open scoped BigOperators
open scoped BigOperators

namespace HarmonicCounterexample.ComplexAngular
open MvPolynomial HarmonicCounterexample.Control
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
lemma conjugate_swapPolynomial (P : SplitPolynomial ι) :
    conjugate (swapPolynomial P) = swapPolynomial (conjugate P) :=
  MvPolynomial.map_rename _ _ _

/-- Conjugation in split coordinates of a real Cartesian polynomial: it also
interchanges z and bar-z, rather than merely conjugating their coefficients. -/
def realConjugatePolynomial : SplitPolynomial ι ≃ₗ⋆[ℂ] SplitPolynomial ι where
  toFun P := conjugate (swapPolynomial P)
  invFun P := conjugate (swapPolynomial P)
  left_inv P := by dsimp only; rw [conjugate_swapPolynomial,conjugate_involutive,swapPolynomial_involutive]
  right_inv P := by dsimp only; rw [conjugate_swapPolynomial,conjugate_involutive,swapPolynomial_involutive]
  map_add' P Q := by simp only [map_add]
  map_smul' c P := by
    change conjugate (swapPolynomial (c • P)) = _
    rw [map_smul]
    simp only [conjugate,smul_eq_C_mul,map_mul,map_C,starRingEnd_apply]

omit [Fintype ι] in
lemma realConjugatePolynomial_pderiv (P : SplitPolynomial ι) (i : ι ⊕ ι) :
    realConjugatePolynomial (pderiv i P) =
      pderiv (Sum.swap i) (realConjugatePolynomial P) := by
  change conjugate (swapPolynomial (pderiv i P)) = _
  rw [swapPolynomial_pderiv,conjugate_pderiv]
  rfl

omit [Fintype ι] in
lemma realConjugatePolynomial_X (i : ι ⊕ ι) :
    realConjugatePolynomial (X i : SplitPolynomial ι) = X (Sum.swap i) := by
  change conjugate (swapPolynomial (X i)) = _
  rw [swapPolynomial_X]
  exact map_X _ _

omit [Fintype ι] in
lemma realConjugatePolynomial_mul (P Q : SplitPolynomial ι) :
    realConjugatePolynomial (P*Q) = realConjugatePolynomial P*realConjugatePolynomial Q := by
  change conjugate (swapPolynomial (P*Q)) = _
  simp only [map_mul]
  rfl

lemma realConjugatePolynomial_mem_harmonicSpace {P : SplitPolynomial ι} {l : ℕ}
    (hP : P ∈ harmonicSpace ι l) : realConjugatePolynomial P ∈ harmonicSpace ι l :=
  conjugate_mem_harmonicSpace (swapPolynomial_mem_harmonicSpace hP)

def spaceRealConjugation (l : ℕ) : harmonicSpace ι l ≃ₗ⋆[ℂ] harmonicSpace ι l where
  toFun P := ⟨realConjugatePolynomial P,realConjugatePolynomial_mem_harmonicSpace P.property⟩
  invFun P := ⟨realConjugatePolynomial P,realConjugatePolynomial_mem_harmonicSpace P.property⟩
  left_inv P := Subtype.ext (realConjugatePolynomial.apply_symm_apply (P : SplitPolynomial ι))
  right_inv P := Subtype.ext (realConjugatePolynomial.apply_symm_apply (P : SplitPolynomial ι))
  map_add' P Q := Subtype.ext (map_add realConjugatePolynomial (P : SplitPolynomial ι) (Q : SplitPolynomial ι))
  map_smul' c P := Subtype.ext (map_smulₛₗ realConjugatePolynomial c (P : SplitPolynomial ι))

end HarmonicCounterexample.ComplexAngular

end

noncomputable section
open Matrix
open scoped BigOperators
open scoped Topology
open Filter
open Matrix
open scoped BigOperators
open Matrix MvPolynomial
open Matrix
open scoped BigOperators
open scoped BigOperators

namespace HarmonicCounterexample.Berger.ComplexStructure
open Matrix

lemma splitFieldMatrix_conjugate {s : ℕ}
    (M : Matrix (Fin s ⊕ Fin s) (Fin s ⊕ Fin s) ℝ) (a b) :
    star (splitFieldMatrix M a b) = splitFieldMatrix M (Sum.swap a) (Sum.swap b) := by
  rw [splitFieldMatrix_apply,splitFieldMatrix_apply]
  rcases a with a | a <;> rcases b with b | b
  all_goals
    simp only [Sum.swap_inl,Sum.swap_inr,coordinatePlane,coordinateSign,Sum.elim_inl,Sum.elim_inr,id_eq]
    simp
    <;> ring

end HarmonicCounterexample.Berger.ComplexStructure

end

noncomputable section
open Matrix
open scoped BigOperators
open scoped Topology
open Filter
open Matrix
open scoped BigOperators
open Matrix MvPolynomial
open Matrix
open scoped BigOperators
open scoped BigOperators

namespace HarmonicCounterexample.ComplexAngular
open MvPolynomial HarmonicCounterexample.Control HarmonicCounterexample.Berger
open HarmonicCounterexample.Berger.ComplexStructure

lemma realConjugatePolynomial_linearField {s : ℕ}
    (M : Matrix (Fin s ⊕ Fin s) (Fin s ⊕ Fin s) ℝ) (P : SplitPolynomial (Fin s)) :
    realConjugatePolynomial (linearField (splitFieldMatrix M) P) =
      linearField (splitFieldMatrix M) (realConjugatePolynomial P) := by
  simp only [linearField_apply,map_sum,map_smulₛₗ,starRingEnd_apply,
    realConjugatePolynomial_mul,realConjugatePolynomial_X,
    realConjugatePolynomial_pderiv,splitFieldMatrix_conjugate]
  apply Fintype.sum_equiv (Equiv.sumComm (Fin s) (Fin s))
  intro i
  apply Fintype.sum_equiv (Equiv.sumComm (Fin s) (Fin s))
  intro j
  rfl

lemma spaceRealConjugation_harmonicField (l : ℕ) (J : ComplexStructure (Fin 8 ⊕ Fin 8))
    (P : harmonicSpace (Fin 8) l) :
    spaceRealConjugation l (harmonicField l J P) =
      harmonicField l J (spaceRealConjugation l P) := by
  apply Subtype.ext
  exact realConjugatePolynomial_linearField J.matrix P.1

lemma spaceRealConjugation_conj_harmonicField (l : ℕ) (J : ComplexStructure (Fin 8 ⊕ Fin 8)) :
    (spaceRealConjugation l).conj (harmonicField l J) = harmonicField l J := by
  ext P : 1
  rw [LinearEquiv.conj_apply_apply,spaceRealConjugation_harmonicField,
    LinearEquiv.apply_symm_apply]

end HarmonicCounterexample.ComplexAngular

end

noncomputable section
open Matrix
open scoped BigOperators
open scoped Topology
open Filter
open Matrix
open scoped BigOperators
open Matrix MvPolynomial
open Matrix
open scoped BigOperators
open scoped BigOperators

namespace HarmonicCounterexample.Control
open Module MvPolynomial HarmonicCounterexample.ComplexAngular HarmonicCounterexample.Berger
attribute [local instance 100] LieRing.ofAssociativeRing

lemma traceFreeEnd_conj {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (e : V ≃ₗ⋆[ℂ] V) (X : Module.End ℂ V) :
    e.conj (traceFreeEnd X) = traceFreeEnd (e.conj X) := by
  have h1 : e.conj (1 : Module.End ℂ V) = 1 := e.conjRingEquiv.map_one
  simp only [traceFreeEnd,LinearMap.coe_mk,AddHom.coe_mk,map_sub,map_smulₛₗ,
    starRingEnd_apply,star_div₀,star_natCast,h1,trace_conj_semilinear]

/-- The genuine REAL generated algebra on the real-Cartesian form of the
complex harmonic space; only real control times and linear combinations occur. -/
def harmonicRealAngularLie (l : ℕ) : LieSubalgebra ℝ
    (Module.End ℂ (harmonicSpace (Fin 8) l)) :=
  LieSubalgebra.lieSpan ℝ _ (Set.range fun J : ComplexStructure (Fin 8 ⊕ Fin 8) =>
    traceFreeEnd (harmonicField l J*harmonicField l J))

/-- Real descent for the actual one-block angular algebra. Every trace-zero
operator preserving the real Cartesian form is generated using real scalars. -/
theorem harmonicRealAngularLie_has_specialLinear (l : ℕ) (hl : 2 ≤ l)
    {X : Module.End ℂ (harmonicSpace (Fin 8) l)}
    (hX : LinearMap.trace ℂ (harmonicSpace (Fin 8) l) X=0)
    (hr : (spaceRealConjugation l).conj X=X) :
    X ∈ harmonicRealAngularLie l := by
  apply real_lieSpan_of_complex _ (realEndConjugation (spaceRealConjugation l))
    (realEndConjugation_I _) (realEndConjugation_lie _)
    (hx := harmonicAngularLie_has_specialLinear l hl hX) (hτx := hr)
  rintro Y ⟨J,rfl⟩
  change (spaceRealConjugation l).conj (traceFreeEnd (harmonicField l J*harmonicField l J)) = _
  rw [traceFreeEnd_conj]
  have he : (spaceRealConjugation l).conj (harmonicField l J*harmonicField l J) =
      (spaceRealConjugation l).conj (harmonicField l J)*(spaceRealConjugation l).conj (harmonicField l J) :=
    (spaceRealConjugation l).conjRingEquiv.map_mul _ _
  rw [he,spaceRealConjugation_conj_harmonicField]

end HarmonicCounterexample.Control

end

noncomputable section
open Matrix
open scoped BigOperators
open scoped Topology
open Filter
open Matrix
open scoped BigOperators
open Matrix MvPolynomial
open Matrix
open scoped BigOperators
open scoped BigOperators
open Matrix

namespace HarmonicCounterexample.Control
attribute [local instance 100] LieRing.ofAssociativeRing
variable {𝕜 ι κ : Type*} [Field 𝕜] [Fintype ι] [DecidableEq ι]

lemma filterEntry_mem_submodule (L : Submodule 𝕜 (Matrix ι ι 𝕜))
    {d : ι → 𝕜} (hd : ∀ Y ∈ L, ⁅diagonal d,Y⁆ ∈ L) (p q i j : ι)
    {X : Matrix ι ι 𝕜} (hX : X ∈ L) : filterEntry d p q i j X ∈ L :=
  L.smul_mem _ (L.sub_mem (hd X hX) (L.smul_mem _ hX))

/-- Finite joint-eigenvalue interpolation isolates a genuine directed matrix
entry. Zeros of the input require no spectral separation. This is the precise
linear-algebra step used after the torus Fourier projection in the manuscript. -/
theorem isolate_entry_submodule (L : Submodule 𝕜 (Matrix ι ι 𝕜))
    (d : κ → ι → 𝕜) (hd : ∀ a Y, Y ∈ L → ⁅diagonal (d a),Y⁆ ∈ L)
    {X : Matrix ι ι 𝕜} (hX : X ∈ L) (p q : ι)
    (hsep : ∀ i j, (i,j) ≠ (p,q) → X i j ≠ 0 →
      ∃ a, d a p-d a q ≠ d a i-d a j) :
    single p q (X p q) ∈ L := by
  have construct (s : Finset (ι×ι)) (hs : (p,q) ∉ s) :
      ∃ Z : Matrix ι ι 𝕜, Z ∈ L ∧ Z p q = X p q ∧
        (∀ i j,X i j = 0 → Z i j = 0) ∧ (∀ r ∈ s,Z r.1 r.2 = 0) := by
    induction s using Finset.induction_on with
    | empty => exact ⟨X,hX,rfl,fun _ _ h => h,by simp⟩
    | @insert r s hr ih =>
      obtain ⟨Z,hZ,ht,hz,hsz⟩ := ih (fun h => hs (Finset.mem_insert_of_mem h))
      by_cases hxr : X r.1 r.2 = 0
      · exact ⟨Z,hZ,ht,hz,fun z h => (Finset.mem_insert.1 h).elim
          (fun h => h ▸ hz r.1 r.2 hxr) (hsz z)⟩
      · obtain ⟨a,ha⟩ := hsep r.1 r.2 (by
          intro he; exact hs (he ▸ Finset.mem_insert_self r s)) hxr
        refine ⟨filterEntry (d a) p q r.1 r.2 Z,filterEntry_mem_submodule L (hd a) p q _ _ hZ,?_,?_,?_⟩
        · rw [filterEntry_apply,inv_mul_cancel₀ (sub_ne_zero.2 ha),one_mul,ht]
        · intro i j hij
          rw [filterEntry_apply,hz i j hij,mul_zero]
        · intro z hz'
          rcases Finset.mem_insert.1 hz' with rfl | hzs
          · rw [filterEntry_apply,sub_self,mul_zero,zero_mul]
          · rw [filterEntry_apply,hsz z hzs,mul_zero]
  obtain ⟨Z,hZ,ht,_,hz⟩ := construct (Finset.univ.erase (p,q)) (Finset.notMem_erase _ _)
  have he : Z = single p q (X p q) := by
    ext i j
    by_cases hij : (i,j) = (p,q)
    · obtain ⟨rfl,rfl⟩ := Prod.mk.inj hij
      simpa using ht
    · have hs : single p q (X p q) i j = 0 :=
        Matrix.single_apply_of_ne p q (X p q) i j (fun h => hij (Prod.ext h.1.symm h.2.symm))
      exact (hz (i,j) (Finset.mem_erase.2 ⟨hij,Finset.mem_univ _⟩)).trans hs.symm
  exact he ▸ hZ

omit [Fintype ι] in
lemma normalize_entry_submodule (L : Submodule 𝕜 (Matrix ι ι 𝕜))
    {p q : ι} {a : 𝕜} (ha : a ≠ 0) (h : single p q a ∈ L) :
    single p q (1:𝕜) ∈ L := by
  have h' := L.smul_mem a⁻¹ h
  simpa only [smul_single,smul_eq_mul,inv_mul_cancel₀ ha] using h'

end HarmonicCounterexample.Control

end

noncomputable section
open Matrix
open scoped BigOperators
open scoped Topology
open Filter
open Matrix
open scoped BigOperators
open Matrix MvPolynomial
open Matrix
open scoped BigOperators
open scoped BigOperators
open Matrix

namespace HarmonicCounterexample.Control
open Matrix
attribute [local instance 100] LieRing.ofAssociativeRing
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma off_diagonal_weight_separation {p q i j : ι} (hpq : p ≠ q) (hne : (i,j) ≠ (p,q)) :
    ∃ a : ι,(Pi.single a (1:ℂ) : ι → ℂ) p-(Pi.single a (1:ℂ) : ι → ℂ) q ≠
      (Pi.single a (1:ℂ) : ι → ℂ) i-(Pi.single a (1:ℂ) : ι → ℂ) j := by
  by_contra hh
  push Not at hh
  have hi : i=p := by
    by_contra hi
    have he := hh p
    by_cases hj : j=p
    · norm_num [Pi.single_apply,hpq,hi,hj] at he
    · simp [hpq,hi,hj] at he
  subst i
  have hj : j=q := by
    by_contra hj
    have he := hh q
    simp [hpq.symm,hj] at he
  exact hne (Prod.ext rfl hj)

lemma ideal_offdiagonal_unit (I : Submodule ℂ (Matrix ι ι ℂ))
    (hinv : ∀ (d : ι → ℂ) (X : Matrix ι ι ℂ),X ∈ I → ⁅diagonal d,X⁆ ∈ I)
    {X : Matrix ι ι ℂ} (hX : X ∈ I) {p q : ι} (hpq : p ≠ q) (hx : X p q ≠ 0) :
    single p q (1:ℂ) ∈ I := by
  apply normalize_entry_submodule I hx
  exact isolate_entry_submodule I (fun a => Pi.single a (1:ℂ))
    (fun a => hinv _) hX p q (fun _ _ h _ => off_diagonal_weight_separation hpq h)

lemma trace_single_offdiagonal (i j : ι) (hij : i ≠ j) :
    (single i j (1:ℂ)).trace = 0 := Matrix.trace_single_eq_of_ne i j 1 hij

lemma central_scalar_lie_zero (c : ℂ) (X : Matrix ι ι ℂ) : ⁅c • (1 : Matrix ι ι ℂ),X⁆ = 0 := by
  simp [Ring.lie_def]

lemma ideal_diagonal_invariant [Nonempty ι] (I : Submodule ℂ (Matrix ι ι ℂ))
    (hinv : ∀ (A X : Matrix ι ι ℂ),A.trace=0 → X ∈ I → ⁅A,X⁆ ∈ I) :
    ∀ (d : ι → ℂ) (X : Matrix ι ι ℂ),X ∈ I → ⁅diagonal d,X⁆ ∈ I := by
  intro d X hX
  let A := diagonal d - ((∑ i,d i)/(Fintype.card ι:ℂ)) • (1 : Matrix ι ι ℂ)
  have hn : (Fintype.card ι:ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hA : A.trace=0 := by
    simp only [A,trace_sub,trace_diagonal,trace_smul,trace_one,smul_eq_mul]
    rw [div_mul_cancel₀ _ hn,sub_self]
  have h := hinv A X hA hX
  simpa only [A,sub_lie,central_scalar_lie_zero,sub_zero] using h

lemma single_lie_single_complex (i j k m : ι) :
    ⁅single i j (1:ℂ),single k m (1:ℂ)⁆ =
      (if j=k then single i m (1:ℂ) else 0)-(if m=i then single k j (1:ℂ) else 0) := by
  rw [Ring.lie_def]
  by_cases h : j=k <;> by_cases h' : m=i
  · subst k; subst m; simp [single_mul_single_same]
  · subst k; simp [h',single_mul_single_same,single_mul_single_of_ne (1:ℂ) j m i h' (1:ℂ)]
  · subst m; simp [h,single_mul_single_same,single_mul_single_of_ne (1:ℂ) i j k h (1:ℂ)]
  · simp [h,h',single_mul_single_of_ne (1:ℂ) i j k h (1:ℂ),
      single_mul_single_of_ne (1:ℂ) k m i h' (1:ℂ)]

lemma ideal_unit_all_units (I : Submodule ℂ (Matrix ι ι ℂ))
    (hinv : ∀ (A X : Matrix ι ι ℂ),A.trace=0 → X ∈ I → ⁅A,X⁆ ∈ I)
    {p q : ι} (hpq : p ≠ q) (hp : single p q (1:ℂ) ∈ I) :
    ∀ i j,i ≠ j → single i j (1:ℂ) ∈ I := by
  have hd : single q q (1:ℂ)-single p p (1:ℂ) ∈ I := by
    have h := hinv (single q p (1:ℂ)) (single p q (1:ℂ)) (trace_single_offdiagonal _ _ hpq.symm) hp
    simpa only [single_lie_single_complex,ite_true] using h
  have hrow (j : ι) (hj : p ≠ j) : single p j (1:ℂ) ∈ I := by
    have h := hinv (single p j (1:ℂ)) _ (trace_single_offdiagonal _ _ hj) hd
    have he : ⁅single p j (1:ℂ),single q q (1:ℂ)-single p p (1:ℂ)⁆ =
        (if j=q then (2:ℂ) else 1) • single p j (1:ℂ) := by
      simp only [lie_sub,single_lie_single_complex]
      by_cases hjq : j=q
      · subst j; simp only [hpq.symm,ite_true,ite_false,sub_zero,zero_sub,sub_neg_eq_add,two_smul]
      · simp [hjq,(Ne.symm hj),hpq.symm]
    rw [he] at h
    have hc : (if j=q then (2:ℂ) else 1) ≠ 0 := by split_ifs <;> norm_num
    have hs := I.smul_mem (if j=q then (2:ℂ) else 1)⁻¹ h
    simpa only [smul_smul,inv_mul_cancel₀ hc,one_smul] using hs
  have hcol (i : ι) (hi : i ≠ p) : single i p (1:ℂ) ∈ I := by
    have h := hinv (single i p (1:ℂ)) _ (trace_single_offdiagonal _ _ hi) hd
    have he : ⁅single i p (1:ℂ),single q q (1:ℂ)-single p p (1:ℂ)⁆ =
        (if i=q then (-2:ℂ) else -1) • single i p (1:ℂ) := by
      simp only [lie_sub,single_lie_single_complex]
      by_cases hiq : i=q
      · subst i; simp only [hpq,ite_true,ite_false,sub_zero,zero_sub,neg_smul,two_smul]; abel
      · simp [hiq,(Ne.symm hiq),(Ne.symm hi),hpq]
    rw [he] at h
    have hc : (if i=q then (-2:ℂ) else -1) ≠ 0 := by split_ifs <;> norm_num
    have hs := I.smul_mem (if i=q then (-2:ℂ) else -1)⁻¹ h
    simpa only [smul_smul,inv_mul_cancel₀ hc,one_smul] using hs
  intro i j hij
  by_cases hip : i=p
  · subst i; exact hrow j hij
  by_cases hjp : j=p
  · subst j; exact hcol i hij
  have h := hinv (single i p (1:ℂ)) _ (trace_single_offdiagonal _ _ hip) (hrow j (Ne.symm hjp))
  simpa [single_lie_single_complex,hij.symm] using h

end HarmonicCounterexample.Control

end

noncomputable section
open Matrix
open scoped BigOperators
open scoped Topology
open Filter
open Matrix
open scoped BigOperators
open Matrix MvPolynomial
open Matrix
open scoped BigOperators
open scoped BigOperators
open Matrix

namespace HarmonicCounterexample.Control
open Matrix
attribute [local instance 100] LieRing.ofAssociativeRing
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

lemma nonzero_tracefree_has_diagonal_difference {X : Matrix ι ι ℂ}
    (hX : X ≠ 0) (ht : X.trace=0) (hoff : ∀ i j,i ≠ j → X i j=0) :
    ∃ p q,X p p ≠ X q q := by
  by_contra hh
  push Not at hh
  let p := Classical.arbitrary ι
  have he : X = X p p • (1 : Matrix ι ι ℂ) := by
    ext i j
    by_cases hij : i=j
    · subst j; simp [hh i p]
    · simp [hoff i j hij,hij]
  have hp : X p p=0 := by
    rw [he,trace_smul,trace_one] at ht
    simp only [smul_eq_mul] at ht
    exact (mul_eq_zero.mp ht).resolve_right (by exact_mod_cast Fintype.card_ne_zero)
  exact hX (by rw [he,hp,zero_smul])

lemma ideal_has_unit (I : Submodule ℂ (Matrix ι ι ℂ))
    (hinv : ∀ (A X : Matrix ι ι ℂ),A.trace=0 → X ∈ I → ⁅A,X⁆ ∈ I)
    {X : Matrix ι ι ℂ} (hX : X ∈ I) (hne : X ≠ 0) (ht : X.trace=0) :
    ∃ p q,p ≠ q ∧ single p q (1:ℂ) ∈ I := by
  by_cases hoff : ∃ p q,p ≠ q ∧ X p q ≠ 0
  · obtain ⟨p,q,hpq,hx⟩ := hoff
    exact ⟨p,q,hpq,ideal_offdiagonal_unit I (ideal_diagonal_invariant I hinv) hX hpq hx⟩
  · push Not at hoff
    obtain ⟨p,q,hpq⟩ := nonzero_tracefree_has_diagonal_difference hne ht hoff
    have hpq' : p ≠ q := fun h => hpq (h ▸ rfl)
    have hY := hinv (single p q 1) X (trace_single_offdiagonal _ _ hpq') hX
    have hy : ⁅single p q (1:ℂ),X⁆ p q = X q q-X p p := by
      simp [Ring.lie_def,Matrix.mul_apply,Matrix.single_apply]
    exact ⟨p,q,hpq',ideal_offdiagonal_unit I (ideal_diagonal_invariant I hinv) hY hpq'
      (by rw [hy]; exact sub_ne_zero.2 hpq.symm)⟩

omit [Nonempty ι] in
lemma tracefree_mem_submodule_of_units (I : Submodule ℂ (Matrix ι ι ℂ)) (a : ι)
    (hoff : ∀ i j,i ≠ j → single i j (1:ℂ) ∈ I)
    (hdiag : ∀ i,single i i (1:ℂ)-single a a 1 ∈ I)
    {X : Matrix ι ι ℂ} (hX : X.trace=0) : X ∈ I := by
  have hm : (∑ i : ι,∑ j : ι,
      (single i j (X i j)-(if i=j then single a a (X i i) else 0))) ∈ I := by
    apply I.sum_mem; intro i _
    apply I.sum_mem; intro j _
    by_cases hij : i=j
    · subst j
      simpa only [ite_true,smul_sub,smul_single,smul_eq_mul,mul_one]
        using I.smul_mem (X i i) (hdiag i)
    · simpa only [hij,ite_false,sub_zero,smul_single,smul_eq_mul,mul_one]
        using I.smul_mem (X i j) (hoff i j hij)
  have he : (∑ i : ι,∑ j : ι,
      (single i j (X i j)-(if i=j then single a a (X i i) else 0))) = X := by
    simp only [Finset.sum_sub_distrib,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
    rw [← Matrix.matrix_eq_sum_single X]
    have hz : (∑ i : ι,single a a (X i i)) = 0 := by
      have hr (i : ι) : single a a (X i i) = X i i • single a a (1:ℂ) := by simp
      simp only [hr,← Finset.sum_smul]
      change trace X • single a a (1:ℂ) = 0
      rw [hX,zero_smul]
    rw [hz,sub_zero]
  exact he ▸ hm

/-- Simplicity, proved entry by entry: every subspace invariant under all
special-linear brackets and containing a nonzero trace-zero matrix contains
all trace-zero matrices. -/
theorem specialLinear_ideal_saturation (I : Submodule ℂ (Matrix ι ι ℂ))
    (hinv : ∀ (A X : Matrix ι ι ℂ),A.trace=0 → X ∈ I → ⁅A,X⁆ ∈ I)
    {X : Matrix ι ι ℂ} (hX : X ∈ I) (hne : X ≠ 0) (ht : X.trace=0)
    {Y : Matrix ι ι ℂ} (hY : Y.trace=0) : Y ∈ I := by
  obtain ⟨p,q,hpq,hp⟩ := ideal_has_unit I hinv hX hne ht
  have hoff := ideal_unit_all_units I hinv hpq hp
  apply tracefree_mem_submodule_of_units I p hoff _ hY
  intro i
  by_cases hi : i=p
  · subst i; simpa only [sub_self] using I.zero_mem
  have h := hinv (single i p 1) _ (trace_single_offdiagonal _ _ hi) (hoff p i (Ne.symm hi))
  simpa only [single_lie_single_complex,ite_true] using h

end HarmonicCounterexample.Control

end

noncomputable section
open Matrix
open scoped BigOperators
open scoped Topology
open Filter
open Matrix
open scoped BigOperators
open Matrix MvPolynomial
open Matrix
open scoped BigOperators
open scoped BigOperators
open Matrix

namespace HarmonicCounterexample.Control
open Matrix LieAlgebra
attribute [local instance 100] LieRing.ofAssociativeRing
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]



theorem specialLinear_isSimple (hn : 1 < Fintype.card ι) :
    LieAlgebra.IsSimple ℂ (SpecialLinear.sl ι ℂ) := by
  refine ⟨?_, SpecialLinear.sl_non_abelian ι ℂ hn⟩
  intro I
  by_cases hI : I = ⊥
  · exact Or.inl hI
  right
  have hx : ∃ X : SpecialLinear.sl ι ℂ, X ∈ I ∧ X ≠ 0 := by
    by_contra hh
    push Not at hh
    exact hI ((LieSubmodule.eq_bot_iff I).2 hh)
  obtain ⟨X,hX,hne⟩ := hx
  let J := I.toSubmodule.map (SpecialLinear.sl ι ℂ).toSubmodule.subtype
  have hJ : ∀ (A B : Matrix ι ι ℂ),A.trace=0 → B ∈ J → ⁅A,B⁆ ∈ J := by
    intro A B hA hB
    obtain ⟨b,hb,rfl⟩ := hB
    let a : SpecialLinear.sl ι ℂ := ⟨A,hA⟩
    exact ⟨⁅a,b⁆,I.lie_mem hb,rfl⟩
  apply top_unique
  intro Y _
  have hxJ : (X : Matrix ι ι ℂ) ∈ J := ⟨X,hX,rfl⟩
  have hx0 : (X : Matrix ι ι ℂ) ≠ 0 := fun h => hne (Subtype.ext h)
  have hy := specialLinear_ideal_saturation J hJ hxJ hx0 X.property Y.property
  obtain ⟨y,hy,he⟩ := hy
  have he' : y=Y := Subtype.ext he
  exact he' ▸ hy

end HarmonicCounterexample.Control

end

noncomputable section
open Matrix
open scoped BigOperators
open scoped Topology
open Filter
open Matrix
open scoped BigOperators
open Matrix MvPolynomial
open Matrix
open scoped BigOperators
open scoped BigOperators
open Matrix

namespace HarmonicCounterexample.Control
open Matrix LieAlgebra Module
attribute [local instance 100] LieRing.ofAssociativeRing
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

lemma specialLinear_finrank_add_one :
    finrank ℂ (SpecialLinear.sl ι ℂ)+1=(Fintype.card ι)^2 := by
  let f := Matrix.traceLinearMap ι ℂ ℂ
  have hf : f ≠ 0 := by
    intro hh
    let i := Classical.arbitrary ι
    have he := congrArg (fun g : Matrix ι ι ℂ →ₗ[ℂ] ℂ => g (Matrix.single i i 1)) hh
    simp [f] at he
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero hf
  change finrank ℂ (SpecialLinear.sl ι ℂ)+1=finrank ℂ (Matrix ι ι ℂ) at h
  simpa only [Module.finrank_matrix,Module.finrank_self,mul_one,pow_two] using h

lemma specialLinear_not_equiv {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (hne : Fintype.card ι ≠ Fintype.card κ) :
    ¬ Nonempty (SpecialLinear.sl ι ℂ ≃ₗ⁅ℂ⁆ SpecialLinear.sl κ ℂ) := by
  rintro ⟨e⟩
  have hi := specialLinear_finrank_add_one (ι:=ι)
  have hk := specialLinear_finrank_add_one (ι:=κ)
  have h := e.toLinearEquiv.finrank_eq
  apply hne
  nlinarith

end HarmonicCounterexample.Control

end

noncomputable section
open Matrix
open scoped BigOperators
open scoped Topology
open Filter
open Matrix
open scoped BigOperators
open Matrix MvPolynomial
open Matrix
open scoped BigOperators
open scoped BigOperators
open Matrix

namespace HarmonicCounterexample.Control
variable {𝕜 ι : Type*} {L : ι → Type*}

instance piLieRing [∀ i, LieRing (L i)] : LieRing (∀ i,L i) where
  bracket x y := fun i => ⁅x i,y i⁆
  add_lie := by intros; funext i; exact add_lie _ _ _
  lie_add := by intros; funext i; exact lie_add _ _ _
  lie_self := by intros; funext i; exact lie_self _
  leibniz_lie := by intros; funext i; exact leibniz_lie _ _ _

instance piLieAlgebra [CommRing 𝕜] [∀ i, LieRing (L i)] [∀ i, LieAlgebra 𝕜 (L i)] :
    LieAlgebra 𝕜 (∀ i,L i) where
  lie_smul := by intros; funext i; exact lie_smul _ _ _

@[simp] theorem pi_lie_apply [∀ i,LieRing (L i)] (x y : ∀ i,L i) (i : ι) :
    ⁅x,y⁆ i = ⁅x i,y i⁆ := rfl

variable [Field 𝕜] [∀ i,LieRing (L i)] [∀ i,LieAlgebra 𝕜 (L i)]

/-- Coordinate projections of the genuine direct-product Lie algebra. -/
def liePiEval (i : ι) : (∀ j,L j) →ₗ⁅𝕜⁆ L i where
  toLinearMap := LinearMap.proj i
  map_lie' := rfl

def zeroCoordinatesIdeal (S : LieSubalgebra 𝕜 (∀ j,L j))
    (hS : ∀ i (x : L i), ∃ v ∈ S,v i=x) (i : ι) (t : Finset ι) : LieIdeal 𝕜 (L i) where
  carrier := {x | ∃ v ∈ S,v i=x ∧ ∀ j ∈ t,v j=0}
  zero_mem' := ⟨0,S.zero_mem,rfl,fun _ _ => rfl⟩
  add_mem' := by
    rintro x y ⟨v,hv,hvi,hvt⟩ ⟨w,hw,hwi,hwt⟩
    exact ⟨v+w,S.add_mem hv hw,by simp [hvi,hwi],fun j hj => by simp [hvt j hj,hwt j hj]⟩
  smul_mem' := by
    rintro a x ⟨v,hv,hvi,hvt⟩
    exact ⟨a • v,S.smul_mem a hv,by simp [hvi],fun j hj => by simp [hvt j hj]⟩
  lie_mem := by
    rintro x y ⟨v,hv,hvi,hvt⟩
    obtain ⟨w,hw,hwi⟩ := hS i x
    exact ⟨⁅w,v⁆,S.lie_mem hw hv,by simp [hvi,hwi],fun j hj => by simp [hvt j hj]⟩

end HarmonicCounterexample.Control

end

noncomputable section
open Matrix
open scoped BigOperators
open scoped Topology
open Filter
open Matrix
open scoped BigOperators
open Matrix MvPolynomial
open Matrix
open scoped BigOperators
open scoped BigOperators
open Matrix

namespace HarmonicCounterexample.Control
variable {𝕜 A B : Type*} [Field 𝕜] [LieRing A] [LieAlgebra 𝕜 A]
  [LieRing B] [LieAlgebra 𝕜 B]

/-- The vertical kernel of a surjective Lie subdirect product. -/
def verticalIdeal (S : LieSubalgebra 𝕜 (A × B))
    (hB : ∀ b : B, ∃ a : A, (a,b) ∈ S) : LieIdeal 𝕜 B where
  carrier := {b | (0,b) ∈ S}
  zero_mem' := S.zero_mem
  add_mem' := fun hx hy => by simpa using S.add_mem hx hy
  smul_mem' := fun t x hx => by simpa using S.smul_mem t hx
  lie_mem := by
    intro b c hc
    obtain ⟨a,ha⟩ := hB b
    simpa using S.lie_mem ha hc

/-- Goursat's argument for simple, nonisomorphic Lie factors. -/
theorem simple_subdirect_eq_top [LieAlgebra.IsSimple 𝕜 A] [LieAlgebra.IsSimple 𝕜 B]
    (hne : ¬ Nonempty (A ≃ₗ⁅𝕜⁆ B)) (S : LieSubalgebra 𝕜 (A × B))
    (hA : ∀ a : A, ∃ b : B, (a,b) ∈ S)
    (hB : ∀ b : B, ∃ a : A, (a,b) ∈ S) : S = ⊤ := by
  let V := verticalIdeal S hB
  rcases LieAlgebra.IsSimple.eq_bot_or_eq_top V with hv | hv
  · let p : S →ₗ⁅𝕜⁆ A := (LieHom.fst 𝕜 A B).comp S.incl
    let q : S →ₗ⁅𝕜⁆ B := (LieHom.snd 𝕜 A B).comp S.incl
    have hpS : Function.Surjective p := by
      intro a
      obtain ⟨b,hb⟩ := hA a
      exact ⟨⟨(a,b),hb⟩,rfl⟩
    have hpI : Function.Injective p := by
      intro x y hxy
      apply Subtype.ext
      apply Prod.ext hxy
      have hd : (x : A×B).2-(y : A×B).2 ∈ V := by
        change (0,(x : A×B).2-(y : A×B).2) ∈ S
        have hd := S.sub_mem x.property y.property
        have hzero : (x : A×B).1-(y : A×B).1=0 := sub_eq_zero.2 hxy
        change ((x : A×B).1-(y : A×B).1,(x : A×B).2-(y : A×B).2) ∈ S at hd
        rwa [hzero] at hd
      rw [hv] at hd
      exact sub_eq_zero.1 hd
    let e : S ≃ₗ⁅𝕜⁆ A := LieEquiv.ofBijective p ⟨hpI,hpS⟩
    let f : A →ₗ⁅𝕜⁆ B := q.comp e.symm.toLieHom
    have hfS : Function.Surjective f := by
      intro b
      obtain ⟨a,ha⟩ := hB b
      refine ⟨e ⟨(a,b),ha⟩,?_⟩
      simp [f,q]
    rcases LieAlgebra.IsSimple.eq_bot_or_eq_top f.ker with hk | hk
    · exact False.elim (hne ⟨LieEquiv.ofBijective f ⟨f.ker_eq_bot.1 hk,hfS⟩⟩)
    · have hb0 (b : B) : b=0 := by
        obtain ⟨a,rfl⟩ := hfS b
        apply LieHom.mem_ker.1
        rw [hk]
        trivial
      exact False.elim (LieAlgebra.IsSimple.non_abelian (R:=𝕜) (L:=B)
        ⟨fun x y => hb0 ⁅x,y⁆⟩)
  · apply top_unique
    intro x _
    obtain ⟨b,hb⟩ := hA x.1
    have hvx : (0,x.2-b) ∈ S := by
      change x.2-b ∈ V
      rw [hv]
      trivial
    have hh := S.add_mem hb hvx
    simpa using hh

end HarmonicCounterexample.Control

end

noncomputable section
open Matrix
open scoped BigOperators
open scoped Topology
open Filter
open Matrix
open scoped BigOperators
open Matrix MvPolynomial
open Matrix
open scoped BigOperators
open scoped BigOperators
open Matrix

namespace HarmonicCounterexample.Control
variable {𝕜 ι : Type*} {L : ι → Type*} [Field 𝕜]
  [∀ i,LieRing (L i)] [∀ i,LieAlgebra 𝕜 (L i)]
  [∀ i,LieAlgebra.IsSimple 𝕜 (L i)]

/-- Simple nonisomorphic factors cannot be diagonally coupled: every subdirect
product is the whole product. The finite-coordinate proof also explains why
pairwise surjectivity suffices for these nonabelian factors. -/
theorem simple_pi_subdirect_eq_top [Fintype ι] [DecidableEq ι]
    (hne : ∀ i j,i ≠ j → ¬ Nonempty (L i ≃ₗ⁅𝕜⁆ L j))
    (S : LieSubalgebra 𝕜 (∀ j,L j))
    (hS : ∀ i (x : L i),∃ v ∈ S,v i=x) : S=⊤ := by
  have hpair (i j : ι) (hij : i ≠ j) :
      ∀ x : L i,∃ v ∈ S,v i=x ∧ v j=0 := by
    let f := (liePiEval (𝕜:=𝕜) (L:=L) i).prod (liePiEval j)
    let T := S.map f
    have hT : T=⊤ := by
      apply simple_subdirect_eq_top (hne i j hij)
      · intro x
        obtain ⟨v,hv,hvi⟩ := hS i x
        exact ⟨v j,v,hv,Prod.ext hvi rfl⟩
      · intro y
        obtain ⟨v,hv,hvj⟩ := hS j y
        exact ⟨v i,v,hv,Prod.ext rfl hvj⟩
    intro x
    have hx : (x,0) ∈ T := by rw [hT]; trivial
    obtain ⟨v,hv,he⟩ := hx
    exact ⟨v,hv,congrArg Prod.fst he,congrArg Prod.snd he⟩
  have hzeros (i : ι) (t : Finset ι) (hi : i ∉ t) :
      zeroCoordinatesIdeal S hS i t=⊤ := by
    induction t using Finset.induction_on with
    | empty =>
      apply top_unique
      intro x _
      obtain ⟨v,hv,hvi⟩ := hS i x
      exact ⟨v,hv,hvi,by simp⟩
    | @insert j t hj ih =>
      have hij : i ≠ j := fun he => hi (by simp [he])
      have hit : i ∉ t := fun he => hi (Finset.mem_insert_of_mem he)
      have ht := ih hit
      rcases LieAlgebra.IsSimple.eq_bot_or_eq_top (zeroCoordinatesIdeal S hS i (insert j t)) with hh | hh
      · exfalso
        apply LieAlgebra.IsSimple.non_abelian (R:=𝕜) (L:=L i)
        constructor
        intro x y
        have hx : x ∈ zeroCoordinatesIdeal S hS i t := by rw [ht]; trivial
        obtain ⟨v,hv,hvi,hvt⟩ := hx
        obtain ⟨w,hw,hwi,hwj⟩ := hpair i j hij y
        have he : ⁅x,y⁆ ∈ zeroCoordinatesIdeal S hS i (insert j t) := by
          refine ⟨⁅v,w⁆,S.lie_mem hv hw,by simp [hvi,hwi],?_⟩
          intro k hk
          rcases Finset.mem_insert.1 hk with rfl | hkt
          · simp [hwj]
          · simp [hvt k hkt]
        rwa [hh] at he
      · exact hh
  apply top_unique
  intro x _
  have hlift (i : ι) : ∃ v ∈ S,v i=x i ∧ ∀ j,j ≠ i → v j=0 := by
    have hz : x i ∈ zeroCoordinatesIdeal S hS i (Finset.univ.erase i) := by
      rw [hzeros i _ (Finset.notMem_erase _ _)]; trivial
    obtain ⟨v,hv,hvi,hvt⟩ := hz
    exact ⟨v,hv,hvi,fun j hji => hvt j (Finset.mem_erase.2 ⟨hji,Finset.mem_univ _⟩)⟩
  choose v hv hvi hvz using hlift
  have hm := S.sum_mem (t:=Finset.univ) (fun i _ => hv i)
  have he : ∑ i,v i=x := by
    funext j
    simp only [Finset.sum_apply]
    rw [Finset.sum_eq_single j]
    · exact hvi j
    · intro b _ hbj
      exact hvz b j (Ne.symm hbj)
    · simp
  exact he ▸ hm

end HarmonicCounterexample.Control

end

noncomputable section
open Matrix
open scoped BigOperators
open scoped Topology
open Filter
open Matrix
open scoped BigOperators
open Matrix MvPolynomial
open Matrix
open scoped BigOperators
open scoped BigOperators
open Matrix

namespace HarmonicCounterexample.Control
variable {𝕜 ι κ : Type*} {L : ι → Type*} [Field 𝕜]
  [∀ i,LieRing (L i)] [∀ i,LieAlgebra 𝕜 (L i)]
  [∀ i,LieAlgebra.IsSimple 𝕜 (L i)] [Fintype ι] [DecidableEq ι]

/-- The same control parameter acts on all blocks. No independent block
controls are smuggled into the simultaneous generating set. -/
theorem simultaneous_simple_generation (g : κ → ∀ i,L i)
    (hne : ∀ i j,i ≠ j → ¬ Nonempty (L i ≃ₗ⁅𝕜⁆ L j))
    (hblocks : ∀ i,LieSubalgebra.lieSpan 𝕜 (L i) (Set.range fun k => g k i)=⊤) :
    LieSubalgebra.lieSpan 𝕜 (∀ i,L i) (Set.range g)=⊤ := by
  apply simple_pi_subdirect_eq_top hne
  intro i x
  have hi : x ∈ (LieSubalgebra.lieSpan 𝕜 (∀ i,L i) (Set.range g)).map (liePiEval i) := by
    rw [LieSubalgebra.map_lieSpan,← Set.range_comp']
    change x ∈ LieSubalgebra.lieSpan 𝕜 (L i) (Set.range fun k => g k i)
    rw [hblocks i]
    trivial
  obtain ⟨v,hv,he⟩ := hi
  exact ⟨v,hv,he⟩

end HarmonicCounterexample.Control

end

noncomputable section
open Matrix
open scoped BigOperators
open scoped Topology
open Filter
open Matrix
open scoped BigOperators
open Matrix MvPolynomial
open Matrix
open scoped BigOperators
open scoped BigOperators
open Matrix

namespace HarmonicCounterexample.Control
open Module LieAlgebra
attribute [local instance 100] LieRing.ofAssociativeRing
variable {V ι : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Nontrivial V]
  [Fintype ι] [DecidableEq ι]

lemma trace_traceFreeEnd (X : Module.End ℂ V) : LinearMap.trace ℂ V (traceFreeEnd X)=0 := by
  have hn : (finrank ℂ V:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (finrank_pos (R:=ℂ) (M:=V))
  simp only [traceFreeEnd,LinearMap.coe_mk,AddHom.coe_mk,map_sub,map_smul,LinearMap.trace_one,smul_eq_mul]
  rw [div_mul_cancel₀ _ hn,sub_self]

lemma traceFreeEnd_idempotent (X : Module.End ℂ V) : traceFreeEnd (traceFreeEnd X)=traceFreeEnd X :=
  traceFreeEnd_eq_self (trace_traceFreeEnd X)

def endTraceFreeLieHom : Module.End ℂ V →ₗ⁅ℂ⁆ Module.End ℂ V where
  toLinearMap := traceFreeEnd
  map_lie' := traceFreeEnd_lie _ _

/-- Actual trace-free coordinate matrices in an arbitrary basis. -/
def endSLMatrixHom (b : Basis ι ℂ V) : Module.End ℂ V →ₗ⁅ℂ⁆ SpecialLinear.sl ι ℂ where
  toLinearMap :=
    ((LinearMap.toMatrix b b).comp traceFreeEnd).codRestrict (SpecialLinear.sl ι ℂ).toSubmodule
      (fun X => by
        change Matrix.trace (LinearMap.toMatrix b b (traceFreeEnd X))=0
        rw [← LinearMap.trace_eq_matrix_trace ℂ b,trace_traceFreeEnd])
  map_lie' := by
    intro X Y
    apply Subtype.ext
    exact ((LinearMap.toMatrixAlgEquiv b).toLieEquiv.toLieHom.comp endTraceFreeLieHom).map_lie X Y

@[simp] lemma endSLMatrixHom_val (b : Basis ι ℂ V) (X : Module.End ℂ V) :
    (endSLMatrixHom b X : Matrix ι ι ℂ) = LinearMap.toMatrix b b (traceFreeEnd X) := rfl

lemma endSLMatrixHom_tracefree_preimage (b : Basis ι ℂ V) (A : SpecialLinear.sl ι ℂ) :
    ∃ X : Module.End ℂ V, LinearMap.trace ℂ V X=0 ∧ endSLMatrixHom b X=A := by
  refine ⟨Matrix.toLin b b A,?_,?_⟩
  · exact (Matrix.trace_toLin_eq A.val b).trans A.property
  · apply Subtype.ext
    rw [endSLMatrixHom_val,traceFreeEnd_eq_self ((Matrix.trace_toLin_eq A.val b).trans A.property)]
    exact LinearMap.toMatrix_toLin b b A.val

/-- Coordinate transport of a proved one-block trace-free generation result. -/
theorem endSLMatrix_span_top {κ : Type*} (b : Basis ι ℂ V) (g : κ → Module.End ℂ V)
    (hg : ∀ X,LinearMap.trace ℂ V X=0 → X ∈ LieSubalgebra.lieSpan ℂ _ (Set.range g)) :
    LieSubalgebra.lieSpan ℂ (SpecialLinear.sl ι ℂ) (Set.range (fun k => endSLMatrixHom b (g k)))=⊤ := by
  let f := endSLMatrixHom b
  have he : (LieSubalgebra.lieSpan ℂ _ (Set.range g)).map f =
      LieSubalgebra.lieSpan ℂ _ (Set.range fun k => endSLMatrixHom b (g k)) := by
    rw [LieSubalgebra.map_lieSpan]
    congr 1
    exact (Set.range_comp' _ _).symm
  rw [← he]
  apply top_unique
  intro A _
  obtain ⟨X,hX,hA⟩ := endSLMatrixHom_tracefree_preimage b A
  exact ⟨X,hg X hX,hA⟩

end HarmonicCounterexample.Control

end

noncomputable section
open Matrix
open scoped BigOperators
open scoped Topology
open Filter
open Matrix
open scoped BigOperators
open Matrix MvPolynomial
open Matrix
open scoped BigOperators
open scoped BigOperators
open Matrix

namespace HarmonicCounterexample.ComplexAngular
open MvPolynomial Module
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

instance complexHomogeneous_finite (σ : Type*) [Fintype σ] (l : ℕ) :
    FiniteDimensional ℂ (homogeneousSubmodule σ ℂ l) :=
  Module.Finite.of_fg (homogeneousSubmodule_fg σ ℂ l)

lemma complexHomogeneous_finrank (σ : Type*) [Fintype σ] (l : ℕ) :
    finrank ℂ (homogeneousSubmodule σ ℂ l) = (Fintype.card σ+l-1).choose l := by
  classical
  rw [homogeneousSubmodule_eq_finsupp_supported]
  have he : {d : σ →₀ ℕ | d.degree=l} =
      (↑((Finset.univ : Finset σ).finsuppAntidiag l) : Set (σ →₀ ℕ)) := by
    ext d
    have hd : d.degree=∑ i : σ,d i := Finsupp.sum_fintype d (fun _ a => a) fun _ => rfl
    simp [Finset.mem_finsuppAntidiag,hd]
  rw [he,(AddMonoidAlgebra.supportedEquivFinsupp
    (R:=ℂ) (S:=ℂ) (↑((Finset.univ : Finset σ).finsuppAntidiag l) : Set (σ →₀ ℕ))).finrank_eq]
  rw [Module.finrank_finsupp_self]
  simp only [Finset.coe_sort_coe,
    Fintype.card_coe,Finset.card_finsuppAntidiag_nat_eq_choose,Finset.card_univ]

def subspaceFischer (S : Submodule ℂ (SplitPolynomial ι)) : S →ₗ[ℂ] Module.Dual ℂ S :=
  S.subtype.dualMap.comp (fischer.comp S.subtype)

omit [DecidableEq ι] in
lemma subspaceFischer_injective (S : Submodule ℂ (SplitPolynomial ι))
    (hc : ∀ P ∈ S,conjugate P ∈ S) : Function.Injective (subspaceFischer S) := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro P hP
  apply Subtype.ext
  apply fischer_definite
  exact congrArg (fun f : Module.Dual ℂ S => f ⟨conjugate P,hc P P.property⟩) hP

omit [DecidableEq ι] in
lemma subspaceFischer_surjective (S : Submodule ℂ (SplitPolynomial ι)) [FiniteDimensional ℂ S]
    (hc : ∀ P ∈ S,conjugate P ∈ S) : Function.Surjective (subspaceFischer S) :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq (K := ℂ) (V := S)).symm).1 (subspaceFischer_injective S hc)

omit [DecidableEq ι] in
lemma quadric_homogeneous : (quadric ι).IsHomogeneous 2 := by
  apply IsHomogeneous.sum
  intro i _
  exact (isHomogeneous_X ℂ (Sum.inl i)).mul (isHomogeneous_X ℂ (Sum.inr i))

def homogeneousQuadricMultiply (l : ℕ) : homogeneousSubmodule (ι ⊕ ι) ℂ l →ₗ[ℂ]
    homogeneousSubmodule (ι ⊕ ι) ℂ (l+2) where
  toFun P := ⟨quadric ι*P,by
    change (quadric ι*(P : SplitPolynomial ι)).IsHomogeneous (l+2)
    have h := quadric_homogeneous.mul P.property
    simpa only [Nat.add_comm 2] using h⟩
  map_add' P Q := Subtype.ext (mul_add _ _ _)
  map_smul' c P := Subtype.ext (mul_smul_comm _ _ _)

omit [DecidableEq ι] in
lemma homogeneousQuadricMultiply_injective [Nontrivial ι] (l : ℕ) :
    Function.Injective (homogeneousQuadricMultiply (ι:=ι) l) := by
  intro P Q h
  exact Subtype.ext (mul_left_cancel₀ quadric_irreducible.ne_zero (congrArg Subtype.val h))

def homogeneousMixedLaplacian (l : ℕ) : homogeneousSubmodule (ι ⊕ ι) ℂ (l+2) →ₗ[ℂ]
    homogeneousSubmodule (ι ⊕ ι) ℂ l where
  toFun P := ⟨mixedLaplacian P,by
    rw [mixedLaplacian_apply]
    apply IsHomogeneous.sum
    intro i _
    have h := (P.property.pderiv (i:=Sum.inr i)).pderiv (i:=Sum.inl i)
    simpa only [show l+2-1-1=l from by omega] using h⟩
  map_add' P Q := Subtype.ext (map_add mixedLaplacian (P : SplitPolynomial ι) (Q : SplitPolynomial ι))
  map_smul' c P := Subtype.ext (map_smul mixedLaplacian c (P : SplitPolynomial ι))

omit [DecidableEq ι] in
lemma homogeneousMixedLaplacian_surjective [Nontrivial ι] (l : ℕ) :
    Function.Surjective (homogeneousMixedLaplacian (ι:=ι) l) := by
  intro Q
  obtain ⟨φ,hφ⟩ := LinearMap.dualMap_surjective_of_injective (homogeneousQuadricMultiply_injective l)
    (subspaceFischer (homogeneousSubmodule (ι ⊕ ι) ℂ l) Q)
  obtain ⟨P,hP⟩ := subspaceFischer_surjective (homogeneousSubmodule (ι ⊕ ι) ℂ (l+2))
    (fun _ h => h.map _) φ
  refine ⟨P,subspaceFischer_injective (homogeneousSubmodule (ι ⊕ ι) ℂ l)
    (fun _ h => h.map _) ?_⟩
  ext R
  have h := congrArg (fun f : Module.Dual ℂ (homogeneousSubmodule (ι ⊕ ι) ℂ l) => f R) hφ
  rw [← hP] at h
  change fischer (P : SplitPolynomial ι) (quadric ι*R) = fischer (Q : SplitPolynomial ι) R at h
  change fischer (mixedLaplacian (P : SplitPolynomial ι)) R = _
  rw [fischer_symm,← fischer_quadric,fischer_symm]
  exact h

def harmonicSpaceKernelEquiv (l : ℕ) : LinearMap.ker (homogeneousMixedLaplacian (ι:=ι) l) ≃ₗ[ℂ]
    harmonicSpace ι (l+2) where
  toFun P := ⟨P.val.val,P.val.property,congrArg Subtype.val P.property⟩
  invFun P := ⟨⟨P.val,P.property.1⟩,Subtype.ext P.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [DecidableEq ι] in
lemma harmonicSpace_finrank_add [Nontrivial ι] (l : ℕ) :
    finrank ℂ (harmonicSpace ι (l+2)) + (2*Fintype.card ι+l-1).choose l =
      (2*Fintype.card ι+l+1).choose (l+2) := by
  have h := LinearMap.finrank_range_add_finrank_ker (homogeneousMixedLaplacian (ι:=ι) l)
  rw [LinearMap.range_eq_top.2 (homogeneousMixedLaplacian_surjective l),
    finrank_top,(harmonicSpaceKernelEquiv l).finrank_eq,complexHomogeneous_finrank] at h
  rw [complexHomogeneous_finrank] at h
  simp only [Fintype.card_sum,← two_mul] at h
  rw [show 2*Fintype.card ι+(l+2)-1 = 2*Fintype.card ι+l+1 from by omega] at h
  simpa only [Nat.add_comm] using h

end HarmonicCounterexample.ComplexAngular

end

noncomputable section
open Matrix
open scoped BigOperators
open scoped Topology
open Filter
open Matrix
open scoped BigOperators
open Matrix MvPolynomial
open Matrix
open scoped BigOperators
open scoped BigOperators
open Matrix

namespace HarmonicCounterexample.ComplexAngular
open Module

lemma harmonicSpace_finrank_sixteen (l : ℕ) :
    finrank ℂ (harmonicSpace (Fin 8) (l+2)) = (l+16).choose 14+(l+15).choose 14 := by
  have h := harmonicSpace_finrank_add (ι:=Fin 8) l
  norm_num only [Fintype.card_fin] at h
  have h1 : (2*8+l-1).choose l=(l+15).choose 15 := by
    rw [show 2*8+l-1=l+15 from by omega,Nat.choose_symm_add]
  have h2 : (2*8+l+1).choose (l+2)=(l+17).choose 15 := by
    rw [show 2*8+l+1=(l+2)+15 from by omega,Nat.choose_symm_add]
  rw [h1,h2] at h
  have h3 := Nat.choose_succ_succ (l+16) 14
  have h4 := Nat.choose_succ_succ (l+15) 14
  norm_num only [Nat.succ_eq_add_one,Nat.add_assoc] at h3 h4
  omega

lemma harmonicSpace_finrank_strictMono :
    StrictMono (fun l : ℕ => finrank ℂ (harmonicSpace (Fin 8) (l+2))) := by
  apply strictMono_nat_of_lt_succ
  intro l
  rw [harmonicSpace_finrank_sixteen,harmonicSpace_finrank_sixteen]
  have h1 := Nat.choose_succ_succ (l+16) 13
  have h2 := Nat.choose_succ_succ (l+15) 13
  have hp := Nat.choose_pos (show 13 ≤ l+16 from by omega)
  norm_num only [Nat.succ_eq_add_one,Nat.add_assoc] at h1 h2 ⊢
  omega

end HarmonicCounterexample.ComplexAngular

end

noncomputable section
open Matrix
open scoped BigOperators
open scoped Topology
open Filter
open Matrix
open scoped BigOperators
open Matrix MvPolynomial
open Matrix
open scoped BigOperators
open scoped BigOperators
open Matrix

namespace HarmonicCounterexample.Control
variable {𝕜 V κ : Type*} [Field 𝕜] [LieRing V] [LieAlgebra 𝕜 V]

lemma lieSpan_range_smul (g : κ → V) (c : 𝕜) (hc : c ≠ 0) :
    LieSubalgebra.lieSpan 𝕜 V (Set.range (fun k => c • g k)) =
      LieSubalgebra.lieSpan 𝕜 V (Set.range g) := by
  apply le_antisymm
  · apply LieSubalgebra.lieSpan_le.2
    rintro _ ⟨k,rfl⟩
    exact LieSubalgebra.smul_mem _ c (LieSubalgebra.subset_lieSpan ⟨k,rfl⟩)
  · apply LieSubalgebra.lieSpan_le.2
    rintro _ ⟨k,rfl⟩
    have h := (LieSubalgebra.lieSpan 𝕜 V (Set.range (fun k => c • g k))).smul_mem c⁻¹
      (LieSubalgebra.subset_lieSpan (Set.mem_range_self k))
    change g k ∈ LieSubalgebra.lieSpan 𝕜 V (Set.range (fun k => c • g k))
    simpa only [smul_smul,inv_mul_cancel₀ hc,one_smul] using h

end HarmonicCounterexample.Control

end

noncomputable section
open Matrix
open scoped BigOperators
open scoped Topology
open Filter
open Matrix
open scoped BigOperators
open Matrix MvPolynomial
open Matrix
open scoped BigOperators
open scoped BigOperators
open Matrix

namespace HarmonicCounterexample.Control
open Module LieAlgebra HarmonicCounterexample.ComplexAngular HarmonicCounterexample.Berger
attribute [local instance 100] LieRing.ofAssociativeRing

/-- The actual complex harmonic degree l+2, coordinatized only after its
Laplacian kernel and dimension have been proved. -/
abbrev harmonicSL (l : ℕ) :=
  SpecialLinear.sl (Fin (finrank ℂ (harmonicSpace (Fin 8) (l+2)))) ℂ

instance harmonicIndex_nonempty (l : ℕ) :
    Nonempty (Fin (finrank ℂ (harmonicSpace (Fin 8) (l+2)))) := by
  have h := harmonicSpace_finrank_lower (ι:=Fin 8) (l+2) (by omega)
  simp only [Fintype.card_fin] at h
  exact Fin.pos_iff_nonempty.1 (by omega)

lemma harmonicIndex_card_gt_one (l : ℕ) :
    1 < Fintype.card (Fin (finrank ℂ (harmonicSpace (Fin 8) (l+2)))) := by
  have h := harmonicSpace_finrank_lower (ι:=Fin 8) (l+2) (by omega)
  simp only [Fintype.card_fin] at h ⊢
  omega

instance harmonicSL_simple (l : ℕ) : LieAlgebra.IsSimple ℂ (harmonicSL l) :=
  specialLinear_isSimple (harmonicIndex_card_gt_one l)

lemma harmonicSL_not_equiv {l j : ℕ} (h : l ≠ j) :
    ¬ Nonempty (harmonicSL l ≃ₗ⁅ℂ⁆ harmonicSL j) := by
  apply specialLinear_not_equiv
  simp only [Fintype.card_fin]
  exact fun he => h (harmonicSpace_finrank_strictMono.injective he)

def harmonicControlMatrix (l : ℕ) (c : ℂ) (J : ComplexStructure (Fin 8 ⊕ Fin 8)) :
    harmonicSL l :=
  endSLMatrixHom (Module.finBasis ℂ (harmonicSpace (Fin 8) (l+2)))
    (c • traceFreeEnd (harmonicField (l+2) J*harmonicField (l+2) J))

lemma harmonicControlMatrix_span_top (l : ℕ) (c : ℂ) (hc : c ≠ 0) :
    LieSubalgebra.lieSpan ℂ (harmonicSL l) (Set.range (harmonicControlMatrix l c))=⊤ := by
  apply endSLMatrix_span_top
  intro X hX
  rw [lieSpan_range_smul _ c hc]
  exact harmonicAngularLie_has_specialLinear (l+2) (by omega) hX

/-- Simultaneous complex special-linear controllability of all active degrees
2,...,L+1 in n=16, with arbitrary nonzero degree weights. Each generator uses
ONE genuine real orthogonal complex structure shared by ALL degrees. -/
theorem harmonic_simultaneous_complex_control (L : ℕ) (c : Fin L → ℂ)
    (hc : ∀ l,c l ≠ 0) :
    LieSubalgebra.lieSpan ℂ (∀ l : Fin L,harmonicSL l.val)
      (Set.range (fun J : ComplexStructure (Fin 8 ⊕ Fin 8) =>
        fun l : Fin L => harmonicControlMatrix l.val (c l) J))=⊤ := by
  apply simultaneous_simple_generation
  · intro i j hij
    exact harmonicSL_not_equiv (fun he => hij (Fin.ext he))
  · intro i
    exact harmonicControlMatrix_span_top i.val (c i) (hc i)

end HarmonicCounterexample.Control

end

noncomputable section
open Matrix
open scoped BigOperators
open scoped Topology
open Filter
open Matrix
open scoped BigOperators
open Matrix MvPolynomial
open Matrix
open scoped BigOperators
open scoped BigOperators
open Matrix

namespace HarmonicCounterexample.Control
open Module
attribute [local instance 100] LieRing.ofAssociativeRing
variable {ι : Type*} {V : ι → Type*} [∀ i,AddCommGroup (V i)]
  [∀ i,Module ℂ (V i)] [∀ i,FiniteDimensional ℂ (V i)] [∀ i,Nontrivial (V i)]

/-- Coordinate-free trace-zero tuples of actual endomorphisms. -/
def traceFreeTuple : LieSubalgebra ℂ (∀ i,Module.End ℂ (V i)) where
  carrier := {X | ∀ i,LinearMap.trace ℂ (V i) (X i)=0}
  zero_mem' := by intro i; exact map_zero _
  add_mem' := by intro X Y hX hY i; exact (map_add _ _ _).trans (by rw [hX i,hY i,zero_add])
  smul_mem' := by
    intro c X hX i
    change LinearMap.trace ℂ (V i) (c • X i)=0
    rw [map_smul,hX i,smul_zero]
  lie_mem' := by intro X Y _ _ i; exact LinearMap.trace_lie (X i) (Y i)

def endSLTupleHom : (∀ i,Module.End ℂ (V i)) →ₗ⁅ℂ⁆
    (∀ i,LieAlgebra.SpecialLinear.sl (Fin (finrank ℂ (V i))) ℂ) where
  toLinearMap := LinearMap.pi (fun i =>
    (endSLMatrixHom (Module.finBasis ℂ (V i))).toLinearMap.comp (LinearMap.proj i))
  map_lie' := by intro X Y; funext i; exact (endSLMatrixHom (Module.finBasis ℂ (V i))).map_lie _ _

lemma endSLTupleHom_injective_on_tracefree {X Y : ∀ i,Module.End ℂ (V i)}
    (hX : X ∈ traceFreeTuple) (hY : Y ∈ traceFreeTuple)
    (he : endSLTupleHom X=endSLTupleHom Y) : X=Y := by
  funext i
  have hi := congrArg (fun Z => (Z i).val) he
  change LinearMap.toMatrix _ _ (traceFreeEnd (X i)) =
    LinearMap.toMatrix _ _ (traceFreeEnd (Y i)) at hi
  rw [traceFreeEnd_eq_self (hX i),traceFreeEnd_eq_self (hY i)] at hi
  exact (LinearMap.toMatrix _ _).injective hi

lemma tuple_tracefree_span_of_matrix_full {κ : Type*} (g : κ → ∀ i,Module.End ℂ (V i))
    (hg : ∀ k,g k ∈ traceFreeTuple)
    (hfull : LieSubalgebra.lieSpan ℂ _ (Set.range (fun k => endSLTupleHom (g k)))=⊤)
    {X : ∀ i,Module.End ℂ (V i)} (hX : X ∈ traceFreeTuple) :
    X ∈ LieSubalgebra.lieSpan ℂ (∀ i,Module.End ℂ (V i)) (Set.range g) := by
  let S := LieSubalgebra.lieSpan ℂ (∀ i,Module.End ℂ (V i)) (Set.range g)
  have hS : S ≤ traceFreeTuple := LieSubalgebra.lieSpan_le.2 (by rintro _ ⟨k,rfl⟩; exact hg k)
  have hi : endSLTupleHom X ∈ S.map endSLTupleHom := by
    change endSLTupleHom X ∈ (LieSubalgebra.lieSpan ℂ _ (Set.range g)).map endSLTupleHom
    rw [LieSubalgebra.map_lieSpan,← Set.range_comp',hfull]
    trivial
  obtain ⟨Y,hY,he⟩ := hi
  have he' := endSLTupleHom_injective_on_tracefree (hS hY) hX he
  exact he' ▸ hY

end HarmonicCounterexample.Control

end

noncomputable section
open Matrix
open scoped BigOperators
open scoped Topology
open Filter
open Matrix
open scoped BigOperators
open Matrix MvPolynomial
open Matrix
open scoped BigOperators
open scoped BigOperators
open Matrix

namespace HarmonicCounterexample.Control.VectorRealDescent
variable {A : Type*} [LieRing A] [LieAlgebra ℂ A] [LieAlgebra ℝ A] [IsScalarTower ℝ ℂ A]

lemma complex_smul_real_parts (c : ℂ) (x : A) :
    c • x = c.re • x + Complex.I • (c.im • x) := by
  rw [← IsScalarTower.algebraMap_smul ℂ c.re x,← IsScalarTower.algebraMap_smul ℂ c.im x]
  rw [smul_smul,← add_smul]
  congr 1
  change c=(c.re:ℂ)+Complex.I*(c.im:ℂ)
  simpa only [mul_comm] using (Complex.re_add_im c).symm

/-- The complex scalar envelope of an actual real Lie algebra, with explicit
real and imaginary witnesses. -/
def complexLieEnvelope (L : LieSubalgebra ℝ A) : LieSubalgebra ℂ A where
  carrier := {x | ∃ a ∈ L,∃ b ∈ L,x=a+Complex.I • b}
  zero_mem' := ⟨0,L.zero_mem,0,L.zero_mem,by simp⟩
  add_mem' := by
    rintro x y ⟨a,ha,b,hb,rfl⟩ ⟨c,hc,d,hd,rfl⟩
    exact ⟨a+c,L.add_mem ha hc,b+d,L.add_mem hb hd,by simp only [smul_add]; abel⟩
  smul_mem' := by
    rintro z x ⟨a,ha,b,hb,rfl⟩
    refine ⟨z.re • a-z.im • b,L.sub_mem (L.smul_mem _ ha) (L.smul_mem _ hb),
      z.im • a+z.re • b,L.add_mem (L.smul_mem _ ha) (L.smul_mem _ hb),?_⟩
    rw [complex_smul_real_parts z]
    simp only [smul_add]
    rw [show (z.re:ℝ) • (Complex.I • b) = Complex.I • (z.re • b) by module,
      show Complex.I • ((z.im:ℝ) • (Complex.I • b)) = -(z.im • b) by
        rw [smul_comm (z.im:ℝ) Complex.I,smul_smul,Complex.I_mul_I,neg_one_smul]]
    abel
  lie_mem' := by
    rintro x y ⟨a,ha,b,hb,rfl⟩ ⟨c,hc,d,hd,rfl⟩
    refine ⟨⁅a,c⁆-⁅b,d⁆,L.sub_mem (L.lie_mem ha hc) (L.lie_mem hb hd),
      ⁅a,d⁆+⁅b,c⁆,L.add_mem (L.lie_mem ha hd) (L.lie_mem hb hc),?_⟩
    simp only [add_lie,lie_add,smul_lie,lie_smul,smul_add,smul_smul,Complex.I_mul_I,neg_one_smul]
    abel

lemma subset_complexLieEnvelope (L : LieSubalgebra ℝ A) {x : A} (hx : x ∈ L) :
    x ∈ complexLieEnvelope L := ⟨x,hx,0,L.zero_mem,by simp⟩

lemma lieSpan_complex_decomposition (s : Set A) {x : A}
    (hx : x ∈ LieSubalgebra.lieSpan ℂ A s) :
    ∃ a ∈ LieSubalgebra.lieSpan ℝ A s,∃ b ∈ LieSubalgebra.lieSpan ℝ A s,
      x=a+Complex.I • b := by
  apply (LieSubalgebra.lieSpan_le.2 (show s ⊆ complexLieEnvelope (LieSubalgebra.lieSpan ℝ A s) from ?_)) hx
  intro y hy
  exact subset_complexLieEnvelope _ (LieSubalgebra.subset_lieSpan hy)

/-- Faithful real descent. A conjugation-fixed element of a complex generated
Lie algebra is already in the real generated algebra, provided all generators
are fixed by the same actual algebra conjugation. -/
theorem real_lieSpan_of_complex (s : Set A)
    (τ : A →ₗ[ℝ] A)
    (hτI : ∀ x,τ (Complex.I • x) = -Complex.I • τ x)
    (hτlie : ∀ x y,τ ⁅x,y⁆ = ⁅τ x,τ y⁆)
    (hs : ∀ x ∈ s,τ x=x) {x : A}
    (hx : x ∈ LieSubalgebra.lieSpan ℂ A s) (hτx : τ x=x) :
    x ∈ LieSubalgebra.lieSpan ℝ A s := by
  let F : LieSubalgebra ℝ A :=
    { (LinearMap.ker (τ-LinearMap.id)) with
      lie_mem' := by
        intro u v hu hv
        have hu' : τ u=u := sub_eq_zero.1 hu
        have hv' : τ v=v := sub_eq_zero.1 hv
        change τ ⁅u,v⁆-⁅u,v⁆=0
        rw [hτlie,hu',hv',sub_self] }
  have hF : LieSubalgebra.lieSpan ℝ A s ≤ F := by
    apply LieSubalgebra.lieSpan_le.2
    intro y hy
    change τ y-y=0
    rw [hs y hy,sub_self]
  obtain ⟨a,ha,b,hb,he⟩ := lieSpan_complex_decomposition s hx
  have hτa : τ a=a := sub_eq_zero.1 (hF ha)
  have hτb : τ b=b := sub_eq_zero.1 (hF hb)
  have he' := congrArg τ he
  rw [map_add,hτI,hτa,hτb,hτx] at he'
  have hz : Complex.I • b = 0 := by
    have hh : (2:ℝ) • (Complex.I • b)=0 := by
      rw [two_smul]
      rw [neg_smul] at he'
      exact eq_neg_iff_add_eq_zero.1 (add_left_cancel (he.symm.trans he'))
    exact (smul_eq_zero.mp hh).resolve_left (by norm_num)
  rw [hz,add_zero] at he
  exact he ▸ ha

end HarmonicCounterexample.Control.VectorRealDescent

end

noncomputable section
open Matrix
open scoped BigOperators
open scoped Topology
open Filter
open Matrix
open scoped BigOperators
open Matrix MvPolynomial
open Matrix
open scoped BigOperators
open scoped BigOperators
open Matrix

namespace HarmonicCounterexample.Control
open Module HarmonicCounterexample.ComplexAngular HarmonicCounterexample.Berger
attribute [local instance 100] LieRing.ofAssociativeRing

/-- Shared weighted angular generators as ACTUAL endomorphisms, not just
coordinate matrices. Positive source weights are allowed in particular. -/
def harmonicTupleGenerator (L : ℕ) (c : Fin L → ℂ)
    (J : ComplexStructure (Fin 8 ⊕ Fin 8)) :
    ∀ l : Fin L,Module.End ℂ (harmonicSpace (Fin 8) (l.val+2)) :=
  fun l => c l • traceFreeEnd (harmonicField (l.val+2) J*harmonicField (l.val+2) J)

lemma harmonicTupleGenerator_tracefree (L : ℕ) (c : Fin L → ℂ)
    (J : ComplexStructure (Fin 8 ⊕ Fin 8)) :
    harmonicTupleGenerator L c J ∈ traceFreeTuple := by
  intro l
  change LinearMap.trace ℂ _ (c l • traceFreeEnd _) = 0
  rw [map_smul,trace_traceFreeEnd,smul_zero]

theorem harmonic_simultaneous_complex_end (L : ℕ) (c : Fin L → ℂ)
    (hc : ∀ l,c l ≠ 0)
    {X : ∀ l : Fin L,Module.End ℂ (harmonicSpace (Fin 8) (l.val+2))}
    (hX : ∀ l,LinearMap.trace ℂ _ (X l)=0) :
    X ∈ LieSubalgebra.lieSpan ℂ _ (Set.range (harmonicTupleGenerator L c)) := by
  apply tuple_tracefree_span_of_matrix_full _ (harmonicTupleGenerator_tracefree L c)
  · exact harmonic_simultaneous_complex_control L c hc
  · exact hX

def harmonicTupleConjugation (L : ℕ) :
    (∀ l : Fin L,Module.End ℂ (harmonicSpace (Fin 8) (l.val+2))) →ₗ[ℝ]
      (∀ l : Fin L,Module.End ℂ (harmonicSpace (Fin 8) (l.val+2))) :=
  LinearMap.pi (fun l => (realEndConjugation (spaceRealConjugation (l.val+2))).comp
    (LinearMap.proj l))

lemma harmonicTupleConjugation_I (L : ℕ)
    (Y : ∀ l : Fin L,Module.End ℂ (harmonicSpace (Fin 8) (l.val+2))) :
    harmonicTupleConjugation L (Complex.I • Y) = -Complex.I • harmonicTupleConjugation L Y := by
  funext l
  exact realEndConjugation_I _ _

lemma harmonicTupleConjugation_lie (L : ℕ)
    (Y Z : ∀ l : Fin L,Module.End ℂ (harmonicSpace (Fin 8) (l.val+2))) :
    harmonicTupleConjugation L ⁅Y,Z⁆ = ⁅harmonicTupleConjugation L Y,harmonicTupleConjugation L Z⁆ := by
  funext l
  exact realEndConjugation_lie _ _ _

lemma harmonic_weighted_generator_real (l : ℕ) (c : ℝ) (J : ComplexStructure (Fin 8 ⊕ Fin 8)) :
    (spaceRealConjugation l).conj ((c:ℂ) • traceFreeEnd (harmonicField l J*harmonicField l J)) =
      (c:ℂ) • traceFreeEnd (harmonicField l J*harmonicField l J) := by
  rw [map_smulₛₗ,show starRingEnd ℂ (c:ℂ) = (c:ℂ) by simp,traceFreeEnd_conj]
  have he : (spaceRealConjugation l).conj (harmonicField l J*harmonicField l J) =
      (spaceRealConjugation l).conj (harmonicField l J)*
      (spaceRealConjugation l).conj (harmonicField l J) :=
    (spaceRealConjugation l).conjRingEquiv.map_mul _ _
  rw [he,spaceRealConjugation_conj_harmonicField]

lemma harmonicTupleGenerator_real (L : ℕ) (c : Fin L → ℝ)
    (J : ComplexStructure (Fin 8 ⊕ Fin 8)) :
    harmonicTupleConjugation L (harmonicTupleGenerator L (fun l => (c l:ℂ)) J) =
      harmonicTupleGenerator L (fun l => (c l:ℂ)) J := by
  funext l
  exact harmonic_weighted_generator_real (l.val+2) (c l) J

/-- Actual simultaneous REAL controllability in every finite set of degrees
2,...,L+1, preserving the source's degree-dependent nonzero real weights.
The real structure is Cartesian coefficient conjugation in split coordinates;
no independent block controls or extra algebra-saturation hypotheses occur. -/
theorem harmonic_simultaneous_real_end (L : ℕ) (c : Fin L → ℝ)
    (hc : ∀ l,c l ≠ 0)
    {X : ∀ l : Fin L,Module.End ℂ (harmonicSpace (Fin 8) (l.val+2))}
    (hX : ∀ l,LinearMap.trace ℂ _ (X l)=0)
    (hr : ∀ l,(spaceRealConjugation (l.val+2)).conj (X l)=X l) :
    X ∈ LieSubalgebra.lieSpan ℝ _
      (Set.range (harmonicTupleGenerator L (fun l => (c l:ℂ)))) := by
  have hcomplex := harmonic_simultaneous_complex_end L (fun l => (c l:ℂ))
    (fun l => Complex.ofReal_ne_zero.mpr (hc l)) hX
  exact VectorRealDescent.real_lieSpan_of_complex _ (harmonicTupleConjugation L)
    (harmonicTupleConjugation_I L) (harmonicTupleConjugation_lie L)
    (by rintro _ ⟨J,rfl⟩; exact harmonicTupleGenerator_real L c J) hcomplex (funext hr)

end HarmonicCounterexample.Control

end

end OAI
