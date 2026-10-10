import OAI.Geometry.HarmonicGrowth.Berger

namespace OAI

noncomputable section

section
open Matrix
open scoped BigOperators
open scoped Topology
open Filter

namespace HarmonicCounterexample.Control

lemma derivative_mem_submodule {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Submodule ℝ E) (hS : IsClosed (S : Set E))
    {f : ℝ → E} {v : E} {t : ℝ} (hf : HasDerivAt f v t) (hm : ∀ x,f x ∈ S) : v ∈ S := by
  apply hS.mem_of_tendsto hf.tendsto_slope
  exact Filter.Eventually.of_forall fun x => S.smul_mem _ (S.sub_mem (hm x) (hm t))

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

lemma conjugation_derivative {g h : ℝ → A} {z : A}
    (hg : HasDerivAt g z 0) (hh : HasDerivAt h (-z) 0)
    (hg0 : g 0 = 1) (hh0 : h 0 = 1) (X : A) :
    HasDerivAt (fun t => g t*X*h t) (z*X-X*z) 0 := by
  convert (hg.mul_const X).mul hh using 1
  simp only [hg0,hh0,one_mul,mul_one,mul_neg,sub_eq_add_neg]

/-- Differentiating a genuine conjugation orbit in a finite-dimensional Lie
subalgebra proves its infinitesimal normalizer property. No Fourier integral
or unproved representation-theoretic closure is substituted. -/
theorem bracket_mem_of_conjugation [FiniteDimensional ℝ A]
    (L : Submodule ℝ A) {g h : ℝ → A} {z : A}
    (hg : HasDerivAt g z 0) (hh : HasDerivAt h (-z) 0)
    (hg0 : g 0 = 1) (hh0 : h 0 = 1)
    (hconj : ∀ t X,X ∈ L → g t*X*h t ∈ L) {X : A} (hX : X ∈ L) : (z*X-X*z) ∈ L :=
  derivative_mem_submodule L L.closed_of_finiteDimensional
    (conjugation_derivative hg hh hg0 hh0 X) (fun t => hconj t X hX)

end HarmonicCounterexample.Control

namespace HarmonicCounterexample.Berger.ComplexStructure
open Matrix NormedSpace
open scoped Matrix.Norms.Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma exp_neg_mul_self (A : Matrix ι ι ℝ) : exp (-A)*exp A = 1 := by
  rw [← Matrix.exp_add_of_commute (-A) A (Commute.refl A).neg_left,neg_add_cancel,exp_zero]

lemma exp_mul_neg_self (A : Matrix ι ι ℝ) : exp A*exp (-A) = 1 := by
  rw [← Matrix.exp_add_of_commute A (-A) (Commute.refl A).neg_right,add_neg_cancel,exp_zero]

lemma exp_skew_transpose (A : Matrix ι ι ℝ) (hA : Aᵀ = -A) :
    (exp A)ᵀ = exp (-A) := by rw [← Matrix.exp_transpose,hA]

/-- An actual smooth orbit of orthogonal complex structures under any skew
infinitesimal rotation; both orientation classes remain available. -/
def rotate (J : ComplexStructure ι) (R : Matrix ι ι ℝ) (hR : Rᵀ = -R) (t : ℝ) :
    ComplexStructure ι where
  matrix := exp (t • R)*J.matrix*exp (-(t • R))
  square := by
    have hi := exp_neg_mul_self (t • R)
    calc
      (exp (t • R)*J.matrix*exp (-(t • R)))*
        (exp (t • R)*J.matrix*exp (-(t • R))) =
        exp (t • R)*(J.matrix*J.matrix)*exp (-(t • R)) := by
          simp only [mul_assoc,← mul_assoc (exp (-(t • R))) (exp (t • R)),hi,one_mul]
      _ = -1 := by rw [J.square,mul_neg,mul_one,neg_mul,exp_mul_neg_self]
  orthogonal := by
    have hs : (t • R)ᵀ = -(t • R) := by simp only [transpose_smul,hR,smul_neg]
    have hns : (-(t • R))ᵀ = -(-(t • R)) := by rw [transpose_neg,hs]
    rw [transpose_mul,transpose_mul,exp_skew_transpose _ hs,exp_skew_transpose _ hns,neg_neg]
    calc
      (exp (t • R)*(J.matrixᵀ*exp (-(t • R))))*
        (exp (t • R)*J.matrix*exp (-(t • R))) =
        exp (t • R)*(J.matrixᵀ*J.matrix)*exp (-(t • R)) := by
          simp only [mul_assoc,← mul_assoc (exp (-(t • R))) (exp (t • R)),
            exp_neg_mul_self,one_mul]
      _ = 1 := by rw [J.orthogonal,mul_one,exp_mul_neg_self]

lemma rotate_zero (J : ComplexStructure ι) (R : Matrix ι ι ℝ) (hR : Rᵀ = -R) :
    (J.rotate R hR 0).matrix = J.matrix := by
  simp [rotate]

lemma rotate_hasDerivAt_zero (J : ComplexStructure ι) (R : Matrix ι ι ℝ) (hR : Rᵀ = -R) :
    HasDerivAt (fun t => (J.rotate R hR t).matrix) (R*J.matrix-J.matrix*R) 0 := by
  have hg := hasDerivAt_exp_smul_const R (0:ℝ)
  simp only [zero_smul,exp_zero,one_mul] at hg
  have hh := hasDerivAt_exp_smul_const (-R) (0:ℝ)
  simp only [smul_neg,zero_smul,neg_zero,exp_zero,one_mul] at hh
  exact HarmonicCounterexample.Control.conjugation_derivative hg hh
    (by simp) (by simp) J.matrix

end HarmonicCounterexample.Berger.ComplexStructure

open Matrix
open scoped BigOperators
open scoped Topology
open Filter
open Matrix

namespace HarmonicCounterexample.Control
attribute [local instance 100] LieRing.ofAssociativeRing
variable {𝕜 ι : Type*} [Field 𝕜] [Fintype ι] [DecidableEq ι]

def traceFree : Matrix ι ι 𝕜 →ₗ[𝕜] Matrix ι ι 𝕜 where
  toFun M := M - (M.trace / (Fintype.card ι : 𝕜)) • 1
  map_add' M N := by simp only [trace_add,add_div,add_smul]; abel
  map_smul' c M := by
    simp only [trace_smul,smul_eq_mul,mul_div_assoc,smul_sub,smul_smul,RingHom.id_apply]

lemma four_square_polarization {A : Type*} [Ring A] (H X Y : A) :
    H*H-(H-2*X)*(H-2*X)-(H-2*Y)*(H-2*Y)+
      (H-2*X-2*Y)*(H-2*X-2*Y)=4*(X*Y+Y*X) := by noncomm_ring

/-- Four sign choices already extract each mixed plane product: no exponential
Walsh sum needs to be computed inside the kernel. Trace subtraction is exact. -/
lemma mixed_product_mem [CharZero 𝕜] (L : LieSubalgebra 𝕜 (Matrix ι ι 𝕜))
    (H X Y : Matrix ι ι 𝕜) (hXY : Commute X Y)
    (h0 : traceFree (H*H) ∈ L)
    (hi : traceFree ((H-2*X)*(H-2*X)) ∈ L)
    (hj : traceFree ((H-2*Y)*(H-2*Y)) ∈ L)
    (hij : traceFree ((H-2*X-2*Y)*(H-2*X-2*Y)) ∈ L) :
    traceFree (X*Y) ∈ L := by
  have h := L.add_mem (L.sub_mem (L.sub_mem h0 hi) hj) hij
  rw [← map_sub,← map_sub,← map_add,four_square_polarization] at h
  have he : (4 : Matrix ι ι 𝕜)*(X*Y+Y*X) = (8:𝕜) • (X*Y) := by
    rw [← hXY.eq]
    ext i j
    simp only [Matrix.smul_apply,mul_apply,ofNat_apply]
    simp
    simp only [Matrix.mul_apply]
    ring
  rw [he,map_smul] at h
  have h' := L.smul_mem (8:𝕜)⁻¹ h
  simpa only [smul_smul,inv_mul_cancel₀ (by norm_num : (8:𝕜) ≠ 0),one_smul] using h'

end HarmonicCounterexample.Control

end

section
open Matrix
open scoped BigOperators
open scoped Topology
open Filter
open Matrix

namespace HarmonicCounterexample.Control

section
open Matrix HarmonicCounterexample.Berger
open scoped Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma traceFree_commutator (A B : Matrix κ κ ℝ) :
    traceFree (A*B-B*A) = A*B-B*A := by
  simp only [traceFree,LinearMap.coe_mk,AddHom.coe_mk,trace_sub]
  rw [trace_mul_comm A B,sub_self,zero_div,zero_smul,sub_zero]

lemma commutator_traceFree (A B : Matrix κ κ ℝ) :
    A*traceFree B-traceFree B*A = A*B-B*A := by
  simp only [traceFree,LinearMap.coe_mk,AddHom.coe_mk,mul_sub,sub_mul,
    mul_smul_comm,smul_mul_assoc,mul_one,one_mul]
  abel

/-- The actual rotation curve makes every skew angular field an infinitesimal
normalizer of the squared-complex-structure generators. The anti-representation
hypothesis is an ordinary algebraic compatibility, proved for actual polynomial
fields in `linearField_bracket`; no Lie-generation conclusion is assumed. -/
lemma square_generator_normalizer
    (ρ : Matrix ι ι ℝ →ₗ[ℝ] Matrix κ κ ℝ)
    (hρ : ∀ M N,ρ (M*N-N*M) = ρ N*ρ M-ρ M*ρ N)
    (L : LieSubalgebra ℝ (Matrix κ κ ℝ))
    (hgen : ∀ J : ComplexStructure ι,traceFree (ρ J.matrix*ρ J.matrix) ∈ L)
    (R : Matrix ι ι ℝ) (hR : Rᵀ = -R) (J : ComplexStructure ι) :
    ⁅ρ R,traceFree (ρ J.matrix*ρ J.matrix)⁆ ∈ L := by
  let c := ρ.toContinuousLinearMap
  have hc : HasDerivAt (fun t => ρ (J.rotate R hR t).matrix)
      (ρ (R*J.matrix-J.matrix*R)) 0 :=
    c.hasFDerivAt.comp_hasDerivAt 0 (J.rotate_hasDerivAt_zero R hR)
  have hs := hc.mul hc
  simp only [J.rotate_zero] at hs
  let tf := (traceFree (𝕜 := ℝ) (ι := κ)).toContinuousLinearMap
  have ht := tf.hasFDerivAt.comp_hasDerivAt 0 hs
  have hval : traceFree (ρ (R*J.matrix-J.matrix*R)*ρ J.matrix+
      ρ J.matrix*ρ (R*J.matrix-J.matrix*R)) =
      -(ρ R*traceFree (ρ J.matrix*ρ J.matrix)-traceFree (ρ J.matrix*ρ J.matrix)*ρ R) := by
    rw [hρ]
    have he : (ρ J.matrix*ρ R-ρ R*ρ J.matrix)*ρ J.matrix+
        ρ J.matrix*(ρ J.matrix*ρ R-ρ R*ρ J.matrix) =
        (ρ J.matrix*ρ J.matrix)*ρ R-ρ R*(ρ J.matrix*ρ J.matrix) := by noncomm_ring
    rw [he,traceFree_commutator,commutator_traceFree]
    noncomm_ring
  have hd : HasDerivAt (fun t => traceFree (ρ (J.rotate R hR t).matrix*
      ρ (J.rotate R hR t).matrix))
      (-(ρ R*traceFree (ρ J.matrix*ρ J.matrix)-traceFree (ρ J.matrix*ρ J.matrix)*ρ R)) 0 := by
    change HasDerivAt (fun t => traceFree (ρ (J.rotate R hR t).matrix*
      ρ (J.rotate R hR t).matrix)) _ 0 at ht
    change HasDerivAt _ (traceFree (ρ (R*J.matrix-J.matrix*R)*ρ J.matrix+
      ρ J.matrix*ρ (R*J.matrix-J.matrix*R))) 0 at ht
    rw [hval] at ht
    exact ht
  have hm := derivative_mem_submodule L.toSubmodule L.toSubmodule.closed_of_finiteDimensional hd
    (fun t => hgen (J.rotate R hR t))
  change ρ R*traceFree (ρ J.matrix*ρ J.matrix)-traceFree (ρ J.matrix*ρ J.matrix)*ρ R ∈ L
  have hn := L.neg_mem hm
  change -(-(ρ R*traceFree (ρ J.matrix*ρ J.matrix)-traceFree (ρ J.matrix*ρ J.matrix)*ρ R)) ∈ L at hn
  simpa only [neg_neg] using hn

/-- Normalizer membership on generators propagates through the genuine Lie
span by Jacobi. This is the closure step needed for torus weight filtering. -/
lemma normalizer_lieSpan {𝕜 A : Type*} [Field 𝕜] [LieRing A] [LieAlgebra 𝕜 A]
    (s : Set A) (z : A)
    (hz : ∀ x ∈ s,⁅z,x⁆ ∈ LieSubalgebra.lieSpan 𝕜 A s) :
    ∀ x ∈ LieSubalgebra.lieSpan 𝕜 A s,⁅z,x⁆ ∈ LieSubalgebra.lieSpan 𝕜 A s := by
  intro x hx
  induction hx using LieSubalgebra.lieSpan_induction with
  | mem x hx => exact hz x hx
  | zero => simp
  | add x y hx hy ihx ihy =>
    simpa only [lie_add] using (LieSubalgebra.lieSpan 𝕜 A s).add_mem ihx ihy
  | smul a x hx ih =>
    simpa only [lie_smul] using (LieSubalgebra.lieSpan 𝕜 A s).smul_mem a ih
  | lie x y hx hy ihx ihy =>
    rw [leibniz_lie]
    exact (LieSubalgebra.lieSpan 𝕜 A s).add_mem
      ((LieSubalgebra.lieSpan 𝕜 A s).lie_mem ihx hy)
      ((LieSubalgebra.lieSpan 𝕜 A s).lie_mem hx ihy)

end

open Matrix HarmonicCounterexample.Berger
open scoped Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
lemma traceFree_commutator_complex (A B : Matrix κ κ ℂ) :
    traceFree (A*B-B*A) = A*B-B*A := by
  simp only [traceFree,LinearMap.coe_mk,AddHom.coe_mk,trace_sub]
  rw [trace_mul_comm A B,sub_self,zero_div,zero_smul,sub_zero]

lemma commutator_traceFree_complex (A B : Matrix κ κ ℂ) :
    A*traceFree B-traceFree B*A = A*B-B*A := by
  simp only [traceFree,LinearMap.coe_mk,AddHom.coe_mk,mul_sub,sub_mul,
    mul_smul_comm,smul_mul_assoc,mul_one,one_mul]
  abel

/-- The actual rotation curve makes every skew angular field an infinitesimal
normalizer of the squared-complex-structure generators. The anti-representation
hypothesis is an ordinary algebraic compatibility, proved for actual polynomial
fields in `linearField_bracket`; no Lie-generation conclusion is assumed. -/
lemma square_generator_normalizer_complex
    (ρ : Matrix ι ι ℝ →ₗ[ℝ] Matrix κ κ ℂ)
    (hρ : ∀ M N,ρ (M*N-N*M) = ρ N*ρ M-ρ M*ρ N)
    (L : LieSubalgebra ℂ (Matrix κ κ ℂ))
    (hgen : ∀ J : ComplexStructure ι,traceFree (ρ J.matrix*ρ J.matrix) ∈ L)
    (R : Matrix ι ι ℝ) (hR : Rᵀ = -R) (J : ComplexStructure ι) :
    ⁅ρ R,traceFree (ρ J.matrix*ρ J.matrix)⁆ ∈ L := by
  let c := ρ.toContinuousLinearMap
  have hc : HasDerivAt (fun t => ρ (J.rotate R hR t).matrix)
      (ρ (R*J.matrix-J.matrix*R)) 0 :=
    c.hasFDerivAt.comp_hasDerivAt 0 (J.rotate_hasDerivAt_zero R hR)
  have hs := hc.mul hc
  simp only [J.rotate_zero] at hs
  let tf := ((traceFree (𝕜 := ℂ) (ι := κ)).restrictScalars ℝ).toContinuousLinearMap
  have ht := tf.hasFDerivAt.comp_hasDerivAt 0 hs
  have hval : traceFree (ρ (R*J.matrix-J.matrix*R)*ρ J.matrix+
      ρ J.matrix*ρ (R*J.matrix-J.matrix*R)) =
      -(ρ R*traceFree (ρ J.matrix*ρ J.matrix)-traceFree (ρ J.matrix*ρ J.matrix)*ρ R) := by
    rw [hρ]
    have he : (ρ J.matrix*ρ R-ρ R*ρ J.matrix)*ρ J.matrix+
        ρ J.matrix*(ρ J.matrix*ρ R-ρ R*ρ J.matrix) =
        (ρ J.matrix*ρ J.matrix)*ρ R-ρ R*(ρ J.matrix*ρ J.matrix) := by noncomm_ring
    rw [he,traceFree_commutator_complex,commutator_traceFree_complex]
    noncomm_ring
  have hd : HasDerivAt (fun t => traceFree (ρ (J.rotate R hR t).matrix*
      ρ (J.rotate R hR t).matrix))
      (-(ρ R*traceFree (ρ J.matrix*ρ J.matrix)-traceFree (ρ J.matrix*ρ J.matrix)*ρ R)) 0 := by
    change HasDerivAt (fun t => traceFree (ρ (J.rotate R hR t).matrix*
      ρ (J.rotate R hR t).matrix)) _ 0 at ht
    change HasDerivAt _ (traceFree (ρ (R*J.matrix-J.matrix*R)*ρ J.matrix+
      ρ J.matrix*ρ (R*J.matrix-J.matrix*R))) 0 at ht
    rw [hval] at ht
    exact ht
  have hm := derivative_mem_submodule (L.toSubmodule.restrictScalars ℝ)
    (L.toSubmodule.restrictScalars ℝ).closed_of_finiteDimensional hd
    (fun t => hgen (J.rotate R hR t))
  change ρ R*traceFree (ρ J.matrix*ρ J.matrix)-traceFree (ρ J.matrix*ρ J.matrix)*ρ R ∈ L
  have hn := L.neg_mem hm
  change -(-(ρ R*traceFree (ρ J.matrix*ρ J.matrix)-traceFree (ρ J.matrix*ρ J.matrix)*ρ R)) ∈ L at hn
  simpa only [neg_neg] using hn

end HarmonicCounterexample.Control

namespace HarmonicCounterexample.Berger.ComplexStructure
open Matrix
variable {s : ℕ}

/-- The manuscript's explicit three-plane complex structure: the disjoint
coordinate swaps turn the standard pairs into (X_i,X_j), (Y_i,X_k), (Y_j,Y_k).
It is an ACTUAL orthogonal complex structure, with no matrix equations assumed. -/
def triple (i j k : Fin s) : ComplexStructure (Fin s ⊕ Fin s) :=
  (block s).reindex ((Equiv.swap (Sum.inr i) (Sum.inl j)).trans
    (Equiv.swap (Sum.inr j) (Sum.inl k)))

def coordinateSign : Fin s ⊕ Fin s → ℂ := Sum.elim (fun _ => 1) (fun _ => -1)
def coordinatePlane : Fin s ⊕ Fin s → Fin s := Sum.elim id id

def signedIndex (i : Fin s) (ε : Bool) : Fin s ⊕ Fin s := if ε then .inl i else .inr i

/-- Pullback matrix in the independent complex coordinates x_i ± i y_i.
This is the exact substitution x=(z+zbar)/2, y=(z-zbar)/(2i), not a spectral
model replacing the real vector field. -/
def splitMatrix (J : ComplexStructure (Fin s ⊕ Fin s)) :
    Matrix (Fin s ⊕ Fin s) (Fin s ⊕ Fin s) ℂ := fun a b =>
  (1/2:ℂ)*((J.matrix (.inl (coordinatePlane a)) (.inl (coordinatePlane b)):ℂ)
    -coordinateSign b*Complex.I*(J.matrix (.inl (coordinatePlane a)) (.inr (coordinatePlane b)):ℂ)
    +coordinateSign a*Complex.I*(J.matrix (.inr (coordinatePlane a)) (.inl (coordinatePlane b)):ℂ)
    +coordinateSign a*coordinateSign b*(J.matrix (.inr (coordinatePlane a)) (.inr (coordinatePlane b)):ℂ))

lemma triple_split_ij (i j k : Fin s) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (ε β : Bool) : splitMatrix (triple i j k) (signedIndex i ε) (signedIndex j β) = -1/2 := by
  cases ε <;> cases β <;>
    norm_num [splitMatrix,triple,reindex,block,signedIndex,coordinatePlane,coordinateSign,
      Equiv.swap_apply_def,Matrix.submatrix,Matrix.one_apply,
      Sum.inl_ne_inr,Sum.inr_ne_inl,Sum.inl.injEq,Sum.inr.injEq,
      hij,hik,hjk,hij.symm,hik.symm,hjk.symm]

lemma triple_split_ik (i j k : Fin s) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (ε γ : Bool) : splitMatrix (triple i j k) (signedIndex i ε) (signedIndex k γ) =
      -Complex.I*coordinateSign (signedIndex i ε)/2 := by
  cases ε <;> cases γ <;>
    norm_num [splitMatrix,triple,reindex,block,signedIndex,coordinatePlane,coordinateSign,
      Equiv.swap_apply_def,Matrix.submatrix,Matrix.one_apply,
      Sum.inl_ne_inr,Sum.inr_ne_inl,Sum.inl.injEq,Sum.inr.injEq,
      hij,hik,hjk,hij.symm,hik.symm,hjk.symm] <;> ring

lemma triple_split_ji (i j k : Fin s) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (ε β : Bool) : splitMatrix (triple i j k) (signedIndex j β) (signedIndex i ε) = 1/2 := by
  cases ε <;> cases β <;>
    norm_num [splitMatrix,triple,reindex,block,signedIndex,coordinatePlane,coordinateSign,
      Equiv.swap_apply_def,Matrix.submatrix,Matrix.one_apply,
      Sum.inl_ne_inr,Sum.inr_ne_inl,Sum.inl.injEq,Sum.inr.injEq,
      hij,hik,hjk,hij.symm,hik.symm,hjk.symm]

lemma triple_split_ki (i j k : Fin s) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (ε γ : Bool) : splitMatrix (triple i j k) (signedIndex k γ) (signedIndex i ε) =
      -Complex.I*coordinateSign (signedIndex i ε)/2 := by
  cases ε <;> cases γ <;>
    norm_num [splitMatrix,triple,reindex,block,signedIndex,coordinatePlane,coordinateSign,
      Equiv.swap_apply_def,Matrix.submatrix,Matrix.one_apply,
      Sum.inl_ne_inr,Sum.inr_ne_inl,Sum.inl.injEq,Sum.inr.injEq,
      hij,hik,hjk,hij.symm,hik.symm,hjk.symm] <;> ring

/-- Complexification of the actual real coordinate matrix. -/
def complexMatrix (J : ComplexStructure (Fin s ⊕ Fin s)) :
    Matrix (Fin s ⊕ Fin s) (Fin s ⊕ Fin s) ℂ := J.matrix.map Complex.ofReal

def splitChange (s : ℕ) : Matrix (Fin s ⊕ Fin s) (Fin s ⊕ Fin s) ℂ :=
  fromBlocks 1 (Complex.I • 1) 1 (-Complex.I • 1)

def unsplitChange (s : ℕ) : Matrix (Fin s ⊕ Fin s) (Fin s ⊕ Fin s) ℂ :=
  (1/2:ℂ) • fromBlocks 1 1 (-Complex.I • 1) (Complex.I • 1)

lemma split_unsplit (s : ℕ) : splitChange s*unsplitChange s = 1 := by
  simp only [splitChange,unsplitChange,mul_smul_comm,fromBlocks_multiply,
    mul_one,mul_smul_comm,smul_smul]
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    by_cases hab : a = b <;> norm_num [Matrix.ofNat_apply,Matrix.one_apply,hab, Sum.inl_ne_inr, Sum.inr_ne_inl]

lemma unsplit_split (s : ℕ) : unsplitChange s*splitChange s = 1 := by
  simp only [splitChange,unsplitChange,smul_mul_assoc,fromBlocks_multiply,
    mul_one,smul_mul_assoc,mul_smul_comm,smul_smul]
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    by_cases hab : a = b <;> norm_num [Matrix.ofNat_apply,Matrix.one_apply,hab, Sum.inl_ne_inr, Sum.inr_ne_inl]

lemma splitMatrix_eq (J : ComplexStructure (Fin s ⊕ Fin s)) :
    splitMatrix J = splitChange s*complexMatrix J*unsplitChange s := by
  ext a b
  rcases a with a | a <;> rcases b with b | b
  all_goals
    simp [splitMatrix,splitChange,unsplitChange,complexMatrix,coordinatePlane,coordinateSign,
      Matrix.mul_apply,Fintype.sum_sum_type,Matrix.one_apply]
  all_goals ring_nf; simp only [Complex.I_sq]; ring

lemma splitMatrix_square (J : ComplexStructure (Fin s ⊕ Fin s)) :
    splitMatrix J*splitMatrix J = -1 := by
  have hj : complexMatrix J*complexMatrix J = -1 := by
    have h := congrArg (Complex.ofRealHom.mapMatrix : Matrix (Fin s ⊕ Fin s) (Fin s ⊕ Fin s) ℝ →+* Matrix (Fin s ⊕ Fin s) (Fin s ⊕ Fin s) ℂ) J.square
    rw [map_mul,map_neg,map_one] at h
    change complexMatrix J*complexMatrix J = -1 at h
    exact h
  rw [splitMatrix_eq]
  calc
    (splitChange s*complexMatrix J*unsplitChange s)*
        (splitChange s*complexMatrix J*unsplitChange s) =
        splitChange s*(complexMatrix J*complexMatrix J)*unsplitChange s := by
      simp only [mul_assoc,← mul_assoc (unsplitChange s) (splitChange s),unsplit_split,one_mul]
    _ = -1 := by rw [hj,mul_neg,mul_one,neg_mul,split_unsplit]

def torusMatrix (r : Fin s → ℝ) : Matrix (Fin s ⊕ Fin s) (Fin s ⊕ Fin s) ℝ :=
  fromBlocks 0 (-(diagonal r)) (diagonal r) 0

lemma torusMatrix_skew (r : Fin s → ℝ) : (torusMatrix r)ᵀ = -torusMatrix r := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    by_cases hab : a = b <;> simp [torusMatrix,Matrix.transpose_apply,hab,eq_comm]

lemma torusMatrix_square (r : Fin s → ℝ) (hr : ∀ i,r i*r i = 1) :
    torusMatrix r*torusMatrix r = -1 := by
  have hd : diagonal r*diagonal r = 1 := by
    rw [diagonal_mul_diagonal]
    simp only [hr,diagonal_one]
  simp only [torusMatrix,fromBlocks_multiply,zero_mul,mul_zero,zero_add,add_zero,
    neg_mul,mul_neg,hd]
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> simp [Matrix.one_apply]

def signedStructure (r : Fin s → ℝ) (hr : ∀ i,r i*r i = 1) :
    ComplexStructure (Fin s ⊕ Fin s) where
  matrix := torusMatrix r
  square := torusMatrix_square r hr
  orthogonal := by rw [torusMatrix_skew,neg_mul,torusMatrix_square r hr,neg_neg]

/-- Real-linear transformation of any actual coordinate field into the source's
independent complex z/bar-z coordinates. -/
def splitFieldMatrix : Matrix (Fin s ⊕ Fin s) (Fin s ⊕ Fin s) ℝ →ₗ[ℝ]
    Matrix (Fin s ⊕ Fin s) (Fin s ⊕ Fin s) ℂ where
  toFun M := splitChange s*M.map Complex.ofReal*unsplitChange s
  map_add' M N := by
    simp only [Matrix.map_add _ Complex.ofReal_add,mul_add,add_mul]
  map_smul' r M := by
    have he : (r • M).map Complex.ofReal = r • M.map Complex.ofReal := by ext i j; simp
    rw [he,mul_smul_comm,smul_mul_assoc]
    rfl

lemma splitFieldMatrix_complex (J : ComplexStructure (Fin s ⊕ Fin s)) :
    splitFieldMatrix J.matrix = splitMatrix J := (splitMatrix_eq J).symm

lemma splitFieldMatrix_mul (M N : Matrix (Fin s ⊕ Fin s) (Fin s ⊕ Fin s) ℝ) :
    splitFieldMatrix (M*N) = splitFieldMatrix M*splitFieldMatrix N := by
  have hf : (M*N).map Complex.ofReal = M.map Complex.ofReal*N.map Complex.ofReal := by
    exact (Complex.ofRealHom.mapMatrix : Matrix (Fin s ⊕ Fin s) (Fin s ⊕ Fin s) ℝ →+*
      Matrix (Fin s ⊕ Fin s) (Fin s ⊕ Fin s) ℂ).map_mul M N
  change splitChange s*(M*N).map Complex.ofReal*unsplitChange s =
    (splitChange s*M.map Complex.ofReal*unsplitChange s)*
    (splitChange s*N.map Complex.ofReal*unsplitChange s)
  rw [hf]
  simp only [mul_assoc,← mul_assoc (unsplitChange s) (splitChange s),unsplit_split,one_mul]

lemma splitFieldMatrix_torus (r : Fin s → ℝ) :
    splitFieldMatrix (torusMatrix r) =
      diagonal (fun a => Complex.I*coordinateSign a*(r (coordinatePlane a):ℂ)) := by
  ext a b
  rcases a with a | a <;> rcases b with b | b
  all_goals
    change (splitChange s*(torusMatrix r).map Complex.ofReal*unsplitChange s) _ _ = _
    simp [splitChange,unsplitChange,torusMatrix,Matrix.mul_apply,Fintype.sum_sum_type,
      Matrix.one_apply,diagonal_apply,coordinateSign,coordinatePlane]
  all_goals by_cases hab : a = b <;> simp [hab]
  all_goals ring_nf

end HarmonicCounterexample.Berger.ComplexStructure

open Matrix
open scoped BigOperators
open scoped Topology
open Filter
open Matrix
open scoped BigOperators
open Matrix MvPolynomial

namespace HarmonicCounterexample.Control
variable {𝕜 ι : Type*} [CommRing 𝕜] [Fintype ι] [DecidableEq ι]

/-- The actual infinitesimal linear coordinate motion, specified on generators. -/
def linearField (M : Matrix ι ι 𝕜) : Derivation 𝕜 (MvPolynomial ι 𝕜) (MvPolynomial ι 𝕜) :=
  MvPolynomial.mkDerivation 𝕜 (fun i => ∑ j : ι,M i j • X j)

omit [DecidableEq ι] in
lemma linearField_X (M : Matrix ι ι 𝕜) (i : ι) :
    linearField M (X i) = ∑ j : ι,M i j • X j := mkDerivation_X _ _ _

omit [DecidableEq ι] in
lemma linearField_add (M N : Matrix ι ι 𝕜) : linearField (M+N) = linearField M+linearField N := by
  apply MvPolynomial.derivation_ext
  intro i
  simp [linearField_X,add_smul,Finset.sum_add_distrib]

omit [DecidableEq ι] in
lemma linearField_smul (c : 𝕜) (M : Matrix ι ι 𝕜) : linearField (c • M) = c • linearField M := by
  apply MvPolynomial.derivation_ext
  intro i
  simp [linearField_X,smul_smul,Finset.smul_sum]

omit [DecidableEq ι] in
/-- Exact anti-representation identity for coordinate vector fields.
The sign is important: fields act on functions by pullback. -/
lemma linearField_bracket (M N : Matrix ι ι 𝕜) :
    ⁅linearField M,linearField N⁆ = linearField (N*M-M*N) := by
  apply MvPolynomial.derivation_ext
  intro i
  simp only [Derivation.commutator_apply,linearField_X,map_sum,Derivation.map_smul,
    Matrix.sub_apply,Matrix.mul_apply,Finset.sum_sub_distrib,sub_smul,Finset.smul_sum,
    Finset.sum_smul,smul_smul]
  congr 1 <;> exact Finset.sum_comm

omit [Fintype ι] [DecidableEq ι] in
lemma derivation_sum_apply {κ : Type*} (s : Finset κ)
    (f : κ → Derivation 𝕜 (MvPolynomial ι 𝕜) (MvPolynomial ι 𝕜)) (P : MvPolynomial ι 𝕜) :
    (∑ i ∈ s,f i) P = ∑ i ∈ s,f i P := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi,Derivation.add_apply,ih]

lemma linearField_apply (M : Matrix ι ι 𝕜) (P : MvPolynomial ι 𝕜) :
    linearField M P = ∑ i : ι,∑ j : ι,M i j • (X j*pderiv i P) := by
  have h : linearField M = ∑ i : ι,(∑ j : ι,M i j • (X j : MvPolynomial ι 𝕜)) • pderiv i := by
    apply MvPolynomial.derivation_ext
    intro k
    simp [linearField_X,Derivation.smul_apply,Pi.single_apply]
  rw [h]
  simp [Derivation.smul_apply,Finset.sum_mul]

def linearFieldMap : Matrix ι ι 𝕜 →ₗ[𝕜] Module.End 𝕜 (MvPolynomial ι 𝕜) where
  toFun M := (linearField M).toLinearMap
  map_add' M N := by rw [linearField_add]; rfl
  map_smul' c M := by rw [linearField_smul]; rfl

end HarmonicCounterexample.Control

end

section
open Matrix
open scoped BigOperators
open scoped Topology
open Filter
open Matrix
open scoped BigOperators
open Matrix MvPolynomial

namespace HarmonicCounterexample.Control

section
open scoped BigOperators
open Matrix MvPolynomial Finsupp
variable {𝕜 ι : Type*} [Field 𝕜] [Fintype ι] [DecidableEq ι]

lemma linearField_diagonal_monomial (d : ι → 𝕜) (ν : ι →₀ ℕ) (c : 𝕜) :
    linearField (diagonal d) (monomial ν c) = (∑ i : ι,d i*(ν i:𝕜)) • monomial ν c := by
  rw [linearField_apply]
  simp only [diagonal_apply,ite_smul,zero_smul,Finset.sum_ite_eq,Finset.mem_univ,ite_true,
    X_mul_pderiv_monomial,← Nat.cast_smul_eq_nsmul 𝕜,smul_smul,Finset.sum_smul]

lemma linearField_square_first (M : Matrix ι ι 𝕜) (P : MvPolynomial ι 𝕜) :
    (∑ i : ι,∑ j : ι,M i j • (linearField M (X j)*pderiv i P)) = linearField (M*M) P := by
  rw [linearField_apply]
  simp only [linearField_X,Matrix.mul_apply,Finset.sum_smul,Finset.sum_mul,Finset.smul_sum,
    smul_mul_assoc,smul_smul]
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_comm

/-- Exact second-order formula: there is no implicit harmonic projection and
no omitted first-order term. -/
lemma linearField_square (M : Matrix ι ι 𝕜) (P : MvPolynomial ι 𝕜) :
    linearField M (linearField M P) = linearField (M*M) P+
      ∑ i : ι,∑ j : ι,M i j • (X j*linearField M (pderiv i P)) := by
  have hleib (A B : MvPolynomial ι 𝕜) : linearField M (A*B) =
      linearField M A*B+A*linearField M B := by
    simpa only [smul_eq_mul,mul_comm,add_comm] using (linearField M).leibniz A B
  conv_lhs => rw [linearField_apply M P]
  simp only [map_sum,Derivation.map_smul,hleib,smul_add,Finset.sum_add_distrib]
  rw [linearField_square_first]

lemma linearField_neg_one (P : MvPolynomial ι 𝕜) {l : ℕ} (hP : P.IsHomogeneous l) :
    linearField (-1 : Matrix ι ι 𝕜) P = -(l:𝕜) • P := by
  have he : (-1 : Matrix ι ι 𝕜) = diagonal (fun _ => -1) := by ext i j; by_cases h : i = j <;> simp [h]
  rw [he,linearField_apply]
  simp only [diagonal_apply,ite_smul,zero_smul,Finset.sum_ite_eq,Finset.mem_univ,ite_true,
    neg_one_smul,Finset.sum_neg_distrib]
  rw [hP.sum_X_mul_pderiv]
  simp only [← Nat.cast_smul_eq_nsmul 𝕜,neg_smul]

lemma linearField_square_complex (M : Matrix ι ι 𝕜) (hM : M*M = -1)
    (P : MvPolynomial ι 𝕜) {l : ℕ} (hP : P.IsHomogeneous l) :
    linearField M (linearField M P) = -(l:𝕜) • P+
      ∑ i : ι,∑ j : ι,M i j • (X j*linearField M (pderiv i P)) := by
  rw [linearField_square,hM,linearField_neg_one P hP]

abbrev MonomialIndex (ι : Type*) (l : ℕ) := {d : ι →₀ ℕ // d.degree = l}

instance monomialIndexFintype (l : ℕ) : Fintype (MonomialIndex ι l) := by
  let e : MonomialIndex ι l ≃ ↥((Finset.univ : Finset ι).finsuppAntidiag l) :=
    { toFun := fun d => ⟨d.1, by
        have h : d.1.degree = ∑ i : ι,d.1 i := Finsupp.sum_fintype d.1 (fun _ a => a) (fun _ => rfl)
        exact Finset.mem_finsuppAntidiag.2 ⟨h.symm.trans d.2,Finset.subset_univ _⟩⟩
      invFun := fun d => ⟨d.1,by
        have h : d.1.degree = ∑ i : ι,d.1 i := Finsupp.sum_fintype d.1 (fun _ a => a) (fun _ => rfl)
        exact h.trans (Finset.mem_finsuppAntidiag.1 d.2).1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Fintype.ofEquiv _ e.symm

/-- Actual coefficient coordinates on homogeneous polynomials. -/
def homogeneousCoords (l : ℕ) :
    homogeneousSubmodule ι 𝕜 l ≃ₗ[𝕜] MonomialIndex ι l →₀ 𝕜 :=
  (LinearEquiv.ofEq _ _ (homogeneousSubmodule_eq_finsupp_supported ι 𝕜 l)).trans
    (AddMonoidAlgebra.supportedEquivFinsupp (R := 𝕜) (S := 𝕜) {d : ι →₀ ℕ | d.degree = l})

def homogeneousBasis (l : ℕ) : Module.Basis (MonomialIndex ι l) 𝕜 (homogeneousSubmodule ι 𝕜 l) :=
  Finsupp.basisSingleOne.map (homogeneousCoords l).symm

omit [Fintype ι] [DecidableEq ι] in
lemma homogeneousCoords_apply (l : ℕ) (P : homogeneousSubmodule ι 𝕜 l) (d : MonomialIndex ι l) :
    homogeneousCoords l P d = P.1.coeff d.1 := rfl

omit [Fintype ι] [DecidableEq ι] in
lemma homogeneousBasis_repr (l : ℕ) (P : homogeneousSubmodule ι 𝕜 l) (d : MonomialIndex ι l) :
    (homogeneousBasis l).repr P d = P.1.coeff d.1 := rfl

omit [Fintype ι] in
lemma homogeneousBasis_val (l : ℕ) (d : MonomialIndex ι l) :
    ((homogeneousBasis (𝕜 := 𝕜) l) d).1 = monomial d.1 1 := by
  apply MvPolynomial.ext
  intro e
  by_cases he : e.degree = l
  · have h := (homogeneousBasis (𝕜 := 𝕜) l).repr_self d
    have h' := DFunLike.congr_fun h ⟨e,he⟩
    change ((homogeneousBasis (𝕜 := 𝕜) l) d).1.coeff e = (Finsupp.single d (1:𝕜)) ⟨e,he⟩ at h'
    simpa only [Finsupp.single_apply,Subtype.ext_iff,coeff_monomial] using h'
  · have hP := ((homogeneousBasis (𝕜 := 𝕜) l) d).property
    have hzero := hP.coeff_eq_zero he
    have hne : d.1 ≠ e := fun hd => he (hd ▸ d.2)
    simp [hzero,coeff_monomial,hne]

lemma linearField_homogeneous {P : MvPolynomial ι 𝕜} {l : ℕ}
    (hP : P.IsHomogeneous l) (M : Matrix ι ι 𝕜) : (linearField M P).IsHomogeneous l := by
  rw [linearField_apply]
  by_cases hl : l = 0
  · have hc : P = C (P.coeff 0) :=
      totalDegree_eq_zero_iff_eq_C.1 ((totalDegree_zero_iff_isHomogeneous ι).2 (hl ▸ hP))
    rw [hc]
    simp only [pderiv_C,mul_zero,smul_zero,Finset.sum_const_zero]
    exact isHomogeneous_zero ι 𝕜 l
  · apply IsHomogeneous.sum
    intro i _
    apply IsHomogeneous.sum
    intro j _
    apply (homogeneousSubmodule ι 𝕜 l).smul_mem
    have h := (isHomogeneous_X 𝕜 j).mul (hP.pderiv (i := i))
    have he : 1+(l-1) = l := by omega
    change (X j*pderiv i P).IsHomogeneous l
    simpa only [he] using h

def homogeneousField (l : ℕ) (M : Matrix ι ι 𝕜) :
    Module.End 𝕜 (homogeneousSubmodule ι 𝕜 l) where
  toFun P := ⟨linearField M P.1,linearField_homogeneous P.2 M⟩
  map_add' _P _Q := Subtype.ext (map_add _ _ _)
  map_smul' _a _P := Subtype.ext (Derivation.map_smul _ _ _)

lemma homogeneousField_bracket (l : ℕ) (M N : Matrix ι ι 𝕜) :
    homogeneousField l (M*N-N*M) = homogeneousField l N*homogeneousField l M-
      homogeneousField l M*homogeneousField l N := by
  apply LinearMap.ext
  intro P
  apply Subtype.ext
  have h := DFunLike.congr_fun (linearField_bracket N M) P.1
  exact h.symm

/-- An actual finite-dimensional representation, in the actual monomial basis. -/
def homogeneousFieldMap (l : ℕ) :
    Matrix ι ι 𝕜 →ₗ[𝕜] Module.End 𝕜 (homogeneousSubmodule ι 𝕜 l) where
  toFun := homogeneousField l
  map_add' M N := by
    apply LinearMap.ext
    intro P
    apply Subtype.ext
    exact DFunLike.congr_fun (linearField_add M N) P.1
  map_smul' a M := by
    apply LinearMap.ext
    intro P
    apply Subtype.ext
    exact DFunLike.congr_fun (linearField_smul a M) P.1

def homogeneousMatrix (l : ℕ) :
    Matrix ι ι 𝕜 →ₗ[𝕜] Matrix (MonomialIndex ι l) (MonomialIndex ι l) 𝕜 :=
  (LinearMap.toMatrix (homogeneousBasis l) (homogeneousBasis l)).toLinearMap.comp
    (homogeneousFieldMap l)

lemma homogeneousMatrix_apply (l : ℕ) (M : Matrix ι ι 𝕜) (μ ν : MonomialIndex ι l) :
    homogeneousMatrix l M μ ν = (linearField M (monomial ν.1 1)).coeff μ.1 := by
  change (LinearMap.toMatrix (homogeneousBasis l) (homogeneousBasis l) (homogeneousField l M)) μ ν = _
  rw [LinearMap.toMatrix_apply]
  rw [homogeneousBasis_repr]
  change (linearField M ((homogeneousBasis l) ν).1).coeff μ.1 = _
  rw [homogeneousBasis_val]

lemma homogeneousMatrix_square_apply (l : ℕ) (M : Matrix ι ι 𝕜) (μ ν : MonomialIndex ι l) :
    (homogeneousMatrix l M*homogeneousMatrix l M) μ ν =
      (linearField M (linearField M (monomial ν.1 1))).coeff μ.1 := by
  change ((LinearMap.toMatrix (homogeneousBasis l) (homogeneousBasis l)) (homogeneousField l M)*
    (LinearMap.toMatrix (homogeneousBasis l) (homogeneousBasis l)) (homogeneousField l M)) μ ν = _
  rw [← LinearMap.toMatrix_mul,LinearMap.toMatrix_apply,homogeneousBasis_repr]
  change (linearField M (linearField M ((homogeneousBasis l) ν).1)).coeff μ.1 = _
  rw [homogeneousBasis_val]

lemma homogeneousMatrix_bracket (l : ℕ) (M N : Matrix ι ι 𝕜) :
    homogeneousMatrix l (M*N-N*M) = homogeneousMatrix l N*homogeneousMatrix l M-
      homogeneousMatrix l M*homogeneousMatrix l N := by
  change (LinearMap.toMatrix (homogeneousBasis l) (homogeneousBasis l))
    (homogeneousField l (M*N-N*M)) = _
  rw [homogeneousField_bracket]
  calc
    _ = (LinearMap.toMatrix (homogeneousBasis l) (homogeneousBasis l))
        (homogeneousField l N*homogeneousField l M)-
      (LinearMap.toMatrix (homogeneousBasis l) (homogeneousBasis l))
        (homogeneousField l M*homogeneousField l N) :=
      map_sub (LinearMap.toMatrix (homogeneousBasis l) (homogeneousBasis l)) _ _
    _ = _ := by rw [LinearMap.toMatrix_mul,LinearMap.toMatrix_mul]; rfl

lemma homogeneousMatrix_diagonal (l : ℕ) (d : ι → 𝕜) :
    homogeneousMatrix l (diagonal d) = diagonal (fun ν : MonomialIndex ι l => ∑ i,d i*(ν.1 i:𝕜)) := by
  ext μ ν
  rw [homogeneousMatrix_apply,linearField_diagonal_monomial,coeff_smul,coeff_monomial]
  by_cases h : μ = ν
  · subst μ; simp
  · have hn : ν.1 ≠ μ.1 := fun he => h (Subtype.ext he.symm)
    simp [h,hn]

end

open Matrix MvPolynomial HarmonicCounterexample.Berger
open HarmonicCounterexample.Berger.ComplexStructure
open scoped BigOperators
variable {s : ℕ}

def angularRepresentation (l : ℕ) :
    Matrix (Fin s ⊕ Fin s) (Fin s ⊕ Fin s) ℝ →ₗ[ℝ]
      Matrix (MonomialIndex (Fin s ⊕ Fin s) l) (MonomialIndex (Fin s ⊕ Fin s) l) ℂ :=
  ((homogeneousMatrix l).restrictScalars ℝ).comp splitFieldMatrix

lemma angularRepresentation_bracket (l : ℕ)
    (M N : Matrix (Fin s ⊕ Fin s) (Fin s ⊕ Fin s) ℝ) :
    angularRepresentation l (M*N-N*M) =
      angularRepresentation l N*angularRepresentation l M-
      angularRepresentation l M*angularRepresentation l N := by
  change homogeneousMatrix l (splitFieldMatrix (M*N-N*M)) = _
  rw [map_sub,splitFieldMatrix_mul,splitFieldMatrix_mul,homogeneousMatrix_bracket]
  rfl

def monomialWeight (ν : Fin s ⊕ Fin s →₀ ℕ) (i : Fin s) : ℂ :=
  (ν (.inl i):ℂ)-ν (.inr i)

lemma angularRepresentation_torus (l : ℕ) (r : Fin s → ℝ) :
    angularRepresentation l (torusMatrix r) = diagonal
      (fun ν : MonomialIndex (Fin s ⊕ Fin s) l =>
        Complex.I*∑ i : Fin s,(r i:ℂ)*monomialWeight ν.1 i) := by
  change homogeneousMatrix l (splitFieldMatrix (torusMatrix r)) = _
  rw [splitFieldMatrix_torus,homogeneousMatrix_diagonal]
  congr 1
  funext ν
  simp only [Fintype.sum_sum_type,coordinateSign,coordinatePlane,Sum.elim_inl,Sum.elim_inr,
    monomialWeight,mul_sub,Finset.sum_sub_distrib,Finset.mul_sum,id_eq]
  rw [← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma angularRepresentation_plane (l : ℕ) (i : Fin s) :
    angularRepresentation l (torusMatrix (Pi.single i 1)) =
      diagonal (fun ν : MonomialIndex (Fin s ⊕ Fin s) l => Complex.I*monomialWeight ν.1 i) := by
  rw [angularRepresentation_torus]
  congr 1
  funext ν
  congr 1
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

end HarmonicCounterexample.Control

end

open Matrix
open scoped BigOperators
open scoped Topology
open Filter
open Matrix
open scoped BigOperators
open Matrix MvPolynomial

namespace HarmonicCounterexample.Control
open Matrix MvPolynomial HarmonicCounterexample.Berger
open HarmonicCounterexample.Berger.ComplexStructure
open scoped BigOperators
attribute [local instance 100] LieRing.ofAssociativeRing
variable {s : ℕ}

/-- The actual squared-complex-structure Lie algebra on homogeneous
polynomials; the restriction to harmonic polynomials is taken later. -/
def angularLie (l : ℕ) : LieSubalgebra ℂ
    (Matrix (MonomialIndex (Fin s ⊕ Fin s) l) (MonomialIndex (Fin s ⊕ Fin s) l) ℂ) :=
  LieSubalgebra.lieSpan ℂ _ (Set.range fun J : ComplexStructure (Fin s ⊕ Fin s) =>
    traceFree (angularRepresentation l J.matrix*angularRepresentation l J.matrix))

lemma angularLie_generator (l : ℕ) (J : ComplexStructure (Fin s ⊕ Fin s)) :
    traceFree (angularRepresentation l J.matrix*angularRepresentation l J.matrix) ∈ angularLie l :=
  LieSubalgebra.subset_lieSpan (Set.mem_range_self J)

lemma angularLie_normalizer (l : ℕ)
    (R : Matrix (Fin s ⊕ Fin s) (Fin s ⊕ Fin s) ℝ) (hR : Rᵀ = -R)
    (X : Matrix (MonomialIndex (Fin s ⊕ Fin s) l) (MonomialIndex (Fin s ⊕ Fin s) l) ℂ)
    (hX : X ∈ angularLie l) : ⁅angularRepresentation l R,X⁆ ∈ angularLie l := by
  apply normalizer_lieSpan _ (angularRepresentation l R) ?_ X hX
  rintro _ ⟨J,rfl⟩
  exact square_generator_normalizer_complex (angularRepresentation l)
    (angularRepresentation_bracket l) (angularLie l) (angularLie_generator l) R hR J

lemma angularLie_weight_normalizer (l : ℕ) (i : Fin s)
    (X : Matrix (MonomialIndex (Fin s ⊕ Fin s) l) (MonomialIndex (Fin s ⊕ Fin s) l) ℂ)
    (hX : X ∈ angularLie l) :
    ⁅diagonal (fun ν : MonomialIndex (Fin s ⊕ Fin s) l => monomialWeight ν.1 i),X⁆ ∈ angularLie l := by
  have h := angularLie_normalizer l (torusMatrix (Pi.single i 1))
    (torusMatrix_skew _) X hX
  have ht := (angularLie l).smul_mem (-Complex.I) h
  rw [← smul_lie,angularRepresentation_plane] at ht
  have hd : (-Complex.I) • diagonal (fun ν : MonomialIndex (Fin s ⊕ Fin s) l =>
      Complex.I*monomialWeight ν.1 i) =
      diagonal (fun ν : MonomialIndex (Fin s ⊕ Fin s) l => monomialWeight ν.1 i) := by
    ext μ ν
    by_cases hμ : μ = ν <;> simp [hμ,← mul_assoc]
  rwa [hd] at ht

/-- The torus field is real-linear in its plane velocities. -/
def torusRepresentation (l : ℕ) : (Fin s → ℝ) →ₗ[ℝ]
    Matrix (MonomialIndex (Fin s ⊕ Fin s) l) (MonomialIndex (Fin s ⊕ Fin s) l) ℂ where
  toFun r := angularRepresentation l (torusMatrix r)
  map_add' r q := by
    have ht : torusMatrix (r+q) = torusMatrix r+torusMatrix q := by
      ext a b
      rcases a with a | a <;> rcases b with b | b <;>
        by_cases hab : a = b <;> simp [torusMatrix,hab,add_comm]
    rw [ht,map_add]
  map_smul' c r := by
    have ht : torusMatrix (c • r) = c • torusMatrix r := by
      ext a b
      rcases a with a | a <;> rcases b with b | b <;>
        by_cases hab : a = b <;> simp [torusMatrix,hab]
    rw [ht,map_smul]
    rfl

lemma torusRepresentation_flip (l : ℕ) (r q : Fin s → ℝ) :
    torusRepresentation l (r-(2:ℝ) • q) = torusRepresentation l r-2*torusRepresentation l q := by
  rw [map_sub,map_smul,two_smul ℝ,two_mul]

lemma angularLie_mixed_torus (l : ℕ) (i j : Fin s) (hij : i ≠ j) :
    traceFree (torusRepresentation l (Pi.single i 1)*torusRepresentation l (Pi.single j 1)) ∈
      angularLie l := by
  let r : Fin s → ℝ := fun _ => 1
  let p : Fin s → ℝ := Pi.single i 1
  let q : Fin s → ℝ := Pi.single j 1
  have hr : ∀ a,r a*r a = 1 := by intro a; simp [r]
  have hp : ∀ a,(r-(2:ℝ) • p) a*(r-(2:ℝ) • p) a = 1 := by
    intro a
    by_cases ha : a = i <;> norm_num [r,p,Pi.single_apply,ha,eq_comm]
  have hq : ∀ a,(r-(2:ℝ) • q) a*(r-(2:ℝ) • q) a = 1 := by
    intro a
    by_cases ha : a = j <;> norm_num [r,q,Pi.single_apply,ha,eq_comm]
  have hpq : ∀ a,(r-(2:ℝ) • p-(2:ℝ) • q) a*(r-(2:ℝ) • p-(2:ℝ) • q) a = 1 := by
    intro a
    by_cases hi : a = i <;> by_cases hj : a = j <;>
      norm_num [r,p,q,Pi.single_apply,hi,hj,eq_comm] <;> simp_all
    all_goals norm_num
  have hc : Commute (torusRepresentation l p) (torusRepresentation l q) := by
    change Commute (angularRepresentation l (torusMatrix p)) (angularRepresentation l (torusMatrix q))
    rw [angularRepresentation_torus,angularRepresentation_torus]
    exact Matrix.commute_diagonal _ _
  apply mixed_product_mem (angularLie l) (torusRepresentation l r)
    (torusRepresentation l p) (torusRepresentation l q) hc
  · exact angularLie_generator l (signedStructure r hr)
  · convert angularLie_generator l (signedStructure (r-(2:ℝ) • p) hp) using 1
    change _ = traceFree (torusRepresentation l (r-(2:ℝ) • p)*torusRepresentation l (r-(2:ℝ) • p))
    rw [torusRepresentation_flip]
  · convert angularLie_generator l (signedStructure (r-(2:ℝ) • q) hq) using 1
    change _ = traceFree (torusRepresentation l (r-(2:ℝ) • q)*torusRepresentation l (r-(2:ℝ) • q))
    rw [torusRepresentation_flip]
  · convert angularLie_generator l (signedStructure (r-(2:ℝ) • p-(2:ℝ) • q) hpq) using 1
    change _ = traceFree (torusRepresentation l (r-(2:ℝ) • p-(2:ℝ) • q)*torusRepresentation l (r-(2:ℝ) • p-(2:ℝ) • q))
    rw [torusRepresentation_flip,torusRepresentation_flip]

lemma angularLie_pair_weight (l : ℕ) (i j : Fin s) (hij : i ≠ j) :
    traceFree (diagonal (fun ν : MonomialIndex (Fin s ⊕ Fin s) l =>
      monomialWeight ν.1 i*monomialWeight ν.1 j)) ∈ angularLie l := by
  have h := angularLie_mixed_torus l i j hij
  change traceFree (angularRepresentation l (torusMatrix (Pi.single i 1))*
    angularRepresentation l (torusMatrix (Pi.single j 1))) ∈ _ at h
  rw [angularRepresentation_plane,angularRepresentation_plane,diagonal_mul_diagonal] at h
  have he : diagonal (fun ν : MonomialIndex (Fin s ⊕ Fin s) l =>
      (Complex.I*monomialWeight ν.1 i)*(Complex.I*monomialWeight ν.1 j)) =
      -diagonal (fun ν : MonomialIndex (Fin s ⊕ Fin s) l => monomialWeight ν.1 i*monomialWeight ν.1 j) := by
    rw [diagonal_neg]
    congr 1
    funext ν
    calc
      _ = Complex.I^2*(monomialWeight ν.1 i*monomialWeight ν.1 j) := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  rw [he,map_neg] at h
  have hn := (angularLie l).neg_mem h
  change -(-traceFree _) ∈ angularLie l at hn
  simpa only [neg_neg] using hn

lemma angularLie_pair_normalizer (l : ℕ) (i j : Fin s) (hij : i ≠ j)
    (X : Matrix (MonomialIndex (Fin s ⊕ Fin s) l) (MonomialIndex (Fin s ⊕ Fin s) l) ℂ)
    (hX : X ∈ angularLie l) :
    ⁅diagonal (fun ν : MonomialIndex (Fin s ⊕ Fin s) l =>
      monomialWeight ν.1 i*monomialWeight ν.1 j),X⁆ ∈ angularLie l := by
  have h := (angularLie l).neg_mem ((angularLie l).lie_mem hX (angularLie_pair_weight l i j hij))
  change -(X*traceFree _-traceFree _*X) ∈ angularLie l at h
  rw [commutator_traceFree_complex] at h
  change _*X-X*_ ∈ angularLie l
  simpa only [neg_sub] using h

end HarmonicCounterexample.Control

end

end OAI
