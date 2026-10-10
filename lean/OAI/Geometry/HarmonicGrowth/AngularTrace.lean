import OAI.Geometry.HarmonicGrowth.Angular

namespace OAI

noncomputable section


namespace HarmonicCounterexample.Angular
open MvPolynomial Matrix HarmonicCounterexample.Control
open scoped BigOperators
variable {n : ℕ}

def planeMatrix (i j : Fin n) : Mat n := fun a b =>
  (if a=i then if b=j then 1 else 0 else 0)-(if a=j then if b=i then 1 else 0 else 0)

lemma planeMatrix_skew (i j : Fin n) (a b : Fin n) : planeMatrix i j a b = -planeMatrix i j b a := by
  simp only [planeMatrix,← ite_and,and_comm]
  ring

lemma planeField_apply (i j : Fin n) (P : PolynomialSpace n) :
    polynomialRotation (planeMatrix i j) P=X j*pderiv i P-X i*pderiv j P := by
  simp [polynomialRotation_apply,planeMatrix,sub_smul,Finset.sum_sub_distrib]

lemma linearField_plane_X (i j a : Fin n) :
    linearField (planeMatrix i j) (X a : PolynomialSpace n)=
      (if a=i then X j else 0)-(if a=j then X i else 0) := by
  simp [linearField_X,planeMatrix,sub_smul,Finset.sum_sub_distrib]

def plane (l : ℕ) (i j : Fin n) : Module.End ℝ (harmonicPolynomials n l) where
  toFun P := ⟨polynomialRotation (planeMatrix i j) P,
    polynomialRotation_homogeneous P.property.1 _,by
      change polynomialLaplacian _=0
      rw [laplacian_rotation_skew _ (planeMatrix_skew i j),P.property.2,map_zero]⟩
  map_add' P Q := Subtype.ext (map_add _ _ _)
  map_smul' c P := Subtype.ext (map_smul _ _ _)

lemma plane_val (l : ℕ) (i j : Fin n) (P : harmonicPolynomials n l) :
    (plane l i j P).val=X j*pderiv i P.val-X i*pderiv j P.val := planeField_apply i j P.val

lemma plane_self (l : ℕ) (i : Fin n) : plane l i i=0 := by
  apply LinearMap.ext;intro P;apply Subtype.ext;simp only [plane_val,sub_self,LinearMap.zero_apply,Submodule.coe_zero]

lemma plane_swap (l : ℕ) (i j : Fin n) : plane l j i= -plane l i j := by
  apply LinearMap.ext;intro P;apply Subtype.ext;simp only [plane_val,LinearMap.neg_apply,Submodule.coe_neg];ring

lemma planeMatrix_eq_single (i j : Fin n) :
    planeMatrix i j=Matrix.single i j 1-Matrix.single j i 1 := by
  ext a b
  simp only [planeMatrix,← ite_and,Matrix.sub_apply,Matrix.single_apply]
  congr 1 <;> congr 1 <;> exact propext (by tauto)

lemma single_product (i j k r : Fin n) :
    (Matrix.single i j (1:ℝ))*Matrix.single k r 1=
      if j=k then Matrix.single i r 1 else 0 := by
  by_cases h : j=k
  · subst k;simp
  · simp [h]

lemma indicator_sub {A : Type*} [AddGroup A] (p : Prop) [Decidable p] (x y : A) :
    (if p then x-y else 0)=(if p then x else 0)-(if p then y else 0) := by
  by_cases h : p <;> simp [h]

lemma map_indicator {A B : Type*} [AddCommGroup A] [Module ℝ A]
    [AddCommGroup B] [Module ℝ B] (f : A →ₗ[ℝ] B) (p : Prop) [Decidable p] (x : A) :
    f (if p then x else 0)=(if p then f x else 0) := by
  by_cases h : p <;> simp [h]

lemma planeMatrix_commutator (i j k r : Fin n) :
    planeMatrix k r*planeMatrix i j-planeMatrix i j*planeMatrix k r=
      (if i=r then planeMatrix k j else 0) -(if j=r then planeMatrix k i else 0)
       -(if i=k then planeMatrix r j else 0)+(if j=k then planeMatrix r i else 0) := by
  simp only [planeMatrix_eq_single,mul_sub,sub_mul,single_product]
  simp only [indicator_sub,eq_comm (a:=r) (b:=i),eq_comm (a:=r) (b:=j),
    eq_comm (a:=k) (b:=i),eq_comm (a:=k) (b:=j)]
  abel

lemma plane_field_val (l : ℕ) (i j : Fin n) (P : harmonicPolynomials n l) :
    (plane l i j P).val=linearField (planeMatrix i j) P.val :=
  rotation_eq_field _ _

lemma linearFieldMap_apply (M : Mat n) (P : PolynomialSpace n) :
    linearFieldMap M P=linearField M P := rfl

lemma plane_bracket (l : ℕ) (i j k r : Fin n) :
    plane l i j*plane l k r-plane l k r*plane l i j =
      (if i=r then plane l k j else 0) -(if j=r then plane l k i else 0)
       -(if i=k then plane l r j else 0)+(if j=k then plane l r i else 0) := by
  have hf := congrArg (linearFieldMap (𝕜:=ℝ)) (planeMatrix_commutator i j k r)
  simp only [map_sub,map_add,map_indicator] at hf
  apply LinearMap.ext;intro P;apply Subtype.ext
  have hh := DFunLike.congr_fun (linearField_bracket (planeMatrix i j) (planeMatrix k r)) P.val
  change _=linearFieldMap _ P.val at hh
  rw [map_sub,hf] at hh
  by_cases h₁ : i=r <;> by_cases h₂ : j=r <;>
    by_cases h₃ : i=k <;> by_cases h₄ : j=k <;>
    simp_all only [not_true_eq_false,ite_true,ite_false,Module.End.mul_apply,
      LinearMap.sub_apply,LinearMap.add_apply,Submodule.coe_sub,Submodule.coe_add,
      Submodule.coe_zero,LinearMap.zero_apply,plane_field_val,
      Derivation.commutator_apply,linearFieldMap_apply]

end HarmonicCounterexample.Angular

end

noncomputable section


namespace HarmonicCounterexample.Angular
open MvPolynomial Matrix HarmonicCounterexample.Control
open scoped BigOperators
variable {n : ℕ} (l : ℕ)

section GenericEnd
variable {V : Type*} [AddCommGroup V] [Module ℝ V]
lemma end_sub_zero (A:Module.End ℝ V) : A-0=A := sub_zero A
lemma end_zero_sub (A:Module.End ℝ V) : 0-A= -A := zero_sub A
lemma end_zero_add (A:Module.End ℝ V) : 0+A=A := zero_add A
lemma end_add_zero (A:Module.End ℝ V) : A+0=A := add_zero A
lemma end_neg_neg (A:Module.End ℝ V) : - -A=A := neg_neg A
lemma end_neg_mul (A B:Module.End ℝ V) : (-A)*B= -(A*B) := neg_mul A B
lemma end_mul_neg (A B:Module.End ℝ V) : A*(-B)= -(A*B) := mul_neg A B
lemma end_mul_zero (A:Module.End ℝ V) : A*0=0 := mul_zero A
lemma end_trace_neg (A:Module.End ℝ V) : LinearMap.trace ℝ V (-A)= -LinearMap.trace ℝ V A := map_neg _ _
lemma end_trace_add (A B:Module.End ℝ V) : LinearMap.trace ℝ V (A+B)=
    LinearMap.trace ℝ V A+LinearMap.trace ℝ V B := map_add _ _ _
lemma end_trace_sub (A B:Module.End ℝ V) : LinearMap.trace ℝ V (A-B)=
    LinearMap.trace ℝ V A-LinearMap.trace ℝ V B := map_sub _ _ _
lemma end_trace_smul (c:ℝ) (A:Module.End ℝ V) : LinearMap.trace ℝ V (c • A)=
    c*LinearMap.trace ℝ V A := map_smul _ _ _
lemma end_trace_sum {α:Type*} (s:Finset α) (A:α→Module.End ℝ V) :
    LinearMap.trace ℝ V (∑a∈s,A a)=∑a∈s,LinearMap.trace ℝ V (A a) := map_sum _ _ _
end GenericEnd

lemma plane_triple {i j k : Fin n} (hij : i≠j) (hik : i≠k) (hjk : j≠k) :
    plane l i j*plane l i k-plane l i k*plane l i j=plane l j k := by
  rw [plane_bracket]
  simp only [hik,hjk,Ne.symm hij,ite_true,ite_false,
    end_sub_zero,end_zero_sub,end_add_zero]
  rw [plane_swap];abel

lemma plane_triple' {i j k : Fin n} (hij : i≠j) (hik : i≠k) (hjk : j≠k) :
    plane l i j*plane l j k-plane l j k*plane l i j= -plane l i k := by
  rw [plane_bracket]
  simp only [hij,hik,hjk,ite_true,ite_false,end_sub_zero,end_zero_add]
  rw [plane_swap]

lemma plane_disjoint {i j k r : Fin n} (hik : i≠k) (hir : i≠r) (hjk : j≠k) (hjr : j≠r) :
    plane l i j*plane l k r-plane l k r*plane l i j=0 := by
  rw [plane_bracket];simp only [hik,hir,hjk,hjr,ite_false,end_sub_zero,end_add_zero]

lemma trace_comm_self {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A B : Module.End ℝ V) : LinearMap.trace ℝ V ((A*B-B*A)*A)=0 := by
  rw [sub_mul,map_sub]
  exact sub_eq_zero.mpr (LinearMap.trace_mul_cycle ℝ B A A).symm

def planePair (i j k r : Fin n) : ℝ :=
  LinearMap.trace ℝ (harmonicPolynomials n l) (plane l i j*plane l k r)

lemma pair_comm (i j k r : Fin n) : planePair l i j k r=planePair l k r i j :=
  LinearMap.trace_mul_comm _ _ _

lemma pair_self (i k r : Fin n) : planePair l i i k r=0 := by
  simp [planePair,plane_self]

lemma pair_swap_left (i j k r : Fin n) : planePair l j i k r= -planePair l i j k r := by
  unfold planePair
  rw [plane_swap l i j,end_neg_mul,end_trace_neg]

lemma pair_swap_right (i j k r : Fin n) : planePair l i j r k= -planePair l i j k r := by
  unfold planePair
  rw [plane_swap l k r,end_mul_neg,end_trace_neg]

lemma pair_shared {i j k : Fin n} (hij : i≠j) (hik : i≠k) (hjk : j≠k) :
    planePair l i j i k=0 := by
  have h := trace_comm_self (plane l i j) (plane l j k)
  rw [plane_triple' l hij hik hjk,end_neg_mul,end_trace_neg] at h
  rw [pair_comm]
  exact neg_eq_zero.mp h

lemma pair_square_shared {i j k : Fin n} (hij : i≠j) (hik : i≠k) (hjk : j≠k) :
    planePair l i j i j=planePair l i k i k := by
  have h := LinearMap.trace_lie_mul_eq (plane l i j) (plane l j k) (plane l i k)
  simp only [Ring.lie_def] at h
  rw [plane_triple' l hij hik hjk] at h
  have hc : plane l j k*plane l i k-plane l i k*plane l j k= -plane l i j := by
    rw [plane_bracket]
    simp only [hjk,Ne.symm hij,Ne.symm hik,ite_true,ite_false,
      end_sub_zero,end_zero_sub,end_add_zero]
  rw [hc,end_neg_mul,end_mul_neg,end_trace_neg,end_trace_neg] at h
  exact neg_injective h.symm

end HarmonicCounterexample.Angular

end

noncomputable section


namespace HarmonicCounterexample.Angular
open scoped BigOperators
variable {n : ℕ} (l : ℕ)

lemma fifth_index (hn : 5≤n) (i j k r : Fin n) :
    ∃ a : Fin n,a≠i ∧ a≠j ∧ a≠k ∧ a≠r := by
  have hc : ({i,j,k,r}:Finset (Fin n)).card ≤ 4 := by
    calc
      _ ≤ ({j,k,r}:Finset (Fin n)).card+1 := Finset.card_insert_le _ _
      _ ≤ (({k,r}:Finset (Fin n)).card+1)+1 := Nat.add_le_add_right (Finset.card_insert_le _ _) _
      _ ≤ ((({r}:Finset (Fin n)).card+1)+1)+1 :=
        Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_insert_le _ _) _) _
      _ = 4 := by simp
  by_contra h
  have hall : (Finset.univ : Finset (Fin n)) ⊆ {i,j,k,r} := by
    intro a _
    by_contra ha
    exact h ⟨a,by simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using ha⟩
  have hh := Finset.card_le_card hall
  simp only [Finset.card_univ,Fintype.card_fin] at hh
  omega

lemma pair_square_swap (i j : Fin n) : planePair l i j i j=planePair l j i j i := by
  rw [pair_swap_left l i j j i,pair_swap_right l i j i j,neg_neg]

lemma pair_square_common {i j k : Fin n} (hij : i≠j) (hik : i≠k) :
    planePair l i j i j=planePair l i k i k := by
  by_cases h : j=k
  · subst k;rfl
  · exact pair_square_shared l hij hik h

lemma pair_square_all (hn : 5≤n) {i j k r : Fin n} (hij : i≠j) (hkr : k≠r) :
    planePair l i j i j=planePair l k r k r := by
  obtain ⟨a,hai,haj,hak,har⟩ := fifth_index hn i j k r
  calc
    _ = planePair l i a i a := pair_square_common l hij (Ne.symm hai)
    _ = planePair l a i a i := pair_square_swap l i a
    _ = planePair l a k a k := pair_square_common l hai hak
    _ = planePair l k a k a := pair_square_swap l a k
    _ = _ := pair_square_common l (Ne.symm hak) hkr

lemma pair_disjoint_zero (hn : 5≤n) {i j k r : Fin n} (hij : i≠j)
    (_ : i≠k) (_ : i≠r) (hjk : j≠k) (hjr : j≠r) : planePair l i j k r=0 := by
  obtain ⟨a,hai,haj,hak,har⟩ := fifth_index hn i j k r
  have h := LinearMap.trace_lie_mul_eq (plane l i a) (plane l a j) (plane l k r)
  simp only [Ring.lie_def] at h
  rw [plane_triple' l (Ne.symm hai) hij haj,plane_disjoint l hak har hjk hjr] at h
  simp only [end_mul_zero,map_zero,end_neg_mul,end_trace_neg] at h
  exact neg_eq_zero.mp h

lemma pair_formula (hn : 5≤n) (i₀ j₀ : Fin n) (h₀ : i₀≠j₀) (i j k r : Fin n) :
    planePair l i j k r=
      (if i=k ∧ j=r then planePair l i₀ j₀ i₀ j₀ else 0)-
      (if i=r ∧ j=k then planePair l i₀ j₀ i₀ j₀ else 0) := by
  by_cases hij : i=j
  · subst j;simp [pair_self,and_comm]
  by_cases hkr : k=r
  · subst r;rw [pair_comm,pair_self];simp
  by_cases hik : i=k
  · subst k
    by_cases hjr : j=r
    · subst r;rw [pair_square_all l hn hij h₀];simp [hij,Ne.symm hij]
    · rw [pair_shared l hij hkr hjr];simp [hjr,hkr]
  by_cases hir : i=r
  · subst r
    rw [pair_swap_right l i j i k]
    by_cases hjk : j=k
    · subst k;rw [pair_square_all l hn hij h₀];simp [hij]
    · rw [pair_shared l hij hik hjk];simp [hik,hjk]
  by_cases hjk : j=k
  · subst k
    rw [pair_swap_left l j i j r,pair_shared l (Ne.symm hij) hkr hir]
    simp [hik,hir]
  by_cases hjr : j=r
  · subst r
    rw [pair_swap_right l i j j k,pair_swap_left l j i j k,pair_shared l (Ne.symm hij) hjk hik]
    simp [hik,hir]
  rw [pair_disjoint_zero l hn hij hik hir hjk hjr]
  simp [hik,hir]

end HarmonicCounterexample.Angular

end

noncomputable section


namespace HarmonicCounterexample.Angular
open MvPolynomial Matrix HarmonicCounterexample.Control
open scoped BigOperators
variable {n : ℕ}

lemma polynomial_plane_square (i j : Fin n) (P : PolynomialSpace n) :
    polynomialRotation (planeMatrix i j) (polynomialRotation (planeMatrix i j) P)=
      X j^2*pderiv i (pderiv i P)+X i^2*pderiv j (pderiv j P)-
      2*X i*X j*pderiv i (pderiv j P)-X i*pderiv i P-X j*pderiv j P+
      (if i=j then 2*X i*pderiv i P else 0) := by
  simp only [planeField_apply,map_sub,pderiv_mul]
  by_cases h : i=j
  · subst j;simp [pderiv_X];ring
  · simp [pderiv_X,h,Ne.symm h]
    rw [pderiv_commute P j i];ring

lemma euler_second {l : ℕ} {P : PolynomialSpace n} (hP : P.IsHomogeneous l) :
    (∑ i : Fin n,∑ j : Fin n,X i*X j*pderiv i (pderiv j P))=
      ((l:ℝ)*((l:ℝ)-1)) • P := by
  have he : (∑ j : Fin n,X j*pderiv j P)=(l:ℝ) • P := by
    simpa only [Nat.cast_smul_eq_nsmul] using hP.sum_X_mul_pderiv
  have hd (i : Fin n) : (∑ j : Fin n,X j*pderiv i (pderiv j P))=
      ((l:ℝ)-1) • pderiv i P := by
    have hh := congrArg (pderiv i) he
    simp only [map_sum,pderiv_mul,Finset.sum_add_distrib] at hh
    simp [pderiv_X,Pi.single_apply,ite_mul] at hh
    simp only [smul_eq_C_mul,map_sub,C_1] at *
    linear_combination hh
  calc
    _ = ∑ i : Fin n,X i*(∑ j : Fin n,X j*pderiv i (pderiv j P)) := by
      simp only [Finset.mul_sum,mul_assoc]
    _ = ∑ i : Fin n,((l:ℝ)-1) • (X i*pderiv i P) := by
      simp only [hd,mul_smul_comm]
    _ = ((l:ℝ)-1) • ((l:ℝ) • P) := by rw [← Finset.smul_sum,he]
    _ = _ := by rw [smul_smul,mul_comm]

lemma sum_plane_square {l : ℕ} {P : PolynomialSpace n}
    (hP : P ∈ harmonicPolynomials n l) :
    (∑ i : Fin n,∑ j : Fin n,
      polynomialRotation (planeMatrix i j) (polynomialRotation (planeMatrix i j) P))=
      (-2*(l:ℝ)*((l:ℝ)+(n:ℝ)-2)) • P := by
  have hp : polynomialLaplacian P=0 := hP.2
  have h₁ : (∑ i : Fin n,∑ j : Fin n,X j^2*pderiv i (pderiv i P))=0 := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum,← polynomialLaplacian_apply,hp,mul_zero,Finset.sum_const_zero]
  have h₂ : (∑ i : Fin n,∑ j : Fin n,X i^2*pderiv j (pderiv j P))=0 := by
    simp only [← Finset.mul_sum,← polynomialLaplacian_apply,hp,mul_zero,Finset.sum_const_zero]
  have he : (∑ i : Fin n,X i*pderiv i P)=(l:ℝ) • P := by
    simpa only [Nat.cast_smul_eq_nsmul] using hP.1.sum_X_mul_pderiv
  simp only [polynomial_plane_square,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  rw [h₁,h₂]
  have hc : (∑ i : Fin n,∑ j : Fin n,2*X i*X j*pderiv i (pderiv j P))=
      ((2:ℝ)*((l:ℝ)*((l:ℝ)-1))) • P := by
    rw [show (2*((l:ℝ)*((l:ℝ)-1))) • P =
      (2:ℝ) • (((l:ℝ)*((l:ℝ)-1)) • P) by rw [smul_smul],← euler_second hP.1]
    simp only [Finset.smul_sum,smul_eq_C_mul,map_ofNat]
    apply Finset.sum_congr rfl;intro i _
    apply Finset.sum_congr rfl;intro j _;ring
  rw [hc]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    Finset.sum_nsmul,Finset.sum_ite_eq,Finset.mem_univ,ite_true,he]
  have hg : (∑ i : Fin n,2*X i*pderiv i P)=(2:ℝ) • ((l:ℝ) • P) := by
    rw [← he]
    simp only [Finset.smul_sum,smul_eq_C_mul,map_ofNat,mul_assoc]
  rw [hg]
  simp only [← Nat.cast_smul_eq_nsmul ℝ,smul_eq_C_mul,map_mul,map_sub,map_add,
    map_neg,C_1,map_natCast,map_ofNat]
  ring

lemma casimir (l : ℕ) :
    (∑ i : Fin n,∑ j : Fin n,plane l i j*plane l i j)=
      (-2*(l:ℝ)*((l:ℝ)+(n:ℝ)-2)) • (1:Module.End ℝ (harmonicPolynomials n l)) := by
  apply LinearMap.ext;intro P;apply Subtype.ext
  simpa only [LinearMap.sum_apply,Module.End.mul_apply,Submodule.coe_sum,plane_val,planeField_apply,
    LinearMap.smul_apply,Module.End.one_apply,Submodule.coe_smul] using
      sum_plane_square P.property

end HarmonicCounterexample.Angular

end

noncomputable section


namespace HarmonicCounterexample.Angular
open MvPolynomial Matrix HarmonicCounterexample.Control Berger
open scoped BigOperators

section Generic
variable {V α:Type*} [AddCommGroup V] [Module ℝ V]
lemma trace_smul_square (c:ℝ) (A:Module.End ℝ V) :
    LinearMap.trace ℝ V ((c • A)*(c • A))=c^2*LinearMap.trace ℝ V (A*A) := by
  rw [smul_mul_assoc,mul_smul_comm,smul_smul,map_smul]
  simp only [smul_eq_mul,pow_two]
variable [Fintype α]
lemma trace_square_sum (c:α→ℝ) (A:α→Module.End ℝ V) :
    LinearMap.trace ℝ V ((∑i,c i • A i)*(∑i,c i • A i))=
      ∑i,∑j,c i*c j*LinearMap.trace ℝ V (A i*A j) := by
  simp only [Finset.sum_mul,Finset.mul_sum,map_sum,smul_mul_assoc,mul_smul_comm,
    map_smul,smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl;intro i _
  apply Finset.sum_congr rfl;intro j _
  ring
end Generic

lemma rotation_sum_planes {n:ℕ} (J:ComplexStructure (Fin n)) (l:ℕ) :
    rotation J l=(1/2:ℝ) • ∑i:Fin n,∑j:Fin n,J.matrix i j • plane l i j := by
  apply LinearMap.ext;intro P;apply Subtype.ext
  change polynomialRotation J.matrix P.val = _
  simp only [LinearMap.smul_apply,LinearMap.sum_apply,Submodule.coe_smul,Submodule.coe_sum,plane_val,
    smul_sub,Finset.sum_sub_distrib,polynomialRotation_apply]
  have hs : (∑i:Fin n,∑j:Fin n,J.matrix i j • (X i*pderiv j P.val))=
      -(∑i:Fin n,∑j:Fin n,J.matrix i j • (X j*pderiv i P.val)) := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl;intro i _
    apply Finset.sum_congr rfl;intro j _
    have h : J.matrix j i= -J.matrix i j := congrFun (congrFun J.skew i) j
    rw [h,neg_smul]
  rw [hs]
  module

lemma plane_square_trace16 (l:ℕ) :
    240*planePair l (0:Fin 16) 1 0 1=
      (-2*(l:ℝ)*((l:ℝ)+14))*(Module.finrank ℝ (harmonicPolynomials 16 l):ℝ) := by
  have h := congrArg (LinearMap.trace ℝ (harmonicPolynomials 16 l)) (casimir (n:=16) l)
  simp only [end_trace_sum,end_trace_smul,LinearMap.trace_one] at h
  change (∑i:Fin 16,∑j:Fin 16,planePair l i j i j)=_ at h
  have he (i j:Fin 16) : planePair l i j i j=
      if i=j then 0 else planePair l (0:Fin 16) 1 0 1 := by
    by_cases hij:i=j
    · subst j;simp [pair_self]
    · rw [ite_eq_right hij]
      exact pair_square_all l (by norm_num) hij (by decide)
  have hh : (∑i:Fin 16,∑j:Fin 16,planePair l i j i j)=
      ∑i:Fin 16,∑j:Fin 16,if i=j then 0 else planePair l (0:Fin 16) 1 0 1 := by
    apply Finset.sum_congr rfl;intro i _
    apply Finset.sum_congr rfl;intro j _;exact he i j
  rw [hh] at h
  simp only [Finset.sum_ite,Finset.sum_const_zero,zero_add,Finset.sum_const] at h
  have hcard (i:Fin 16) : (Finset.univ.filter (fun j:Fin 16 => ¬ i=j)).card=15 := by
    have hf : Finset.univ.filter (fun j:Fin 16 => ¬ i=j)=Finset.univ.erase i := by
      ext j;simp [eq_comm]
    rw [hf,Finset.card_erase_of_mem (Finset.mem_univ i)]
    rfl
  simp only [hcard,Finset.sum_const,Finset.card_univ,Fintype.card_fin] at h
  norm_num only [nsmul_eq_mul] at h
  convert h using 1 <;> ring

lemma rotation_trace16 (J:ComplexStructure (Fin 16)) (l:ℕ) :
    LinearMap.trace ℝ (harmonicPolynomials 16 l) (rotation J l*rotation J l)=
      (8:ℝ)*planePair l (0:Fin 16) 1 0 1 := by
  classical
  rw [rotation_sum_planes,trace_smul_square]
  have hf : (∑i:Fin 16,∑j:Fin 16,J.matrix i j • plane l i j)=
      ∑p:Fin 16×Fin 16,J.matrix p.1 p.2 • plane l p.1 p.2 := by
    rw [Fintype.sum_prod_type]
  rw [hf,trace_square_sum]
  simp only [Fintype.sum_prod_type]
  change (1/2:ℝ)^2*(∑i:Fin 16,∑j:Fin 16,∑k:Fin 16,∑r:Fin 16,
    J.matrix i j*J.matrix k r*planePair l i j k r)=_
  have he (i j:Fin 16) :
      (∑k:Fin 16,∑r:Fin 16,J.matrix i j*J.matrix k r*planePair l i j k r)=
        (J.matrix i j*J.matrix i j-J.matrix i j*J.matrix j i)*planePair l (0:Fin 16) 1 0 1 := by
    have hterm (k r:Fin 16) : J.matrix i j*J.matrix k r*planePair l i j k r=
        (if i=k ∧ j=r then J.matrix i j*J.matrix k r*planePair l (0:Fin 16) 1 0 1 else 0)-
        (if i=r ∧ j=k then J.matrix i j*J.matrix k r*planePair l (0:Fin 16) 1 0 1 else 0) := by
      rw [pair_formula l (by norm_num : 5≤16) 0 1 (by decide) i j k r]
      simp only [mul_sub,mul_ite,mul_zero]
    simp only [hterm,Finset.sum_sub_distrib]
    simp only [ite_and,Finset.sum_ite_irrel,Finset.sum_const_zero,
      Finset.sum_ite_eq,Finset.mem_univ,ite_true]
    ring
  simp only [he]
  have hs (i:Fin 16) : ∑j:Fin 16,
      (J.matrix i j*J.matrix i j-J.matrix i j*J.matrix j i)*planePair l (0:Fin 16) 1 0 1=
        2*planePair l (0:Fin 16) 1 0 1 := by
    have hj (j:Fin 16) : J.matrix j i= -J.matrix i j := congrFun (congrFun J.skew i) j
    calc
      _ = (∑j:Fin 16,J.matrix i j*J.matrix i j)*(2*planePair l (0:Fin 16) 1 0 1) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl;intro j _
        rw [hj j];ring
      _ = _ := by rw [complexStructure_rows J i i];simp only [ite_true,one_mul]
  simp only [hs,Finset.sum_const,Finset.card_univ,Fintype.card_fin]
  norm_num;ring

lemma rotation_square_trace16 (J:ComplexStructure (Fin 16)) (l:ℕ) :
    LinearMap.trace ℝ (harmonicPolynomials 16 l) (rotation J l*rotation J l)=
      -((l:ℝ)*((l:ℝ)+14)/15)*(Module.finrank ℝ (harmonicPolynomials 16 l):ℝ) := by
  rw [rotation_trace16]
  have h := plane_square_trace16 l
  linarith

end HarmonicCounterexample.Angular

end

end OAI
