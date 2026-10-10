import OAI.RepresentationTheory.KazhdanLusztig.Frobenius

namespace OAI

/-!
Bott-Samelson tensor ranges, actual sections, grading and right kernels.
-/

section

namespace KLInvariance
open TensorProduct
universe uc ua un uv up
variable {C : Type uc} [CommRing C] {A : Type ua} [CommRing A] [Algebra C A]
  {N : Type un} [AddCommGroup N] [Module C N]
  {V : Type uv} [AddCommGroup V] [Module A V]
  {P : Type up} [AddCommGroup P] [Module A P]
 theorem tensor_range_le_of_one_tmul (F : (A ⊗[C] N) →ₗ[A] V) (G : P →ₗ[A] V)
    (h : ∀ n : N, F ((1 : A) ⊗ₜ[C] n) ∈ LinearMap.range G) :
    LinearMap.range F ≤ LinearMap.range G := by
  rintro _ ⟨m,rfl⟩
  induction m using TensorProduct.inductionOn with
  | add m n hm hn => rw [map_add]; exact (LinearMap.range G).add_mem hm hn
  | tmul a n =>
    have he : a ⊗ₜ[C] n = a • ((1 : A) ⊗ₜ[C] n) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul,mul_one]
    rw [he,map_smul]
    exact (LinearMap.range G).smul_mem a (h n)
 theorem tensor_maps_eq_of_one_tmul (F G : (A ⊗[C] N) →ₗ[A] V)
    (h : ∀ n : N, F ((1 : A) ⊗ₜ[C] n)=G ((1 : A) ⊗ₜ[C] n)) : F=G := by
  apply LinearMap.ext
  intro m
  induction m using TensorProduct.inductionOn with
  | add m n hm hn => rw [map_add,map_add,hm,hn]
  | tmul a n =>
    have he : a ⊗ₜ[C] n = a • ((1 : A) ⊗ₜ[C] n) := by
      rw [TensorProduct.smul_tmul',smul_eq_mul,mul_one]
    rw [he,map_smul,map_smul,h n]

 theorem codRestrict_surjective_of_range_le (G : P →ₗ[A] V) (S : Submodule A V)
    (hG : ∀ p, G p ∈ S) (hS : S ≤ LinearMap.range G) :
    Function.Surjective (LinearMap.codRestrict S G hG) := by
  intro z
  obtain ⟨p,hp⟩ := hS z.property
  exact ⟨p,Subtype.ext hp⟩
end KLInvariance

end


section

namespace KLInvariance.TitsSpace
open Module TensorProduct FrobeniusDuality ReflectionFrobenius
universe u v up
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section
attribute [local instance] restrictedModule restrictedTower restrictedFree restrictedFinite
 theorem bottWeightProjection_range_le (i : I) (l : List I) (x : W)
    {P : Type up} [AddCommGroup P] [Module (SymmetricCoefficient (M := M)) P]
    (G : P →ₗ[SymmetricCoefficient (M := M)]
      ({e : BottIndex (i::l) // bottWeight cs (i::l) e=x} → SymmetricCoefficient (M := M)))
    (h : ∀ n : BottSamelsonModule cs l,
      bottWeightProjection cs (i::l) x ((1 : SymmetricCoefficient (M := M)) ⊗ₜ[simpleFixed cs i] n) ∈ LinearMap.range G) :
    LinearMap.range (bottWeightProjection cs (i::l) x) ≤ LinearMap.range G := by
  exact tensor_range_le_of_one_tmul (C := simpleFixed cs i)
    (A := SymmetricCoefficient (M := M)) (N := BottSamelsonModule cs l)
    (bottWeightProjection cs (i::l) x) G h
 theorem bottTensor_maps_eq (i : I) (l : List I)
    {P : Type up} [AddCommGroup P] [Module (SymmetricCoefficient (M := M)) P]
    (F G : BottSamelsonModule cs (i::l) →ₗ[SymmetricCoefficient (M := M)] P)
    (h : ∀ n : BottSamelsonModule cs l,
      F ((1 : SymmetricCoefficient (M := M)) ⊗ₜ[simpleFixed cs i] n)=
      G ((1 : SymmetricCoefficient (M := M)) ⊗ₜ[simpleFixed cs i] n)) : F=G :=
  tensor_maps_eq_of_one_tmul (C := simpleFixed cs i)
    (A := SymmetricCoefficient (M := M)) (N := BottSamelsonModule cs l) F G h

end
end KLInvariance.TitsSpace

end


section

/-! The genuine head-word stalk is an integral reflected pair lattice of the
tail word. This supplies the stalk-freeness step once tail edge exactness is
proved; it does not assume the desired main conclusion. -/
namespace KLInvariance.TitsSpace
open Module TensorProduct FrobeniusDuality ReflectionFrobenius ReflectionPairTranslation
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section
attribute [local instance] restrictedModule restrictedTower restrictedFree restrictedFinite

 omit [Fintype I] in
 theorem bottWeight_tail_zero (i : I) (l : List I) (x : W)
    (e : {e : BottIndex (i::l) // bottWeight cs (i::l) e=x}) (h : e.val.1=0) :
    bottWeight cs l e.val.2=x := by
  simpa only [bottWeight,ite_eq_left h] using e.property

 omit [Fintype I] in
 theorem bottWeight_tail_one (i : I) (l : List I) (x : W)
    (e : {e : BottIndex (i::l) // bottWeight cs (i::l) e=x}) (h : e.val.1≠0) :
    bottWeight cs l e.val.2=cs.simple i*x := by
  have he : cs.simple i*bottWeight cs l e.val.2=x := by
    simpa only [bottWeight,ite_eq_right h] using e.property
  simpa only [cs.simple_mul_simple_cancel_left] using (congrArg (cs.simple i * ·) he)

 def bottHeadPairCoordinates (i : I) (l : List I) (x : W) :
    (bottStalk cs l x × Twist (coefficientAction cs (cs.simple i)).toRingEquiv
      (bottStalk cs l (cs.simple i*x))) →ₗ[SymmetricCoefficient (M := M)]
      ({e : BottIndex (i::l) // bottWeight cs (i::l) e=x} → SymmetricCoefficient (M := M)) where
  toFun p e := if h : e.val.1=0 then
      p.1.val ⟨e.val.2,bottWeight_tail_zero cs i l x e h⟩
    else coefficientAction cs (cs.simple i)
      (p.2.val.val ⟨e.val.2,bottWeight_tail_one cs i l x e h⟩)
  map_add' p q := by
    funext e
    by_cases h : e.val.1=0
    · simp only [Pi.add_apply,dite_eq_left h]; rfl
    · simp only [Pi.add_apply,dite_eq_right h]
      exact map_add (coefficientAction cs (cs.simple i)) _ _
  map_smul' r p := by
    funext e
    dsimp
    split_ifs with h
    · rfl
    · change coefficientAction cs (cs.simple i)
        (coefficientAction cs (cs.simple i) r * _) = r * coefficientAction cs (cs.simple i) _
      rw [map_mul,simple_involutive]; rfl

 theorem bottHeadPairCoordinates_injective (i : I) (l : List I) (x : W) :
    Function.Injective (bottHeadPairCoordinates cs i l x) := by
  rintro ⟨p,q⟩ ⟨p',q'⟩ h
  apply Prod.ext
  · apply Subtype.ext
    funext e
    have hh := congrFun h ⟨(0,e.val),by simpa only [bottWeight,ite_true] using e.property⟩
    simpa only [bottHeadPairCoordinates,LinearMap.coe_mk,AddHom.coe_mk,dite_eq_left rfl,dite_true] using hh
  · apply Twist.ext
    apply Subtype.ext
    funext e
    have he : bottWeight cs (i::l) (1,e.val)=x := by
      change (if (1 : Fin 2)=0 then _ else cs.simple i*bottWeight cs l e.val)=x
      rw [ite_eq_right (by decide),e.property,cs.simple_mul_simple_cancel_left]
    have hh := congrFun h ⟨(1,e.val),he⟩
    have hh' : coefficientAction cs (cs.simple i) (q.val.val e) =
        coefficientAction cs (cs.simple i) (q'.val.val e) := by
      simpa only [bottHeadPairCoordinates,LinearMap.coe_mk,AddHom.coe_mk,
        dite_eq_right (show (1 : Fin 2)≠0 by decide)] using hh
    exact (coefficientAction cs (cs.simple i)).injective hh'

 theorem simpleReverseDivisibility (i : I) (a : SymmetricCoefficient (M := M)) :
    simpleRootPolynomial (M := M) i ∣ coefficientAction cs (cs.simple i) a-a :=
  (dvd_sub_comm).mpr (simple_divisible cs i a)

 variable (i : I) (l : List I) (x : W)

 def bottHeadPairLattice := lattice (bottStalkProjection cs l x)
    (bottStalkProjection cs l (cs.simple i*x)) (coefficientAction cs (cs.simple i)).toRingEquiv
    (simpleRootPolynomial (M := M) i) (simpleReverseDivisibility cs i) (bottSimpleEdge_kernel_inclusion cs i l x)

 instance bottHeadPairAddCommGroup : AddCommGroup (bottHeadPairLattice cs i l x) :=
  Submodule.addCommGroup (bottHeadPairLattice cs i l x)

 instance bottHeadPairModule : Module (SymmetricCoefficient (M := M)) (bottHeadPairLattice cs i l x) :=
  Submodule.module (bottHeadPairLattice cs i l x)

 theorem bottHeadPairCoordinates_seed (n : BottSamelsonModule cs l) :
    bottHeadPairCoordinates cs i l x
      (bottStalkProjection cs l x n,⟨bottStalkProjection cs l (cs.simple i*x) n⟩) =
    bottWeightProjection cs (i::l) x ((1 : SymmetricCoefficient (M := M)) ⊗ₜ[simpleFixed cs i] n) := by
  funext e
  change (if h : e.val.1=0 then _ else _) = (1 : SymmetricCoefficient (M := M))*(if e.val.1=0 then _ else _)
  rw [one_mul]
  split_ifs <;> rfl

 def bottHeadPairToStalk : bottHeadPairLattice cs i l x →ₗ[
     SymmetricCoefficient (M := M)] bottStalk cs (i::l) x :=
  LinearMap.codRestrict (bottStalk cs (i::l) x)
    ((bottHeadPairCoordinates cs i l x).comp (bottHeadPairLattice cs i l x).subtype) (by
      rintro ⟨⟨p,q⟩,n,hn,hn'⟩
      refine ⟨(1 : SymmetricCoefficient (M := M)) ⊗ₜ[simpleFixed cs i] n,?_⟩
      change bottWeightProjection cs (i::l) x _=bottHeadPairCoordinates cs i l x (p,q)
      rw [← bottHeadPairCoordinates_seed]
      congr 1
      exact Prod.ext hn (Twist.ext hn'))

 theorem bottHeadPairToStalk_injective : Function.Injective (bottHeadPairToStalk cs i l x) := by
  intro p q h
  apply Subtype.ext
  exact bottHeadPairCoordinates_injective cs i l x (congrArg Subtype.val h)

 theorem bottHeadPair_range :
    LinearMap.range (bottWeightProjection cs (i::l) x) ≤
      LinearMap.range ((bottHeadPairCoordinates cs i l x).comp
        (bottHeadPairLattice cs i l x).subtype) := by
  refine bottWeightProjection_range_le cs i l x (P := bottHeadPairLattice cs i l x)
    ((bottHeadPairCoordinates cs i l x).comp (bottHeadPairLattice cs i l x).subtype) ?_
  intro n
  refine ⟨⟨(bottStalkProjection cs l x n,⟨bottStalkProjection cs l (cs.simple i*x) n⟩),n,rfl,rfl⟩,?_⟩
  exact bottHeadPairCoordinates_seed cs i l x n

 theorem bottHeadPairToStalk_surjective : Function.Surjective (bottHeadPairToStalk cs i l x) := by
  exact codRestrict_surjective_of_range_le (A := SymmetricCoefficient (M := M))
    (P := bottHeadPairLattice cs i l x)
    (V := {e : BottIndex (i::l) // bottWeight cs (i::l) e=x} → SymmetricCoefficient (M := M))
    ((bottHeadPairCoordinates cs i l x).comp (bottHeadPairLattice cs i l x).subtype)
    (bottStalk cs (i::l) x) _ (bottHeadPair_range cs i l x)

 def bottHeadPairEquiv : bottHeadPairLattice cs i l x ≃ₗ[
     SymmetricCoefficient (M := M)] bottStalk cs (i::l) x :=
  LinearEquiv.ofBijective (bottHeadPairToStalk cs i l x)
    ⟨bottHeadPairToStalk_injective cs i l x,bottHeadPairToStalk_surjective cs i l x⟩

end
end KLInvariance.TitsSpace

end


section

/-! The top projection lattice of a reduced actual tensor word is exactly A.
This verifies the genuine rank-one top used in the BMP summand construction;
it does not assert that the other projection lattices form a flabby sheaf. -/
namespace KLInvariance.TitsSpace
open Module TensorProduct
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 def bottFullIndex : (l : List I) → BottIndex l
  | [] => PUnit.unit
  | _::l => (1,bottFullIndex l)

omit [Fintype I] in
 theorem bottWeight_full (l : List I) :
    bottWeight cs l (bottFullIndex l)=cs.wordProd l := by
  induction l with
  | nil => exact cs.wordProd_nil.symm
  | cons i l ih =>
    simp only [bottFullIndex,bottWeight,show (1:Fin 2) ≠ 0 by decide,ite_false,
      cs.wordProd_cons,ih]

omit [Fintype I] in
 theorem bottSubword_length_eq_full (l : List I) (e : BottIndex l)
    (h : (bottSubword l e).length=l.length) : e=bottFullIndex l := by
  induction l with
  | nil =>
    change PUnit at e
    change e=(PUnit.unit : PUnit)
    exact Subsingleton.elim _ _
  | cons i l ih =>
    change Fin 2 × BottIndex l at e
    by_cases he : e.1=0
    · simp only [bottSubword,ite_eq_left he,List.length_cons] at h
      have hn := (bottSubword_sublist l e.2).length_le
      omega
    · have he1 : e.1=1 := by omega
      simp only [bottSubword,ite_eq_right he,List.length_cons] at h
      exact Prod.ext he1 (ih e.2 (Nat.succ.inj h))

omit [Fintype I] in
 theorem bottWeight_eq_top (l : List I) (hl : cs.IsReduced l) (e : BottIndex l)
    (he : bottWeight cs l e=cs.wordProd l) : e=bottFullIndex l := by
  apply bottSubword_length_eq_full
  apply Nat.le_antisymm (bottSubword_sublist l e).length_le
  have hh := cs.length_wordProd_le (bottSubword l e)
  rwa [bottSubword_wordProd,he,hl.eq] at hh

 def bottUnit : (l : List I) → BottSamelsonModule cs l
  | [] => (1 : SymmetricCoefficient (M := M))
  | i::l => 1 ⊗ₜ[simpleFixed cs i] bottUnit l

 theorem bottEvaluation_unit (l : List I) (e : BottIndex l) :
    bottEvaluation cs l e (bottUnit cs l)=1 := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change bottEvaluation cs (i::l) e (1 ⊗ₜ[simpleFixed cs i] bottUnit cs l)=1
    rw [bottEvaluation_tmul,ih]
    split_ifs <;> simp only [map_one,mul_one]

 theorem bottEvaluation_surjective (l : List I) (e : BottIndex l) :
    Function.Surjective (bottEvaluation cs l e) := by
  intro a
  refine ⟨a • bottUnit cs l,?_⟩
  rw [map_smul,bottEvaluation_unit,smul_eq_mul,mul_one]

 def bottTopCoordinate (l : List I) : bottStalk cs l (cs.wordProd l) →ₗ[
    SymmetricCoefficient (M := M)] SymmetricCoefficient (M := M) :=
  (LinearMap.proj ⟨bottFullIndex l,bottWeight_full cs l⟩).comp
    (bottStalk cs l (cs.wordProd l)).subtype

 theorem bottTopCoordinate_bijective (l : List I) (hl : cs.IsReduced l) :
    Function.Bijective (bottTopCoordinate cs l) := by
  constructor
  · intro a b hab
    apply Subtype.ext
    funext e
    have he : e=⟨bottFullIndex l,bottWeight_full cs l⟩ :=
      Subtype.ext (bottWeight_eq_top cs l hl e.val e.property)
    subst e
    exact hab
  · intro a
    obtain ⟨m,hm⟩ := bottEvaluation_surjective cs l (bottFullIndex l) a
    exact ⟨bottStalkProjection cs l (cs.wordProd l) m,hm⟩

 def bottTopStalkEquiv (l : List I) (hl : cs.IsReduced l) :
    bottStalk cs l (cs.wordProd l) ≃ₗ[SymmetricCoefficient (M := M)]
      SymmetricCoefficient (M := M) :=
  LinearEquiv.ofBijective (bottTopCoordinate cs l) (bottTopCoordinate_bijective cs l hl)

end
end KLInvariance.TitsSpace

end


section

/-! The genuine subexpression projections preserve the actual word grading.
In particular the top projection of a reduced tensor word is a graded copy of
A, rather than just an ungraded rank-one lattice. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem bottEvaluation_basis_homogeneous (l : List I) (e f : BottIndex l) :
    bottEvaluationMatrix cs l e f ∈ symmetricGrading basis (bottDegree l f) := by
  induction l with
  | nil =>
    change PUnit at e f
    change (Basis.singleton PUnit (SymmetricCoefficient (M := M)) f) ∈
      symmetricGrading basis 0
    simp only [Basis.singleton_apply]
    exact SetLike.one_mem_graded _
  | cons i l ih =>
    change Fin 2 × BottIndex l at e f
    rcases e with ⟨r,j⟩
    rcases f with ⟨c,k⟩
    rw [bottEvaluationMatrix_cons]
    by_cases hc : c=0
    · subst c
      simp only [ite_true,bottDegree,Fin.val_zero,Nat.cast_zero,zero_add]
      split_ifs
      · exact ih j k
      · exact coefficientAction_homogeneous cs basis _ _ _ (ih j k)
    · have hc1 : c=1 := by omega
      subst c
      simp only [show (1:Fin 2) ≠ 0 by decide,ite_false,bottDegree,Fin.val_one,Nat.cast_one]
      split_ifs
      · exact SetLike.GradedMul.mul_mem (simpleRoot_homogeneous basis i) (ih j k)
      · exact SetLike.GradedMul.mul_mem ((symmetricGrading basis 1).neg_mem
          (simpleRoot_homogeneous basis i))
          (coefficientAction_homogeneous cs basis _ _ _ (ih j k))

 theorem bottEvaluation_homogeneous (l : List I) (e : BottIndex l)
    (n : ℤ) (m : BottSamelsonModule cs l) (hm : m ∈ bottPiece cs basis l n) :
    bottEvaluation cs l e m ∈ symmetricGrading basis n := by
  classical
  have hexp : bottEvaluation cs l e m = ∑ f : BottIndex l,
      (bottBasis cs l).repr m f * bottEvaluationMatrix cs l e f := by
    conv_lhs => rw [← (bottBasis cs l).sum_repr m]
    simp only [map_sum,map_smul,smul_eq_mul,bottEvaluationMatrix]
  rw [hexp]
  apply Submodule.sum_mem
  intro f _
  change ∀ f, (bottBasis cs l).repr m f ∈
    symmetricGrading basis (n-bottDegree l f) at hm
  have h := SetLike.GradedMul.mul_mem (hm f)
    (bottEvaluation_basis_homogeneous cs basis l e f)
  simpa only [sub_add_cancel] using h

 theorem bottEvaluation_component (l : List I) (e : BottIndex l)
    (n : ℤ) (m : BottSamelsonModule cs l) :
    component (symmetricGrading basis) n (bottEvaluation cs l e m) =
      bottEvaluation cs l e (component (bottPiece cs basis l) n m) := by
  simpa only [sub_zero] using map_component (bottPiece cs basis l) (symmetricGrading basis)
    (bottEvaluation cs l e) 0 (by simpa only [add_zero] using bottEvaluation_homogeneous cs basis l e) n m

 theorem bottUnit_homogeneous (l : List I) : bottUnit cs l ∈ bottPiece cs basis l 0 := by
  have he : component (bottPiece cs basis l) 0 (bottUnit cs l)=bottUnit cs l := by
    apply bottEvaluation_injective cs l
    funext e
    change bottEvaluation cs l e (component (bottPiece cs basis l) 0 (bottUnit cs l)) =
      bottEvaluation cs l e (bottUnit cs l)
    rw [← bottEvaluation_component,bottEvaluation_unit]
    exact DirectSum.decompose_of_mem_same (symmetricGrading basis) (SetLike.one_mem_graded _)
  rw [← he]
  exact (DirectSum.decompose (bottPiece cs basis l) (bottUnit cs l) 0).property

end
end KLInvariance.TitsSpace

end


section

/-! Actual integral projection and support lattices inherit their grading from
the genuine tensor word. In particular a homogeneous stalk vector has a
homogeneous tensor lift. No freeness/character claim is assumed. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 def bottCoordinatePiece (l : List I) (x : W) : ℤ → Submodule ℝ
    ({e : BottIndex l // bottWeight cs l e=x} → SymmetricCoefficient (M := M)) :=
  piPiece (fun _ => symmetricGrading basis)

 instance bottCoordinatePiece_decomposition (l : List I) (x : W) :
    DirectSum.Decomposition (bottCoordinatePiece cs basis l x) := by
  classical
  exact (pi_isInternal (fun _ : {e : BottIndex l // bottWeight cs l e=x} =>
    symmetricGrading basis)).chooseDecomposition

 instance bottCoordinatePiece_graded (l : List I) (x : W) :
    SetLike.GradedSMul (symmetricGrading basis) (bottCoordinatePiece cs basis l x) :=
  inferInstanceAs (SetLike.GradedSMul (symmetricGrading basis)
    (piPiece (fun _ : {e : BottIndex l // bottWeight cs l e=x} => symmetricGrading basis)))

 theorem bottWeightProjection_homogeneous (l : List I) (x : W) (n : ℤ)
    (m : BottSamelsonModule cs l) (hm : m ∈ bottPiece cs basis l n) :
    bottWeightProjection cs l x m ∈ bottCoordinatePiece cs basis l x n := by
  intro e _
  exact bottEvaluation_homogeneous cs basis l e.val n m hm

 theorem bottStalk_homogeneous (l : List I) (x : W) :
    ∀ n f, f ∈ bottStalk cs l x →
      component (bottCoordinatePiece cs basis l x) n f ∈ bottStalk cs l x := by
  exact range_homogeneous (bottPiece cs basis l) (bottCoordinatePiece cs basis l x)
    (bottWeightProjection cs l x) 0 (by
      simpa only [add_zero] using bottWeightProjection_homogeneous cs basis l x)

 def bottStalkPiece (l : List I) (x : W) : ℤ → Submodule ℝ (bottStalk cs l x) :=
  subPiece (bottCoordinatePiece cs basis l x) (bottStalk cs l x)

 instance bottStalkPiece_decomposition (l : List I) (x : W) :
    DirectSum.Decomposition (bottStalkPiece cs basis l x) :=
  (sub_isInternal (bottCoordinatePiece cs basis l x) (bottStalk cs l x)
    (bottStalk_homogeneous cs basis l x)).chooseDecomposition

 instance bottStalkPiece_graded (l : List I) (x : W) :
    SetLike.GradedSMul (symmetricGrading basis) (bottStalkPiece cs basis l x) :=
  inferInstanceAs (SetLike.GradedSMul (symmetricGrading basis)
    (subPiece (bottCoordinatePiece cs basis l x) (bottStalk cs l x)))

 theorem bottStalkProjection_homogeneous (l : List I) (x : W) (n : ℤ)
    (m : BottSamelsonModule cs l) (hm : m ∈ bottPiece cs basis l n) :
    bottStalkProjection cs l x m ∈ bottStalkPiece cs basis l x n :=
  bottWeightProjection_homogeneous cs basis l x n m hm

 theorem bottStalk_homogeneous_lift (l : List I) (x : W) (n : ℤ)
    (s : bottStalk cs l x) (hs : s ∈ bottStalkPiece cs basis l x n) :
    ∃ m : BottSamelsonModule cs l, m ∈ bottPiece cs basis l n ∧
      bottStalkProjection cs l x m=s := by
  obtain ⟨m,hm⟩ := bottStalkProjection_surjective cs l x s
  refine ⟨component (bottPiece cs basis l) n m,
    (DirectSum.decompose (bottPiece cs basis l) m n).property,?_⟩
  have he := map_component (bottPiece cs basis l) (bottStalkPiece cs basis l x)
    (bottStalkProjection cs l x) 0 (by
      simpa only [add_zero] using bottStalkProjection_homogeneous cs basis l x) n m
  rw [sub_zero,hm,show component (bottStalkPiece cs basis l x) n s=s from
    DirectSum.decompose_of_mem_same _ hs] at he
  exact he.symm

 theorem bottWeightSupported_homogeneous (l : List I) (x : W) :
    ∀ n m, m ∈ bottWeightSupported cs l x →
      component (bottPiece cs basis l) n m ∈ bottWeightSupported cs l x := by
  intro n m hm e he
  rw [← bottEvaluation_component,hm e he,map_zero]

 def bottSupportPiece (l : List I) (x : W) :
    ℤ → Submodule ℝ (bottWeightSupported cs l x) :=
  subPiece (bottPiece cs basis l) (bottWeightSupported cs l x)

 instance bottSupportPiece_decomposition (l : List I) (x : W) :
    DirectSum.Decomposition (bottSupportPiece cs basis l x) :=
  (sub_isInternal (bottPiece cs basis l) (bottWeightSupported cs l x)
    (bottWeightSupported_homogeneous cs basis l x)).chooseDecomposition

 instance bottSupportPiece_graded (l : List I) (x : W) :
    SetLike.GradedSMul (symmetricGrading basis) (bottSupportPiece cs basis l x) :=
  inferInstanceAs (SetLike.GradedSMul (symmetricGrading basis)
    (subPiece (bottPiece cs basis l) (bottWeightSupported cs l x)))

omit [Fintype σ] in
 theorem bottTopStalkEquiv_homogeneous (l : List I) (hl : cs.IsReduced l)
    (n : ℤ) (s : bottStalk cs l (cs.wordProd l)) :
    bottTopStalkEquiv cs l hl s ∈ symmetricGrading basis n ↔
      s ∈ bottStalkPiece cs basis l (cs.wordProd l) n := by
  constructor
  · intro h e _
    have he : e=⟨bottFullIndex l,bottWeight_full cs l⟩ :=
      Subtype.ext (bottWeight_eq_top cs l hl e.val e.property)
    subst e
    exact h
  · intro h
    exact h ⟨bottFullIndex l,bottWeight_full cs l⟩ (Set.mem_univ _)

end
end KLInvariance.TitsSpace

end


section

/-! Restriction of the honest reflection-twisted module to the fixed base field.
The automorphism fixes the base field, so no scalar information is discarded. -/
namespace KLInvariance.ReflectionPairTranslation.Twist
universe uk ur uy
variable {k : Type uk} [Field k] {R : Type ur} [CommRing R] [Algebra k R]
  (τ : R ≃ₐ[k] R) (Y : Type uy) [AddCommGroup Y] [Module R Y] [Module k Y]
  [IsScalarTower k R Y]

instance scalarModule : Module k (Twist τ.toRingEquiv Y) :=
  ({ equivVal τ.toRingEquiv Y with map_add' := fun _ _ => rfl } :
    Twist τ.toRingEquiv Y ≃+ Y).module k

instance scalarTower : IsScalarTower k R (Twist τ.toRingEquiv Y) where
  smul_assoc c r y := by
    apply Twist.ext
    change τ (c • r) • y.val=c • (τ r • y.val)
    rw [map_smul,smul_assoc]

def scalarEquiv : Twist τ.toRingEquiv Y ≃ₗ[k] Y where
  toFun := val
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end KLInvariance.ReflectionPairTranslation.Twist

end


section

/-! Homogeneous perfect pairings on the actual integral free modules.  The
inverse grading is proved, not inferred merely after fraction-field extension. -/
namespace KLInvariance.Graded
open Module
universe uk ua um un ui
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {N : Type um} [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]
  {P : Type un} [AddCommGroup P] [Module A P] [Module k P] [IsScalarTower k A P]
noncomputable section

omit [Algebra k A] [IsScalarTower k A N] [IsScalarTower k A P] in
 theorem equiv_inverse_homogeneous
    (𝓝 : ℤ → Submodule k N) (𝓟 : ℤ → Submodule k P)
    [DirectSum.Decomposition 𝓝] [DirectSum.Decomposition 𝓟]
    (e : N ≃ₗ[A] P) (d : ℤ)
    (he : ∀ n x, x ∈ 𝓝 n → e x ∈ 𝓟 (n+d))
    (n : ℤ) (y : P) (hy : y ∈ 𝓟 n) : e.symm y ∈ 𝓝 (n-d) := by
  have hc : component 𝓝 (n-d) (e.symm y) = e.symm y := by
    apply e.injective
    change e.toLinearMap (component 𝓝 (n-d) (e.symm y)) = e.toLinearMap (e.symm y)
    rw [← map_component 𝓝 𝓟 e.toLinearMap d he n (e.symm y)]
    simp only [LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply]
    exact DirectSum.decompose_of_mem_same 𝓟 hy
  rw [← hc]
  exact (DirectSum.decompose 𝓝 (e.symm y) (n-d)).property

variable (𝓐 : ℤ → Submodule k A) [DirectSum.Decomposition 𝓐]
  [SetLike.GradedMonoid 𝓐] {ι : Type ui} [Fintype ι] [DecidableEq ι]
  (b : Basis ι A N) (d : ι → ℤ)

omit [DirectSum.Decomposition 𝓐] in
 theorem pairing_to_dual_homogeneous (p : N →ₗ[A] Dual A N) (l : ℤ)
    (hp : ∀ i j, p (b i) (b j) ∈ 𝓐 (d i+d j-l))
    {n : ℤ} {x : N} (hx : x ∈ basisPiece 𝓐 b d n) :
    p x ∈ basisPiece 𝓐 b.dualBasis (fun i => -d i) (n-l) := by
  rw [mem_basisPiece]
  intro i
  rw [Basis.dualBasis_repr]
  have h := pairing_homogeneous 𝓐 b d p l hp hx (basis_mem_piece 𝓐 b d i)
  convert h using 1
  congr 1
  omega

 theorem perfectPairing_inverse_homogeneous (p : N ≃ₗ[A] Dual A N) (l : ℤ)
    (hp : ∀ i j, p (b i) (b j) ∈ 𝓐 (d i+d j-l))
    {n : ℤ} {y : Dual A N}
    (hy : y ∈ basisPiece 𝓐 b.dualBasis (fun i => -d i) n) :
    p.symm y ∈ basisPiece 𝓐 b d (n+l) := by
  have he : ∀ m x, x ∈ basisPiece 𝓐 b d m →
      p x ∈ basisPiece 𝓐 b.dualBasis (fun i => -d i) (m+(-l)) := by
    intro m x hx
    exact pairing_to_dual_homogeneous 𝓐 b d p.toLinearMap l hp hx
  simpa only [sub_neg_eq_add] using equiv_inverse_homogeneous
    (basisPiece 𝓐 b d) (basisPiece 𝓐 b.dualBasis (fun i => -d i)) p (-l) he n y hy

end
end KLInvariance.Graded

end


section

/-! The genuine head-word projection maps, on the fixed real field, preserve
homogeneous degrees. These maps are not abstract character operators. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded ReflectionPairTranslation
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 def bottHeadLeft (i : I) (l : List I) (x : W) :
    bottStalk cs (i::l) x →ₗ[SymmetricCoefficient (M := M)] bottStalk cs l x :=
  (ReflectionPairTranslation.left (bottStalkProjection cs l x)
    (bottStalkProjection cs l (cs.simple i*x)) (coefficientAction cs (cs.simple i)).toRingEquiv
    (simpleRootPolynomial (M := M) i) (simpleReverseDivisibility cs i)
    (bottSimpleEdge_kernel_inclusion cs i l x)).comp (bottHeadPairEquiv cs i l x).symm.toLinearMap

 def bottHeadRight (i : I) (l : List I) (x : W) :
    bottStalk cs (i::l) x →ₗ[ℝ] bottStalk cs l (cs.simple i*x) :=
  (Twist.scalarEquiv (coefficientAction cs (cs.simple i)) _).toLinearMap.comp
    (((LinearMap.snd (SymmetricCoefficient (M := M)) (bottStalk cs l x)
      (Twist (coefficientAction cs (cs.simple i)).toRingEquiv (bottStalk cs l (cs.simple i*x)))).comp
        ((bottHeadPairLattice cs i l x).subtype.comp
          (bottHeadPairEquiv cs i l x).symm.toLinearMap)).restrictScalars ℝ)

 theorem bottHeadLeft_surjective (i : I) (l : List I) (x : W) :
    Function.Surjective (bottHeadLeft cs i l x) :=
  (left_surjective _ _ _ _ _ _ (bottStalkProjection_surjective cs l x)).comp
    (bottHeadPairEquiv cs i l x).symm.surjective

 theorem bottHeadPairEquiv_coordinates (i : I) (l : List I) (x : W)
    (m : bottStalk cs (i::l) x) :
    bottHeadPairCoordinates cs i l x ((bottHeadPairEquiv cs i l x).symm m).val=m.val :=
  congrArg Subtype.val ((bottHeadPairEquiv cs i l x).apply_symm_apply m)

omit [Fintype σ] in
 theorem bottHeadLeft_homogeneous (i : I) (l : List I) (x : W) (n : ℤ)
    (m : bottStalk cs (i::l) x) (hm : m ∈ bottStalkPiece cs basis (i::l) x n) :
    bottHeadLeft cs i l x m ∈ bottStalkPiece cs basis l x n := by
  intro e _
  change (bottHeadLeft cs i l x m).val e ∈ symmetricGrading basis n
  let E : {e : BottIndex (i::l) // bottWeight cs (i::l) e=x} :=
    ⟨(0,e.val),by simpa only [bottWeight,ite_true] using e.property⟩
  have he := congrFun (bottHeadPairEquiv_coordinates cs i l x m) E
  have hh : (bottHeadLeft cs i l x m).val e=m.val E := by
    change ((bottHeadPairEquiv cs i l x).symm m).val.1.val e=m.val E at he
    exact he
  rw [hh]
  exact hm E (Set.mem_univ E)

 theorem bottHeadRight_homogeneous (i : I) (l : List I) (x : W) (n : ℤ)
    (m : bottStalk cs (i::l) x) (hm : m ∈ bottStalkPiece cs basis (i::l) x n) :
    bottHeadRight cs i l x m ∈ bottStalkPiece cs basis l (cs.simple i*x) n := by
  intro e _
  change (bottHeadRight cs i l x m).val e ∈ symmetricGrading basis n
  let E : {e : BottIndex (i::l) // bottWeight cs (i::l) e=x} :=
    ⟨(1,e.val),by simp only [bottWeight,ite_eq_right (show (1:Fin 2)≠0 by decide),
      e.property,cs.simple_mul_simple_cancel_left]⟩
  have he := congrFun (bottHeadPairEquiv_coordinates cs i l x m) E
  have hh : coefficientAction cs (cs.simple i) ((bottHeadRight cs i l x m).val e)=m.val E := by
    change coefficientAction cs (cs.simple i)
      (((bottHeadPairEquiv cs i l x).symm m).val.2.val.val e)=m.val E at he
    exact he
  have h := coefficientAction_homogeneous cs basis (cs.simple i) n (m.val E)
    (hm E (Set.mem_univ E))
  rw [← hh,simple_involutive] at h
  exact h

end
end KLInvariance.TitsSpace

end


section

/-! The two common tail components of a reflected tensor. They are defined
on the actual tensor, so divisibility assertions at different weights use the
same tail vectors rather than unrelated existential lifts. -/
namespace KLInvariance.ReflectionPairTranslation
open TensorProduct
universe uc ua un
variable {C : Type uc} [CommRing C] {A : Type ua} [CommRing A] [Algebra C A]
  {N : Type un} [AddCommGroup N] [Module A N] [Module C N] [IsScalarTower C A N]
  (τ : A ≃+* A) (hfix : ∀ c : C, τ (algebraMap C A c)=algebraMap C A c)
noncomputable section

 def tensorFirst : (A ⊗[C] N) →ₗ[A] N :=
  AlgebraTensorModule.lift ((LinearMap.id : A →ₗ[A] A).smulRight
    (LinearMap.id : N →ₗ[C] N))

 @[simp] theorem tensorFirst_tmul (a : A) (n : N) :
    tensorFirst (C := C) (a ⊗ₜ[C] n)=a • n := rfl

 def tensorSecond : (A ⊗[C] N) →ₗ[A] Twist τ N := by
  letI : Module C (Twist τ N) := Module.compHom _ (algebraMap C A)
  letI : IsScalarTower C A (Twist τ N) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let F : N →ₗ[C] Twist τ N := {
    toFun := Twist.mk
    map_add' := fun _ _ => rfl
    map_smul' := fun c n => by
      apply Twist.ext
      change c • n=τ (algebraMap C A c) • n
      rw [hfix,algebraMap_smul] }
  exact AlgebraTensorModule.lift ((LinearMap.id : A →ₗ[A] A).smulRight F)

 @[simp] theorem tensorSecond_tmul (a : A) (n : N) :
    tensorSecond τ hfix (a ⊗ₜ[C] n)=Twist.mk (τ a • n) := rfl

 def twistMap {P : Type*} [AddCommGroup P] [Module A P] (f : N →ₗ[A] P) :
    Twist τ N →ₗ[A] Twist τ P where
  toFun m := ⟨f m.val⟩
  map_add' m n := Twist.ext (map_add f m.val n.val)
  map_smul' a m := Twist.ext (map_smul f (τ a) m.val)
end
end KLInvariance.ReflectionPairTranslation

end


section

namespace KLInvariance.TitsSpace
open Module TensorProduct FrobeniusDuality ReflectionFrobenius ReflectionPairTranslation
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section
attribute [local instance] restrictedModule restrictedTower restrictedFree restrictedFinite

 def bottHeadTail (i : I) (l : List I) : BottSamelsonModule cs (i::l) →ₗ[
    SymmetricCoefficient (M := M)] BottSamelsonModule cs l :=
  tensorFirst (C := simpleFixed cs i)

 def bottHeadReflectedTail (i : I) (l : List I) : BottSamelsonModule cs (i::l) →ₗ[
    SymmetricCoefficient (M := M)] Twist (coefficientAction cs (cs.simple i)).toRingEquiv
      (BottSamelsonModule cs l) :=
  tensorSecond (C := simpleFixed cs i) (coefficientAction cs (cs.simple i)).toRingEquiv
    (fun c => c.property)

 theorem bottHeadTail_seed (i : I) (l : List I) (n : BottSamelsonModule cs l) :
    bottHeadTail cs i l ((1 : SymmetricCoefficient (M := M)) ⊗ₜ[simpleFixed cs i] n)=n := by
  exact one_smul _ n

 theorem bottHeadReflectedTail_seed (i : I) (l : List I) (n : BottSamelsonModule cs l) :
    bottHeadReflectedTail cs i l ((1 : SymmetricCoefficient (M := M)) ⊗ₜ[simpleFixed cs i] n)=Twist.mk n := by
  change Twist.mk ((coefficientAction cs (cs.simple i)) 1 • n)=Twist.mk n
  rw [map_one,one_smul]

 def bottHeadLocalPair (i : I) (l : List I) (x : W) : BottSamelsonModule cs (i::l) →ₗ[
    SymmetricCoefficient (M := M)]
    (bottStalk cs l x × Twist (coefficientAction cs (cs.simple i)).toRingEquiv
      (bottStalk cs l (cs.simple i*x))) :=
  ((bottStalkProjection cs l x).comp (bottHeadTail cs i l)).prod
    ((twistMap (coefficientAction cs (cs.simple i)).toRingEquiv
      (bottStalkProjection cs l (cs.simple i*x))).comp (bottHeadReflectedTail cs i l))

 theorem bottHeadLocalPair_seed (i : I) (l : List I) (x : W) (n : BottSamelsonModule cs l) :
    bottHeadLocalPair cs i l x ((1 : SymmetricCoefficient (M := M)) ⊗ₜ[simpleFixed cs i] n)=
      (bottStalkProjection cs l x n,Twist.mk (bottStalkProjection cs l (cs.simple i*x) n)) := by
  change ((bottStalkProjection cs l x) (bottHeadTail cs i l _),
    (twistMap (coefficientAction cs (cs.simple i)).toRingEquiv
      (bottStalkProjection cs l (cs.simple i*x))) (bottHeadReflectedTail cs i l _)) = _
  rw [bottHeadTail_seed,bottHeadReflectedTail_seed]
  rfl
end
end KLInvariance.TitsSpace

end


section
namespace KLInvariance
universe ua up uv un
variable {A : Type ua} [CommRing A]
  {P : Type up} [AddCommGroup P] [Module A P]
  {V : Type uv} [AddCommGroup V] [Module A V]
  {N : Type un} [AddCommGroup N] [Module A N]
 theorem linearMap_mem_of_coordinates (S : Submodule A P)
    (F : P →ₗ[A] V) (G : N →ₗ[A] P) (E : N →ₗ[A] V)
    (hF : Function.Injective F) (heq : F.comp G = E)
    (hrange : LinearMap.range E ≤ LinearMap.range (F.comp S.subtype)) (n : N) : G n ∈ S := by
  obtain ⟨p,hp⟩ := hrange (show E n ∈ LinearMap.range E from ⟨n,rfl⟩)
  have he : (p : P) = G n := hF (hp.trans (LinearMap.congr_fun heq n).symm)
  exact he ▸ p.property
end KLInvariance

end


section

namespace KLInvariance.TitsSpace
open Module TensorProduct FrobeniusDuality ReflectionFrobenius ReflectionPairTranslation
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section
attribute [local instance] restrictedModule restrictedTower restrictedFree restrictedFinite

 theorem bottHeadLocalPair_coordinates (i : I) (l : List I) (x : W) :
    (bottHeadPairCoordinates cs i l x).comp (bottHeadLocalPair cs i l x) =
      bottWeightProjection cs (i::l) x := by
  apply bottTensor_maps_eq cs i l
  intro n
  change bottHeadPairCoordinates cs i l x (bottHeadLocalPair cs i l x _) = _
  rw [bottHeadLocalPair_seed,bottHeadPairCoordinates_seed]

 theorem bottHeadLocalPair_mem (i : I) (l : List I) (x : W)
    (m : BottSamelsonModule cs (i::l)) :
    bottHeadLocalPair cs i l x m ∈ bottHeadPairLattice cs i l x := by
  exact linearMap_mem_of_coordinates (bottHeadPairLattice cs i l x)
    (bottHeadPairCoordinates cs i l x) (bottHeadLocalPair cs i l x)
    (bottWeightProjection cs (i::l) x) (bottHeadPairCoordinates_injective cs i l x)
    (bottHeadLocalPair_coordinates cs i l x) (bottHeadPair_range cs i l x) m

 theorem bottHeadLocalPair_zero_iff (i : I) (l : List I) (x : W)
    (m : BottSamelsonModule cs (i::l)) :
    bottStalkProjection cs (i::l) x m=0 ↔ bottHeadLocalPair cs i l x m=0 := by
  constructor
  · intro h
    apply bottHeadPairCoordinates_injective cs i l x
    rw [map_zero]
    have hh := congrArg Subtype.val h
    change bottWeightProjection cs (i::l) x m=0 at hh
    exact (LinearMap.congr_fun (bottHeadLocalPair_coordinates cs i l x) m).trans hh
  · intro h
    apply Subtype.ext
    change bottWeightProjection cs (i::l) x m=0
    rw [← LinearMap.congr_fun (bottHeadLocalPair_coordinates cs i l x) m]
    change bottHeadPairCoordinates cs i l x (bottHeadLocalPair cs i l x m)=0
    rw [h,map_zero]

 theorem bottHeadLocalPair_value (i : I) (l : List I) (x : W)
    (m : BottSamelsonModule cs (i::l)) :
    bottHeadLocalPair cs i l x m =
      (bottStalkProjection cs l x (bottHeadTail cs i l m),
       Twist.mk (bottStalkProjection cs l (cs.simple i*x) (bottHeadReflectedTail cs i l m).val)) := rfl

 theorem bottHeadLocalPair_toStalk (i : I) (l : List I) (x : W)
    (m : BottSamelsonModule cs (i::l)) :
    bottHeadPairToStalk cs i l x ⟨bottHeadLocalPair cs i l x m,bottHeadLocalPair_mem cs i l x m⟩ =
      bottStalkProjection cs (i::l) x m := by
  apply Subtype.ext
  exact LinearMap.congr_fun (bottHeadLocalPair_coordinates cs i l x) m

 theorem bottHeadStalk_divisible_of_pair (i : I) (l : List I) (x : W)
    (m : BottSamelsonModule cs (i::l)) (β : SymmetricCoefficient (M := M))
    (p : bottStalk cs l x × Twist (coefficientAction cs (cs.simple i)).toRingEquiv
      (bottStalk cs l (cs.simple i*x)))
    (hm : bottHeadLocalPair cs i l x m=β • p) (hp : p ∈ bottHeadPairLattice cs i l x) :
    ∃ z : bottStalk cs (i::l) x, bottStalkProjection cs (i::l) x m=β • z := by
  let z : bottHeadPairLattice cs i l x := ⟨p,hp⟩
  refine ⟨bottHeadPairToStalk cs i l x z,?_⟩
  have he : (⟨bottHeadLocalPair cs i l x m,bottHeadLocalPair_mem cs i l x m⟩ :
      bottHeadPairLattice cs i l x) = β • z := Subtype.ext hm
  calc
    bottStalkProjection cs (i::l) x m =
        bottHeadPairToStalk cs i l x ⟨bottHeadLocalPair cs i l x m,bottHeadLocalPair_mem cs i l x m⟩ :=
      (bottHeadLocalPair_toStalk cs i l x m).symm
    _ = bottHeadPairToStalk cs i l x (β • z) := congrArg (bottHeadPairToStalk cs i l x) he
    _ = β • bottHeadPairToStalk cs i l x z := map_smul _ _ _

end
end KLInvariance.TitsSpace

end


section

namespace KLInvariance.FiniteFreeScalar
universe ur um un ui
variable {R : Type ur} [CommRing R]
  {M : Type um} [AddCommGroup M] [Module R M]
  {ι : Type ui} [Fintype ι] (b : Module.Basis ι R M)


 theorem exists_smul_iff (r : R) (m : M) :
    (∃ n, r • n = m) ↔ ∀ i, r ∣ b.equivFun m i := by
  classical
  constructor
  · rintro ⟨n,rfl⟩ i
    exact ⟨b.equivFun n i, by simp⟩
  · intro h
    choose n hn using h
    refine ⟨b.equivFun.symm n,b.equivFun.injective ?_⟩
    ext i
    simp only [map_smul,LinearEquiv.apply_symm_apply,Pi.smul_apply,smul_eq_mul]
    exact (hn i).symm

include b in
 theorem exists_prod_smul [DecompositionMonoid R] {J : Type*} (s : Finset J) (r : J → R)
    (hrel : (s : Set J).Pairwise (Function.onFun IsRelPrime r)) (m : M)
    (h : ∀ j ∈ s, ∃ n, r j • n = m) : ∃ n, (∏ j ∈ s, r j) • n = m := by
  apply (exists_smul_iff b _ m).mpr
  intro i
  apply Finset.prod_dvd_of_isRelPrime hrel
  intro j hj
  exact (exists_smul_iff b _ _).mp (h j hj) i

include b in


 theorem scalar_quotient_regular
    {N : Type un} [AddCommGroup N] [Module R N]
    (q : M →ₗ[R] N) (hq : Function.Surjective q)
    (a r : R) (ha : Prime a) (hr : ¬ a ∣ r)
    (hker : ∀ m, q m = 0 ↔ ∃ n, m=a • n) :
    Function.Injective (fun v : N => r • v) := by
  suffices hh : ∀ v : N, r • v = 0 → v = 0 by
    intro v w hvw
    change r • v = r • w at hvw
    have hv : r • (v-w) = 0 := by rw [smul_sub,hvw,sub_self]
    exact sub_eq_zero.mp (hh _ hv)
  intro v hv
  obtain ⟨m,rfl⟩ := hq v
  have h0 : q (r • m) = 0 := by simpa only [map_smul] using hv
  obtain ⟨n,hn⟩ := (hker _).mp h0
  have hdiv : ∀ i, a ∣ b.equivFun m i := by
    intro i
    have hc := congrArg (fun z => b.equivFun z i) hn
    simp only [map_smul,Pi.smul_apply,smul_eq_mul] at hc
    apply (ha.dvd_mul.mp ?_).resolve_left hr
    exact ⟨b.equivFun n i,hc⟩
  obtain ⟨z,hz⟩ := (exists_smul_iff b a m).mpr hdiv
  exact (hker m).mpr ⟨z,hz.symm⟩

end KLInvariance.FiniteFreeScalar

end


section

/-! Intermediate standard-filtration predicates on the genuine tensor word.
These are proved by word induction; they are not main-theorem assumptions. -/
namespace KLInvariance.TitsSpace
open Module ReflectionFrobenius
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 def BottKernelExact (l : List I) : Prop :=
  ∀ (x t : W) (a : I → ℝ), Represents M cs t a →
    cs.length x < cs.length (t*x) →
    ∀ m : BottSamelsonModule cs l, bottStalkProjection cs l x m=0 →
      ∃ z : bottStalk cs l (t*x), bottStalkProjection cs l (t*x) m=
        SymmetricAlgebra.ι ℝ (Extended M) (embed M a) • z

 theorem simple_represents (i : I) : Represents M cs (cs.simple i) (root i) := by
  refine ⟨1,i,?_,?_⟩
  · simp
  · simp

 theorem represents_polynomial_prime {t : W} {a : I → ℝ} (ha : Represents M cs t a) :
    Prime (SymmetricAlgebra.ι ℝ (Extended M) (embed M a)) := by
  apply EdgeAlgebra.symmetric_ι_prime
  intro h
  exact ha.isRoot.ne_zero (congrArg Prod.fst h)

 theorem represents_polynomial_not_dvd {t s : W} {a b : I → ℝ}
    (ha : Represents M cs t a) (hb : Represents M cs s b) (hne : t≠s) :
    ¬ SymmetricAlgebra.ι ℝ (Extended M) (embed M a) ∣
      SymmetricAlgebra.ι ℝ (Extended M) (embed M b) := by
  rw [EdgeAlgebra.symmetric_ι_dvd_iff]
  intro h
  have hi := hb.extended_independent_of_ne ha (Ne.symm hne)
  obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp h
  exact (linearIndependent_fin2.mp hi).2 r hr

 theorem bottStalk_smul_injective (l : List I) (x : W)
    {r : SymmetricCoefficient (M := M)} (hr : r≠0) :
    Function.Injective (fun z : bottStalk cs l x => r • z) :=
  smul_right_injective (bottStalk cs l x) hr

 instance bottStalkFinite (l : List I) (x : W) :
    Module.Finite (SymmetricCoefficient (M := M)) (bottStalk cs l x) :=
  Module.Finite.of_surjective (bottStalkProjection cs l x) (bottStalkProjection_surjective cs l x)

 theorem bottReflectionEdge_annihilated (l : List I) (x t : W) {a : I → ℝ}
    (ha : Represents M cs t a)
    (z : PairProjection.Edge (bottStalkProjection cs l x) (bottStalkProjection cs l (t*x))) :
    SymmetricAlgebra.ι ℝ (Extended M) (embed M a) • z=0 := by
  obtain ⟨p,hp⟩ := reflectionCoefficient_difference cs ha x
  rw [← hp]
  exact PairProjection.difference_annihilates _ _
    (bottStalkProjection_surjective cs _ _) (bottStalkProjection_surjective cs _ _)
    (bottSamelsonRight cs l p) _ _
    (bottStalkProjection_right cs _ _ p) (bottStalkProjection_right cs _ _ p) z

 theorem BottKernelExact.upper_kernel {l : List I} (H : BottKernelExact cs l)
    (x t : W) {a : I → ℝ} (ha : Represents M cs t a)
    (hlt : cs.length x < cs.length (t*x)) (z : bottStalk cs l (t*x)) :
    PairProjection.upper (bottStalkProjection cs l x) (bottStalkProjection cs l (t*x)) z=0 ↔
      ∃ w, z=SymmetricAlgebra.ι ℝ (Extended M) (embed M a) • w :=
  PairProjection.upper_kernel_of_divisibility _ _ _ (H x t a ha hlt)
    (bottReflectionEdge_annihilated cs l x t ha) z

 theorem BottKernelExact.kernel_iff {l : List I} (H : BottKernelExact cs l)
    (x t : W) {a : I → ℝ} (ha : Represents M cs t a)
    (hlt : cs.length x < cs.length (t*x)) (z : bottStalk cs l (t*x)) :
    (∃ m, bottStalkProjection cs l x m=0 ∧ bottStalkProjection cs l (t*x) m=z) ↔
      ∃ w, z=SymmetricAlgebra.ι ℝ (Extended M) (embed M a) • w := by
  rw [← PairProjection.kernel_upper]
  exact H.upper_kernel cs x t ha hlt z

 theorem BottKernelExact.kernel_iff_of_mul {l : List I} (H : BottKernelExact cs l)
    (x y t : W) {a : I → ℝ} (ha : Represents M cs t a) (hxy : t*x=y)
    (hlt : cs.length x < cs.length y) (z : bottStalk cs l y) :
    (∃ m, bottStalkProjection cs l x m=0 ∧ bottStalkProjection cs l y m=z) ↔
      ∃ w, z=SymmetricAlgebra.ι ℝ (Extended M) (embed M a) • w := by
  subst y
  exact H.kernel_iff cs x t ha hlt z

 theorem BottKernelExact.projection_of_mul {l : List I} (H : BottKernelExact cs l)
    (x y t : W) {a : I → ℝ} (ha : Represents M cs t a) (hxy : t*x=y)
    (hlt : cs.length x < cs.length y) (m : BottSamelsonModule cs l)
    (hm : bottStalkProjection cs l x m=0) :
    ∃ z : bottStalk cs l y, bottStalkProjection cs l y m=
      SymmetricAlgebra.ι ℝ (Extended M) (embed M a) • z := by
  subst y
  exact H x t a ha hlt m hm

end
end KLInvariance.TitsSpace

end


section

namespace KLInvariance.TitsSpace
open Module ReflectionFrobenius ReflectionPairTranslation
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem bottSimpleEdge_regular (i : I) (l : List I)
    (H : BottKernelExact cs l)
    (F : ∀ x : W, Module.Free (SymmetricCoefficient (M := M)) (bottStalk cs l x))
    (x : W) (β : SymmetricCoefficient (M := M)) (hβ : ¬simpleRootPolynomial (M := M) i ∣ β) :
    Function.Injective (fun e : PairProjection.Edge (bottStalkProjection cs l x)
      (bottStalkProjection cs l (cs.simple i*x)) => β • e) := by
  have hα : Prime (simpleRootPolynomial (M := M) i) :=
    represents_polynomial_prime cs (simple_represents cs i)
  rcases lt_or_gt_of_ne (cs.length_simple_mul_ne x i) with hdesc | hasc
  · let := F x
    apply FiniteFreeScalar.scalar_quotient_regular
      (Module.Free.chooseBasis (SymmetricCoefficient (M := M)) (bottStalk cs l x))
      (PairProjection.lower (bottStalkProjection cs l x) (bottStalkProjection cs l (cs.simple i*x)))
      (PairProjection.lower_surjective _ _ (bottStalkProjection_surjective cs l (cs.simple i*x)))
      (simpleRootPolynomial (M := M) i) β hα hβ
    intro z
    rw [PairProjection.kernel_lower]
    have hh := H.kernel_iff_of_mul cs (cs.simple i*x) x (cs.simple i)
      (simple_represents cs i) (cs.simple_mul_simple_cancel_left i) hdesc z
    simpa only [and_comm,simpleRootPolynomial,extendedRoot] using hh
  · let := F (cs.simple i*x)
    exact FiniteFreeScalar.scalar_quotient_regular
      (Module.Free.chooseBasis (SymmetricCoefficient (M := M)) (bottStalk cs l (cs.simple i*x)))
      (PairProjection.upper (bottStalkProjection cs l x) (bottStalkProjection cs l (cs.simple i*x)))
      (PairProjection.upper_surjective _ _ (bottStalkProjection_surjective cs l x))
      (simpleRootPolynomial (M := M) i) β hα hβ
      (H.upper_kernel cs x (cs.simple i) (simple_represents cs i) hasc)

 theorem bottHeadPairLattice_saturated (i : I) (l : List I)
    (H : BottKernelExact cs l)
    (F : ∀ x : W, Module.Free (SymmetricCoefficient (M := M)) (bottStalk cs l x))
    (x : W) (β : SymmetricCoefficient (M := M)) (hβ : ¬simpleRootPolynomial (M := M) i ∣ β)
    (p : bottStalk cs l x × Twist (coefficientAction cs (cs.simple i)).toRingEquiv
      (bottStalk cs l (cs.simple i*x))) :
    β • p ∈ bottHeadPairLattice cs i l x ↔ p ∈ bottHeadPairLattice cs i l x :=
  lattice_saturated (bottStalkProjection cs l x) (bottStalkProjection cs l (cs.simple i*x))
    (coefficientAction cs (cs.simple i)).toRingEquiv (simpleRootPolynomial (M := M) i)
    (simpleReverseDivisibility cs i) (bottSimpleEdge_kernel_inclusion cs i l x)
    β (bottSimpleEdge_annihilated cs i l x) (bottSimpleEdge_regular cs i l H F x β hβ) p

end
end KLInvariance.TitsSpace

end


section


namespace KLInvariance.TitsSpace
open Module ReflectionFrobenius ReflectionPairTranslation
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem bottHeadStalk_divisible (i : I) (l : List I)
    (H : BottKernelExact cs l)
    (F : ∀ x : W, Module.Free (SymmetricCoefficient (M := M)) (bottStalk cs l x))
    (x : W) (m : BottSamelsonModule cs (i::l)) (β : SymmetricCoefficient (M := M))
    (hβ : ¬simpleRootPolynomial (M := M) i ∣ β)
    (p : bottStalk cs l x × Twist (coefficientAction cs (cs.simple i)).toRingEquiv
      (bottStalk cs l (cs.simple i*x)))
    (hm : bottHeadLocalPair cs i l x m=β • p) :
    ∃ z : bottStalk cs (i::l) x, bottStalkProjection cs (i::l) x m=β • z := by
  have hp := bottHeadLocalPair_mem cs i l x m
  have hp' : β • p ∈ bottHeadPairLattice cs i l x := hm ▸ hp
  exact bottHeadStalk_divisible_of_pair cs i l x m β p hm
    ((bottHeadPairLattice_saturated cs i l H F x β hβ p).mp hp')

 theorem bottKernelExact_cons_nonhead (i : I) (l : List I)
    (H : BottKernelExact cs l)
    (F : ∀ x : W, Module.Free (SymmetricCoefficient (M := M)) (bottStalk cs l x))
    (x t : W) (a : I → ℝ) (ha : Represents M cs t a)
    (hlt : cs.length x < cs.length (t*x)) (hts : t≠cs.simple i)
    (m : BottSamelsonModule cs (i::l)) (hm : bottStalkProjection cs (i::l) x m=0) :
    ∃ z : bottStalk cs (i::l) (t*x), bottStalkProjection cs (i::l) (t*x) m=
      SymmetricAlgebra.ι ℝ (Extended M) (embed M a) • z := by
  have he : t*x≠cs.simple i*x := fun h => hts (mul_right_cancel h)
  have hstep : BruhatStep cs x (t*x) := ⟨hlt,t,ha.isReflection,rfl⟩
  have hstep' := bruhatStep_simple_mul cs hstep i he
  have hconj : (cs.simple i*t*(cs.simple i)⁻¹)*(cs.simple i*x)=cs.simple i*(t*x) := by group
  have hzero := (bottHeadLocalPair_zero_iff cs i l x m).mp hm
  have hμ : bottStalkProjection cs l x (bottHeadTail cs i l m)=0 := congrArg Prod.fst hzero
  have hν : bottStalkProjection cs l (cs.simple i*x) (bottHeadReflectedTail cs i l m).val=0 :=
    congrArg (fun p => p.2.val) hzero
  obtain ⟨p,hp⟩ := H x t a ha hlt (bottHeadTail cs i l m) hμ
  obtain ⟨q,hq⟩ := H.projection_of_mul cs (cs.simple i*x) (cs.simple i*(t*x))
    (cs.simple i*t*(cs.simple i)⁻¹) (ha.act (cs.simple i)) hconj hstep'.1
    (bottHeadReflectedTail cs i l m).val hν
  let β : SymmetricCoefficient (M := M) := SymmetricAlgebra.ι ℝ (Extended M) (embed M a)
  let p' : bottStalk cs l (t*x) × Twist (coefficientAction cs (cs.simple i)).toRingEquiv
      (bottStalk cs l (cs.simple i*(t*x))) := (p,⟨q⟩)
  have hβ' : coefficientAction cs (cs.simple i) β =
      SymmetricAlgebra.ι ℝ (Extended M) (embed M (action M cs (cs.simple i) a)) := by
    rw [coefficientAction_ι,extendedAction_restrict]
  have heq : bottHeadLocalPair cs i l (t*x) m=β • p' := by
    apply Prod.ext
    · exact hp
    · apply Twist.ext
      change bottStalkProjection cs l (cs.simple i*(t*x))
        (bottHeadReflectedTail cs i l m).val = coefficientAction cs (cs.simple i) β • q
      rw [hβ']
      exact hq
  have hn : ¬simpleRootPolynomial (M := M) i ∣ β :=
    represents_polynomial_not_dvd cs (simple_represents cs i) ha (Ne.symm hts)
  exact bottHeadStalk_divisible cs i l H F (t*x) m β hn p' heq

 theorem bottKernelExact_cons (i : I) (l : List I)
    (H : BottKernelExact cs l)
    (F : ∀ x : W, Module.Free (SymmetricCoefficient (M := M)) (bottStalk cs l x)) :
    BottKernelExact cs (i::l) := by
  intro x t a ha hlt m hm
  by_cases hts : t=cs.simple i
  · subst t
    obtain ⟨z,hz⟩ := bottSimpleWall_kernel_projection cs i l x hm
    rcases ha.unique_up_to_sign (simple_represents cs i) with h|h
    · subst a
      exact ⟨z,hz⟩
    · subst a
      refine ⟨-z,?_⟩
      rw [hz]
      change simpleRootPolynomial (M := M) i • z =
        SymmetricAlgebra.ι ℝ (Extended M) (embed M (-root i)) • (-z)
      have he : embed M (-root i) = -embed M (root i) := by simp [embed]
      have hn : SymmetricAlgebra.ι ℝ (Extended M) (embed M (-root i)) =
          -simpleRootPolynomial (M := M) i := by
        rw [he]
        exact (SymmetricAlgebra.ι ℝ (Extended M)).map_neg _
      rw [hn]
      exact (neg_smul_neg _ z).symm
  · exact bottKernelExact_cons_nonhead cs i l H F x t a ha hlt hts m hm

end
end KLInvariance.TitsSpace

end


section

namespace KLInvariance.ReflectionPairTranslation
universe u v w z
variable {R : Type u} [CommRing R]
  {N : Type v} [AddCommGroup N] [Module R N]
  {X : Type w} [AddCommGroup X] [Module R X]
  {Y : Type z} [AddCommGroup Y] [Module R Y]
  (f : N →ₗ[R] X) (g : N →ₗ[R] Y) (τ : R ≃+* R) (α : R)
  (hdiv : ∀ r : R, α ∣ τ r-r)
  (hinc : ∀ y : Y, ∃ n : N, f n=0 ∧ g n=α • y)
  (hker : ∀ x : X, (∃ n : N, f n=x ∧ g n=0) ↔ ∃ z : X, x=α • z)

 def right : lattice f g τ α hdiv hinc →ₗ[R] Twist τ Y :=
  (LinearMap.snd R X (Twist τ Y)).comp (lattice f g τ α hdiv hinc).subtype

 theorem right_surjective (hg : Function.Surjective g) :
    Function.Surjective (right f g τ α hdiv hinc) := by
  intro y
  obtain ⟨n,hn⟩ := hg y.val
  exact ⟨⟨(f n,y),n,rfl,hn⟩,rfl⟩

 def rightKernelMap : X →ₗ[R] LinearMap.ker (right f g τ α hdiv hinc) where
  toFun x := ⟨⟨(α • x,⟨0⟩),(hker (α • x)).mpr ⟨x,rfl⟩⟩,rfl⟩
  map_add' x y := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact smul_add α x y
    · apply Twist.ext
      exact (zero_add (0 : Y)).symm
  map_smul' r x := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact smul_comm α r x
    · apply Twist.ext
      exact (smul_zero _).symm

 theorem rightKernelMap_surjective :
    Function.Surjective (rightKernelMap f g τ α hdiv hinc hker) := by
  rintro ⟨⟨⟨x,y⟩,n,hn,hn'⟩,hy⟩
  have hy' : y.val=0 := congrArg Twist.val hy
  obtain ⟨z,hz⟩ := (hker x).mp ⟨n,hn,hn'.trans hy'⟩
  refine ⟨z,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext hz.symm (Twist.ext hy'.symm)

 theorem rightKernelMap_injective (hinj : Function.Injective (fun x : X => α • x)) :
    Function.Injective (rightKernelMap f g τ α hdiv hinc hker) := by
  intro x y h
  exact hinj (congrArg (fun p => p.val.val.1) h)

 noncomputable def rightKernelEquiv (hinj : Function.Injective (fun x : X => α • x)) :
    X ≃ₗ[R] LinearMap.ker (right f g τ α hdiv hinc) :=
  LinearEquiv.ofBijective (rightKernelMap f g τ α hdiv hinc hker)
    ⟨rightKernelMap_injective f g τ α hdiv hinc hker hinj,
      rightKernelMap_surjective f g τ α hdiv hinc hker⟩

 include hker in
 theorem lattice_free_right (hg : Function.Surjective g)
    (hinj : Function.Injective (fun x : X => α • x))
    [Module.Free R X] [Module.Free R Y] :
    Module.Free R (lattice f g τ α hdiv hinc) := by
  let : Module.Free R (LinearMap.ker (right f g τ α hdiv hinc)) :=
    Module.Free.of_equiv (rightKernelEquiv f g τ α hdiv hinc hker hinj)
  exact free_of_surjective_of_ker_free (right f g τ α hdiv hinc)
    (right_surjective f g τ α hdiv hinc hg)
end KLInvariance.ReflectionPairTranslation

end


section

namespace KLInvariance.TitsSpace
open Module ReflectionFrobenius ReflectionPairTranslation
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem bottStalk_free_cons (i : I) (l : List I)
    (H : BottKernelExact cs l)
    (F : ∀ x : W, Module.Free (SymmetricCoefficient (M := M)) (bottStalk cs l x))
    (x : W) : Module.Free (SymmetricCoefficient (M := M)) (bottStalk cs (i::l) x) := by
  let := F x
  let := F (cs.simple i*x)
  have hα : simpleRootPolynomial (M := M) i ≠ 0 :=
    (represents_polynomial_prime cs (simple_represents cs i)).ne_zero
  have hlattice : Module.Free (SymmetricCoefficient (M := M)) (bottHeadPairLattice cs i l x) := by
    rcases lt_or_gt_of_ne (cs.length_simple_mul_ne x i) with hdesc | hasc
    · apply lattice_free_right
        (bottStalkProjection cs l x) (bottStalkProjection cs l (cs.simple i*x))
        (coefficientAction cs (cs.simple i)).toRingEquiv (simpleRootPolynomial (M := M) i)
        (simpleReverseDivisibility cs i) (bottSimpleEdge_kernel_inclusion cs i l x)
      · intro z
        have hh := H.kernel_iff_of_mul cs (cs.simple i*x) x (cs.simple i)
          (simple_represents cs i) (cs.simple_mul_simple_cancel_left i) hdesc z
        simpa only [and_comm,simpleRootPolynomial,extendedRoot] using hh
      · exact bottStalkProjection_surjective cs l (cs.simple i*x)
      · exact bottStalk_smul_injective cs l x hα
    · exact lattice_free (bottStalkProjection cs l x) (bottStalkProjection cs l (cs.simple i*x))
        (coefficientAction cs (cs.simple i)).toRingEquiv (simpleRootPolynomial (M := M) i)
        (simpleReverseDivisibility cs i) (bottSimpleEdge_kernel_inclusion cs i l x)
        (H.kernel_iff cs x (cs.simple i) (simple_represents cs i) hasc)
        (bottStalkProjection_surjective cs l x)
        (bottStalk_smul_injective cs l (cs.simple i*x) hα)
  let := hlattice
  exact Module.Free.of_equiv (bottHeadPairEquiv cs i l x)

 theorem bottStalk_nil_subsingleton (x : W) (hx : x≠1) : Subsingleton (bottStalk cs [] x) := by
  constructor
  intro p q
  apply Subtype.ext
  funext e
  exact False.elim (hx e.property.symm)

 theorem bottStalk_nil_free (x : W) :
    Module.Free (SymmetricCoefficient (M := M)) (bottStalk cs [] x) := by
  by_cases hx : x=1
  · subst x
    exact Module.Free.of_equiv (bottTopStalkEquiv cs [] (by simp [CoxeterSystem.IsReduced])).symm
  · let := bottStalk_nil_subsingleton cs x hx
    infer_instance

 theorem bottKernelExact_nil : BottKernelExact cs [] := by
  intro x t a ha hlt m hm
  have hx : t*x≠1 := by
    intro h
    rw [h] at hlt
    rw [cs.length_one] at hlt
    exact Nat.not_lt_zero _ hlt
  let := bottStalk_nil_subsingleton cs (t*x) hx
  exact ⟨0,Subsingleton.elim _ _⟩

end
end KLInvariance.TitsSpace

end


section

/-! Pair-projection edges of actual finite graded modules. The hypotheses say
only that the two actual weight projections are homogeneous and surjective. -/
namespace KLInvariance.Graded.ModuleData
open PairProjection
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {M X Y : ModuleData.{uk,ua,um} 𝓐}
  (f : Hom M X) (g : Hom M Y)
noncomputable section

 theorem pairLower_kernel_homogeneous (n : ℤ) (z : X)
    (hz : lower f.map g.map z=0) :
    lower f.map g.map (component X.piece n z)=0 := by
  obtain ⟨m,hm,hy⟩ := (kernel_lower f.map g.map z).mp hz
  apply (kernel_lower f.map g.map _).mpr
  refine ⟨component M.piece n m,?_,?_⟩
  · rw [← f.component,hm]
  · rw [← g.component,hy,map_zero]

 def pairEdgePiece (n : ℤ) : Submodule k (Edge f.map g.map) :=
  (X.piece n).map ((lower f.map g.map).restrictScalars k)

 def pairEdge (hg : Function.Surjective g.map) : ModuleData.{uk,ua,um} 𝓐 where
  obj := ModuleCat.of A (Edge f.map g.map)
  kModule := inferInstance
  tower := inferInstance
  piece := pairEdgePiece f g
  decomposition := (image_isInternal X.piece ((lower f.map g.map).restrictScalars k)
    (lower_surjective f.map g.map hg) (pairLower_kernel_homogeneous f g)).chooseDecomposition
  graded := ⟨by
    rintro i j a z ha ⟨w,hw,rfl⟩
    exact ⟨a • w,SetLike.GradedSMul.smul_mem ha hw,map_smul (lower f.map g.map) a w⟩⟩
  nonneg := by
    intro n hn
    unfold pairEdgePiece
    rw [X.nonneg n hn,Submodule.map_bot]
  finite := Module.Finite.of_surjective (lower f.map g.map) (lower_surjective f.map g.map hg)

 def pairLower (hg : Function.Surjective g.map) : Hom X (pairEdge f g hg) where
  map := lower f.map g.map
  graded := fun _ z hz => ⟨z,hz,rfl⟩

 theorem Hom.homogeneous_lift (hg : Function.Surjective g.map) (n : ℤ)
    (y : Y) (hy : y ∈ Y.piece n) : ∃ m : M, m ∈ M.piece n ∧ g.map m=y := by
  obtain ⟨m,hm⟩ := hg y
  refine ⟨Graded.component M.piece n m,(DirectSum.decompose M.piece m n).property,?_⟩
  rw [← g.component,hm]
  exact DirectSum.decompose_of_mem_same Y.piece hy

 def pairUpper (hg : Function.Surjective g.map) : Hom Y (pairEdge f g hg) where
  map := upper f.map g.map
  graded := by
    intro n y hy
    obtain ⟨m,hm,rfl⟩ := g.homogeneous_lift hg n y hy
    exact ⟨f.map m,f.graded n m hm,compatible f.map g.map m⟩

end
end KLInvariance.Graded.ModuleData

end


section

/-! The genuine projection WORD sheaf with its nonnegative grading and finite
integral stalk/edge modules. No free-stalk, flabbiness, or KL character claim
is smuggled into the grading. The universe here contains both the finite
Coxeter matrix and its standard Coxeter group, as needed by the main reduction. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

omit [Fintype σ] in
 theorem bottStalkPiece_negative (l : List I) (x : W) (n : ℤ) (hn : n<0) :
    bottStalkPiece cs basis l x n=⊥ := by
  apply subPiece_eq_bot
  exact piPiece_eq_bot (fun _ => symmetricGrading basis) n
    (fun _ => symmetricGrading_negative basis n hn)

 def bottStalkData (l : List I) (x : W) : ModuleData.{0,u,u} (symmetricGrading basis) where
  obj := ModuleCat.of _ (bottStalk cs l x)
  kModule := inferInstance
  tower := inferInstance
  piece := bottStalkPiece cs basis l x
  decomposition := inferInstance
  graded := inferInstance
  nonneg := bottStalkPiece_negative cs basis l x
  finite := Module.Finite.of_surjective (bottStalkProjection cs l x)
    (bottStalkProjection_surjective cs l x)

 theorem bottPiece_negative (l : List I) (n : ℤ) (hn : n<0) :
    bottPiece cs basis l n=⊥ := by
  apply bot_unique
  intro m hm
  change m=0
  apply bottEvaluation_injective cs l
  funext e
  have h := bottEvaluation_homogeneous cs basis l e n m hm
  rw [symmetricGrading_negative basis n hn,Submodule.mem_bot] at h
  exact h.trans (map_zero (bottEvaluation cs l e)).symm

 def bottWordData (l : List I) : ModuleData.{0,u,u} (symmetricGrading basis) where
  obj := ModuleCat.of _ (BottSamelsonModule cs l)
  kModule := inferInstance
  tower := inferInstance
  piece := bottPiece cs basis l
  decomposition := inferInstance
  graded := inferInstance
  nonneg := bottPiece_negative cs basis l
  finite := inferInstance

 def bottStalkHom (l : List I) (x : W) :
    ModuleData.Hom (bottWordData cs basis l) (bottStalkData cs basis l x) where
  map := bottStalkProjection cs l x
  graded := bottStalkProjection_homogeneous cs basis l x

 theorem bottStalkHom_surjective (l : List I) (x : W) :
    Function.Surjective (bottStalkHom cs basis l x).map :=
  bottStalkProjection_surjective cs l x

 def bottEdgeData (l : List I) (x y : W) : ModuleData.{0,u,u} (symmetricGrading basis) :=
  ModuleData.pairEdge (bottStalkHom cs basis l x) (bottStalkHom cs basis l y)
    (bottStalkHom_surjective cs basis l y)

 def bottLowerHom (l : List I) (x y : W) :
    ModuleData.Hom (bottStalkData cs basis l x) (bottEdgeData cs basis l x y) :=
  ModuleData.pairLower (bottStalkHom cs basis l x) (bottStalkHom cs basis l y)
    (bottStalkHom_surjective cs basis l y)

 def bottUpperHom (l : List I) (x y : W) :
    ModuleData.Hom (bottStalkData cs basis l y) (bottEdgeData cs basis l x y) :=
  ModuleData.pairUpper (bottStalkHom cs basis l x) (bottStalkHom cs basis l y)
    (bottStalkHom_surjective cs basis l y)

 def bottGradedProjectionSheaf (l : List I) (u b : W) :
    GradedSheaf (𝓐 := symmetricGrading basis) (graph cs u b) where
  vertex x := bottStalkData cs basis l x.val
  edge e := bottEdgeData cs basis l (source cs u b e).val (target cs u b e).val
  lower e := bottLowerHom cs basis l (source cs u b e).val (target cs u b e).val
  upper e := bottUpperHom cs basis l (source cs u b e).val (target cs u b e).val

 theorem bottGradedProjectionSheaf_forget (l : List I) (u b : W) :
    (bottGradedProjectionSheaf cs basis l u b).forget=bottProjectionSheaf cs l u b := rfl

end
end KLInvariance.TitsSpace

end


section

/-! Unconditional integral free stalks and exact oriented edge kernels for
all tensor words. These are the local parts of BMP recognition; flabbiness
and the KL character are not asserted here. -/
namespace KLInvariance.TitsSpace
open Module MomentGraph BruhatGraph
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem bottStandardStalks (l : List I) :
    BottKernelExact cs l ∧ ∀ x : W,
      Module.Free (SymmetricCoefficient (M := M)) (bottStalk cs l x) := by
  induction l with
  | nil => exact ⟨bottKernelExact_nil cs,bottStalk_nil_free cs⟩
  | cons i l h => exact ⟨bottKernelExact_cons cs i l h.1 h.2,
      bottStalk_free_cons cs i l h.1 h.2⟩

 theorem bottKernelExact (l : List I) : BottKernelExact cs l := (bottStandardStalks cs l).1

 instance bottStalkFree (l : List I) (x : W) :
    Module.Free (SymmetricCoefficient (M := M)) (bottStalk cs l x) :=
  (bottStandardStalks cs l).2 x

 theorem bottProjectionSheaf_upper_kernel (l : List I) (u b : W) (e : Edge cs u b)
    {a : I → ℝ} (ha : Represents M cs (label cs u b e) a)
    (z : (bottProjectionSheaf cs l u b).vertex (target cs u b e)) :
    (bottProjectionSheaf cs l u b).upper e z=0 ↔
      ∃ w, z=SymmetricAlgebra.ι ℝ (Extended M) (embed M a) • w := by
  change PairProjection.upper (bottStalkProjection cs l (source cs u b e).val)
      (bottStalkProjection cs l (target cs u b e).val) z=0 ↔ _
  exact (PairProjection.kernel_upper _ _ z).trans
    ((bottKernelExact cs l).kernel_iff_of_mul cs _ _ _ ha
      (label_mul_source cs u b e) e.property.1 z)

end
end KLInvariance.TitsSpace

end


section

/-! Transport of actual linear-map kernels along a source isomorphism. -/
namespace KLInvariance
universe ur um un up
variable {R : Type ur} [Ring R]
  {M : Type um} [AddCommGroup M] [Module R M]
  {N : Type un} [AddCommGroup N] [Module R N]
  {P : Type up} [AddCommGroup P] [Module R P]

def kernelSourceEquiv (f : M →ₗ[R] P) (e : M ≃ₗ[R] N) :
    LinearMap.ker f ≃ₗ[R] LinearMap.ker (f.comp e.symm.toLinearMap) where
  toFun x := ⟨e x.val,by simpa only [LinearMap.mem_ker,LinearMap.comp_apply,
    LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply] using x.property⟩
  invFun y := ⟨e.symm y.val,y.property⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv y := Subtype.ext (e.apply_symm_apply y.val)
  map_add' x y := Subtype.ext (map_add e x.val y.val)
  map_smul' r x := Subtype.ext (map_smul e r x.val)

end KLInvariance

end


section

/-! The actual ascent short exact sequence of word stalks has kernel the
upper tail stalk shifted by one. This is the degree-one Hecke normalization. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded ReflectionPairTranslation
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 def bottHeadKernelEquiv (i : I) (l : List I) (x : W)
    (h : cs.length x<cs.length (cs.simple i*x)) :
    bottStalk cs l (cs.simple i*x) ≃ₗ[ℝ] LinearMap.ker (bottHeadLeft cs i l x) :=
  (Twist.scalarEquiv (coefficientAction cs (cs.simple i)) _).symm.trans
    (((kernelEquiv (bottStalkProjection cs l x) (bottStalkProjection cs l (cs.simple i*x))
      (coefficientAction cs (cs.simple i)).toRingEquiv (simpleRootPolynomial (M := M) i)
      (simpleReverseDivisibility cs i) (bottSimpleEdge_kernel_inclusion cs i l x)
      ((bottKernelExact cs l).kernel_iff cs x (cs.simple i) (simple_represents cs i) h)
      (bottStalk_smul_injective cs l (cs.simple i*x) (simpleRootPolynomial_ne_zero i))).trans
      (kernelSourceEquiv _ (bottHeadPairEquiv cs i l x))).restrictScalars ℝ)

 theorem bottHeadKernelEquiv_eval (i : I) (l : List I) (x : W)
    (h : cs.length x<cs.length (cs.simple i*x))
    (y : bottStalk cs l (cs.simple i*x))
    (e : {e : BottIndex (i::l) // bottWeight cs (i::l) e=x}) :
    (bottHeadKernelEquiv cs i l x h y).val.val e=
      if he : e.val.1=0 then 0 else coefficientAction cs (cs.simple i)
        (simpleRootPolynomial (M := M) i * y.val ⟨e.val.2,bottWeight_tail_one cs i l x e he⟩) := rfl

 def bottHeadKernelPiece (i : I) (l : List I) (x : W) :
    ℤ → Submodule ℝ (LinearMap.ker (bottHeadLeft cs i l x)) :=
  subPiece (bottStalkPiece cs basis (i::l) x) (LinearMap.ker (bottHeadLeft cs i l x))

 theorem bottHeadLeft_kernel_homogeneous (i : I) (l : List I) (x : W) :
    ∀ n m, m ∈ LinearMap.ker (bottHeadLeft cs i l x) →
      component (bottStalkPiece cs basis (i::l) x) n m ∈ LinearMap.ker (bottHeadLeft cs i l x) := by
  intro n m hm
  have h := map_component (bottStalkPiece cs basis (i::l) x) (bottStalkPiece cs basis l x)
    (bottHeadLeft cs i l x) 0 (by
      intro j z hz
      simpa only [add_zero] using (bottHeadLeft_homogeneous cs basis i l x j z hz)) n m
  change bottHeadLeft cs i l x _=0
  rw [sub_zero] at h
  rw [← h,LinearMap.mem_ker.mp hm,map_zero]

 instance bottHeadKernelPiece_decomposition (i : I) (l : List I) (x : W) :
    DirectSum.Decomposition (bottHeadKernelPiece cs basis i l x) :=
  (sub_isInternal (bottStalkPiece cs basis (i::l) x) (LinearMap.ker (bottHeadLeft cs i l x))
    (bottHeadLeft_kernel_homogeneous cs basis i l x)).chooseDecomposition

 theorem bottHeadKernelEquiv_homogeneous (i : I) (l : List I) (x : W)
    (h : cs.length x<cs.length (cs.simple i*x)) (n : ℤ)
    (y : bottStalk cs l (cs.simple i*x)) (hy : y ∈ bottStalkPiece cs basis l (cs.simple i*x) n) :
    bottHeadKernelEquiv cs i l x h y ∈ bottHeadKernelPiece cs basis i l x (n+1) := by
  intro e _
  change (bottHeadKernelEquiv cs i l x h y).val.val e ∈ symmetricGrading basis (n+1)
  rw [bottHeadKernelEquiv_eval]
  split_ifs with he
  · exact Submodule.zero_mem _
  · apply coefficientAction_homogeneous cs basis
    have hy' : y.val ⟨e.val.2,bottWeight_tail_one cs i l x e he⟩ ∈ symmetricGrading basis n :=
      hy ⟨e.val.2,bottWeight_tail_one cs i l x e he⟩ (Set.mem_univ _)
    have hp := SetLike.GradedMul.mul_mem (simpleRoot_homogeneous basis i) hy'
    simpa only [add_comm] using hp

end
end KLInvariance.TitsSpace

end


section

/-! A homogeneous integral equivalence induces genuine shifted degreewise
vector-space equivalences, including its inverse grading. -/
namespace KLInvariance.Graded
universe uk um un
variable {k : Type uk} [Field k]
  {M : Type um} [AddCommGroup M] [Module k M]
  {N : Type un} [AddCommGroup N] [Module k N]
  (𝓜 : ℤ → Submodule k M) (𝓝 : ℤ → Submodule k N)
  [DirectSum.Decomposition 𝓜] [DirectSum.Decomposition 𝓝]
  (e : M ≃ₗ[k] N) (d : ℤ)
  (he : ∀ n m, m ∈ 𝓜 n → e m ∈ 𝓝 (n+d))
noncomputable section

 def homogeneousPieceEquiv (n : ℤ) : 𝓜 n ≃ₗ[k] 𝓝 (n+d) where
  toFun m := ⟨e m.val,he n m.val m.property⟩
  invFun v := ⟨e.symm v.val,by
    simpa only [add_sub_cancel_right] using
      equiv_inverse_homogeneous 𝓜 𝓝 e d he (n+d) v.val v.property⟩
  left_inv v := Subtype.ext (e.symm_apply_apply v.val)
  right_inv v := Subtype.ext (e.apply_symm_apply v.val)
  map_add' v w := Subtype.ext (map_add e v.val w.val)
  map_smul' r v := Subtype.ext (map_smul e r v.val)

include e he in
 theorem finrank_homogeneousEquiv (n : ℤ) :
    Module.finrank k (𝓝 n)=Module.finrank k (𝓜 (n-d)) := by
  have h := (homogeneousPieceEquiv 𝓜 𝓝 e d he (n-d)).finrank_eq
  have hn : n-d+d=n := by omega
  rw [hn] at h
  exact h.symm

end
end KLInvariance.Graded

end


section

/-! Finiteness of true submodule and finite product homogeneous components. -/
namespace KLInvariance.Graded
universe uk ua um ui
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {M : Type um} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]

 instance subPiece_finite (𝓜 : ℤ → Submodule k M) (S : Submodule A M) (n : ℤ)
    [Module.Finite k (𝓜 n)] : Module.Finite k (subPiece 𝓜 S n) := by
  let f : subPiece 𝓜 S n →ₗ[k] 𝓜 n :=
    { toFun := fun v => ⟨v.val.val,v.property⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  apply Module.Finite.of_injective f
  intro v w h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : 𝓜 n => z.val) h

 variable {ι : Type ui} [Finite ι] {P : ι → Type um}
   [∀ i, AddCommGroup (P i)] [∀ i, Module k (P i)]

 instance piPiece_finite (𝓟 : ∀ i, ℤ → Submodule k (P i)) (n : ℤ)
    [∀ i, Module.Finite k (𝓟 i n)] : Module.Finite k (piPiece 𝓟 n) := by
  let f : piPiece 𝓟 n →ₗ[k] (∀ i, 𝓟 i n) :=
    { toFun := fun v i => ⟨v.val i,v.property i (Set.mem_univ i)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  apply Module.Finite.of_injective f
  intro v w h
  apply Subtype.ext
  funext i
  exact congrArg Subtype.val (congrFun h i)

end KLInvariance.Graded

end


section

/-! The genuine Bott--Samelson stalk Hilbert coefficients satisfy the simple
reflection ascent recurrence. Both exactness and the degree-one kernel shift
were constructed integrally above; no KL character theorem is assumed. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 instance symmetricGrading_finite (n : ℤ) : Module.Finite ℝ (symmetricGrading basis n) :=
  inferInstanceAs (Module.Finite ℝ ((polynomialGrading ℝ σ n).map
    (SymmetricAlgebra.equivMvPolynomial basis).symm.toLinearMap))

 instance bottCoordinatePiece_finite (l : List I) (x : W) (n : ℤ) :
    Module.Finite ℝ (bottCoordinatePiece cs basis l x n) := by
  classical
  exact piPiece_finite _ n

 instance bottStalkPiece_finite (l : List I) (x : W) (n : ℤ) :
    Module.Finite ℝ (bottStalkPiece cs basis l x n) :=
  inferInstanceAs (Module.Finite ℝ (subPiece (bottCoordinatePiece cs basis l x) (bottStalk cs l x) n))

 theorem bottStalk_finrank_ascent (i : I) (l : List I) (x : W)
    (h : cs.length x<cs.length (cs.simple i*x)) (n : ℤ) :
    Module.finrank ℝ (bottStalkPiece cs basis (i::l) x n)=
      Module.finrank ℝ (bottStalkPiece cs basis l x n)+
      Module.finrank ℝ (bottStalkPiece cs basis l (cs.simple i*x) (n-1)) := by
  have hdim := Hilbert.finrank_exact (bottStalkPiece cs basis (i::l) x)
    (bottStalkPiece cs basis l x) (bottHeadLeft cs i l x)
    (bottHeadLeft_homogeneous cs basis i l x) (bottHeadLeft_surjective cs i l x) n
  have hk := finrank_homogeneousEquiv (k := ℝ)
    (N := LinearMap.ker (bottHeadLeft cs i l x)) (bottStalkPiece cs basis l (cs.simple i*x))
    (bottHeadKernelPiece cs basis i l x) (bottHeadKernelEquiv cs i l x h) 1
    (bottHeadKernelEquiv_homogeneous cs basis i l x h) n
  change Module.finrank ℝ (bottStalkPiece cs basis (i::l) x n)=
    Module.finrank ℝ (bottHeadKernelPiece cs basis i l x n)+
      Module.finrank ℝ (bottStalkPiece cs basis l x n) at hdim
  rw [hk] at hdim
  omega

end
end KLInvariance.TitsSpace

end


section

/-! Honest change of the coefficient algebra along an algebra equivalence.
Both scalar actions and semilinear identifications are explicit. -/
namespace KLInvariance
universe uk ua ub um un
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {B : Type ub} [CommRing B] [Algebra k B]

@[ext] structure CoefficientChange (_e : A ≃ₐ[k] B) (M : Type um) where
  val : M

namespace CoefficientChange
variable (e : A ≃ₐ[k] B) (M : Type um) [AddCommGroup M] [Module A M] [Module k M]
  [IsScalarTower k A M]

 def equivVal : CoefficientChange e M ≃ M where
  toFun := val
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl

 instance : AddCommGroup (CoefficientChange e M) := (equivVal e M).addCommGroup
 instance : Module B (CoefficientChange e M) := by
   letI : Module B M := Module.compHom M e.symm.toRingHom
   exact ({ equivVal e M with map_add' := fun _ _ => rfl } : CoefficientChange e M ≃+ M).module B
 instance : Module k (CoefficientChange e M) :=
   ({ equivVal e M with map_add' := fun _ _ => rfl } : CoefficientChange e M ≃+ M).module k
 instance : IsScalarTower k B (CoefficientChange e M) where
   smul_assoc c b m := by
     apply CoefficientChange.ext
     change e.symm (c • b) • m.val=c • (e.symm b • m.val)
     rw [map_smul,smul_assoc]

 local instance : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.of_ringEquiv_symm e.toRingEquiv
 local instance : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e.toRingEquiv

 def equiv : M ≃ₛₗ[e.toRingHom] CoefficientChange e M where
   toFun := mk
   invFun := val
   left_inv _ := rfl
   right_inv _ := rfl
   map_add' _ _ := rfl
   map_smul' a m := by
     change mk (a • m)=mk (e.symm (e a) • m)
     rw [e.symm_apply_apply]

 def kEquiv : M ≃ₗ[k] CoefficientChange e M where
   toFun := mk
   invFun := val
   left_inv _ := rfl
   right_inv _ := rfl
   map_add' _ _ := rfl
   map_smul' _ _ := rfl

 instance [Module.Free A M] : Module.Free B (CoefficientChange e M) :=
   Module.Free.of_equiv (equiv e M)
 instance [Module.Finite A M] : Module.Finite B (CoefficientChange e M) :=
   Module.Finite.of_surjective (equiv e M).toLinearMap (equiv e M).surjective

 variable {M} {N : Type un} [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]
 def map (f : M →ₗ[A] N) : CoefficientChange e M →ₗ[B] CoefficientChange e N where
   toFun m := mk (f m.val)
   map_add' m n := CoefficientChange.ext (map_add f m.val n.val)
   map_smul' b m := CoefficientChange.ext (map_smul f (e.symm b) m.val)

 omit [Module k M] [IsScalarTower k A M] [Module k N] [IsScalarTower k A N] in
 theorem map_injective (f : M →ₗ[A] N) (hf : Function.Injective f) :
     Function.Injective (map e f) := fun _m _n h => CoefficientChange.ext (hf (congrArg val h))
 omit [Module k M] [IsScalarTower k A M] [Module k N] [IsScalarTower k A N] in
 theorem map_surjective (f : M →ₗ[A] N) (hf : Function.Surjective f) :
     Function.Surjective (map e f) := by
   intro n
   obtain ⟨m,hm⟩ := hf n.val
   exact ⟨mk m,CoefficientChange.ext hm⟩

end CoefficientChange
end KLInvariance

end


section

/-! Grading-preserving coefficient change on the actual finite modules. -/
namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A B : Type ua} [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B]
  {𝓐 : ℤ → Submodule k A} {𝓑 : ℤ → Submodule k B}
  (e : A ≃ₐ[k] B) (he : ∀ n a, a∈𝓐 n ↔ e a∈𝓑 n)
noncomputable section

 def changePiece (M : ModuleData.{uk,ua,um} 𝓐) : ℤ → Submodule k (CoefficientChange e M) :=
  fun n => (M.piece n).map (CoefficientChange.kEquiv e M).toLinearMap

 theorem mem_changePiece (M : ModuleData.{uk,ua,um} 𝓐) (n : ℤ) (m : CoefficientChange e M) :
    m ∈ changePiece e M n ↔ m.val ∈ M.piece n := by
  constructor
  · rintro ⟨x,hx,hxm⟩
    change CoefficientChange.mk x=m at hxm
    exact (congrArg CoefficientChange.val hxm) ▸ hx
  · intro hm
    exact ⟨m.val,hm,rfl⟩

 def change (M : ModuleData.{uk,ua,um} 𝓐) : ModuleData.{uk,ua,um} 𝓑 where
  obj := ModuleCat.of B (CoefficientChange e M)
  kModule := inferInstance
  tower := inferInstance
  piece := changePiece e M
  decomposition := by
    apply DirectSum.IsInternal.chooseDecomposition
    apply image_isInternal M.piece (CoefficientChange.kEquiv e M).toLinearMap
      (CoefficientChange.kEquiv e M).surjective
    intro n m hm
    have hz : m=0 := congrArg CoefficientChange.val hm
    subst m
    simp only [map_zero]
  graded := by
    constructor
    intro i j b m hb hm
    apply (mem_changePiece e M (i+j) _).mpr
    change e.symm b • m.val ∈ M.piece (i+j)
    have ha : e.symm b ∈ 𝓐 i := (he i _).mpr (by simpa using hb)
    exact SetLike.GradedSMul.smul_mem ha ((mem_changePiece e M j m).mp hm)
  nonneg n hn := by simp only [changePiece,M.nonneg n hn,Submodule.map_bot]
  finite := inferInstance

 def changeHom {M N : ModuleData.{uk,ua,um} 𝓐} (f : Hom M N) :
    Hom (change e he M) (change e he N) where
  map := CoefficientChange.map e f.map
  graded n m hm := (mem_changePiece e N n _).mpr
    (f.graded n m.val ((mem_changePiece e M n m).mp hm))

 theorem change_free (M : ModuleData.{uk,ua,um} 𝓐) [Module.Free A M] :
    Module.Free B (change e he M) := inferInstanceAs (Module.Free B (CoefficientChange e M))

end
end KLInvariance.Graded.ModuleData

end


section

/-! The genuine nonnegative polynomial generator character of word stalks,
with its convergent Hilbert-series interpretation. No KL identification is
asserted or included in the definition. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 def bottPolynomialStalkData (l : List I) (x : W) :
    ModuleData.{0,u,u} (polynomialGrading ℝ σ) :=
  ModuleData.change (SymmetricAlgebra.equivMvPolynomial basis) (mem_symmetricGrading basis)
    (bottStalkData cs basis l x)

 instance bottPolynomialStalkFree (l : List I) (x : W) :
    Module.Free (MvPolynomial σ ℝ) (bottPolynomialStalkData cs basis l x) :=
  inferInstanceAs (Module.Free (MvPolynomial σ ℝ)
    (CoefficientChange (SymmetricAlgebra.equivMvPolynomial basis) (bottStalk cs l x)))

 def bottStalkCharacter (l : List I) (x : W) : Polynomial ℤ :=
  Graded.character (σ := σ) (bottPolynomialStalkData cs basis l x).piece
    (bottPolynomialStalkData cs basis l x).nonneg

 theorem bottPolynomialStalk_finrank (l : List I) (x : W) (n : ℤ) :
    Module.finrank ℝ ((bottPolynomialStalkData cs basis l x).piece n)=
      Module.finrank ℝ (bottStalkPiece cs basis l x n) :=
  LinearEquiv.finrank_map_eq
    (CoefficientChange.kEquiv (SymmetricAlgebra.equivMvPolynomial basis)
      (bottStalkData cs basis l x)) _

 theorem bottStalkCharacter_hasSum (l : List I) (x : W) {q : ℝ}
    (hq : 0<q) (hq1 : q<1) :
    HasSum (fun n : ℤ => (Module.finrank ℝ (bottStalkPiece cs basis l x n) : ℝ)*q^n)
      (Polynomial.eval₂ (Int.castRingHom ℝ) q (bottStalkCharacter cs basis l x) *
        (1-q)⁻¹ ^ Fintype.card σ) := by
  have hh := (exists_nonnegativeBasis (k := ℝ) (σ := σ) (𝓜 := (bottPolynomialStalkData cs basis l x).piece)
    (bottPolynomialStalkData cs basis l x).nonneg).some.hasSum hq hq1
  apply hh.congr_fun
  intro n
  rw [bottPolynomialStalk_finrank]

end
end KLInvariance.TitsSpace

end


section

namespace KLInvariance
universe ur um un up
variable {R : Type ur} [Ring R]
  {M : Type um} [AddCommGroup M] [Module R M]
  {N : Type un} [AddCommGroup N] [Module R N]
  {P : Type up} [AddCommGroup P] [Module R P]

def kernelTargetEquiv (f : M →ₗ[R] N) (e : N ≃ₗ[R] P) :
    LinearMap.ker f ≃ₗ[R] LinearMap.ker (e.toLinearMap.comp f) where
  toFun x := ⟨x.val, by
    change e (f x.val)=0
    rw [LinearMap.mem_ker.mp x.property,map_zero]⟩
  invFun y := ⟨y.val, by
    apply e.injective
    simpa only [LinearMap.comp_apply,LinearEquiv.coe_coe,map_zero] using (LinearMap.mem_ker.mp y.property)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end KLInvariance

end


section

namespace KLInvariance
universe uk ua um un up uq
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {M : Type um} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
  {N : Type un} [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
  {P : Type up} [AddCommGroup P] [Module k P] [Module A P] [IsScalarTower k A P]
  {Q : Type uq} [AddCommGroup Q] [Module k Q]

def kernelMixedEquiv (f : M →ₗ[A] P) (e : M ≃ₗ[A] N) (g : P ≃ₗ[k] Q) :
    LinearMap.ker f ≃ₗ[k] LinearMap.ker
      (g.toLinearMap.comp ((f.comp e.symm.toLinearMap).restrictScalars k)) where
  toFun x := ⟨e x.val, by
    change g (f (e.symm (e x.val)))=0
    rw [e.symm_apply_apply,LinearMap.mem_ker.mp x.property,map_zero]⟩
  invFun y := ⟨e.symm y.val, by
    apply g.injective
    have hy : g (f (e.symm y.val))=0 := y.property
    simpa only [map_zero] using hy⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv y := Subtype.ext (e.apply_symm_apply y.val)
  map_add' x y := Subtype.ext (map_add e x.val y.val)
  map_smul' c x := Subtype.ext (map_smul (e.restrictScalars k) c x.val)

end KLInvariance

end


section

/-! The descent short exact sequence for the actual word projection lattice.
Its kernel has the genuine degree-one shift, over the unchanged realization. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded ReflectionPairTranslation
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem bottHeadRight_surjective (i : I) (l : List I) (x : W) :
    Function.Surjective (bottHeadRight cs i l x) :=
  (Twist.scalarEquiv (coefficientAction cs (cs.simple i)) _).surjective.comp
    ((right_surjective _ _ _ _ _ _ (bottStalkProjection_surjective cs l (cs.simple i*x))).comp
      (bottHeadPairEquiv cs i l x).symm.surjective)

 theorem bottDescentKernel (i : I) (l : List I) (x : W)
    (h : cs.length (cs.simple i*x)<cs.length x) (z : bottStalk cs l x) :
    (∃ n, bottStalkProjection cs l x n=z ∧ bottStalkProjection cs l (cs.simple i*x) n=0) ↔
      ∃ w, z=simpleRootPolynomial (M := M) i • w := by
  have hh := (bottKernelExact cs l).kernel_iff_of_mul cs (cs.simple i*x) x (cs.simple i)
    (simple_represents cs i) (cs.simple_mul_simple_cancel_left i) h z
  simpa only [and_comm,simpleRootPolynomial,embed,extendedRoot] using hh

 def bottHeadRightKernelEquiv (i : I) (l : List I) (x : W)
    (h : cs.length (cs.simple i*x)<cs.length x) :
    bottStalk cs l x ≃ₗ[ℝ] LinearMap.ker (bottHeadRight cs i l x) :=
  ((rightKernelEquiv (bottStalkProjection cs l x) (bottStalkProjection cs l (cs.simple i*x))
      (coefficientAction cs (cs.simple i)).toRingEquiv (simpleRootPolynomial (M := M) i)
      (simpleReverseDivisibility cs i) (bottSimpleEdge_kernel_inclusion cs i l x)
      (bottDescentKernel cs i l x h)
      (bottStalk_smul_injective cs l x (simpleRootPolynomial_ne_zero i))).restrictScalars ℝ).trans
    (kernelMixedEquiv _ (bottHeadPairEquiv cs i l x)
      (Twist.scalarEquiv (coefficientAction cs (cs.simple i)) _))

 theorem bottHeadRightKernelEquiv_eval (i : I) (l : List I) (x : W)
    (h : cs.length (cs.simple i*x)<cs.length x) (y : bottStalk cs l x)
    (e : {e : BottIndex (i::l) // bottWeight cs (i::l) e=x}) :
    (bottHeadRightKernelEquiv cs i l x h y).val.val e=
      if he : e.val.1=0 then simpleRootPolynomial (M := M) i *
        y.val ⟨e.val.2,bottWeight_tail_zero cs i l x e he⟩ else 0 := by
  change (if he : e.val.1=0 then _ else coefficientAction cs (cs.simple i) 0)=_
  split_ifs
  · rfl
  · exact map_zero _

 def bottHeadRightKernelPiece (i : I) (l : List I) (x : W) :
    ℤ → Submodule ℝ (LinearMap.ker (bottHeadRight cs i l x)) :=
  subPiece (bottStalkPiece cs basis (i::l) x) (LinearMap.ker (bottHeadRight cs i l x))

 theorem bottHeadRight_kernel_homogeneous (i : I) (l : List I) (x : W) :
    ∀ n m, m ∈ LinearMap.ker (bottHeadRight cs i l x) →
      component (bottStalkPiece cs basis (i::l) x) n m ∈ LinearMap.ker (bottHeadRight cs i l x) := by
  exact kernel_homogeneous (A := ℝ) (bottStalkPiece cs basis (i::l) x)
    (bottStalkPiece cs basis l (cs.simple i*x)) (bottHeadRight cs i l x) 0 (by
      intro j z hz
      simpa only [add_zero] using (bottHeadRight_homogeneous cs basis i l x j z hz))

 instance bottHeadRightKernelPiece_decomposition (i : I) (l : List I) (x : W) :
    DirectSum.Decomposition (bottHeadRightKernelPiece cs basis i l x) :=
  (sub_isInternal (bottStalkPiece cs basis (i::l) x) (LinearMap.ker (bottHeadRight cs i l x))
    (bottHeadRight_kernel_homogeneous cs basis i l x)).chooseDecomposition

 theorem bottHeadRightKernelEquiv_homogeneous (i : I) (l : List I) (x : W)
    (h : cs.length (cs.simple i*x)<cs.length x) (n : ℤ)
    (y : bottStalk cs l x) (hy : y ∈ bottStalkPiece cs basis l x n) :
    bottHeadRightKernelEquiv cs i l x h y ∈ bottHeadRightKernelPiece cs basis i l x (n+1) := by
  intro e _
  change (bottHeadRightKernelEquiv cs i l x h y).val.val e ∈ symmetricGrading basis (n+1)
  rw [bottHeadRightKernelEquiv_eval]
  split_ifs with he
  · have hy' : y.val ⟨e.val.2,bottWeight_tail_zero cs i l x e he⟩ ∈ symmetricGrading basis n :=
      hy ⟨e.val.2,bottWeight_tail_zero cs i l x e he⟩ (Set.mem_univ _)
    have hp := SetLike.GradedMul.mul_mem (simpleRoot_homogeneous basis i) hy'
    simpa only [add_comm] using hp
  · exact Submodule.zero_mem _

end
end KLInvariance.TitsSpace

end


section

/-! Uniqueness and degree-one exact recurrences of actual polynomial Hilbert
numerators, with no character-theorem assumptions. -/

end

end OAI
