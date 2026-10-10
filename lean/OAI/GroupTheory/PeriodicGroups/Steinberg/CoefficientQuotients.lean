import Mathlib
import OAI.GroupTheory.PeriodicGroups.Steinberg.MonomialPresentation

namespace OAI

section
universe u v w
namespace SourceBurnside
namespace FiniteSteinbergPresentation
open MonomialCompletion
variable {n : ℕ} {α : Type u}
abbrev Group (n : ℕ) (α : Type u) := PresentedGroup {r | Rel n α r}

instance finitelyPresented [Finite α] : Group.IsFinitelyPresented (Group n α) := by
  have : Finite {r | Rel n α r} := (rel_finite (n := n) (α := α)).to_subtype
  infer_instance

noncomputable def seed : Seed n α (Group n α) where
  g p w := if h : w.length ≤ 2 then PresentedGroup.of (p, ⟨w, h⟩) else 1
  square p w hw := by
    simp only [dite_eq_left hw]
    have h := PresentedGroup.one_of_mem (Rel.square p ⟨w, hw⟩)
    simp only [map_pow, gen] at h
    exact h
  commute p q u v hu hv h₁ h₂ := by
    simp only [dite_eq_left hu, dite_eq_left hv]
    apply (bracket_eq_one_iff _ _).mp
    have h := PresentedGroup.one_of_mem (Rel.commute p q h₁ h₂ ⟨u, hu⟩ ⟨v, hv⟩)
    simp only [map_bracket, gen] at h
    exact h
  product i j k hij hjk hik u v huv := by
    have hu : u.length ≤ 2 := by omega
    have hv : v.length ≤ 2 := by omega
    have hw : (u ++ v).length ≤ 2 := by simp only [List.length_append]; omega
    simp only [dite_eq_left hu, dite_eq_left hv, dite_eq_left hw]
    have h := PresentedGroup.mk_eq_mk_of_mul_inv_mem
      (Rel.product i j k hij hjk hik ⟨u, hu⟩ ⟨v, hv⟩ huv)
    simp only [map_bracket, gen] at h
    exact h

@[simp] theorem seed_short (p : Root n) (w : ShortWord α) :
    seed.g p w.val = (PresentedGroup.of (p, w) : Group n α) := by simp [seed, w.property]

noncomputable def monomial (w : List α) : Polynomial α := MonoidAlgebra.single (FreeMonoid.ofList w) 1

@[simp] theorem monomial_append (u v : List α) : monomial (u ++ v) = monomial u * monomial v := by
  rw [monomial, monomial, monomial, MonoidAlgebra.single_mul_single, one_mul]
  rfl

 theorem monomial_add_self (u : List α) : monomial u + monomial u = 0 := by
  rw [monomial, ← MonoidAlgebra.single_add, show (1 : ZMod 2) + 1 = 0 by decide,
    MonoidAlgebra.single_zero]

noncomputable def toSteinberg : Group n α →* Steinberg n (Polynomial α) :=
  PresentedGroup.toGroup (f := fun g : Gen n α => Steinberg.x g.1 (monomial g.2.val)) (by
    intro r hr
    cases hr with
    | square p w =>
      simp only [map_pow, gen, FreeGroup.lift_apply_of]
      rw [pow_two, ← Steinberg.x_add, monomial_add_self, Steinberg.x_zero]
    | commute p q h₁ h₂ u v =>
      simp only [map_bracket, gen, FreeGroup.lift_apply_of]
      exact (bracket_eq_one_iff _ _).mpr (Steinberg.x_commute p q h₁ h₂ _ _)
    | product i j k hij hjk hik u v h =>
      simp only [map_mul, map_inv, map_bracket, gen, FreeGroup.lift_apply_of]
      rw [Steinberg.x_mul i j k hij hjk hik, monomial_append, mul_inv_cancel])

@[simp] theorem toSteinberg_of (p : Root n) (w : ShortWord α) :
    toSteinberg (PresentedGroup.of (p, w) : Group n α) = Steinberg.x p (monomial w.val) :=
  PresentedGroup.toGroup.of _

noncomputable def fromSteinberg (hn : 5 ≤ n) : Steinberg n (Polynomial α) →* Group n α :=
  MonomialCompletion.lift seed hn

@[simp] theorem fromSteinberg_x (hn : 5 ≤ n) (p : Root n) (f : Polynomial α) :
    fromSteinberg hn (Steinberg.x p f) = poly seed hn p f := by
  simp [fromSteinberg, MonomialCompletion.lift]

 theorem toSteinberg_seed (p : Root n) (w : List α) (hw : w.length ≤ 2) :
    toSteinberg (seed.g p w : Group n α) = Steinberg.x p (monomial w) := by
  rw [seed_short p ⟨w, hw⟩, toSteinberg_of]

 theorem toSteinberg_word (hn : 5 ≤ n) (p : Root n) (w : List α) :
    toSteinberg (word seed hn p w : Group n α) = Steinberg.x p (monomial w) := by
  induction w generalizing p with
  | nil => rw [word_short _ _ _ _ (by simp), toSteinberg_seed _ _ (by simp)]
  | cons a v ih =>
    by_cases hv : v.length ≤ 1
    · rw [word_short _ _ _ _ (by simp only [List.length_cons]; omega),
        toSteinberg_seed _ _ (by simp only [List.length_cons]; omega)]
    · rw [word_long _ _ _ _ _ (by omega), map_bracket,
        word_short _ _ _ _ (by simp), toSteinberg_seed _ _ (by simp), ih,
        Steinberg.x_mul p.row (middle hn p) p.col
          (middle_ne_row hn p).symm (middle_ne_col hn p) p.ne]
      exact congrArg (Steinberg.x p) (monomial_append [a] v).symm

 theorem toSteinberg_poly (hn : 5 ≤ n) (p : Root n) (f : Polynomial α) :
    toSteinberg (poly seed hn p f : Group n α) = Steinberg.x p f := by
  induction f using MonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => rw [poly_add, map_mul, hf, hg, Steinberg.x_add]
  | single w a =>
    rcases zmod_two_cases a with rfl | rfl
    · simp
    · rw [poly_single, toSteinberg_word]
      rfl

 theorem from_to (hn : 5 ≤ n) :
    (fromSteinberg (α := α) hn).comp toSteinberg = MonoidHom.id (Group n α) := by
  apply PresentedGroup.ext
  rintro ⟨p, w⟩
  simp only [MonoidHom.comp_apply, toSteinberg_of, fromSteinberg_x, MonoidHom.id_apply]
  change poly seed hn p (MonoidAlgebra.single (FreeMonoid.ofList w.val) 1) = _
  rw [poly_single]
  change word seed hn p w.val = _
  rw [word_short _ _ _ _ w.property]
  exact seed_short p w

 theorem to_from (hn : 5 ≤ n) :
    toSteinberg.comp (fromSteinberg (α := α) hn) = MonoidHom.id (Steinberg n (Polynomial α)) := by
  apply Steinberg.hom_ext
  intro p f
  simp only [MonoidHom.comp_apply, fromSteinberg_x, toSteinberg_poly, MonoidHom.id_apply]

noncomputable def equiv (hn : 5 ≤ n) : Group n α ≃* Steinberg n (Polynomial α) where
  toFun := toSteinberg
  invFun := fromSteinberg hn
  left_inv a := DFunLike.congr_fun (from_to hn) a
  right_inv a := DFunLike.congr_fun (to_from hn) a
  map_mul' := toSteinberg.map_mul

 theorem free_finitelyPresented [Finite α] (hn : 5 ≤ n) :
    _root_.Group.IsFinitelyPresented (Steinberg n (Polynomial α)) :=
  _root_.Group.IsFinitelyPresented.equiv (equiv hn)

end FiniteSteinbergPresentation

namespace SteinbergQuotient

variable {n : ℕ} {R : Type u} [Ring R]

def killedIdeal {G : Type v} [Group G] (hn : 5 ≤ n) (f : Steinberg n R →* G) :
    TwoSidedIdeal R :=
  TwoSidedIdeal.mk' {a | ∀ p, f (Steinberg.x p a) = 1}
    (by intro p; simp)
    (by intro a b ha hb p; rw [Steinberg.x_add, map_mul, ha, hb, one_mul])
    (by intro a ha p; rw [Steinberg.x_neg, map_inv, ha, inv_one])
    (by
      intro a b hb p
      obtain ⟨j, hji, hjk, _, _⟩ := exists_fresh hn p.row p.col p.row p.col
      rw [← Steinberg.x_mul p.row j p.col hji.symm hjk p.ne, map_bracket, hb]
      simp [bracket])
    (by
      intro a b ha p
      obtain ⟨j, hji, hjk, _, _⟩ := exists_fresh hn p.row p.col p.row p.col
      rw [← Steinberg.x_mul p.row j p.col hji.symm hjk p.ne, map_bracket, ha]
      simp [bracket])

@[simp] theorem mem_killedIdeal {G : Type v} [Group G] (hn : 5 ≤ n)
    (f : Steinberg n R →* G) (a : R) :
    a ∈ killedIdeal hn f ↔ ∀ p, f (Steinberg.x p a) = 1 := by
  simp [killedIdeal]

variable (S : Set R)

def rootRelations : Set (Steinberg n R) := {g | ∃ p a, a ∈ S ∧ g = Steinberg.x p a}

abbrev normal : Subgroup (Steinberg n R) := Subgroup.normalClosure (rootRelations (n := n) S)

abbrev Quot := Steinberg n R ⧸ normal (n := n) S

abbrev coeffIdeal := TwoSidedIdeal.span S

abbrev Coeff := (coeffIdeal S).ringCon.Quotient

abbrev proj : Steinberg n R →* Quot (n := n) S := QuotientGroup.mk' (normal S)

 theorem killed (hn : 5 ≤ n) {a : R} (ha : a ∈ coeffIdeal S) (p : Root n) :
    proj S (Steinberg.x p a) = 1 := by
  have hs : coeffIdeal S ≤ killedIdeal hn (proj (n := n) S) := by
    apply TwoSidedIdeal.span_le.mpr
    intro b hb
    apply (mem_killedIdeal hn _ _).mpr
    intro q
    apply (QuotientGroup.eq_one_iff _).mpr
    exact Subgroup.subset_normalClosure ⟨q, b, hb, rfl⟩
  exact (mem_killedIdeal hn _ _).mp (hs ha) p

noncomputable def quotientRoot (hn : 5 ≤ n) (p : Root n) : Coeff S → Quot (n := n) S :=
  Quotient.lift (fun a => proj S (Steinberg.x p a)) (by
    intro a b hab
    have hk := killed S hn ((coeffIdeal S).rel_iff a b |>.mp hab) p
    rw [sub_eq_add_neg, Steinberg.x_add, Steinberg.x_neg, map_mul, map_inv] at hk
    exact mul_inv_eq_one.mp hk)

@[simp] theorem quotientRoot_mk (hn : 5 ≤ n) (p : Root n) (a : R) :
    quotientRoot S hn p ((coeffIdeal S).ringCon.mk' a) = proj S (Steinberg.x p a) := rfl

noncomputable def fromCoeff (hn : 5 ≤ n) : Steinberg n (Coeff S) →* Quot (n := n) S :=
  Steinberg.lift (quotientRoot S hn)
    (by
      intro p a b
      obtain ⟨a, rfl⟩ := (coeffIdeal S).ringCon.mk'_surjective a
      obtain ⟨b, rfl⟩ := (coeffIdeal S).ringCon.mk'_surjective b
      rw [← map_add, quotientRoot_mk, quotientRoot_mk, quotientRoot_mk,
        Steinberg.x_add, map_mul])
    (by
      intro p q h₁ h₂ a b
      obtain ⟨a, rfl⟩ := (coeffIdeal S).ringCon.mk'_surjective a
      obtain ⟨b, rfl⟩ := (coeffIdeal S).ringCon.mk'_surjective b

      exact (Steinberg.x_commute p q h₁ h₂ a b).map (proj S))
    (by
      intro i j k hij hjk hik a b
      obtain ⟨a, rfl⟩ := (coeffIdeal S).ringCon.mk'_surjective a
      obtain ⟨b, rfl⟩ := (coeffIdeal S).ringCon.mk'_surjective b
      rw [← map_mul, quotientRoot_mk, quotientRoot_mk, quotientRoot_mk,
        ← map_bracket, Steinberg.x_mul])

@[simp] theorem fromCoeff_x (hn : 5 ≤ n) (p : Root n) (a : R) :
    fromCoeff S hn (Steinberg.x p ((coeffIdeal S).ringCon.mk' a)) =
      proj S (Steinberg.x p a) := by
  change quotientRoot S hn p ((coeffIdeal S).ringCon.mk' a) = _
  rfl

 theorem normal_le_ker : normal (n := n) S ≤ (Steinberg.map (n := n) (coeffIdeal S).ringCon.mk').ker := by
  apply Subgroup.normalClosure_le_normal
  rintro g ⟨p, a, ha, rfl⟩
  change Steinberg.map (n := n) (coeffIdeal S).ringCon.mk' (Steinberg.x p a) = 1
  rw [Steinberg.map_x]
  have ha0 : (coeffIdeal S).ringCon.mk' a = 0 := by
    apply ((coeffIdeal S).ringCon.eq).mpr
    exact TwoSidedIdeal.subset_span ha
  rw [ha0, Steinberg.x_zero]

noncomputable def toCoeff : Quot (n := n) S →* Steinberg n (Coeff S) :=
  QuotientGroup.lift (normal S) (Steinberg.map (n := n) (coeffIdeal S).ringCon.mk') (normal_le_ker S)

@[simp] theorem toCoeff_proj (g : Steinberg n R) :
    toCoeff S (proj S g) = Steinberg.map (n := n) (coeffIdeal S).ringCon.mk' g := rfl

 theorem fromCoeff_comp_toCoeff (hn : 5 ≤ n) :
    (fromCoeff S hn).comp (toCoeff S) = MonoidHom.id (Quot (n := n) S) := by
  have h : ((fromCoeff S hn).comp (toCoeff S)).comp (proj S) = proj (n := n) S := by
    apply Steinberg.hom_ext
    intro p a
    change fromCoeff S hn (toCoeff S (proj S (Steinberg.x p a))) = _
    rw [toCoeff_proj, Steinberg.map_x, fromCoeff_x]
  apply MonoidHom.ext
  intro g
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (normal S) g
  exact DFunLike.congr_fun h g

 theorem toCoeff_comp_fromCoeff (hn : 5 ≤ n) :
    (toCoeff S).comp (fromCoeff S hn) = MonoidHom.id (Steinberg n (Coeff S)) := by
  apply Steinberg.hom_ext
  intro p a
  obtain ⟨a, rfl⟩ := (coeffIdeal S).ringCon.mk'_surjective a
  change toCoeff S (fromCoeff S hn (Steinberg.x p ((coeffIdeal S).ringCon.mk' a))) = _
  rw [fromCoeff_x, toCoeff_proj, Steinberg.map_x]
  rfl

noncomputable def equiv (hn : 5 ≤ n) : Quot (n := n) S ≃* Steinberg n (Coeff S) where
  toFun := toCoeff S
  invFun := fromCoeff S hn
  left_inv g := DFunLike.congr_fun (fromCoeff_comp_toCoeff S hn) g
  right_inv g := DFunLike.congr_fun (toCoeff_comp_fromCoeff S hn) g
  map_mul' := (toCoeff S).map_mul

 theorem rootRelations_finite (hS : S.Finite) : (rootRelations (n := n) S).Finite := by
  have h : rootRelations (n := n) S =
      (fun z : Root n × R => Steinberg.x z.1 z.2) '' (Set.univ ×ˢ S) := by
    ext g
    constructor
    · rintro ⟨p, a, ha, rfl⟩
      exact ⟨(p, a), ⟨Set.mem_univ _, ha⟩, rfl⟩
    · rintro ⟨⟨p, a⟩, ⟨_, ha⟩, rfl⟩
      exact ⟨p, a, ha, rfl⟩
  rw [h]
  exact ((Set.finite_univ : (Set.univ : Set (Root n)).Finite).prod hS).image _

 theorem normal_finitelyGenerated (hS : S.Finite) :
    (normal (n := n) S).IsFinitelyNormallyGenerated :=
  ⟨rootRelations S, rootRelations_finite S hS, rfl⟩

 theorem finitelyPresented (hn : 5 ≤ n) (hS : S.Finite)
    [Group.IsFinitelyPresented (Steinberg n R)] :
    Group.IsFinitelyPresented (Steinberg n (Coeff S)) := by
  have : Group.IsFinitelyPresented (Quot (n := n) S) :=
    Group.IsFinitelyPresented.quotient (normal S) (normal_finitelyGenerated S hS)
  exact Group.IsFinitelyPresented.equiv (equiv S hn)

end SteinbergQuotient

theorem steinberg_finitelyPresented {n : ℕ} (hn : 5 ≤ n) {α : Type u} [Finite α]
    (S : Set (MonomialCompletion.Polynomial α)) (hS : S.Finite) :
    Group.IsFinitelyPresented (Steinberg n (SteinbergQuotient.Coeff S)) := by
  have : Group.IsFinitelyPresented (Steinberg n (MonomialCompletion.Polynomial α)) :=
    FiniteSteinbergPresentation.free_finitelyPresented hn
  exact SteinbergQuotient.finitelyPresented S hn hS

end SourceBurnside
namespace SourceBurnside.WordAlgebra.Table
noncomputable section
open Classical
variable {α K : Type*} [CommRing K]
local instance polyAlgebra (T : Table α) : _root_.Algebra (_root_.Polynomial K) (_root_.Polynomial (T.Algebra (K:=K))) := _root_.Polynomial.algebra K _

def polynomialCoefficients (T : Table α) :
    T.Algebra (K:=_root_.Polynomial K) →ₐ[_root_.Polynomial K] _root_.Polynomial (T.Algebra (K:=K)) := by
  let g : FreeMonoid α →* _root_.Polynomial (T.Algebra (K:=K)) :=
    _root_.Polynomial.C.toMonoidHom.comp (wordHom T)
  let F := MonoidAlgebra.lift (_root_.Polynomial K) (_root_.Polynomial (T.Algebra (K:=K))) (FreeMonoid α) g
  have H : T.ideal (K:=_root_.Polynomial K) ≤ TwoSidedIdeal.ker F := by
    apply TwoSidedIdeal.span_le.mpr
    rintro v (⟨a,b,hab,rfl⟩|⟨a,ha,rfl⟩)
    · change F (monomial a-monomial b)=0
      simp only [map_sub,F,monomial,MonoidAlgebra.lift_single,one_smul,g,
        MonoidHom.comp_apply,wordHom,MonoidHom.coe_mk,OneHom.coe_mk]
      rw [T.word_rep hab,sub_self]
    · change F (monomial a)=0
      simp only [F,monomial,MonoidAlgebra.lift_single,one_smul,g,
        MonoidHom.comp_apply,wordHom,MonoidHom.coe_mk,OneHom.coe_mk]
      change _root_.Polynomial.C (T.word (K:=K) a)=0
      rw [T.word_zero ha, map_zero]
  apply RingCon.liftₐ _ F
  intro a b hab
  change F a=F b
  apply sub_eq_zero.mp
  exact (map_sub F a b).symm.trans (H ((T.ideal (K:=_root_.Polynomial K)).rel_iff a b |>.mp hab))
@[simp] lemma polynomialCoefficients_word (T : Table α) (w : FreeMonoid α) :
    T.polynomialCoefficients (K:=K) (T.word w)=_root_.Polynomial.C (T.word (K:=K) w) := by
  change (MonoidAlgebra.lift (_root_.Polynomial K) (_root_.Polynomial (T.Algebra (K:=K))) (FreeMonoid α)
    (_root_.Polynomial.C.toMonoidHom.comp (wordHom T))) (monomial w)=_
  simp [monomial,MonoidAlgebra.lift_single,wordHom]
end
end SourceBurnside.WordAlgebra.Table

namespace SourceBurnside.MatrixTests
noncomputable section
open Classical
variable {A ι : Type*} [Ring A] [Fintype ι] [DecidableEq ι]

def polynomialMatrix : Polynomial (Matrix ι ι A) →+* Matrix ι ι (Polynomial A) :=
  Polynomial.eval₂RingHom' Polynomial.C.mapMatrix (Matrix.scalar ι Polynomial.X)
    (fun _ => (Matrix.scalar_commute Polynomial.X Polynomial.commute_X _).symm)
@[simp] lemma polynomialMatrix_monomial (n : ℕ) (M : Matrix ι ι A) (i j : ι) :
    polynomialMatrix (Polynomial.monomial n M) i j=Polynomial.monomial n (M i j) := by
  simp only [polynomialMatrix,Polynomial.eval₂RingHom'_apply,Polynomial.eval₂_monomial,
    ←map_pow,RingHom.mapMatrix_apply]
  simp only [Matrix.scalar_apply,Matrix.mul_diagonal,Matrix.map_apply]
  exact Polynomial.C_mul_X_pow_eq_monomial (R:=A) (a:=M i j) (n:=n)
lemma polynomialMatrix_coeff (p : Polynomial (Matrix ι ι A)) (n : ℕ) (i j : ι) :
    (polynomialMatrix p i j).coeff n=p.coeff n i j := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add,Matrix.add_apply,Polynomial.coeff_add,hp,hq]
  | monomial m a =>
    rw [polynomialMatrix_monomial]
    simp only [Polynomial.coeff_monomial]
    split_ifs <;> rfl
lemma polynomialMatrix_injective : Function.Injective (polynomialMatrix (A:=A) (ι:=ι)) := by
  intro p q hpq
  ext n i j
  simpa only [←polynomialMatrix_coeff] using congrArg (fun M : Matrix ι ι (Polynomial A)=>(M i j).coeff n) hpq
end
end SourceBurnside.MatrixTests

namespace SourceBurnside.MatrixTests
noncomputable section
open Classical
open scoped BigOperators
variable {Γ R : Type*} [Fintype Γ] [Semiring R]
omit [Fintype Γ] in
lemma eval_monomial_one (f : Γ → R) (v : List Γ) :
    CutReduction.eval (fun c=>Polynomial.monomial 1 (f c)) v=
      Polynomial.monomial v.length (CutReduction.eval f v) := by
  induction v with
  | nil => simp [CutReduction.eval]
  | cons c v ih =>
    change Polynomial.monomial 1 (f c)*CutReduction.eval (fun c=>Polynomial.monomial 1 (f c)) v=_
    rw [ih,Polynomial.monomial_mul_monomial]
    simp [CutReduction.eval,Nat.add_comm]

lemma chunkSum_monomial (len : Γ → ℕ) (f : Γ → R) (n : ℕ) :
    CutReduction.chunkSum len (fun c=>Polynomial.monomial 1 (f c)) n=
      WeightedTests.lengthPolynomial len f n := by
  unfold CutReduction.chunkSum
  rw [Finset.sum_filter,CutReduction.candidates,Finset.sum_image]
  · simp_rw [eval_monomial_one]
    rw [Fintype.sum_sigma]
    simp only [List.length_ofFn,CutReduction.eval,List.map_ofFn,List.sum_ofFn]
    change (∑r : Fin (n+1),∑v : Fin r.val→Γ,
      if WeightedTests.length len v=n then Polynomial.monomial r.val (WeightedTests.product f v) else 0)=_
    exact Fin.sum_univ_eq_sum_range (fun r=>∑v : Fin r→Γ, if WeightedTests.length len v=n then Polynomial.monomial r (WeightedTests.product f v) else 0) (n+1)
  · exact fun _ _ _ _ h=>bounded_list_injective n h
end
end SourceBurnside.MatrixTests

namespace SourceBurnside.MatrixTests
noncomputable section
open Classical
open scoped BigOperators
variable {K A B ι : Type*} [CommRing K] [Ring A] [Ring B] [Algebra K A]
variable [Algebra (Polynomial K) B] [Fintype ι] [DecidableEq ι]
local instance : Algebra (Polynomial K) (Polynomial A) := Polynomial.algebra K A
lemma polynomial_tensor (F : B →ₐ[Polynomial K] Polynomial A)
    (x : B) (a : A) (hx : F x=Polynomial.C a) (W : Matrix ι ι K) :
    F.mapMatrix (tensor (fun i j=>Polynomial.monomial 1 (W i j)) x)=
      polynomialMatrix (Polynomial.monomial 1 (tensor W a)) := by
  apply Matrix.ext
  intro i j
  change F (Polynomial.monomial 1 (W i j) • x)=_
  rw [map_smul,hx,polynomialMatrix_monomial]
  change Polynomial.monomial 1 (W i j) • Polynomial.C a=
    Polynomial.monomial 1 (W i j • a)
  rw [Algebra.smul_def,Polynomial.algebraMap_def]
  change Polynomial.map (algebraMap K A) (Polynomial.monomial 1 (W i j))*Polynomial.C a=_
  rw [Polynomial.map_monomial]
  change Polynomial.monomial 1 ((algebraMap K A) (W i j))*Polynomial.monomial 0 a=_
  rw [Polynomial.monomial_mul_monomial]
  simp only [Nat.add_zero,Algebra.smul_def]
variable {Γ R S : Type*} [Fintype Γ] [Semiring R] [Semiring S]
lemma map_chunkSum (F : R →+* S) (len : Γ → ℕ) (f : Γ → R) (n : ℕ) :
    F (CutReduction.chunkSum len f n)=CutReduction.chunkSum len (fun c=>F (f c)) n := by
  simp only [CutReduction.chunkSum,CutReduction.eval,map_sum,map_list_prod,List.map_map,Function.comp_def]

lemma map_test_polynomial {α : Type*} [Fintype α]
    (F : B →ₐ[Polynomial K] Polynomial A) (f : α → B) (g : α → A)
    (hf : ∀v : List α,F (DirectCancellation.eval f v)=Polynomial.C (DirectCancellation.eval g v))
    (label : Γ → List α) (W : Γ → Matrix ι ι K) (n : ℕ) :
    F.mapMatrix (chunkSum label (fun c i j=>Polynomial.monomial 1 (W c i j)) f n)=
      polynomialMatrix (WeightedTests.lengthPolynomial (fun c=>(label c).length)
        (fun c=>tensor (W c) (DirectCancellation.eval g (label c))) n) := by
  let l : Γ → ℕ := fun c=>(label c).length
  let t : Γ → Matrix ι ι A := fun c=>tensor (W c) (DirectCancellation.eval g (label c))
  let tp : Γ → Matrix ι ι B := fun c=>tensor (fun i j=>Polynomial.monomial 1 (W c i j)) (DirectCancellation.eval f (label c))
  change F.toRingHom.mapMatrix (CutReduction.chunkSum l tp n)=polynomialMatrix (WeightedTests.lengthPolynomial l t n)
  have ht : (fun c=>F.toRingHom.mapMatrix (tp c))=(fun c=>polynomialMatrix (Polynomial.monomial 1 (t c))) := by
    funext c
    exact polynomial_tensor F _ _ (hf (label c)) (W c)
  exact (map_chunkSum F.toRingHom.mapMatrix l tp n).trans
    ((congrArg (fun w=>CutReduction.chunkSum l w n) ht).trans
      ((map_chunkSum polynomialMatrix l (fun c=>Polynomial.monomial 1 (t c)) n).symm.trans
        (congrArg polynomialMatrix (chunkSum_monomial l t n))))
end
end SourceBurnside.MatrixTests

namespace SourceBurnside.SourceMachine.MachineHierarchy
noncomputable section
open Classical FiniteTable
open scoped BigOperators
variable {D : ℕ} {hD : 2 ≤ D} (A : MachineHierarchy D hD)
variable {h : ℕ} (hh : A.threshold ≤ h) (K : Type) [CommRing K] [CharP K 2]
variable {ι Γ : Type} [Fintype ι] [DecidableEq ι] [Fintype Γ]

theorem word_matrix_sum_nilpotent (hDbig : 10*(10000+1)*(10+1)<D)
    (label : Γ → List (Codec.Raw h)) (hne : ∀c,label c≠[]) (W : Γ → Matrix ι ι K) :
    IsNilpotent (∑c,MatrixTests.tensor (W c) (DirectCancellation.eval (A.letters hh K) (label c))) := by
  let : _root_.Algebra (Polynomial K) (Polynomial (A.Algebra K h hh)) := Polynomial.algebra K _
  let F := (A.table h hh).polynomialCoefficients (K:=K)
  have hF : ∀v : List (Codec.Raw h),F (DirectCancellation.eval (A.letters hh (Polynomial K)) v)=
      Polynomial.C (DirectCancellation.eval (A.letters hh K) v) := by
    intro v
    rw [A.eval_letters,A.eval_letters]
    exact WordAlgebra.Table.polynomialCoefficients_word _ _
  let b : ℕ := 1+∑c,(label c).length
  have hb : 0<b := by dsimp [b];omega
  have hl : ∀c,(label c).length ≤ b := by
    intro c
    have hc := Finset.single_le_sum (fun i (_ : i∈(Finset.univ : Finset Γ))=>Nat.zero_le ((label i).length)) (Finset.mem_univ c)
    exact hc.trans (by dsimp [b];omega)
  let P : Γ → Matrix ι ι (Polynomial K) := fun c i j=>Polynomial.monomial 1 (W c i j)
  obtain ⟨N,hN⟩ := A.all_chunk_tests hh (Polynomial K) hDbig (Fintype.card ι) b hb
    ι Γ le_rfl label hne hl P
  apply WeightedTests.nilpotent_of_eventually_zero_lengthPolynomial (fun c=>(label c).length)
    (fun c=>List.length_pos_iff.mpr (hne c))
  refine ⟨N,fun n hn=>?_⟩
  apply MatrixTests.polynomialMatrix_injective
  rw [map_zero]
  have he := MatrixTests.map_test_polynomial F (A.letters hh (Polynomial K)) (A.letters hh K) hF label W n
  exact he.symm.trans ((congrArg F.mapMatrix (hN n hn)).trans (map_zero _))
end
end SourceBurnside.SourceMachine.MachineHierarchy

namespace SourceBurnside.SourceMachine.MachineHierarchy
noncomputable section
open Classical FiniteTable
open scoped BigOperators
variable {D : ℕ} {hD : 2 ≤ D} (A : MachineHierarchy D hD)
variable {h : ℕ} (hh : A.threshold ≤ h) (K : Type) [CommRing K]

def positiveSpan : Submodule K (A.Algebra K h hh) :=
  Submodule.span K (Set.range (fun w : {w : List (Codec.Raw h) // w≠[]}=>
    DirectCancellation.eval (A.letters hh K) w.val))
variable [CharP K 2]

theorem positive_matrix_nilpotent (hDbig : 10*(10000+1)*(10+1)<D)
    {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι (A.Algebra K h hh))
    (hM : ∀i j,M i j∈A.positiveSpan hh K) : IsNilpotent M := by
  let P := {w : List (Codec.Raw h) // w≠[]}
  have H (i j : ι) : ∃p : P →₀ K,
      p.sum (fun w a=>a • DirectCancellation.eval (A.letters hh K) w.val)=M i j :=
    Finsupp.mem_span_range_iff_exists_finsupp.mp (hM i j)
  choose p hp using H
  let Γ := Σi : ι,Σj : ι,{w : P // w∈(p i j).support}
  let label : Γ → List (Codec.Raw h) := fun c=>c.2.2.val.val
  let W : Γ → Matrix ι ι K := fun c=>Matrix.single c.1 c.2.1 (p c.1 c.2.1 c.2.2.val)
  have hz (w : P) : (0:K) • DirectCancellation.eval (A.letters hh K) w.val=0 := by
    exact @zero_smul K (A.Algebra K h hh) inferInstance inferInstance inferInstance _
  have he : (∑c : Γ,MatrixTests.tensor (W c) (DirectCancellation.eval (A.letters hh K) (label c)))=M := by
    apply Matrix.ext
    intro i j
    simp only [Matrix.sum_apply,Γ,Fintype.sum_sigma,MatrixTests.tensor,W,label,Matrix.single_apply]
    simp only [ite_smul,ite_and,hz,Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    exact (Finset.sum_coe_sort (p i j).support
      (fun w : P=>(p i j) w • DirectCancellation.eval (A.letters hh K) w.val)).trans (hp i j)
  rw [←he]
  exact A.word_matrix_sum_nilpotent hh K hDbig label (fun c=>c.2.2.val.property) W
end
end SourceBurnside.SourceMachine.MachineHierarchy

namespace SourceBurnside.WordAlgebra.Table
noncomputable section
open Classical
variable {α K : Type*} [CommRing K]
def augWords : FreeMonoid α →* K := FreeMonoid.lift (fun _=>0)
lemma augWords_spec (w : FreeMonoid α) : augWords (K:=K) w=if w.length=0 then 1 else 0 := by
  rw [augWords,FreeMonoid.lift_apply]
  change (List.map (fun _ : α=>(0:K)) w.toList).prod=(if w.toList.length=0 then 1 else 0)
  cases he : w.toList with
  | nil => simp
  | cons a w => simp

def augmentation (T : Table α) (hh : T.Homogeneous) (hz : ∀z∈T.zero,z≠1) : T.Algebra (K:=K) →ₐ[K] K := by
  let F := MonoidAlgebra.lift K K (FreeMonoid α) (augWords (K:=K))
  have H : T.ideal (K:=K) ≤ TwoSidedIdeal.ker F := by
    apply TwoSidedIdeal.span_le.mpr
    rintro v (⟨a,b,hab,rfl⟩|⟨a,ha,rfl⟩)
    · change F (monomial a-monomial b)=0
      simp only [map_sub,F,monomial,MonoidAlgebra.lift_single,one_smul,augWords_spec]
      rw [hh a b hab,sub_self]
    · change F (monomial a)=0
      simp only [F,monomial,MonoidAlgebra.lift_single,one_smul,augWords_spec]
      exact ite_eq_right (fun h=>hz a ha (FreeMonoid.length_eq_zero.mp h))
  apply RingCon.liftₐ _ F
  intro a b hab
  change F a=F b
  apply sub_eq_zero.mp
  exact (map_sub F a b).symm.trans (H ((T.ideal (K:=K)).rel_iff a b |>.mp hab))
@[simp] lemma augmentation_word (T : Table α) (hh : T.Homogeneous) (hz : ∀z∈T.zero,z≠1) (w : FreeMonoid α) :
    T.augmentation (K:=K) hh hz (T.word w)=if w.length=0 then 1 else 0 := by
  change (MonoidAlgebra.lift K K (FreeMonoid α) (augWords (K:=K))) (monomial w)=_
  simp [monomial,MonoidAlgebra.lift_single,augWords_spec]
lemma quotient_smul (T : Table α) (k : K) (p : Polynomial K α) : T.quotient (k • p)=k • T.quotient p :=
  map_smul (RingCon.mkₐ K (T.ideal (K:=K)).ringCon) k p

lemma sub_augmentation_mem (T : Table α) (hh : T.Homogeneous) (hz : ∀z∈T.zero,z≠1)
    (P : Submodule K (T.Algebra (K:=K))) (hpos : ∀w : FreeMonoid α,w≠1 → T.word w∈P)
    (x : T.Algebra (K:=K)) : x-algebraMap K _ (T.augmentation hh hz x)∈P := by
  obtain ⟨p,rfl⟩ := (T.ideal (K:=K)).ringCon.mk'_surjective x
  induction p using MonoidAlgebra.induction_on with
  | of w =>
    change T.word w-algebraMap K _ (T.augmentation hh hz (T.word w))∈P
    by_cases hw : w=1
    · simp [hw]
    · rw [augmentation_word,ite_eq_right (fun h=>hw (FreeMonoid.length_eq_zero.mp h)),map_zero,sub_zero]
      exact hpos w hw
  | add p q hp hq =>
    have he : T.quotient (p+q)-algebraMap K _ (T.augmentation hh hz (T.quotient (p+q)))=
        (T.quotient p-algebraMap K _ (T.augmentation hh hz (T.quotient p)))+
        (T.quotient q-algebraMap K _ (T.augmentation hh hz (T.quotient q))) := by
      simp only [map_add]
      abel
    rw [he]
    exact P.add_mem hp hq
  | smul k p hp =>
    rw [quotient_smul,map_smul,smul_eq_mul,map_mul,←Algebra.smul_def,←smul_sub]
    exact P.smul_mem k hp
lemma kernel_mem (T : Table α) (hh : T.Homogeneous) (hz : ∀z∈T.zero,z≠1)
    (P : Submodule K (T.Algebra (K:=K))) (hpos : ∀w : FreeMonoid α,w≠1 → T.word w∈P)
    (x : T.Algebra (K:=K)) (hx : T.augmentation hh hz x=0) : x∈P := by
  have H := sub_augmentation_mem T hh hz P hpos x
  simpa only [hx,map_zero,sub_zero] using H
end
end SourceBurnside.WordAlgebra.Table

namespace SourceBurnside.SourceMachine.MachineHierarchy
noncomputable section
open Classical FiniteTable
variable {D : ℕ} {hD : 2 ≤ D} (A : MachineHierarchy D hD)
variable {h : ℕ} (hh : A.threshold ≤ h)
lemma table_homogeneous : (A.table h hh).Homogeneous :=
  Codec.algebraTable_homogeneous (A.threshold_four.trans hh)
lemma table_zero_nonempty : ∀z∈(A.table h hh).zero,z≠1 := by
  intro z hz he
  have hn := (Codec.zero_lengths (A.height_pos hh) (A.schedule h hh) (10000*(D*h)) z.toList hz).1
  simp [he] at hn

def augmentation (K : Type) [CommRing K] : A.Algebra K h hh →ₐ[K] K :=
  (A.table h hh).augmentation (A.table_homogeneous hh) (A.table_zero_nonempty hh)
lemma augmentation_kernel_positive (K : Type) [CommRing K] (x : A.Algebra K h hh)
    (hx : A.augmentation hh K x=0) : x∈A.positiveSpan hh K := by
  apply (A.table h hh).kernel_mem (A.table_homogeneous hh) (A.table_zero_nonempty hh) _ _ x hx
  intro w hw
  apply Submodule.subset_span
  refine ⟨⟨w.toList,?_⟩,?_⟩
  · intro he
    apply hw
    simpa using congrArg FreeMonoid.ofList he
  · exact A.eval_letters hh K w.toList

theorem matrixNilKernel (hDbig : 10*(10000+1)*(10+1)<D) :
    MatrixNilKernel (A.augmentation hh (ZMod 2)).toRingHom := by
  intro n M hM
  apply A.positive_matrix_nilpotent hh (ZMod 2) hDbig M
  intro i j
  exact A.augmentation_kernel_positive hh (ZMod 2) (M i j) (hM i j)

theorem matrix_periodic (hDbig : 10*(10000+1)*(10+1)<D) (n : ℕ) :
    Periodic (Matrix (Fin n) (Fin n) (A.Algebra (ZMod 2) h hh))ˣ := by
  let := A.infinite_algebra (ZMod 2) h hh
  let : CharP (A.Algebra (ZMod 2) h hh) 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) (A.Algebra (ZMod 2) h hh)).injective 2
  exact matrix_units_periodic (A.augmentation hh (ZMod 2)).toRingHom (A.matrixNilKernel hh hDbig) n
end
end SourceBurnside.SourceMachine.MachineHierarchy

namespace SourceBurnside.FiniteTable.Codec
noncomputable section
open Classical WordAlgebra
variable {h d : ℕ} {hh : 0<h} {S : Schedule (2^h)}
def boundedWords (h n : ℕ) : Set (FreeMonoid (Raw h)) :=
  Set.range (fun v : Σ m : Fin (n+1), Fin m.val → Raw h => FreeMonoid.ofList (List.ofFn v.2))
lemma finite_boundedWords (h n : ℕ) : (boundedWords h n).Finite := Set.finite_range _
lemma mem_boundedWords (w : FreeMonoid (Raw h)) {n : ℕ} (hw : w.toList.length ≤ n) :
    w∈boundedWords h n := by
  refine ⟨⟨⟨w.toList.length,by omega⟩,w.toList.get⟩,?_⟩
  simp

lemma finite_algebraTable_relations (h4 : 4 ≤ h) (K : Type*) [Ring K] :
    ((algebraTable hh S d).relations (K:=K)).Finite := by
  have hr : {vw : FreeMonoid (Raw h) × FreeMonoid (Raw h) | (algebraTable hh S d).rep vw.1 vw.2}.Finite := by
    apply ((finite_boundedWords h 2).prod (finite_boundedWords h 2)).subset
    rintro ⟨v,w⟩ hvw
    obtain ⟨hl,hn,hk⟩ := replacement_lengths h4 S d v.toList w.toList hvw
    exact ⟨mem_boundedWords v hk,mem_boundedWords w (hl ▸ hk)⟩
  have hz : (algebraTable hh S d).zero.Finite := by
    apply (finite_boundedWords h 2).subset
    intro w hw
    exact mem_boundedWords w (zero_lengths hh S d w.toList hw).2
  let f : FreeMonoid (Raw h) × FreeMonoid (Raw h) → WordAlgebra.Polynomial K (Raw h) :=
    fun vw => monomial vw.1 - monomial vw.2
  apply ((hr.image f).union (hz.image (monomial (K:=K)))).subset
  rintro p (⟨v,w,hvw,rfl⟩ | ⟨w,hw,rfl⟩)
  · exact Or.inl ⟨(v,w),hvw,rfl⟩
  · exact Or.inr ⟨w,hw,rfl⟩
end
end SourceBurnside.FiniteTable.Codec
namespace SourceBurnside.SourceMachine.MachineHierarchy
noncomputable section
open FiniteTable
variable {D : ℕ} {hD : 2 ≤ D} (A : MachineHierarchy D hD)

theorem steinberg_finitely_presented {h : ℕ} (hh : A.threshold ≤ h) :
    Group.IsFinitelyPresented (Steinberg 12 (A.Algebra (ZMod 2) h hh)) :=
  steinberg_finitelyPresented (by decide) (A.table h hh).relations
    (Codec.finite_algebraTable_relations (A.threshold_four.trans hh) _)
theorem steinberg_infinite {h : ℕ} (hh : A.threshold ≤ h) :
    Infinite (Steinberg 12 (A.Algebra (ZMod 2) h hh)) := by
  let := A.infinite_algebra (ZMod 2) h hh
  exact Elementary.steinberg_infinite ⟨0,1,by decide⟩

theorem infinite_and_fp {h : ℕ} (hh : A.threshold ≤ h) :
    Infinite (Steinberg 12 (A.Algebra (ZMod 2) h hh)) ∧
      Group.IsFinitelyPresented (Steinberg 12 (A.Algebra (ZMod 2) h hh)) :=
  ⟨A.steinberg_infinite hh,A.steinberg_finitely_presented hh⟩
end
end SourceBurnside.SourceMachine.MachineHierarchy

namespace SourceBurnside.ConcreteSource
noncomputable section

def dilation : ℕ := 10*(10000+1)*(10+1)+1
lemma dilation_two : 2≤dilation := by decide
lemma dilation_large : 10*(10000+1)*(10+1)<dilation := by decide
def machine := SourceMachine.hierarchy dilation dilation_two
def height := machine.threshold

abbrev R := machine.Algebra (ZMod 2) height (by rfl)
def augmentation : R →ₐ[ZMod 2] ZMod 2 := machine.augmentation (by rfl) (ZMod 2)
instance ring_infinite : Infinite R := machine.infinite_algebra (ZMod 2) height (by rfl)
instance characteristic : CharP R 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) R).injective 2

theorem steinberg_infinite : Infinite (Steinberg 12 R) := machine.steinberg_infinite (by rfl)

theorem steinberg_finitely_presented : Group.IsFinitelyPresented (Steinberg 12 R) :=
  machine.steinberg_finitely_presented (by rfl)
theorem matrix_nil_kernel : MatrixNilKernel augmentation.toRingHom :=
  machine.matrixNilKernel (by rfl) dilation_large
theorem matrix_periodic (n : ℕ) : Periodic (Matrix (Fin n) (Fin n) R)ˣ :=
  machine.matrix_periodic (by rfl) dilation_large n

theorem image_element_periodic (n : ℕ) (g : Steinberg n R) :
    ∃ m : ℕ, 0 < m ∧ (Elementary.representation g) ^ m = 1 := matrix_periodic n _
end
end SourceBurnside.ConcreteSource

namespace SourceBurnside.WordAlgebra.Table
noncomputable section
open Classical
variable {α K : Type*} [CommRing K]

def gradingWords (T : Table α) : FreeMonoid α →* _root_.Polynomial (T.Algebra (K:=K)) where
  toFun w := _root_.Polynomial.monomial w.length (T.word w)
  map_one' := by simp
  map_mul' a b := by simp [FreeMonoid.length_mul,word_mul,_root_.Polynomial.monomial_mul_monomial]

def gradingHom (T : Table α) (hh : T.Homogeneous) :
    T.Algebra (K:=K) →ₐ[K] _root_.Polynomial (T.Algebra (K:=K)) := by
  let F := MonoidAlgebra.lift K (_root_.Polynomial (T.Algebra (K:=K))) (FreeMonoid α) T.gradingWords
  have hw (w : FreeMonoid α) : F (monomial w)=_root_.Polynomial.monomial w.length (T.word w) := by
    simp [F,monomial,MonoidAlgebra.lift_single,gradingWords]
  have H : T.ideal (K:=K) ≤ TwoSidedIdeal.ker F := by
    apply TwoSidedIdeal.span_le.mpr
    rintro v (⟨a,b,hab,rfl⟩|⟨a,ha,rfl⟩)
    · change F (monomial a-monomial b)=0
      rw [map_sub,hw,hw,hh a b hab,T.word_rep hab,sub_self]
    · change F (monomial a)=0
      rw [hw,T.word_zero ha]
      exact map_zero _
  apply RingCon.liftₐ _ F
  intro a b hab
  apply sub_eq_zero.mp
  exact (map_sub F a b).symm.trans (H ((T.ideal (K:=K)).rel_iff a b |>.mp hab))
@[simp] lemma gradingHom_word (T : Table α) (hh : T.Homogeneous) (w : FreeMonoid α) :
    T.gradingHom (K:=K) hh (T.word w)=_root_.Polynomial.monomial w.length (T.word w) := by
  change (MonoidAlgebra.lift K (_root_.Polynomial (T.Algebra (K:=K))) (FreeMonoid α) T.gradingWords) (monomial w)=_
  simp [monomial,MonoidAlgebra.lift_single,gradingWords]
lemma algHom_ext_word (T : Table α) {S : Type*} [Semiring S] [_root_.Algebra K S]
    (f g : T.Algebra (K:=K) →ₐ[K] S) (hw : ∀w,f (T.word w)=g (T.word w)) : f=g := by
  apply AlgHom.ext
  intro x
  obtain ⟨p,rfl⟩ := (T.ideal (K:=K)).ringCon.mk'_surjective x
  induction p using MonoidAlgebra.induction_on with
  | of w => exact hw w
  | add p q hp hq => simpa only [map_add] using congrArg₂ (fun a b : S=>a+b) hp hq
  | smul k p hp =>
    change f (T.quotient (k • p))=g (T.quotient (k • p))
    rw [quotient_smul,map_smul,map_smul,hp]

def evalZero (T : Table α) : _root_.Polynomial (T.Algebra (K:=K)) →ₐ[K] T.Algebra (K:=K) :=
  _root_.Polynomial.eval₂AlgHom (AlgHom.id K _) 0 (fun _=>Commute.zero_right _)
def evalOne (T : Table α) : _root_.Polynomial (T.Algebra (K:=K)) →ₐ[K] T.Algebra (K:=K) :=
  _root_.Polynomial.eval₂AlgHom (AlgHom.id K _) 1 (fun _=>Commute.one_right _)
lemma evalOne_gradingHom (T : Table α) (hh : T.Homogeneous) :
    T.evalOne.comp (T.gradingHom (K:=K) hh)=AlgHom.id K _ := by
  apply T.algHom_ext_word
  intro w
  simp [evalOne,_root_.Polynomial.eval₂AlgHom_apply,_root_.Polynomial.eval₂_monomial]
lemma evalZero_gradingHom (T : Table α) (hh : T.Homogeneous) (hz : ∀z∈T.zero,z≠1) :
    T.evalZero.comp (T.gradingHom (K:=K) hh)=(Algebra.ofId K _).comp (T.augmentation hh hz) := by
  apply T.algHom_ext_word
  intro w
  by_cases hw : w=1
  · simp [hw,evalZero,_root_.Polynomial.eval₂AlgHom_apply]
  · have hl : w.length≠0 := fun h=>hw (FreeMonoid.length_eq_zero.mp h)
    simp [evalZero,_root_.Polynomial.eval₂AlgHom_apply,_root_.Polynomial.eval₂_monomial,hl]
end
end SourceBurnside.WordAlgebra.Table

end

end OAI
