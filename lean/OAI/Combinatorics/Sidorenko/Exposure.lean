import OAI.Combinatorics.Sidorenko.PairBounds

namespace OAI

namespace SidorenkoCounterexample
open scoped BigOperators
section Sequential
variable {A : Type*} [Finite A]

def SeqValid (k : ℕ) (R : (Fin k → A) → Prop)
    (P : (n : ℕ) → (Fin (k+n) → A) → A → Prop) :
    (n : ℕ) → (Fin (k+n) → A) → Prop
  | 0,x => R x
  | n+1,x => SeqValid k R P n (Fin.init x) ∧ P n (Fin.init x) (x (Fin.last (k+n)))

abbrev ValidSeq (k : ℕ) (R : (Fin k → A) → Prop)
    (P : (n : ℕ) → (Fin (k+n) → A) → A → Prop) (n : ℕ) :=
  {x : Fin (k+n) → A // SeqValid k R P n x}

noncomputable def validSeqSuccEquiv (k : ℕ) (R : (Fin k → A) → Prop)
    (P : (n : ℕ) → (Fin (k+n) → A) → A → Prop) (n : ℕ) :
    ValidSeq k R P (n+1) ≃ Σ x : ValidSeq k R P n, {a : A // P n x.val a} where
  toFun x := ⟨⟨Fin.init x.val,x.property.1⟩,⟨x.val (Fin.last (k+n)),x.property.2⟩⟩
  invFun x := ⟨Fin.snoc (α := fun _ => A) x.1.val x.2.val,by
    have hs : Fin.snoc (α := fun _ => A) x.1.val x.2.val (Fin.last (k+n))=x.2.val := Fin.snoc_last (α := fun _ => A) x.2.val x.1.val
    change SeqValid k R P n (Fin.init (Fin.snoc (α := fun _ => A) x.1.val x.2.val)) ∧
      P n (Fin.init (Fin.snoc (α := fun _ => A) x.1.val x.2.val)) (Fin.snoc (α := fun _ => A) x.1.val x.2.val (Fin.last (k+n)))
    rw [Fin.init_snoc,hs]
    exact ⟨x.1.property,x.2.property⟩⟩
  left_inv x := Subtype.ext (Fin.snoc_init_self x.val)
  right_inv x := by
    rcases x with ⟨⟨x,hx⟩,⟨a,ha⟩⟩
    dsimp
    apply Sigma.ext
    · apply Subtype.ext
      exact Fin.init_snoc (α := fun _ => A) a x
    · apply (Subtype.heq_iff_coe_eq
        (p := fun b => P n (Fin.init (Fin.snoc (α := fun _ => A) x a)) b)
        (q := fun b => P n x b) (fun b => by rw [Fin.init_snoc])).mpr
      exact Fin.snoc_last (α := fun _ => A) a x

 theorem validSeq_card_bound (k : ℕ) (R : (Fin k → A) → Prop)
    (P : (n : ℕ) → (Fin (k+n) → A) → A → Prop) (B : ℕ → ℝ)
    (hB : ∀ n, 0≤B n) (hb : ∀ n (x : ValidSeq k R P n), (Nat.card {a : A // P n x.val a}:ℝ) ≤ B n)
    (n : ℕ) : (Nat.card (ValidSeq k R P n):ℝ) ≤
      Nat.card {x : Fin k → A // R x} * ∏ i : Fin n, B i.val := by
  classical
  induction n with
  | zero => simp only [Fin.prod_univ_zero,mul_one]; exact le_rfl
  | succ n ih =>
    let := Fintype.ofFinite (ValidSeq k R P n)
    rw [Nat.card_congr (validSeqSuccEquiv k R P n),Nat.card_sigma,Nat.cast_sum]
    calc
      _ ≤ ∑ _x : ValidSeq k R P n, B n := Finset.sum_le_sum (fun x _ => hb n x)
      _ = (Nat.card (ValidSeq k R P n):ℝ)*B n := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
      _ ≤ (Nat.card {x : Fin k → A // R x} * ∏ i : Fin n, B i.val)*B n := mul_le_mul_of_nonneg_right ih (hB n)
      _ = _ := by rw [Fin.prod_univ_castSucc]; simp only [Fin.val_castSucc,Fin.val_last]; ring
end Sequential
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
def faceVertex : Fin 22 → Fin 3 → Fin 13 := ![![0, 1, 3], ![0, 1, 9], ![0, 2, 3], ![0, 2, 9], ![1, 3, 10], ![1, 7, 10], ![1, 7, 12], ![1, 9, 12], ![2, 3, 4], ![2, 4, 9], ![3, 4, 11], ![3, 10, 11], ![4, 8, 9], ![4, 8, 11], ![5, 6, 7], ![5, 6, 11], ![5, 7, 10], ![5, 10, 11], ![6, 7, 12], ![6, 8, 11], ![6, 8, 12], ![8, 9, 12]]
def classFace : Fin 6 → Fin 11 → Fin 22 := ![![0, 1, 2, 4, 5, 16, 14, 18, 20, 19, 13], ![3, 9, 8, 10, 11, 17, 15, 12, 21, 7, 6], ![0, 2, 8, 9, 12, 4, 11, 5, 6, 18, 14], ![1, 3, 7, 21, 20, 19, 13, 10, 15, 17, 16], ![0, 1, 3, 9, 7, 6, 5, 16, 14, 15, 19], ![2, 8, 10, 11, 4, 17, 13, 12, 21, 20, 18]]
def classPoint : Fin 6 → Fin 13 → Fin 13 := ![![0, 1, 3, 9, 2, 10, 7, 5, 6, 12, 8, 11, 4], ![0, 2, 9, 4, 3, 11, 10, 5, 6, 8, 12, 1, 7], ![0, 1, 3, 2, 4, 9, 8, 10, 11, 7, 12, 6, 5], ![0, 1, 9, 2, 12, 8, 6, 11, 4, 3, 5, 10, 7], ![0, 1, 3, 9, 2, 4, 12, 7, 10, 5, 6, 11, 8], ![0, 2, 3, 4, 11, 10, 1, 5, 8, 9, 12, 6, 7]]
def classOldZero : Fin 6 → Fin 10 → Fin 13 := ![![0, 0, 1, 1, 6, 7, 8, 8, 8, 10], ![1, 1, 4, 4, 6, 7, 3, 9, 2, 11], ![0, 3, 3, 4, 1, 2, 1, 1, 9, 11], ![0, 1, 2, 5, 6, 5, 8, 6, 10, 10], ![0, 0, 4, 1, 1, 1, 7, 9, 9, 10], ![1, 2, 2, 2, 5, 3, 3, 8, 8, 11]]
def classOldOne : Fin 6 → Fin 10 → Fin 13 := ![![1, 2, 2, 5, 5, 6, 6, 9, 10, 11], ![2, 3, 3, 5, 5, 5, 2, 2, 10, 10], ![2, 2, 4, 5, 2, 7, 7, 9, 10, 9], ![2, 2, 4, 4, 5, 7, 7, 7, 7, 11], ![1, 3, 3, 3, 6, 7, 8, 7, 10, 11], ![2, 3, 4, 5, 4, 4, 8, 9, 10, 10]]
def classOldPair : Fin 6 → Fin 10 → Fin 33 := ![![5, 1, 6, 11, 20, 25, 30, 31, 28, 22], ![4, 7, 8, 13, 21, 27, 10, 18, 16, 15], ![1, 2, 7, 10, 6, 12, 11, 19, 23, 30], ![3, 9, 16, 24, 28, 22, 14, 29, 27, 26], ![5, 3, 4, 9, 15, 19, 20, 25, 32, 29], ![2, 8, 13, 12, 21, 14, 17, 18, 24, 31]]
def classNewPairZero : Fin 6 → Fin 10 → Fin 33 := ![![3, 0, 11, 19, 25, 32, 31, 28, 29, 17], ![7, 2, 13, 12, 26, 32, 17, 24, 9, 19], ![0, 7, 4, 17, 11, 13, 19, 15, 30, 32], ![0, 15, 18, 28, 29, 17, 8, 32, 26, 25], ![3, 0, 7, 15, 19, 11, 25, 32, 27, 28], ![7, 13, 12, 6, 26, 17, 10, 24, 28, 30]]
def classNewPairOne : Fin 6 → Fin 10 → Fin 33 := ![![9, 2, 12, 20, 26, 30, 23, 24, 22, 14], ![10, 8, 14, 21, 27, 29, 18, 16, 15, 23], ![2, 8, 10, 18, 12, 21, 20, 23, 31, 25], ![4, 16, 24, 31, 22, 14, 13, 27, 21, 20], ![9, 4, 10, 16, 23, 20, 26, 30, 29, 22], ![8, 14, 21, 11, 27, 22, 18, 16, 31, 23]]
def classParent : Fin 6 → Fin 10 → Fin 11 := ![![0, 0, 0, 3, 4, 5, 6, 7, 8, 9], ![0, 1, 2, 3, 4, 5, 1, 7, 8, 9], ![0, 1, 2, 3, 0, 5, 5, 7, 8, 9], ![0, 0, 2, 3, 4, 5, 6, 5, 8, 9], ![0, 1, 2, 1, 4, 5, 6, 7, 8, 9], ![0, 1, 2, 3, 3, 2, 6, 7, 8, 9]]

 theorem faceVertex_correct : ∀ j, faces j={faceVertex j 0,faceVertex j 1,faceVertex j 2} := by decide
 theorem classPoint_bijective : ∀ c, Function.Bijective (classPoint c) := by decide
 theorem classFace_injective : ∀ c, Function.Injective (classFace c) := by decide
 theorem classOldZero_lt : ∀ c n, (classOldZero c n).val<3+n.val := by decide
 theorem classOldOne_lt : ∀ c n, (classOldOne c n).val<3+n.val := by decide
 theorem classRoot_correct : ∀ c, faces (classFace c 0)={classPoint c 0,classPoint c 1,classPoint c 2} := by decide
 theorem classStep_correct : ∀ c n, faces (classFace c n.succ)=
    {classPoint c (classOldZero c n),classPoint c (classOldOne c n),classPoint c ⟨3+n.val,by omega⟩} := by decide
 theorem classOldPair_correct : ∀ c n, pairVertices (classOldPair c n)=
    {classPoint c (classOldZero c n),classPoint c (classOldOne c n)} := by decide
 theorem classNewPairZero_correct : ∀ c n, pairVertices (classNewPairZero c n)=
    {classPoint c (classOldZero c n),classPoint c ⟨3+n.val,by omega⟩} := by decide
 theorem classNewPairOne_correct : ∀ c n, pairVertices (classNewPairOne c n)=
    {classPoint c (classOldOne c n),classPoint c ⟨3+n.val,by omega⟩} := by decide
 theorem classParent_lt : ∀ c n, (classParent c n).val<n.val+1 := by decide
 theorem classOldPair_parent : ∀ c n, pairVertices (classOldPair c n) ⊆ faces (classFace c (classParent c n)) := by decide
 theorem classOldPair_injective : ∀ c, Function.Injective (classOldPair c) := by decide
 def classContains (c : Fin 6) (j : Fin 22) : Prop := ∃ n, classFace c n=j
 instance (c : Fin 6) (j : Fin 22) : Decidable (classContains c j) := inferInstanceAs (Decidable (∃ n, classFace c n=j))
 def classInternal (c : Fin 6) (e : Fin 33) : Prop := ∀ k, classContains c (pairFace e k)
 instance (c : Fin 6) (e : Fin 33) : Decidable (classInternal c e) := inferInstanceAs (Decidable (∀ k, classContains c (pairFace e k)))
 theorem classFace_occurs : ∀ j, (Finset.univ.filter fun cn : Fin 6 × Fin 11 => classFace cn.1 cn.2=j).card=3 := by decide
 theorem classInternal_occurs : ∀ e, (Finset.univ.filter fun c => classInternal c e).card=3-separationCount e := by decide
 theorem classOldPair_internal : ∀ c n, classInternal c (classOldPair c n) := by decide
 theorem classStep_pairs : ∀ c n, Finset.image (facePair (classFace c n.succ)) Finset.univ =
    {classOldPair c n,classNewPairZero c n,classNewPairOne c n} := by decide
 theorem classStep_pairs_distinct : ∀ c n, classOldPair c n≠classNewPairZero c n ∧
    classOldPair c n≠classNewPairOne c n ∧ classNewPairZero c n≠classNewPairOne c n := by decide

 theorem faceVertex_injective : ∀ j, Function.Injective (faceVertex j) := by decide
 theorem faceVertex_pairs : ∀ j k, pairVertices (facePair j k)=
    (![ {faceVertex j 0,faceVertex j 1}, {faceVertex j 0,faceVertex j 2}, {faceVertex j 1,faceVertex j 2}] : Fin 3 → Finset (Fin 13)) k := by decide
 theorem classRootPairZero : ∀ c, pairVertices (facePair (classFace c 0) 0)={classPoint c 0,classPoint c 1} := by decide
 theorem classRootPairOne : ∀ c, pairVertices (facePair (classFace c 0) 1)={classPoint c 0,classPoint c 2} := by decide
 theorem classRootPairTwo : ∀ c, pairVertices (facePair (classFace c 0) 2)={classPoint c 1,classPoint c 2} := by decide
 theorem classTree_occurs : ∀ e, (Finset.univ.filter fun cn : Fin 6 × Fin 10 => classOldPair cn.1 cn.2=e).card=3-separationCount e := by decide
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
 theorem inverse_power_inequality (q C L N : ℝ) (a : ℕ) (hq : 0<q)
    (h : q^a*N≤C*L) : N≤C*L*q^(-(a:ℝ)) := by
  rw [Real.rpow_neg hq.le,Real.rpow_natCast,←div_eq_mul_inv]
  apply (le_div_iff₀ (pow_pos hq a)).mpr
  simpa only [mul_comm] using h
section RawProfile
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
def naturalProfileCost (D c u v w : ℕ) : ℕ :=
  (D+1)*c+((u-c+1).choose 2+(v-c+1).choose 2+(w-c+1).choose 2)
 theorem tripleProfile_card_raw (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) (c u v w : ℕ) (hc : c≤D) :
    (Nat.card (TripleDimProfile ω c u v w):ℝ) ≤ fullProfileConstant D *
      (Nat.card (SymplecticLagrangian ω):ℝ)^3 * (Fintype.card K:ℝ)^(-(naturalProfileCost D c u v w:ℝ)) := by
  have hq : 0<(Fintype.card K:ℝ) := by exact_mod_cast Fintype.card_pos (α:=K)
  have hb := (symplecticLagrangian_card_bounds ω h2 ha hω D hD).1
  apply inverse_power_inequality _ _ _ _ _ hq
  calc
    _ ≤ fullProfileConstant D*(Fintype.card K:ℝ)^(3*(D+1).choose 2) :=
      tripleProfile_card_upper ω h2 ha hω D hD c u v w hc
    _ ≤ _ := by
      gcongr
      · exact (fullProfileConstant_pos D).le
      · rw [mul_comm 3, pow_mul]
        exact pow_le_pow_left₀ (by positivity) hb 3
 theorem conditionalProfile_card_raw (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) (L M : SymplecticLagrangian ω) (c v w : ℕ) (hc : c≤D) :
    (Nat.card (PairCompletion ω L M c v w):ℝ) ≤ fullProfileConstant D *
      (Nat.card (SymplecticLagrangian ω):ℝ) * (Fintype.card K:ℝ)^
        (((finrank K ↥(L.val ⊓ M.val)+1).choose 2:ℝ)-(naturalProfileCost D c (finrank K ↥(L.val ⊓ M.val)) v w:ℝ)) := by
  have hq : 0<(Fintype.card K:ℝ) := by exact_mod_cast Fintype.card_pos (α:=K)
  have hb := (symplecticLagrangian_card_bounds ω h2 ha hω D hD).1
  have hh := conditionalProfile_card_upper ω h2 ha hω D hD L M c v w hc
  have hh' : (Fintype.card K:ℝ)^(naturalProfileCost D c (finrank K ↥(L.val ⊓ M.val)) v w)*
      (Nat.card (PairCompletion ω L M c v w):ℝ) ≤ fullProfileConstant D*
        ((Nat.card (SymplecticLagrangian ω):ℝ)*(Fintype.card K:ℝ)^((finrank K ↥(L.val ⊓ M.val)+1).choose 2)) := by
    change (Fintype.card K:ℝ)^(naturalProfileCost D c (finrank K ↥(L.val ⊓ M.val)) v w)*
      (Nat.card (PairCompletion ω L M c v w):ℝ) ≤ _ at hh
    refine hh.trans ?_
    rw [pow_add]
    calc
      _ ≤ fullProfileConstant D*((Fintype.card K:ℝ)^((finrank K ↥(L.val ⊓ M.val)+1).choose 2)*
        (Nat.card (SymplecticLagrangian ω):ℝ)) := by gcongr; exact (fullProfileConstant_pos D).le
      _ = _ := by ring
  have hh'' := inverse_power_inequality _ _ _ _ _ hq hh'
  convert hh'' using 1
  rw [Real.rpow_sub hq,Real.rpow_natCast,Real.rpow_natCast]
  rw [Real.rpow_neg hq.le,Real.rpow_natCast]
  ring
end RawProfile
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
noncomputable def tupleThreeEquiv {A : Type*} : (Fin 3 → A) ≃ A × A × A where
  toFun x := (x 0,x 1,x 2)
  invFun x := ![x.1,x.2.1,x.2.2]
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv _ := rfl

def faceNaturalCost (D : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (j : Fin 22) : ℕ :=
  (D+1)*c j+∑ k : Fin 3, (h (facePair j k)-c j+1).choose 2
 theorem root_natural_cost (D : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (j : Fin 22) :
    naturalProfileCost D (c j) (h (facePair j 0)) (h (facePair j 1)) (h (facePair j 2))=faceNaturalCost D c h j := by
  simp only [naturalProfileCost,faceNaturalCost,Fin.sum_univ_three]
 theorem step_natural_cost (D : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (κ : Fin 6) (n : Fin 10) :
    naturalProfileCost D (c (classFace κ n.succ)) (h (classOldPair κ n))
      (h (classNewPairZero κ n)) (h (classNewPairOne κ n))=faceNaturalCost D c h (classFace κ n.succ) := by
  let f (e : Fin 33) := (h e-c (classFace κ n.succ)+1).choose 2
  have hs : (∑ e ∈ Finset.univ.image (facePair (classFace κ n.succ)), f e)=
      ∑ k : Fin 3, f (facePair (classFace κ n.succ) k) :=
    Finset.sum_image (fun a _ b _ hab => facePair_injective _ hab)
  rw [classStep_pairs] at hs
  obtain ⟨h01,h02,h12⟩ := classStep_pairs_distinct κ n
  simp only [Finset.sum_insert,Finset.mem_insert,Finset.mem_singleton,h01,h02,h12,
    or_self,not_false_eq_true,Finset.sum_singleton] at hs
  unfold naturalProfileCost faceNaturalCost
  change _ = (D+1)*c (classFace κ n.succ)+∑ k, f (facePair (classFace κ n.succ) k)
  rw [←hs]
  simp only [f]
  omega
section ExposureProfile
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
def PointProfile (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (L : Fin 13 → SymplecticLagrangian ω) : Prop :=
  (∀ j, finrank K ↥((faces j).inf fun i => (L i).val : Submodule K E)=c j) ∧
  (∀ e, finrank K ↥((pairVertices e).inf fun i => (L i).val : Submodule K E)=h e)
def LocalProfile (c u v w : ℕ) (L M N : SymplecticLagrangian ω) : Prop :=
  finrank K ↥((L.val ⊓ M.val) ⊓ N.val)=c ∧ finrank K ↥(L.val ⊓ M.val)=u ∧
  finrank K ↥(L.val ⊓ N.val)=v ∧ finrank K ↥(M.val ⊓ N.val)=w
 theorem PointProfile.local {c : Fin 22 → ℕ} {h : Fin 33 → ℕ} {L : Fin 13 → SymplecticLagrangian ω}
    (hL : PointProfile ω c h L) (j : Fin 22) (i k l : Fin 13) (e f g : Fin 33)
    (hj : faces j={i,k,l}) (he : pairVertices e={i,k}) (hf : pairVertices f={i,l})
    (hg : pairVertices g={k,l}) : LocalProfile ω (c j) (h e) (h f) (h g) (L i) (L k) (L l) := by
  classical
  unfold PointProfile at hL
  refine ⟨?_,?_,?_,?_⟩
  · have hh := hL.1 j
    rw [hj,Finset.inf_insert,Finset.inf_insert,Finset.inf_singleton,←inf_assoc] at hh
    exact hh
  · have hh := hL.2 e
    rw [he,Finset.inf_insert,Finset.inf_singleton] at hh
    exact hh
  · have hh := hL.2 f
    rw [hf,Finset.inf_insert,Finset.inf_singleton] at hh
    exact hh
  · have hh := hL.2 g
    rw [hg,Finset.inf_insert,Finset.inf_singleton] at hh
    exact hh

def classRootConstraint (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (κ : Fin 6) (x : Fin 3 → SymplecticLagrangian ω) : Prop :=
  LocalProfile ω (c (classFace κ 0)) (h (facePair (classFace κ 0) 0))
    (h (facePair (classFace κ 0) 1)) (h (facePair (classFace κ 0) 2)) (x 0) (x 1) (x 2)

def classStepConstraint (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (κ : Fin 6)
    (n : ℕ) (x : Fin (3+n) → SymplecticLagrangian ω) (Y : SymplecticLagrangian ω) : Prop :=
  if hn : n<10 then
    LocalProfile ω (c (classFace κ ⟨n+1,by omega⟩)) (h (classOldPair κ ⟨n,hn⟩))
      (h (classNewPairZero κ ⟨n,hn⟩)) (h (classNewPairOne κ ⟨n,hn⟩))
      (x ⟨(classOldZero κ ⟨n,hn⟩).val,classOldZero_lt κ ⟨n,hn⟩⟩)
      (x ⟨(classOldOne κ ⟨n,hn⟩).val,classOldOne_lt κ ⟨n,hn⟩⟩) Y
  else False
noncomputable def rootConstraintEquiv (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (κ : Fin 6) :
    {x : Fin 3 → SymplecticLagrangian ω // classRootConstraint ω c h κ x} ≃
      TripleDimProfile ω (c (classFace κ 0)) (h (facePair (classFace κ 0) 0))
        (h (facePair (classFace κ 0) 1)) (h (facePair (classFace κ 0) 2)) :=
  tupleThreeEquiv.subtypeEquiv (fun _ => Iff.rfl)

variable [Fintype K] [Finite E]
noncomputable def classStepBound (D : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (κ : Fin 6) (n : ℕ) : ℝ :=
  if hn : n<10 then fullProfileConstant D*(Nat.card (SymplecticLagrangian ω):ℝ)*
    (Fintype.card K:ℝ)^(((h (classOldPair κ ⟨n,hn⟩)+1).choose 2:ℝ)-(faceNaturalCost D c h (classFace κ ⟨n+1,by omega⟩):ℝ))
  else 0
 omit [Finite E] in
 theorem classStepBound_nonneg (D : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (κ : Fin 6) (n : ℕ) :
    0≤classStepBound ω D c h κ n := by
  unfold classStepBound
  split_ifs
  · exact mul_nonneg (mul_nonneg (fullProfileConstant_pos D).le (by positivity)) (Real.rpow_nonneg (by positivity) _)
  · exact le_rfl
 theorem classStep_card_bound (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (hc : ∀ j, c j≤D)
    (κ : Fin 6) (n : ℕ) (x : Fin (3+n) → SymplecticLagrangian ω) :
    (Nat.card {Y : SymplecticLagrangian ω // classStepConstraint ω c h κ n x Y}:ℝ) ≤ classStepBound ω D c h κ n := by
  classical
  by_cases hn : n<10
  · let L := x ⟨(classOldZero κ ⟨n,hn⟩).val,classOldZero_lt κ ⟨n,hn⟩⟩
    let M := x ⟨(classOldOne κ ⟨n,hn⟩).val,classOldOne_lt κ ⟨n,hn⟩⟩
    let j : Fin 22 := classFace κ ⟨n+1,by omega⟩
    let e := classOldPair κ ⟨n,hn⟩
    let f := classNewPairZero κ ⟨n,hn⟩
    let g := classNewPairOne κ ⟨n,hn⟩
    have hp : ∀ Y, classStepConstraint ω c h κ n x Y ↔ LocalProfile ω (c j) (h e) (h f) (h g) L M Y := by
      intro Y; simp only [classStepConstraint,dite_eq_left hn]; rfl
    by_cases hh : finrank K ↥(L.val ⊓ M.val)=h e
    · have heq : Nat.card {Y // classStepConstraint ω c h κ n x Y}=Nat.card (PairCompletion ω L M (c j) (h f) (h g)) := by
        apply Nat.card_congr
        exact Equiv.subtypeEquivRight (fun Y => by rw [hp]; exact ⟨fun hY => ⟨hY.1,hY.2.2⟩,fun hY => ⟨hY.1,hh,hY.2⟩⟩)
      rw [heq]
      have hb := conditionalProfile_card_raw ω h2 ha hω D hD L M (c j) (h f) (h g) (hc j)
      rw [hh] at hb
      have hcost := step_natural_cost D c h κ ⟨n,hn⟩
      change naturalProfileCost D (c j) (h e) (h f) (h g)=faceNaturalCost D c h j at hcost
      rw [hcost] at hb
      simpa only [classStepBound,dite_eq_left hn, e,j] using hb
    · have hem : IsEmpty {Y // classStepConstraint ω c h κ n x Y} := ⟨fun Y => hh ((hp Y.val).mp Y.property).2.1⟩
      have hz := Nat.card_eq_zero.mpr (Or.inl hem)
      rw [hz,Nat.cast_zero]
      exact classStepBound_nonneg ω D c h κ n
  · have hem : IsEmpty {Y // classStepConstraint ω c h κ n x Y} :=
      ⟨fun Y => by simpa only [classStepConstraint,dite_eq_right hn] using Y.property⟩
    rw [Nat.card_eq_zero.mpr (Or.inl hem),Nat.cast_zero,classStepBound,dite_eq_right hn]

noncomputable def classPrefix (κ : Fin 6) (L : Fin 13 → SymplecticLagrangian ω)
    (n : ℕ) (hn : n≤10) : Fin (3+n) → SymplecticLagrangian ω :=
  fun i => L (classPoint κ ⟨i.val,by omega⟩)
 omit [Fintype K] [Finite E] in
 theorem classPrefix_valid {c : Fin 22 → ℕ} {h : Fin 33 → ℕ}
    {L : Fin 13 → SymplecticLagrangian ω} (hL : PointProfile ω c h L)
    (κ : Fin 6) (n : ℕ) (hn : n≤10) :
    SeqValid 3 (classRootConstraint ω c h κ) (classStepConstraint ω c h κ) n (classPrefix ω κ L n hn) := by
  induction n with
  | zero =>
    exact PointProfile.local ω hL _ _ _ _ _ _ _ (classRoot_correct κ)
      (classRootPairZero κ) (classRootPairOne κ) (classRootPairTwo κ)
  | succ n ih =>
    have hn' : n<10 := by omega
    refine ⟨?_,?_⟩
    · exact ih (by omega)
    · simp only [classStepConstraint,dite_eq_left hn']
      exact PointProfile.local ω hL _ _ _ _ _ _ _ (classStep_correct κ ⟨n,hn'⟩)
        (classOldPair_correct κ ⟨n,hn'⟩) (classNewPairZero_correct κ ⟨n,hn'⟩)
        (classNewPairOne_correct κ ⟨n,hn'⟩)
noncomputable def pointProfile_class_injection (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (κ : Fin 6) :
    {L : Fin 13 → SymplecticLagrangian ω // PointProfile ω c h L} ↪
      ValidSeq 3 (classRootConstraint ω c h κ) (classStepConstraint ω c h κ) 10 where
  toFun L := ⟨classPrefix ω κ L.val 10 le_rfl,classPrefix_valid ω L.property κ 10 le_rfl⟩
  inj' := by
    intro L M hm
    apply Subtype.ext
    funext i
    obtain ⟨j,hj⟩ := (classPoint_bijective κ).2 i
    have hh := congrFun (congrArg Subtype.val hm) j
    change L.val (classPoint κ j)=M.val (classPoint κ j) at hh
    simpa only [hj] using hh
 theorem classRoot_card_bound (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (hc : ∀ j, c j≤D)
    (κ : Fin 6) : (Nat.card {x : Fin 3 → SymplecticLagrangian ω // classRootConstraint ω c h κ x}:ℝ) ≤
      fullProfileConstant D*(Nat.card (SymplecticLagrangian ω):ℝ)^3*
        (Fintype.card K:ℝ)^(-(faceNaturalCost D c h (classFace κ 0):ℝ)) := by
  rw [Nat.card_congr (rootConstraintEquiv ω c h κ)]
  have hb := tripleProfile_card_raw ω h2 ha hω D hD (c (classFace κ 0))
    (h (facePair (classFace κ 0) 0)) (h (facePair (classFace κ 0) 1))
    (h (facePair (classFace κ 0) 2)) (hc _)
  simpa only [root_natural_cost] using hb


noncomputable def classExponent (D : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (κ : Fin 6) : ℝ :=
  -(∑ i : Fin 11, (faceNaturalCost D c h (classFace κ i):ℝ))+
    ∑ i : Fin 10, ((h (classOldPair κ i)+1).choose 2:ℝ)
 omit [Finite E] in
 theorem classStepBound_product (D : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (κ : Fin 6) :
    (∏ n : Fin 10, classStepBound ω D c h κ n.val)=
      (fullProfileConstant D*(Nat.card (SymplecticLagrangian ω):ℝ))^10*
        (Fintype.card K:ℝ)^(∑ n : Fin 10,
          (((h (classOldPair κ n)+1).choose 2:ℝ)-(faceNaturalCost D c h (classFace κ n.succ):ℝ))) := by
  have hq : 0<(Fintype.card K:ℝ) := by exact_mod_cast Fintype.card_pos (α:=K)
  simp only [classStepBound,dite_eq_left (Fin.isLt _),Fin.eta,Finset.prod_mul_distrib,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [Real.rpow_sum_of_pos hq,mul_pow]
  rfl
 theorem pointProfile_class_card_bound (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (hc : ∀ j, c j≤D)
    (κ : Fin 6) : (Nat.card {L : Fin 13 → SymplecticLagrangian ω // PointProfile ω c h L}:ℝ) ≤
      (fullProfileConstant D)^11*(Nat.card (SymplecticLagrangian ω):ℝ)^13*
        (Fintype.card K:ℝ)^(classExponent D c h κ) := by
  have hq : 0<(Fintype.card K:ℝ) := by exact_mod_cast Fintype.card_pos (α:=K)
  have hs := validSeq_card_bound 3 (classRootConstraint ω c h κ) (classStepConstraint ω c h κ)
    (classStepBound ω D c h κ) (classStepBound_nonneg ω D c h κ)
    (fun n x => classStep_card_bound ω h2 ha hω D hD c h hc κ n x.val) 10
  have hr := classRoot_card_bound ω h2 ha hω D hD c h hc κ
  have hi : (Nat.card {L : Fin 13 → SymplecticLagrangian ω // PointProfile ω c h L}:ℝ) ≤
      Nat.card (ValidSeq 3 (classRootConstraint ω c h κ) (classStepConstraint ω c h κ) 10) := by
    exact_mod_cast Nat.card_le_card_of_injective _ (pointProfile_class_injection ω c h κ).injective
  calc
    _ ≤ _ := hi.trans hs
    _ ≤ (fullProfileConstant D*(Nat.card (SymplecticLagrangian ω):ℝ)^3*
        (Fintype.card K:ℝ)^(-(faceNaturalCost D c h (classFace κ 0):ℝ)))*
        ∏ n : Fin 10,classStepBound ω D c h κ n.val :=
      mul_le_mul_of_nonneg_right hr (Finset.prod_nonneg fun n _ => classStepBound_nonneg ω D c h κ n.val)
    _ = _ := by
      rw [classStepBound_product]
      have he : -(faceNaturalCost D c h (classFace κ 0):ℝ)+
          (∑ n : Fin 10, (((h (classOldPair κ n)+1).choose 2:ℝ)-
            (faceNaturalCost D c h (classFace κ n.succ):ℝ)))=classExponent D c h κ := by
        unfold classExponent
        rw [Fin.sum_univ_succ (fun i : Fin 11 => (faceNaturalCost D c h (classFace κ i):ℝ)),Finset.sum_sub_distrib]
        ring
      rw [←he,Real.rpow_add hq]
      ring
end ExposureProfile

 theorem sum_class_faces (f : Fin 22 → ℝ) :
    (∑ κ : Fin 6, ∑ n : Fin 11, f (classFace κ n))=3*∑ j, f j := by
  rw [←Fintype.sum_prod_type (fun p : Fin 6 × Fin 11 => f (classFace p.1 p.2))]
  rw [←Finset.sum_fiberwise Finset.univ (fun p : Fin 6 × Fin 11 => classFace p.1 p.2)]
  have he (j : Fin 22) : (∑ p ∈ Finset.univ.filter (fun p : Fin 6 × Fin 11 => classFace p.1 p.2=j),
      f (classFace p.1 p.2))=3*f j := by
    calc _ = ∑ _p ∈ Finset.univ.filter (fun p : Fin 6 × Fin 11 => classFace p.1 p.2=j), f j := by
            apply Finset.sum_congr rfl
            intro p hp
            rw [(Finset.mem_filter.mp hp).2]
         _ = _ := by rw [Finset.sum_const,classFace_occurs]; simp only [nsmul_eq_mul,Nat.cast_ofNat]
  simp_rw [he]
  rw [Finset.mul_sum]
 theorem sum_class_old_pairs (f : Fin 33 → ℝ) :
    (∑ κ : Fin 6, ∑ n : Fin 10, f (classOldPair κ n))=∑ e, (3-(separationCount e:ℝ))*f e := by
  rw [←Fintype.sum_prod_type (fun p : Fin 6 × Fin 10 => f (classOldPair p.1 p.2))]
  rw [←Finset.sum_fiberwise Finset.univ (fun p : Fin 6 × Fin 10 => classOldPair p.1 p.2)]
  apply Finset.sum_congr rfl
  intro e _
  calc _ = ∑ _p ∈ Finset.univ.filter (fun p : Fin 6 × Fin 10 => classOldPair p.1 p.2=e), f e := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [(Finset.mem_filter.mp hp).2]
       _ = _ := by rw [Finset.sum_const,classTree_occurs]; simp only [nsmul_eq_mul,Nat.cast_sub (separationCount_le e),Nat.cast_ofNat]
noncomputable def profileCost (D : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) : ℝ :=
  (∑ j, (faceNaturalCost D c h j:ℝ))/2-(∑ e, (3-(separationCount e:ℝ))*triangular (h e))/6
 theorem sum_class_exponent (D : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) :
    (∑ κ, classExponent D c h κ)= -6*profileCost D c h := by
  simp only [classExponent,Finset.sum_add_distrib,Finset.sum_neg_distrib,triangular_nat]
  rw [sum_class_faces (fun j => (faceNaturalCost D c h j:ℝ)),sum_class_old_pairs (fun e => triangular (h e))]
  unfold profileCost
  ring

section GlobalExposure
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
 theorem pointProfile_card_bound (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (hc : ∀ j, c j≤D) :
    (Nat.card {L : Fin 13 → SymplecticLagrangian ω // PointProfile ω c h L}:ℝ) ≤
      (fullProfileConstant D)^11*(Nat.card (SymplecticLagrangian ω):ℝ)^13*
        (Fintype.card K:ℝ)^(-profileCost D c h) := by
  have hq : 0<(Fintype.card K:ℝ) := by exact_mod_cast Fintype.card_pos (α:=K)
  have hb := Finset.prod_le_prod₀ (s:=Finset.univ) (f:=fun _κ : Fin 6 =>
      (Nat.card {L : Fin 13 → SymplecticLagrangian ω // PointProfile ω c h L}:ℝ))
    (fun _κ _ => Nat.cast_nonneg _) (fun κ _ => pointProfile_class_card_bound ω h2 ha hω D hD c h hc κ)
  simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hb
  rw [←Real.rpow_sum_of_pos hq,sum_class_exponent] at hb
  have he : -6*profileCost D c h=(-profileCost D c h)*(6:ℕ) := by norm_num; ring
  rw [he,Real.rpow_mul_natCast hq.le] at hb
  have hC := fullProfileConstant_pos D
  apply (pow_le_pow_iff_left₀ (Nat.cast_nonneg _) (by positivity) (by norm_num : (6:ℕ)≠0)).mp
  simpa only [mul_pow] using hb
end GlobalExposure
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
section ZeroSequential
variable {A : Type*} [Finite A]
def ZeroSeqValid (P : (n : ℕ) → (Fin n → A) → A → Prop) :
    (n : ℕ) → (Fin n → A) → Prop
  | 0,_ => True
  | n+1,x => ZeroSeqValid P n (Fin.init x) ∧ P n (Fin.init x) (x (Fin.last n))
abbrev ZeroValidSeq (P : (n : ℕ) → (Fin n → A) → A → Prop) (n : ℕ) :=
  {x : Fin n → A // ZeroSeqValid P n x}
noncomputable def zeroValidSeqSuccEquiv
    (P : (n : ℕ) → (Fin n → A) → A → Prop) (n : ℕ) :
    ZeroValidSeq P (n+1) ≃ Σ x : ZeroValidSeq P n, {a : A // P n x.val a} where
  toFun x := ⟨⟨Fin.init x.val,x.property.1⟩,⟨x.val (Fin.last n),x.property.2⟩⟩
  invFun x := ⟨Fin.snoc (α := fun _ => A) x.1.val x.2.val,by
    have hs : Fin.snoc (α := fun _ => A) x.1.val x.2.val (Fin.last n)=x.2.val := Fin.snoc_last (α := fun _ => A) x.2.val x.1.val
    change ZeroSeqValid P n (Fin.init (Fin.snoc (α := fun _ => A) x.1.val x.2.val)) ∧
      P n (Fin.init (Fin.snoc (α := fun _ => A) x.1.val x.2.val)) (Fin.snoc (α := fun _ => A) x.1.val x.2.val (Fin.last n))
    rw [Fin.init_snoc,hs]
    exact ⟨x.1.property,x.2.property⟩⟩
  left_inv x := Subtype.ext (Fin.snoc_init_self x.val)
  right_inv x := by
    rcases x with ⟨⟨x,hx⟩,⟨a,ha⟩⟩
    dsimp
    apply Sigma.ext
    · apply Subtype.ext
      exact Fin.init_snoc (α := fun _ => A) a x
    · apply (Subtype.heq_iff_coe_eq
        (p := fun b => P n (Fin.init (Fin.snoc (α := fun _ => A) x a)) b)
        (q := fun b => P n x b) (fun b => by rw [Fin.init_snoc])).mpr
      exact Fin.snoc_last (α := fun _ => A) a x

 theorem zeroValidSeq_card_bound
    (P : (n : ℕ) → (Fin n → A) → A → Prop) (B : ℕ → ℝ)
    (hB : ∀ n, 0≤B n) (hb : ∀ n (x : ZeroValidSeq P n), (Nat.card {a : A // P n x.val a}:ℝ) ≤ B n)
    (n : ℕ) : (Nat.card (ZeroValidSeq P n):ℝ) ≤
      ∏ i : Fin n, B i.val := by
  classical
  induction n with
  | zero =>
    rw [Fin.prod_univ_zero]
    norm_num [ZeroValidSeq,ZeroSeqValid,Nat.card_eq_fintype_card,Fintype.card_subtype]
  | succ n ih =>
    let := Fintype.ofFinite (ZeroValidSeq P n)
    rw [Nat.card_congr (zeroValidSeqSuccEquiv P n),Nat.card_sigma,Nat.cast_sum]
    calc
      _ ≤ ∑ _x : ZeroValidSeq P n, B n := Finset.sum_le_sum (fun x _ => hb n x)
      _ = (Nat.card (ZeroValidSeq P n):ℝ)*B n := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
      _ ≤ (∏ i : Fin n, B i.val)*B n := mul_le_mul_of_nonneg_right ih (hB n)
      _ = _ := by rw [Fin.prod_univ_castSucc]; simp only [Fin.val_castSucc,Fin.val_last]
end ZeroSequential
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section OrthogonalTuple
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)

def OrthogonalStep (R : ℕ → ℕ → Prop) (n : ℕ) (x : Fin n → E) (y : E) : Prop :=
  LinearIndependent K (Fin.snoc (α := fun _ => E) x y) ∧ ∀ i : Fin n, R i.val n → ω (x i) y=0
abbrev OrthogonalTuple (R : ℕ → ℕ → Prop) (n : ℕ) :=
  {x : Fin n → E // LinearIndependent K x ∧ ∀ i j : Fin n, i.val<j.val → R i.val j.val → ω (x i) (x j)=0}
 theorem orthogonalSeq_independent (R : ℕ → ℕ → Prop) (n : ℕ)
    (x : ZeroValidSeq (OrthogonalStep ω R) n) : LinearIndependent K x.val := by
  cases n with
  | zero =>
    exact linearIndependent_empty_type
  | succ n =>
    have hx := x.property.2.1
    rwa [Fin.snoc_init_self] at hx
 theorem orthogonalTuple_valid (R : ℕ → ℕ → Prop) (n : ℕ) (x : OrthogonalTuple ω R n) :
    ZeroSeqValid (OrthogonalStep ω R) n x.val := by
  induction n with
  | zero => trivial
  | succ n ih =>
    have hli : LinearIndependent K (Fin.init x.val) := x.property.1.comp Fin.castSucc (Fin.castSucc_injective n)
    have hrel : ∀ i j : Fin n, i.val<j.val → R i.val j.val → ω (Fin.init x.val i) (Fin.init x.val j)=0 := by
      intro i j hij hr
      exact x.property.2 i.castSucc j.castSucc hij hr
    refine ⟨ih ⟨Fin.init x.val,hli,hrel⟩,?_,?_⟩
    · simpa only [Fin.snoc_init_self] using x.property.1
    · intro i hir
      exact x.property.2 i.castSucc (Fin.last n) i.isLt (by simpa only [Fin.val_castSucc,Fin.val_last,Nat.zero_add] using hir)
noncomputable def orthogonalTupleToSeq (R : ℕ → ℕ → Prop) (n : ℕ) :
    OrthogonalTuple ω R n ↪ ZeroValidSeq (OrthogonalStep ω R) n where
  toFun x := ⟨x.val,orthogonalTuple_valid ω R n x⟩
  inj' := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : ZeroValidSeq (OrthogonalStep ω R) n => z.val) h
noncomputable def priorConstraintCount (R : ℕ → ℕ → Prop) (n : ℕ) : ℕ :=
  Nat.card {i : Fin n // R i.val n}
variable [Fintype K] [Finite E]
 theorem independent_orthogonal_card (hω : ω.Nondegenerate) {n : ℕ} (x : Fin n → E)
    (hx : LinearIndependent K x) (s : Finset (Fin n)) :
    Nat.card {y : E // ∀ i∈s, ω (x i) y=0}=(Fintype.card K)^(finrank K E-s.card) := by
  classical
  let z : s → E := fun i => x i.val
  let S : Submodule K E := Submodule.span K (Set.range z)
  have hli : LinearIndependent K z := hx.comp (fun i : s => i.val) Subtype.val_injective
  have hdim : finrank K S=s.card := by rw [finrank_span_eq_card hli,Fintype.card_coe]
  have he : {y : E // ∀ i∈s, ω (x i) y=0} ≃ ω.orthogonal S :=
    Equiv.subtypeEquivRight (fun y => by
      constructor
      · intro hy
        rw [LinearMap.BilinForm.mem_orthogonal_iff]
        have hh : S ≤ LinearMap.ker (ω.flip y) := by
          apply Submodule.span_le.mpr
          rintro _ ⟨i,rfl⟩
          exact hy i.val i.property
        intro v hv
        exact hh hv
      · intro hy i hi
        exact hy (x i) (Submodule.subset_span ⟨⟨i,hi⟩,rfl⟩))
  rw [Nat.card_congr he,Module.natCard_eq_pow_finrank (K := K),Nat.card_eq_fintype_card,
    ω.finrank_orthogonal hω S,hdim]
 theorem orthogonalStep_card_bound (hω : ω.Nondegenerate) (R : ℕ → ℕ → Prop)
    (n : ℕ) (x : ZeroValidSeq (OrthogonalStep ω R) n) :
    (Nat.card {y : E // OrthogonalStep ω R n x.val y}:ℝ) ≤
      (Fintype.card K:ℝ)^(finrank K E-priorConstraintCount R n) := by
  classical
  let s : Finset (Fin n) := Finset.univ.filter fun i => R i.val n
  have he : s.card=priorConstraintCount R n := by
    rw [priorConstraintCount,Nat.card_eq_fintype_card,Fintype.card_subtype]
  have hi : Nat.card {y : E // OrthogonalStep ω R n x.val y} ≤ Nat.card {y : E // ∀ i∈s, ω (x.val i) y=0} :=
    Nat.card_le_card_of_injective (fun y => ⟨y.val,fun i hi => y.property.2 i (Finset.mem_filter.mp hi).2⟩)
      (by
        intro a b h
        apply Subtype.ext
        exact congrArg (fun z : {y : E // ∀ i∈s, ω (x.val i) y=0} => z.val) h)
  rw [independent_orthogonal_card ω hω x.val (orthogonalSeq_independent ω R n x),he] at hi
  exact_mod_cast hi
 theorem orthogonalTuple_card_bound (hω : ω.Nondegenerate) (R : ℕ → ℕ → Prop) (n : ℕ) :
    (Nat.card (OrthogonalTuple ω R n):ℝ) ≤
      (Fintype.card K:ℝ)^(∑ i : Fin n, (finrank K E-priorConstraintCount R i.val)) := by
  classical
  have hs := zeroValidSeq_card_bound (OrthogonalStep ω R)
    (fun i => (Fintype.card K:ℝ)^(finrank K E-priorConstraintCount R i))
    (fun _ => by positivity) (orthogonalStep_card_bound ω hω R) n
  rw [Finset.prod_pow_eq_pow_sum] at hs
  have hh : (Nat.card (OrthogonalTuple ω R n):ℝ) ≤ Nat.card (ZeroValidSeq (OrthogonalStep ω R) n) := by
    exact_mod_cast Nat.card_le_card_of_injective _ (orthogonalTupleToSeq ω R n).injective
  exact hh.trans hs
end OrthogonalTuple
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
noncomputable def constraintPairCount (R : ℕ → ℕ → Prop) (n : ℕ) : ℕ := by
  classical
  exact ∑ j : Fin n, ∑ i : Fin n, if i.val<j.val ∧ R i.val j.val then 1 else 0
 theorem sum_priorConstraintCount (R : ℕ → ℕ → Prop) (n : ℕ) :
    (∑ i : Fin n, priorConstraintCount R i.val)=constraintPairCount R n := by
  classical
  apply Finset.sum_congr rfl
  intro j _
  let e : {i : Fin j.val // R i.val j.val} ≃ {i : Fin n // i.val<j.val ∧ R i.val j.val} :=
    { toFun := fun i => ⟨⟨i.val.val,lt_trans (by simpa only [Nat.zero_add] using i.val.isLt) j.isLt⟩,by simpa only [Nat.zero_add] using i.val.isLt,i.property⟩
      invFun := fun i => ⟨⟨i.val.val,by simpa only [Nat.zero_add] using i.property.1⟩,i.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [priorConstraintCount,Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_subtype]
  simp only [Finset.sum_boole,Nat.cast_id]
section TupleRpow
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
 theorem orthogonalTuple_card_rpow (hω : ω.Nondegenerate) (R : ℕ → ℕ → Prop) (n : ℕ)
    (hn : n≤finrank K E) :
    (Nat.card {x : Fin n → E // LinearIndependent K x ∧
      ∀ i j : Fin n, i.val<j.val → R i.val j.val → ω (x i) (x j)=0}:ℝ) ≤
      (Fintype.card K:ℝ)^((n:ℝ)*finrank K E-constraintPairCount R n) := by
  classical
  have hb := orthogonalTuple_card_bound ω hω R n
  have hle (i : Fin n) : priorConstraintCount R i.val≤finrank K E := by
    have hh : Nat.card {j : Fin i.val // R j.val i.val} ≤ Nat.card (Fin i.val) :=
      Nat.card_le_card_of_injective _ Subtype.val_injective
    simp only [Nat.card_eq_fintype_card,Fintype.card_fin] at hh
    simpa only [priorConstraintCount,Nat.card_eq_fintype_card] using hh.trans (i.isLt.le.trans hn)
  have he : ((∑ i : Fin n, (finrank K E-priorConstraintCount R i.val):ℕ):ℝ)=
      (n:ℝ)*finrank K E-constraintPairCount R n := by
    rw [Nat.cast_sum]
    simp only [Nat.cast_sub (hle _),Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,nsmul_eq_mul,←Nat.cast_sum,sum_priorConstraintCount]
  rw [←Real.rpow_natCast,he] at hb
  unfold OrthogonalTuple at hb
  exact hb
end TupleRpow
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
 theorem nat_card_subtype_sum {A : Type*} [Fintype A] (P : A → Prop) [DecidablePred P] :
    Nat.card {a : A // P a}=∑ a : A, if P a then (1:ℕ) else 0 := by
  classical
  simp only [Nat.card_eq_fintype_card,Fintype.card_subtype,Finset.sum_boole,Nat.cast_id]
 theorem double_constraintPairCount (R : ℕ → ℕ → Prop) (n : ℕ)
    (hR : ∀ i j, R i j → R j i) :
    2*constraintPairCount R n = Nat.card {p : Fin n × Fin n // p.1≠p.2 ∧ R p.1.val p.2.val} := by
  classical
  rw [nat_card_subtype_sum,Fintype.sum_prod_type]
  have he (i j : Fin n) :
      (if i≠j ∧ R i.val j.val then (1:ℕ) else 0)=
      (if i.val<j.val ∧ R i.val j.val then 1 else 0)+
      (if j.val < i.val ∧ R j.val i.val then 1 else 0) := by
    have hr : R i.val j.val ↔ R j.val i.val := ⟨hR _ _,hR _ _⟩
    rcases lt_trichotomy i.val j.val with h|h|h
    · have hne : i≠j := fun hh => by subst j; exact (lt_irrefl _ h)
      simp [hne,h,not_lt.mpr h.le]
    · have hij : i=j := Fin.ext h
      simp [hij]
    · have hne : i≠j := fun hh => by subst j; exact (lt_irrefl _ h)
      simp [hne,h,not_lt.mpr h.le,←hr]
  simp_rw [he,Finset.sum_add_distrib]
  rw [Finset.sum_comm (f:=fun i j : Fin n => if i.val<j.val ∧ R i.val j.val then (1:ℕ) else 0)]
  unfold constraintPairCount
  omega
section AbstractTuple
variable {K E A : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E] [Fintype A]
variable (ω : LinearMap.BilinForm K E)
abbrev ConstrainedTuple (R : A → A → Prop) :=
  {x : A → E // LinearIndependent K x ∧ ∀ a b, R a b → ω (x a) (x b)=0}
noncomputable def enumeratedRelation (R : A → A → Prop) (e : Fin (Fintype.card A) ≃ A) : ℕ → ℕ → Prop :=
  fun i j => ∃ (hi : i<Fintype.card A) (hj : j<Fintype.card A), R (e ⟨i,hi⟩) (e ⟨j,hj⟩)
 theorem enumeratedRelation_symm (R : A → A → Prop) (hR : ∀ a b, R a b → R b a)
    (e : Fin (Fintype.card A) ≃ A) (i j : ℕ) :
    enumeratedRelation R e i j → enumeratedRelation R e j i := by
  rintro ⟨hi,hj,h⟩
  exact ⟨hj,hi,hR _ _ h⟩
 theorem constrainedTuple_card_rpow (hω : ω.Nondegenerate) (R : A → A → Prop)
    (hR : ∀ a b, R a b → R b a) (hn : Fintype.card A≤finrank K E) :
    (Nat.card (ConstrainedTuple ω R):ℝ) ≤
      (Fintype.card K:ℝ)^((Fintype.card A:ℝ)*finrank K E-
        (Nat.card {p : A×A // p.1≠p.2 ∧ R p.1 p.2}:ℝ)/2) := by
  classical
  let e : Fin (Fintype.card A) ≃ A := (Fintype.equivFin A).symm
  let Q := enumeratedRelation R e
  have hb := orthogonalTuple_card_rpow ω hω Q (Fintype.card A) hn
  let f : ConstrainedTuple ω R →
      {x : Fin (Fintype.card A) → E // LinearIndependent K x ∧ ∀ i j, i.val<j.val → Q i.val j.val → ω (x i) (x j)=0} :=
    fun x => ⟨fun i=>x.val (e i),x.property.1.comp e e.injective,by
      intro i j _ hij
      obtain ⟨hi,hj,h⟩ := hij
      exact x.property.2 _ _ h⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    funext a
    have hh := congrArg (fun z => z.val (e.symm a)) h
    simpa only [f,Equiv.apply_symm_apply] using hh
  have hc := Nat.card_le_card_of_injective f hf
  have he : {p : Fin (Fintype.card A) × Fin (Fintype.card A) // p.1≠p.2 ∧ Q p.1.val p.2.val} ≃
      {p : A×A // p.1≠p.2 ∧ R p.1 p.2} :=
    (e.prodCongr e).subtypeEquiv (by
      intro p
      change (p.1≠p.2 ∧ enumeratedRelation R e p.1.val p.2.val) ↔ (e p.1≠e p.2 ∧ R (e p.1) (e p.2))
      simp only [e.injective.ne_iff,enumeratedRelation]
      constructor
      · rintro ⟨hne,hi,hj,h⟩
        exact ⟨hne,h⟩
      · rintro ⟨hne,h⟩
        exact ⟨hne,p.1.isLt,p.2.isLt,h⟩)
  have hd := double_constraintPairCount Q (Fintype.card A) (enumeratedRelation_symm R hR e)
  rw [Nat.card_congr he] at hd
  have hd' : (constraintPairCount Q (Fintype.card A):ℝ)=
      (Nat.card {p : A×A // p.1≠p.2 ∧ R p.1 p.2}:ℝ)/2 := by
    have hdc : (2:ℝ)*constraintPairCount Q (Fintype.card A)=(Nat.card {p : A×A // p.1≠p.2 ∧ R p.1 p.2}:ℝ) := by exact_mod_cast hd
    linarith
  rw [hd'] at hb
  exact (by exact_mod_cast hc : (Nat.card (ConstrainedTuple ω R):ℝ)≤_).trans hb
end AbstractTuple
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section ResidualCount
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
 theorem independentTuples_card_lower (k : ℕ) (hE : finrank K E=k) :
    (Fintype.card K:ℝ)^(k*k) ≤ 2^k*(Nat.card (IndependentTuple K E k):ℝ) := by
  classical
  have hq : (2:ℝ)≤Fintype.card K := by exact_mod_cast (Fintype.one_lt_card (α:=K))
  have hq0 : (0:ℝ)<Fintype.card K := by linarith
  have hle (i : Fin k) : Fintype.card K ^ i.val ≤ Fintype.card K ^ k :=
    Nat.pow_le_pow_right Fintype.card_pos i.isLt.le
  have hp (i : Fin k) : (Fintype.card K:ℝ)^k ≤
      2*((Fintype.card K:ℝ)^k-(Fintype.card K:ℝ)^i.val) := by
    have h₁ : 2*(Fintype.card K:ℝ)^i.val ≤ (Fintype.card K:ℝ)^(i.val+1) := by
      rw [pow_succ]
      nlinarith [pow_nonneg hq0.le i.val]
    have h₂ : (Fintype.card K:ℝ)^(i.val+1) ≤ (Fintype.card K:ℝ)^k :=
      pow_le_pow_right₀ (by linarith) i.isLt
    linarith
  have h := Finset.prod_le_prod₀ (s:=Finset.univ) (fun _i : Fin k => fun _ => pow_nonneg hq0.le k)
    (fun i _ => hp i)
  rw [IndependentTuple,card_linearIndependent (by omega),hE,Nat.cast_prod]
  simp only [Nat.cast_sub (hle _),Nat.cast_pow] 
  simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,←pow_mul,Finset.prod_mul_distrib] using h

variable (ω : LinearMap.BilinForm K E)
 theorem containingLagrangian_card_rpow (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) (S : Submodule K E) :
    (Nat.card {L : SymplecticLagrangian ω // S≤L.val}:ℝ) ≤
      lagrangianConstant D * (Nat.card (SymplecticLagrangian ω):ℝ) *
        (Fintype.card K:ℝ)^(-(D:ℝ)*finrank K S+(finrank K S:ℝ)*(finrank K S-1)/2) := by
  classical
  have hq : 0<(Fintype.card K:ℝ) := by exact_mod_cast Fintype.card_pos (α:=K)
  by_cases his : S≤ω.orthogonal S
  · have hs := isotropic_finrank_le_half ω hω D hD S his
    have h := (containingLagrangian_card_bounds ω h2 ha hω D hD S his).2
    have hl := (symplecticLagrangian_card_bounds ω h2 ha hω D hD).1
    have hC := lagrangianConstant_mono (Nat.sub_le D (finrank K S))
    have he : (((D-finrank K S+1).choose 2:ℕ):ℝ) =
        ((D+1).choose 2:ℕ) + (-(D:ℝ)*finrank K S+(finrank K S:ℝ)*(finrank K S-1)/2) := by
      rw [Nat.cast_choose_two,Nat.cast_choose_two]
      simp only [Nat.cast_add,Nat.cast_one,Nat.cast_sub hs]
      ring
    rw [←Real.rpow_natCast,he,Real.rpow_add hq] at h
    calc
      _ ≤ _ := h
      _ ≤ _ := by
        rw [Real.rpow_natCast,←mul_assoc]
        exact mul_le_mul_of_nonneg_right (mul_le_mul hC hl (by positivity) (lagrangianConstant_pos D).le) (Real.rpow_nonneg hq.le _)
  · have hz : Nat.card {L : SymplecticLagrangian ω // S≤L.val}=0 := by
      let : IsEmpty {L : SymplecticLagrangian ω // S≤L.val} := ⟨fun L => his (by
        calc
          S ≤ L.val.val := L.property
          _ = ω.orthogonal L.val.val := L.val.property.symm
          _ ≤ ω.orthogonal S := ω.orthogonal_le L.property)⟩
      exact Nat.card_eq_zero.mpr (Or.inl inferInstance)
    rw [hz,Nat.cast_zero]
    exact mul_nonneg (mul_nonneg (lagrangianConstant_pos D).le (Nat.cast_nonneg _)) (Real.rpow_nonneg hq.le _)
end ResidualCount
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section FamilySpan
variable {K E I : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype I]
variable [Finite E]
abbrev FamilySpanStratum (h : I → ℕ) (k : ℕ) :=
  {A : (i : I) → DimSubspace K E (h i) // finrank K ↥(⨆ i, (A i).val)=k}
noncomputable def familySpanCoding (h : I → ℕ) (k : ℕ) (A : FamilySpanStratum (K:=K) (E:=E) h k) :
    Σ W : DimSubspace K E k, (i : I) → DimSubspace K W.val (h i) :=
  ⟨⟨⨆ i, (A.val i).val,A.property⟩,fun i => restrictDimSubspace (⨆ i, (A.val i).val)
    (A.val i) (le_iSup (fun i => (A.val i).val) i)⟩
omit [Fintype I] [Finite E] in
 theorem familySpanCoding_injective (h : I → ℕ) (k : ℕ) :
    Function.Injective (familySpanCoding (K:=K) (E:=E) h k) := by
  let recover : (Σ W : DimSubspace K E k, (i : I) → DimSubspace K W.val (h i)) → (I → Submodule K E) :=
    fun x i => (x.2 i).val.map x.1.val.subtype
  have he (A : FamilySpanStratum (K:=K) (E:=E) h k) : recover (familySpanCoding h k A)=fun i => (A.val i).val := by
    funext i
    change ((A.val i).val.comap (⨆ j, (A.val j).val).subtype).map (⨆ j, (A.val j).val).subtype = _
    rw [Submodule.map_comap_subtype]
    exact inf_eq_right.mpr (le_iSup (fun j => (A.val j).val) i)
  intro A B hAB
  have hh := congrArg recover hAB
  rw [he,he] at hh
  apply Subtype.ext
  funext i
  exact Subtype.ext (congrFun hh i)
variable [Fintype K]
 theorem familySpan_card_upper (h : I → ℕ) (k : ℕ) (hk : k≤finrank K E) (hh : ∀ i, h i≤k) :
    (Nat.card (FamilySpanStratum (K:=K) (E:=E) h k):ℝ) ≤
      2^(k+∑ i, h i)*(Fintype.card K:ℝ)^(k*(finrank K E-k)+∑ i, h i*(k-h i)) := by
  classical
  let := Fintype.ofFinite (DimSubspace K E k)
  have hf (W : DimSubspace K E k) :
      (Nat.card ((i : I) → DimSubspace K W.val (h i)):ℝ) ≤
      (2:ℝ)^(∑ i, h i)*(Fintype.card K:ℝ)^(∑ i, h i*(k-h i)) := by
    rw [Nat.card_pi,Nat.cast_prod]
    have hh' (i : I) := subspace_count_upper (K:=K) (V:=W.val) (h i) (by rw [W.property];exact hh i)
    simp only [W.property] at hh'
    have hp := Finset.prod_le_prod₀ (s:=Finset.univ) (fun i _ => Nat.cast_nonneg (Nat.card (DimSubspace K W.val (h i)))) (fun i _ => hh' i)
    simpa only [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum] using hp
  have hs := real_card_sigma_le (B:=DimSubspace K E k) _ hf
  have hi : (Nat.card (FamilySpanStratum (K:=K) (E:=E) h k):ℝ) ≤
      Nat.card (Σ W : DimSubspace K E k, (i : I) → DimSubspace K W.val (h i)) := by
    exact_mod_cast Nat.card_le_card_of_injective _ (familySpanCoding_injective (K:=K) (E:=E) h k)
  calc
    _ ≤ _ := hi.trans hs
    _ ≤ (2^k*(Fintype.card K:ℝ)^(k*(finrank K E-k))) *
        (2^(∑ i, h i)*(Fintype.card K:ℝ)^(∑ i, h i*(k-h i))) :=
      mul_le_mul_of_nonneg_right (subspace_count_upper k hk) (by positivity)
    _ = _ := by rw [pow_add,pow_add];ring
end FamilySpan
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section DirectFamilies
variable {K E I : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype I]
variable [Finite E]
variable (ω : LinearMap.BilinForm K E)
abbrev DirectFamily (h : I → ℕ) (R : I → I → Prop) :=
  {A : (i : I) → DimSubspace K E (h i) // iSupIndep (fun i => (A i).val) ∧
    ∀ i j, R i j → ∀ x∈(A i).val, ∀ y∈(A j).val, ω x y=0}
abbrev FamilyBases {h : I → ℕ} {R : I → I → Prop} (A : DirectFamily ω h R) :=
  (i : I) → IndependentTuple K (A.val i).val (h i)
omit [Fintype I] in
 theorem directFamilyBases_independent {h : I → ℕ} {R : I → I → Prop}
    (A : DirectFamily ω h R) (b : FamilyBases ω A) :
    LinearIndependent K (fun x : Σ i, Fin (h i) => (((b x.1).val x.2 : (A.val x.1).val):E)) := by
  classical
  apply linearIndependent_iUnion_finite (f := fun (i : I) (a : Fin (h i)) => ((b i).val a:E))
  · intro i
    exact (b i).property.map' (A.val i).val.subtype (Submodule.ker_subtype _)
  · intro i t _ hi
    have he (j : I) : Submodule.span K (Set.range (fun a => (((b j).val a : (A.val j).val):E)))=(A.val j).val :=
      tuple_spans (h j) (A.val j) (b j)
    simp_rw [he]
    exact A.property.1.disjoint_biSup hi
noncomputable def directBasisForget (h : I → ℕ) (R : I → I → Prop)
    (x : Σ A : DirectFamily ω h R, FamilyBases ω A) :
    ConstrainedTuple ω (fun a b : Σ i, Fin (h i) => R a.1 b.1) :=
  ⟨fun a => ((x.2 a.1).val a.2:E),directFamilyBases_independent ω x.1 x.2,
    fun a b hr => x.1.property.2 a.1 b.1 hr _ ((x.2 a.1).val a.2).property _ ((x.2 b.1).val b.2).property⟩
omit [Fintype I] in
 theorem directBasisForget_injective (h : I → ℕ) (R : I → I → Prop) :
    Function.Injective (directBasisForget ω h R) := by
  rintro ⟨A,s⟩ ⟨B,t⟩ hh
  have hv (i : I) (a : Fin (h i)) : ((s i).val a:E)=((t i).val a:E) :=
    congrArg (fun x : ConstrainedTuple ω (fun a b : Σ i, Fin (h i) => R a.1 b.1) => x.val ⟨i,a⟩) hh
  have hAB : A=B := by
    apply Subtype.ext
    funext i
    apply Subtype.ext
    rw [←tuple_spans (h i) (A.val i) (s i),←tuple_spans (h i) (B.val i) (t i)]
    congr 2
    exact funext (hv i)
  subst B
  congr 1
  funext i
  apply Subtype.ext
  funext a
  exact Subtype.ext (hv i a)
variable [Fintype K]
 theorem familyBases_card_lower {h : I → ℕ} {R : I → I → Prop} (A : DirectFamily ω h R) :
    (Fintype.card K:ℝ)^(∑ i, h i*h i) ≤ 2^(∑ i, h i)*(Nat.card (FamilyBases ω A):ℝ) := by
  classical
  have hp := Finset.prod_le_prod₀ (s:=Finset.univ)
    (fun i _ => pow_nonneg (Nat.cast_nonneg (Fintype.card K)) (h i*h i))
    (fun i _ => independentTuples_card_lower (E:=(A.val i).val) (h i) (A.val i).property)
  rw [FamilyBases,Nat.card_pi,Nat.cast_prod]
  simpa only [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum] using hp
 theorem directFamily_card_bound (hω : ω.Nondegenerate) (h : I → ℕ) (R : I → I → Prop)
    (hR : ∀ i j, R i j → R j i) (hn : (∑ i, h i)≤finrank K E) :
    (Nat.card (DirectFamily ω h R):ℝ) ≤ 2^(∑ i,h i)*
      (Fintype.card K:ℝ)^((finrank K E:ℝ)*(∑ i, h i)-
        (Nat.card {p : (Σ i, Fin (h i))×(Σ i, Fin (h i)) // p.1≠p.2 ∧ R p.1.1 p.2.1}:ℝ)/2-
        ∑ i, (h i:ℝ)^2) := by
  classical
  let := Fintype.ofFinite (DirectFamily ω h R)
  have hq : 0<(Fintype.card K:ℝ) := by exact_mod_cast Fintype.card_pos (α:=K)
  have hb := constrainedTuple_card_rpow ω hω (fun a b : Σ i, Fin (h i) => R a.1 b.1)
    (fun a b hr => hR _ _ hr) (by simpa only [Fintype.card_sigma,Fintype.card_fin] using hn)
  have hf : (Nat.card (Σ A : DirectFamily ω h R, FamilyBases ω A):ℝ) ≤
      Nat.card (ConstrainedTuple ω (fun a b : Σ i, Fin (h i) => R a.1 b.1)) := by
    exact_mod_cast Nat.card_le_card_of_injective _ (directBasisForget_injective ω h R)
  have hl : (Nat.card (DirectFamily ω h R):ℝ)*(Fintype.card K:ℝ)^(∑ i, h i*h i) ≤
      2^(∑ i, h i)*(Nat.card (Σ A : DirectFamily ω h R, FamilyBases ω A):ℝ) := by
    rw [Nat.card_sigma,Nat.cast_sum,Finset.mul_sum]
    calc
      _ = ∑ _A : DirectFamily ω h R, (Fintype.card K:ℝ)^(∑ i, h i*h i) := by
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
      _ ≤ _ := Finset.sum_le_sum (fun A _ => familyBases_card_lower ω A)
  have hm := hl.trans (mul_le_mul_of_nonneg_left (hf.trans hb) (by positivity : (0:ℝ)≤2^(∑ i,h i)))
  have he : ((∑ i, h i*h i:ℕ):ℝ)=∑ i, (h i:ℝ)^2 := by simp only [Nat.cast_sum,Nat.cast_mul,pow_two]
  rw [←Real.rpow_natCast,he] at hm
  have hsum : (Fintype.card (Σ i, Fin (h i)):ℝ)=∑ i, (h i:ℝ) := by simp only [Fintype.card_sigma,Fintype.card_fin,Nat.cast_sum]
  rw [hsum] at hm
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hq _)).mpr at hm
  rw [mul_div_assoc,←Real.rpow_sub hq] at hm
  simpa only [Nat.cast_sum,mul_comm (∑ i, (h i:ℝ)) (finrank K E:ℝ)] using hm
end DirectFamilies
end SidorenkoCounterexample

end OAI
