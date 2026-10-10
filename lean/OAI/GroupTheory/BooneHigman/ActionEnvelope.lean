import OAI.GroupTheory.BooneHigman.AffineModules
import OAI.GroupTheory.BooneHigman.SteinbergPresentation
import OAI.GroupTheory.BooneHigman.GroupInput

namespace OAI

noncomputable section

/-!
Full finitely presented faithful two-transitive action envelope and type-(A) applications.
-/

namespace FiniteAlgebraicEnvelopes
variable {A B : Type*} [Group A] [Group B]

/-- Intertwining of bijections propagates to every integer iterate. -/
theorem intertwine_zpow (F : A → B) (s : MulAut A) (t : MulAut B)
    (h : ∀ x, F (s x)=t (F x)) (n : ℤ) (x : A) : F ((s^n) x)=(t^n) (F x) := by
  have hinv (x : A) : F (s⁻¹ x)=t⁻¹ (F x) := by
    apply t.injective
    simpa only [MulAut.apply_inv_self] using (h (s⁻¹ x)).symm
  induction n using Int.induction_on generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [zpow_add,zpow_add,zpow_one,zpow_one]
    change F ((s^(n:ℤ)) (s x))=(t^(n:ℤ)) (t (F x))
    rw [ih,h]
  | pred n ih =>
    rw [sub_eq_add_neg,zpow_add,zpow_add,zpow_neg_one,zpow_neg_one]
    change F ((s^(-(n:ℤ))) (s⁻¹ x))=(t^(-(n:ℤ))) (t⁻¹ (F x))
    rw [ih,hinv]

namespace SequentialLimit
variable (f : Monoid.End A) (g : Monoid.End B)

def torusCongr (e : Limit f ≃* Limit g) (he : ∀ x, e (shift f x)=shift g (e x)) :
    Torus f ≃* Torus g :=
  SemidirectProduct.congr e (MulEquiv.refl _) (by
    intro z
    ext x
    exact intertwine_zpow e (shift f) (shift g) he z.toAdd x)

def quotientTorusEquiv (q : A →* B) (hq : ∀ x, q (f x)=g (q x))
    (hs : Function.Surjective q) (hk : ∀ x, q x=1 → f x=1) : Torus f ≃* Torus g :=
  torusCongr f g (equivalence f g q hq hs hk) (map_shift f g q hq)

end SequentialLimit
end FiniteAlgebraicEnvelopes

namespace FiniteAlgebraicEnvelopes.LimitAction

section
open SequentialLimit
variable {Q V : Type*} [Group Q] [Group V]
variable (α : Q →* MulAut V) (f : Monoid.End Q) (g : Monoid.End V)
variable (hc : ∀ x v, g (α x v)=α (f x) (g v))

def affineShift : MulAut (AffineLimit α f g hc) :=
  SemidirectProduct.congr (shift g) (shift f) (by intro x; ext v; exact (action_shift α f g hc x v).symm)

@[simp] theorem affineShift_left (a : AffineLimit α f g hc) :
    (affineShift α f g hc a).left=shift g a.left := rfl
@[simp] theorem affineShift_right (a : AffineLimit α f g hc) :
    (affineShift α f g hc a).right=shift f a.right := rfl

@[simp] theorem affineShift_zpow_left (z : ℤ) (a : AffineLimit α f g hc) :
    (((affineShift α f g hc)^z) a).left=((shift g)^z) a.left :=
  intertwine_zpow SemidirectProduct.left (affineShift α f g hc) (shift g) (fun _ => rfl) z a
@[simp] theorem affineShift_zpow_right (z : ℤ) (a : AffineLimit α f g hc) :
    (((affineShift α f g hc)^z) a).right=((shift f)^z) a.right :=
  intertwine_zpow SemidirectProduct.right (affineShift α f g hc) (shift f) (fun _ => rfl) z a

abbrev AffineTorus := (AffineLimit α f g hc) ⋊[zpowersHom _ (affineShift α f g hc)] Multiplicative ℤ

theorem affineLimitEquivalence_shift (x : Limit (affineStep α f g hc)) :
    affineLimitEquivalence α f g hc (shift (affineStep α f g hc) x)=
      affineShift α f g hc (affineLimitEquivalence α f g hc x) := by
  obtain ⟨i,a,rfl⟩ := DirectLimit.exists_eq_mk (transition (affineStep α f g hc)) x
  rfl

def affineTorusEquivalence : Torus (affineStep α f g hc) ≃* AffineTorus α f g hc :=
  SemidirectProduct.congr (affineLimitEquivalence α f g hc) (MulEquiv.refl _) (by
    intro z
    apply MulEquiv.ext
    intro x
    exact intertwine_zpow (affineLimitEquivalence α f g hc) (shift (affineStep α f g hc))
      (affineShift α f g hc) (affineLimitEquivalence_shift α f g hc) z.toAdd x)

/-- Reassociation retains the same translation, linear and stable coordinates. -/
def reassociateTorus : AffineTorus α f g hc ≃* (Limit g) ⋊[torusAction α f g hc] Torus f where
  toFun a := ⟨a.left.left,⟨a.left.right,a.right⟩⟩
  invFun a := ⟨⟨a.left,a.right.left⟩,a.right.right⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' a b := by
    apply SemidirectProduct.ext
    · change a.left.left * action α f g hc a.left.right ((((affineShift α f g hc)^a.right.toAdd) b.left).left)=
        a.left.left * action α f g hc a.left.right (((shift g)^a.right.toAdd) b.left.left)
      rw [affineShift_zpow_left]
    · apply SemidirectProduct.ext
      · change a.left.right * (((affineShift α f g hc)^a.right.toAdd) b.left).right=
          a.left.right * ((shift f)^a.right.toAdd) b.left.right
        rw [affineShift_zpow_right]
      · rfl

def fullGroupEquivalence : Torus (affineStep α f g hc) ≃* (Limit g) ⋊[torusAction α f g hc] Torus f :=
  (affineTorusEquivalence α f g hc).trans (reassociateTorus α f g hc)

end

open SequentialLimit
variable {P Q V : Type*} [Group P] [Group Q] [Group V]
variable (α : P →* MulAut V) (β : Q →* MulAut V)
variable (f : Monoid.End P) (h : Monoid.End Q) (g : Monoid.End V)
variable (hcα : ∀ x v, g (α x v)=α (f x) (g v))
variable (hcβ : ∀ x v, g (β x v)=β (h x) (g v))
variable (q : P →* Q) (hq : ∀ x, q (f x)=h (q x))
variable (hαβ : ∀ x v, α x v=β (q x) v)

def affineQuotient : (V ⋊[α] P) →* (V ⋊[β] Q) :=
  SemidirectProduct.map (MonoidHom.id V) q (by intro x; ext v; exact hαβ x v)

theorem affineQuotient_surjective (hs : Function.Surjective q) :
    Function.Surjective (affineQuotient α β q hαβ) := by
  intro a
  obtain ⟨p,hp⟩ := hs a.right
  exact ⟨⟨a.left,p⟩,SemidirectProduct.ext rfl hp⟩

include hq in
theorem affineQuotient_natural (a : V ⋊[α] P) :
    affineQuotient α β q hαβ (affineStep α f g hcα a)=
      affineStep β h g hcβ (affineQuotient α β q hαβ a) :=
  SemidirectProduct.ext rfl (hq a.right)

theorem affineQuotient_kernel (hk : ∀ x, q x=1 → f x=1) (a : V ⋊[α] P)
    (ha : affineQuotient α β q hαβ a=1) : affineStep α f g hcα a=1 := by
  have hl : a.left=1 := congrArg SemidirectProduct.left ha
  have hr : q a.right=1 := congrArg SemidirectProduct.right ha
  apply SemidirectProduct.ext
  · change g a.left=1
    rw [hl,map_one]
  · exact hk a.right hr

def affineQuotientTorusEquivalence (hs : Function.Surjective q) (hk : ∀ x, q x=1 → f x=1) :
    Torus (affineStep α f g hcα) ≃* Torus (affineStep β h g hcβ) :=
  quotientTorusEquiv _ _ (affineQuotient α β q hαβ)
    (affineQuotient_natural α β f h g hcα hcβ q hq hαβ) (affineQuotient_surjective α β q hαβ hs)
    (affineQuotient_kernel α β f g hcα q hαβ hk)

def affineQuotientFullEquivalence (hs : Function.Surjective q) (hk : ∀ x, q x=1 → f x=1) :
    Torus (affineStep α f g hcα) ≃* (Limit g) ⋊[torusAction β h g hcβ] Torus h :=
  (affineQuotientTorusEquivalence α β f h g hcα hcβ q hq hαβ hs hk).trans
    (fullGroupEquivalence β h g hcβ)

end FiniteAlgebraicEnvelopes.LimitAction

namespace FiniteAlgebraicEnvelopes.NonunitalTensor

section
open SequentialLimit
variable {k B : Type*} [CommRing k] [Ring B] [Algebra k B]
variable (φ : B →ₙₐ[k] B)

def torusAction : Torus (linearStep φ) →* MulAut (Limit (columnStep φ)) :=
  LimitAction.torusAction (linearAction (k:=k) (B:=B)) (linearStep φ) (columnStep φ)
    (linear_column_compatible φ)

theorem torusAction_injective (hφ : Function.Injective φ) (hφ1 : φ 1≠1) (b : B)
    (hd : ∀ r : Enveloping.Coeff k B, Enveloping.act k B (coefficientRing φ r) b=0 → r=0) :
    Function.Injective (torusAction φ) :=
  LimitAction.torusAction_injective (linearAction (k:=k) (B:=B)) (linearStep φ) (columnStep φ)
    (linear_column_compatible φ) (limitAction_injective φ hφ b hd)
    (ColumnLimit.transition_injective _ hφ) (ColumnLimit.marker_not_range _ hφ1)

@[simp] theorem torusAction_inl (x : Limit (linearStep φ)) :
    torusAction φ (SemidirectProduct.inl x)=limitAction φ x := by
  exact LimitAction.torusAction_inl _ _ _ _ x

abbrev SteinbergGroup := Steinberg.Group (Fin 6) (Enveloping.Coeff k B)
def steinbergStep : Monoid.End (SteinbergGroup (k:=k) (B:=B)) :=
  Steinberg.coefficientMap (coefficientRing φ)

theorem steinberg_column_compatible (x : SteinbergGroup (k:=k) (B:=B)) (v : Columns (B:=B)) :
    columnStep φ (AffineAction.action x v)=AffineAction.action (steinbergStep φ x) (columnStep φ v) := by
  rw [←MatrixModule.elementaryAction_quotient,←MatrixModule.elementaryAction_quotient]
  change columnStep φ (linearAction (Steinberg.elementaryQuotient x) v)=
    linearAction (Steinberg.elementaryQuotient (steinbergStep φ x)) (columnStep φ v)
  erw [steinbergStep,Steinberg.elementary_natural]
  exact linear_column_compatible φ _ _

def affineSteinbergStep : Monoid.End ((Columns (B:=B)) ⋊[AffineAction.action] SteinbergGroup (k:=k) (B:=B)) :=
  LimitAction.affineStep AffineAction.action (steinbergStep φ) (columnStep φ)
    (steinberg_column_compatible φ)

def affineTorusFullEquivalence (p q : Steinberg.SupportedPair (φ : B →ₙ+* B))
    (hpq : p.V*q.U=0) (hqp : q.V*p.U=0) (hsum : p.U*p.V+q.U*q.V=φ 1) :
    Torus (affineSteinbergStep φ) ≃* (Limit (columnStep φ)) ⋊[torusAction φ] Torus (linearStep φ) :=
  LimitAction.affineQuotientFullEquivalence AffineAction.action linearAction
    (steinbergStep φ) (linearStep φ) (columnStep φ)
    (steinberg_column_compatible φ) (linear_column_compatible φ)
    Steinberg.elementaryQuotient (Steinberg.elementary_natural (coefficientRing φ))
    (by intro x v; exact DFunLike.congr_fun (MatrixModule.elementaryAction_quotient x).symm v)
    Steinberg.elementaryQuotient_surjective
    (by intro x hx; apply annihilation φ p q hpq hqp hsum x; exact congrArg Subtype.val hx)

end

open SequentialLimit
variable {k A B : Type*} [CommRing k] [Ring A] [Ring B] [Algebra k A] [Algebra k B] [IsSimpleRing A]
variable (i : A →ₙₐ[k] B) (j : B →ₙₐ[k] A) (hj : Function.Injective j)

include hj in
theorem columnStep_transitive (v w : Columns (B:=B)) (hv : v≠1) (hw : w≠1) :
    ∃ x : LinearGroup (k:=k) (B:=B), linearAction x (columnStep (i.comp j) v)=columnStep (i.comp j) w := by
  have hn (u : Columns (B:=B)) (hu : u≠1) : (fun c : Fin 6 => j (u.toAdd c))≠0 := by
    intro hz
    apply hu
    apply Multiplicative.toAdd.injective
    funext c
    apply hj
    exact (congrFun hz c).trans (map_zero j).symm
  obtain ⟨z,hz⟩ := RowControl.transitive_nonzero i (fun c => j (v.toAdd c)) (fun c => j (w.toAdd c))
    (hn v hv) (hn w hw)
  refine ⟨Steinberg.elementaryQuotient z,?_⟩
  change MatrixModule.elementaryAction (Steinberg.elementaryQuotient z) (columnStep (i.comp j) v)=columnStep (i.comp j) w
  rw [MatrixModule.elementaryAction_quotient]
  apply Multiplicative.toAdd.injective
  exact hz

include hj in
theorem limit_transitive :
    ∀ left right : Limit (columnStep (i.comp j)), left≠1 → right≠1 →
      ∃ actor : Limit (linearStep (i.comp j)), limitAction (i.comp j) actor left=right :=
  LimitAction.transitive_nonone (linearAction (k:=k) (B:=B)) (linearStep (i.comp j)) (columnStep (i.comp j))
    (linear_column_compatible (i.comp j)) (columnStep_transitive i j hj)

end FiniteAlgebraicEnvelopes.NonunitalTensor

section
namespace FiniteAlgebraicEnvelopes.Contracted
instance countableAlgebra (k H : Type*) [CommRing k] [MonoidWithZero H] [Countable k] [Countable H] :
    Countable (Algebra k H) := by
  let : Countable (MonoidAlgebra k H) := MonoidAlgebra.coeff_injective.countable
  exact (zeroIdeal k H).ringCon.mkₐ_surjective (α:=k) |>.countable
end FiniteAlgebraicEnvelopes.Contracted
namespace FiniteAlgebraicEnvelopes.Bootstrap.Source
variable {G : Type*} [Group G] {n : ℕ} (s : Fin n → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word n => evalWord s w=1))

instance bigAlgebra_countable : Countable (BigAlgebra s h (ZMod 2)) := by
  let : Countable (K s h) := (PresentedMonoid.surjective_mk (rels := Compiler.Word.Rel (KAlphabet) (KMachine s h))).countable
  exact Contracted.countableAlgebra _ _

def columnTransition : Monoid.End (Multiplicative (Fin 6 → BigAlgebra s h (ZMod 2))) :=
  ColumnLimit.transition (phi s h (ZMod 2) : _ →ₙ+* _)

abbrev ColumnSpace := SequentialLimit.Limit (columnTransition s h)

instance columnSpace_countable : Countable (ColumnSpace s h) := by
  let : Countable (Multiplicative (Fin 6 → BigAlgebra s h (ZMod 2))) := Multiplicative.toAdd.injective.countable
  exact SequentialLimit.countable_limit (columnTransition s h)

theorem columnSpace_infinite : Infinite (ColumnSpace s h) :=
  ColumnLimit.limit_infinite (B:=BigAlgebra s h (ZMod 2)) (phi s h (ZMod 2) : BigAlgebra s h (ZMod 2) →ₙ+* BigAlgebra s h (ZMod 2))
    (phi_injective s h (ZMod 2)) (phi_one_ne_one s h (ZMod 2))

end FiniteAlgebraicEnvelopes.Bootstrap.Source
end

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source

section
variable {G : Type*} [Group G] {n : ℕ} (s : Fin n → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word n => evalWord s w=1))
variable (k : Type*) [CommRing k] [Nontrivial k]

theorem fixed_tensor_detector (r : R s h k)
    (hr : Enveloping.act k (BigAlgebra s h k) (psi s h k r) (detectingElement s h k)=0) : r=0 := by
  apply detectionLinear_injective s h k
  rw [detectionLinear_apply,hr,LinearMap.map_zero]

def linearAction := NonunitalTensor.limitAction (phi s h k)

theorem linearAction_injective : Function.Injective (linearAction s h k) :=
  NonunitalTensor.limitAction_injective (phi s h k)
  (phi_injective s h k) (detectingElement s h k) (fixed_tensor_detector s h k)

end

variable {G : Type*} [Group G] {n : ℕ} (s : Fin n → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word n => evalWord s w=1))

theorem linear_transitive :
    ∀ left right : ColumnSpace s h, left≠1 → right≠1 →
      ∃ actor : SequentialLimit.Limit (NonunitalTensor.linearStep (phi s h (ZMod 2))),
        linearAction s h (ZMod 2) actor left=right :=
  letI := smallAlgebra_simple s h (ZMod 2)
  NonunitalTensor.limit_transitive (algebraEmbedding s h (ZMod 2)) (j s h (ZMod 2))
    (j_injective s h (ZMod 2))

end FiniteAlgebraicEnvelopes.Bootstrap.Source

namespace FiniteAlgebraicEnvelopes.SequentialLimit
variable {Q : Type*} [Group Q] (f : Monoid.End Q)

instance torus_finitelyGenerated [Group.FG Q] : Group.FG (Torus f) := by
  obtain ⟨S,hS,hfin⟩ := Group.fg_iff.mp (inferInstance : Group.FG Q)
  let T : Set (Torus f) := insert (stable f) (base f '' S)
  let H := Subgroup.closure T
  have ht : stable f∈H := Subgroup.subset_closure (Set.mem_insert _ _)
  have hb (x : Q) : base f x∈H := by
    have hh : Subgroup.closure S≤H.comap (base f) := (Subgroup.closure_le (H.comap (base f))).mpr (by
      intro x hx
      exact Subgroup.subset_closure (Set.mem_insert_of_mem _ ⟨x,hx,rfl⟩))
    rw [hS] at hh
    exact hh (Subgroup.mem_top x)
  have hl (x : Limit f) : (SemidirectProduct.inl x : Torus f)∈H := by
    obtain ⟨i,q,rfl⟩ := DirectLimit.exists_eq_mk (transition f) x
    change SemidirectProduct.inl (of f i q)∈H
    rw [inl_of]
    exact H.mul_mem (H.mul_mem (H.pow_mem ht i) (hb q)) (H.inv_mem (H.pow_mem ht i))
  have hr (z : Multiplicative ℤ) : (SemidirectProduct.inr z : Torus f)∈H := by
    have he : z=(Multiplicative.ofAdd 1)^z.toAdd := by
      apply Multiplicative.toAdd.injective
      simp
    have he' : (SemidirectProduct.inr z : Torus f)=(stable f)^z.toAdd := by
      calc
        _ = SemidirectProduct.inr ((Multiplicative.ofAdd 1)^z.toAdd) := congrArg SemidirectProduct.inr he
        _ = _ := map_zpow SemidirectProduct.inr _ _
    rw [he']
    exact H.zpow_mem ht _
  apply Group.fg_iff.mpr
  refine ⟨T,?_,(hfin.image (base f)).insert (stable f)⟩
  apply top_unique
  intro a _
  change a∈H
  rcases a with ⟨x,z⟩
  rw [SemidirectProduct.mk_eq_inl_mul_inr]
  exact H.mul_mem (hl x) (hr z)

end FiniteAlgebraicEnvelopes.SequentialLimit

namespace FiniteAlgebraicEnvelopes.AffinePermutation
variable {Q V : Type*} [Group Q] [Group V] (α : Q →* MulAut V)

instance action : MulAction (V ⋊[α] Q) V where
  smul a v := a.left * α a.right v
  one_smul v := by
    change (1 : V) * α (1 : Q) v = v
    simp
  mul_smul a b v := by
    change (a*b).left * α (a*b).right v = a.left * α a.right (b.left * α b.right v)
    simp [map_mul,mul_assoc]

@[simp] theorem smul_apply (a : V ⋊[α] Q) (v : V) : a • v=a.left*α a.right v := rfl

theorem faithful (hα : Function.Injective α) : FaithfulSMul (V ⋊[α] Q) V where
  eq_of_smul_eq_smul := by
    intro a b hab
    have hl : a.left=b.left := by simpa using hab 1
    have hr : a.right=b.right := hα (by
      apply MulEquiv.ext
      intro v
      have he := hab v
      simp only [smul_apply,hl] at he
      exact mul_left_cancel he)
    exact SemidirectProduct.ext hl hr

/-- The ordinary affine formula upgrades linear nonzero transitivity to ordered-pair transitivity. -/
theorem two_transitive
    (ht : ∀ v w : V, v≠1 → w≠1 → ∃ x : Q, α x v=w)
    (x₁ x₂ y₁ y₂ : V) (hx : x₁≠x₂) (hy : y₁≠y₂) :
    ∃ a : V ⋊[α] Q, a • x₁=y₁ ∧ a • x₂=y₂ := by
  have hxx : x₁⁻¹*x₂≠1 := by intro h; exact hx (inv_mul_eq_one.mp h)
  have hyy : y₁⁻¹*y₂≠1 := by intro h; exact hy (inv_mul_eq_one.mp h)
  obtain ⟨q,hq⟩ := ht (x₁⁻¹*x₂) (y₁⁻¹*y₂) hxx hyy
  have hh : α q x₂=α q x₁*(y₁⁻¹*y₂) := by
    have he := congrArg (fun z => α q x₁*z) hq
    simpa only [map_mul,map_inv,mul_inv_cancel_left] using he
  refine ⟨⟨y₁*(α q x₁)⁻¹,q⟩,?_,?_⟩
  · simp [smul_apply,mul_assoc]
  · simp [smul_apply,hh,mul_assoc]

/-- The stabilizer of the distinguished identity point is exactly the linear factor. -/
def stabilizerEquivalence : MulAction.stabilizer (V ⋊[α] Q) (1:V) ≃* Q :=
  MulEquiv.ofBijective (SemidirectProduct.rightHom.comp (MulAction.stabilizer (V ⋊[α] Q) (1:V)).subtype) (by
    constructor
    · intro a b he
      apply Subtype.ext
      apply SemidirectProduct.ext
      · have ha : a.val.left=1 := by
          have ha : a.val • (1:V)=1 := a.property
          simpa only [smul_apply,map_one,mul_one] using ha
        have hb : b.val.left=1 := by
          have hb : b.val • (1:V)=1 := b.property
          simpa only [smul_apply,map_one,mul_one] using hb
        exact ha.trans hb.symm
      · exact he
    · intro q
      refine ⟨⟨SemidirectProduct.inr q,?_⟩,rfl⟩
      change (SemidirectProduct.inr q : V ⋊[α] Q) • (1:V)=1
      simp)

/-- At every point, evaluation determines the translation from the linear component. -/
def stabilizerEquivalenceAt (v : V) : MulAction.stabilizer (V ⋊[α] Q) v ≃* Q :=
  MulEquiv.ofBijective (SemidirectProduct.rightHom.comp (MulAction.stabilizer (V ⋊[α] Q) v).subtype) (by
    constructor
    · intro a b he
      apply Subtype.ext
      apply SemidirectProduct.ext
      · have ha : a.val.left * α a.val.right v=v := a.property
        have hb : b.val.left * α b.val.right v=v := b.property
        change a.val.right=b.val.right at he
        rw [he] at ha
        exact mul_right_cancel (ha.trans hb.symm)
      · exact he
    · intro q
      refine ⟨⟨⟨v*(α q v)⁻¹,q⟩,?_⟩,rfl⟩
      change (v*(α q v)⁻¹)*α q v=v
      simp)

instance stabilizer_finitelyGenerated [Group.FG Q] (v : V) :
    Group.FG (MulAction.stabilizer (V ⋊[α] Q) v) :=
  Group.fg_of_surjective (f := (stabilizerEquivalenceAt α v).symm.toMonoidHom)
    (stabilizerEquivalenceAt α v).symm.surjective

end FiniteAlgebraicEnvelopes.AffinePermutation

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source
variable {G : Type*} [Group G] {n : ℕ} (s : Fin n → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word n => evalWord s w=1))

abbrev LinearTorus := SequentialLimit.Torus (NonunitalTensor.linearStep (phi s h (ZMod 2)))

instance elementary_finitelyGenerated : Group.FG (Steinberg.ElementaryGroup (R s h (ZMod 2))) :=
  Group.fg_of_surjective Steinberg.elementaryQuotient_surjective

instance linearTorus_finitelyGenerated : Group.FG (LinearTorus s h) :=
  SequentialLimit.torus_finitelyGenerated _

def fullLinearAction : LinearTorus s h →* MulAut (ColumnSpace s h) :=
  NonunitalTensor.torusAction (phi s h (ZMod 2))

theorem fullLinearAction_injective : Function.Injective (fullLinearAction s h) :=
  NonunitalTensor.torusAction_injective (phi s h (ZMod 2))
  (phi_injective s h (ZMod 2)) (phi_one_ne_one s h (ZMod 2))
  (detectingElement s h (ZMod 2)) (fixed_tensor_detector s h (ZMod 2))

theorem fullLinear_transitive (v w : ColumnSpace s h) (hv : v≠1) (hw : w≠1) :
    ∃ a : LinearTorus s h, fullLinearAction s h a v=w := by
  obtain ⟨x,hx⟩ := linear_transitive s h v w hv hw
  refine ⟨SemidirectProduct.inl x,?_⟩
  exact hx

abbrev FullGroup := ColumnSpace s h ⋊[fullLinearAction s h] LinearTorus s h

instance fullAction_faithful : FaithfulSMul (FullGroup s h) (ColumnSpace s h) :=
  AffinePermutation.faithful (fullLinearAction s h) (fullLinearAction_injective s h)

theorem fullAction_two_transitive (x₁ x₂ y₁ y₂ : ColumnSpace s h) (hx : x₁≠x₂) (hy : y₁≠y₂) :
    ∃ a : FullGroup s h, a • x₁=y₁ ∧ a • x₂=y₂ :=
  AffinePermutation.two_transitive (fullLinearAction s h) (fullLinear_transitive s h) x₁ x₂ y₁ y₂ hx hy

instance fullAction_stabilizer_fg (x : ColumnSpace s h) :
    Group.FG (MulAction.stabilizer (FullGroup s h) x) :=
  AffinePermutation.stabilizer_finitelyGenerated (fullLinearAction s h) x

def affineTransition := NonunitalTensor.affineSteinbergStep (phi s h (ZMod 2))

/-- The literal affine-Steinberg mapping torus is the previously constructed full action group. -/
def affineTorusEquivalence : SequentialLimit.Torus (affineTransition s h) ≃* FullGroup s h :=
  NonunitalTensor.affineTorusFullEquivalence (phi s h (ZMod 2)) (pair0 s h (ZMod 2)) (pair1 s h (ZMod 2))
    (pair0_pair1 s h (ZMod 2)) (pair1_pair0 s h (ZMod 2)) (pairs_sum s h (ZMod 2))

end FiniteAlgebraicEnvelopes.Bootstrap.Source

namespace FiniteAlgebraicEnvelopes.Steinberg
open scoped commutatorElement
variable {R ι : Type*} [Ring R] [Fintype ι] [DecidableEq ι]

def diagonalUnits : (ι → Rˣ) →* (Matrix ι ι R)ˣ where
  toFun d :=
    { val := Matrix.diagonal (fun i => (d i : R))
      inv := Matrix.diagonal (fun i => (↑((d i)⁻¹) : R))
      val_inv := by rw [Matrix.diagonal_mul_diagonal]; simp
      inv_val := by rw [Matrix.diagonal_mul_diagonal]; simp }
  map_one' := by apply Units.ext; simp
  map_mul' d e := by apply Units.ext; simp [Matrix.diagonal_mul_diagonal]

@[simp] theorem diagonalUnits_val (d : ι → Rˣ) :
    (diagonalUnits d).val=Matrix.diagonal (fun i => (d i : R)) := rfl

def weylUnit (p q : ι) (hpq : p≠q) (u : Rˣ) : Group ι R :=
  root p q hpq (u:R)*root q p hpq.symm (-(↑(u⁻¹):R))*root p q hpq (u:R)

theorem weylUnit_matrix (p q : ι) (hpq : p≠q) (u : Rˣ) :
    (matrixMap (weylUnit p q hpq u)).val=1-Matrix.single p p (1:R)-Matrix.single q q (1:R)+
      Matrix.single p q (u:R)-Matrix.single q p (↑(u⁻¹):R) := by
  simp only [weylUnit,map_mul,Units.val_mul,matrixMap_root,elementary_val]
  simp only [add_mul,mul_add,one_mul,mul_one,Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne _ _ _ _ hpq.symm,
    mul_neg,neg_mul,Units.mul_inv,Units.inv_mul,←Matrix.single_neg,add_zero]
  abel

def balancedUnit (p q : ι) (hpq : p≠q) (u : Rˣ) : Group ι R :=
  weylUnit p q hpq u*weylUnit p q hpq (-1)

theorem balancedUnit_matrix (p q : ι) (hpq : p≠q) (u : Rˣ) :
    matrixMap (balancedUnit p q hpq u)=diagonalUnits (fun i => if i=p then u else if i=q then u⁻¹ else 1) := by
  apply Units.ext
  rw [balancedUnit,map_mul,Units.val_mul,weylUnit_matrix,weylUnit_matrix,diagonalUnits_val]
  simp only [Units.val_neg,Units.val_one,inv_neg,inv_one]
  simp only [add_mul,mul_add,sub_mul,mul_sub,one_mul,mul_one,
    Matrix.single_mul_single_same,Matrix.single_mul_single_of_ne _ _ _ _ hpq,
    Matrix.single_mul_single_of_ne _ _ _ _ hpq.symm,
    mul_neg,←Matrix.single_neg,add_zero]
  ext i j
  by_cases hip : i=p <;> by_cases hiq : i=q <;> by_cases hij : i=j
  all_goals subst_vars
  all_goals simp_all [Matrix.single,Matrix.diagonal,eq_comm]

def singleDiagonal (p : ι) : Rˣ →* (Matrix ι ι R)ˣ := diagonalUnits.comp
  { toFun := fun u i => if i=p then u else 1
    map_one' := by funext i; simp
    map_mul' := by intro a b; funext i; by_cases hi : i=p <;> simp [hi] }

@[simp] theorem singleDiagonal_val (p : ι) (u : Rˣ) :
    (singleDiagonal p u).val=Matrix.diagonal (fun i => if i=p then (u:R) else 1) := by
  change Matrix.diagonal (fun i => (↑(if i=p then u else 1):R))=_
  congr 1
  funext i
  by_cases hi : i=p <;> simp [hi]

theorem singleDiagonal_injective (p : ι) : Function.Injective (singleDiagonal (R:=R) p) := by
  intro a b he
  apply Units.ext
  have hh := congrArg (fun m : (Matrix ι ι R)ˣ => m.val p p) he
  simpa only [singleDiagonal_val,Matrix.diagonal_apply_eq,ite_true] using hh

theorem balancedUnit_commutator (p q r : ι) (hpq : p≠q) (hpr : p≠r) (hqr : q≠r) (a b : Rˣ) :
    ⁅matrixMap (balancedUnit p q hpq a),matrixMap (balancedUnit p r hpr b)⁆=
      singleDiagonal p ⁅a,b⁆ := by
  rw [balancedUnit_matrix,balancedUnit_matrix,←map_commutatorElement]
  change diagonalUnits _=diagonalUnits _
  congr 1
  funext i
  by_cases hip : i=p <;> by_cases hiq : i=q <;> by_cases hir : i=r
  all_goals simp_all [commutatorElement_def,eq_comm]

theorem singleDiagonal_commutator_mem (p q r : ι) (hpq : p≠q) (hpr : p≠r) (hqr : q≠r) (a b : Rˣ) :
    singleDiagonal p ⁅a,b⁆ ∈ (matrixMap : Group ι R →* (Matrix ι ι R)ˣ).range := by
  refine ⟨⁅balancedUnit p q hpq a,balancedUnit p r hpr b⁆,?_⟩
  rw [map_commutatorElement,balancedUnit_commutator p q r hpq hpr hqr]

variable {G : Type*} [_root_.Group G]

def firstFactor : G →* G × G where
  toFun g := (g,1)
  map_one' := rfl
  map_mul' _ _ := by ext <;> simp

def inputDiagonal (f : G×G →* Rˣ) := (singleDiagonal (ι:=Fin 6) (R:=R) 0).comp (f.comp firstFactor)

theorem inputDiagonal_injective (f : G×G →* Rˣ) (hf : Function.Injective f) : Function.Injective (inputDiagonal f) :=
  (singleDiagonal_injective 0).comp (hf.comp (by intro x y he; exact congrArg Prod.fst he))

def elementaryEmbedding (f : G×G →* Rˣ) (b : Rˣ)
    (hc : ∀ g : G, ⁅f (g,g),b⁆=f (g,1)) :
    G →* (matrixMap : Group (Fin 6) R →* (Matrix (Fin 6) (Fin 6) R)ˣ).range :=
  (inputDiagonal f).codRestrict _ (by
    intro g
    change singleDiagonal (0:Fin 6) (f (g,1)) ∈ _
    rw [←hc g]
    exact singleDiagonal_commutator_mem 0 1 2 (by decide) (by decide) (by decide) _ _)

theorem elementaryEmbedding_injective (f : G×G →* Rˣ) (hf : Function.Injective f) (b : Rˣ)
    (hc : ∀ g : G, ⁅f (g,g),b⁆=f (g,1)) : Function.Injective (elementaryEmbedding f b hc) := by
  intro x y he
  exact inputDiagonal_injective f hf (congrArg Subtype.val he)

end FiniteAlgebraicEnvelopes.Steinberg

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source
open scoped commutatorElement
variable {G H : Type*} [Group G] [Group H] {n : ℕ} (s : Fin n → H)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word n => evalWord s w=1))
variable (hs : Subgroup.closure (Set.range s)=⊤)
variable (f : G×G →* H) (t : H) (hc : ∀ g : G, ⁅f (g,g),t⁆=f (g,1))

def elementaryInput : G →* Steinberg.ElementaryGroup (R s h (ZMod 2)) :=
  Steinberg.elementaryEmbedding ((coefficientUnits s h (ZMod 2) hs).comp f)
    (coefficientUnits s h (ZMod 2) hs t) (by
      intro g
      change ⁅coefficientUnits s h (ZMod 2) hs (f (g,g)),coefficientUnits s h (ZMod 2) hs t⁆=
        coefficientUnits s h (ZMod 2) hs (f (g,1))
      rw [←map_commutatorElement,hc])

theorem elementaryInput_injective (hf : Function.Injective f) :
    Function.Injective (elementaryInput s h hs f t hc) := by
  apply Steinberg.elementaryEmbedding_injective
  exact (coefficientUnits_injective s h (ZMod 2) hs).comp hf

def elementaryInFull : Steinberg.ElementaryGroup (R s h (ZMod 2)) →* FullGroup s h :=
  SemidirectProduct.inr.comp (SemidirectProduct.inl.comp
    (SequentialLimit.of (NonunitalTensor.linearStep (phi s h (ZMod 2))) 0))

theorem elementaryInFull_injective : Function.Injective (elementaryInFull s h) :=
  SemidirectProduct.inr_injective.comp (SemidirectProduct.inl_injective.comp
    (SequentialLimit.of_injective _ (linearTransition_injective s h (ZMod 2)) 0))

def inputInFull : G →* FullGroup s h :=
  (elementaryInFull s h).comp (elementaryInput s h hs f t hc)

theorem inputInFull_injective (hf : Function.Injective f) : Function.Injective (inputInFull s h hs f t hc) :=
  (elementaryInFull_injective s h).comp (elementaryInput_injective s h hs f t hc hf)

end FiniteAlgebraicEnvelopes.Bootstrap.Source

namespace FiniteAlgebraicEnvelopes

/-- The actual constructed group, all action invariants and the original input embedding.
This lemma deliberately does not claim finite presentation and is not the envelope theorem. -/
theorem input_full_action {G : Type*} [Group G] (hG : HasDecidableWordProblem G) :
    ∃ (Γ : Type) (_ : Group Γ) (X : Type) (_ : MulAction Γ X),
      Countable X ∧ Infinite X ∧ FaithfulSMul Γ X ∧
      (∀ x₁ x₂ y₁ y₂ : X, x₁≠x₂ → y₁≠y₂ → ∃ g : Γ, g • x₁=y₁ ∧ g • x₂=y₂) ∧
      (∀ x : X, Group.FG (MulAction.stabilizer Γ x)) ∧
      ∃ f : G →* Γ, Function.Injective f := by
  obtain ⟨H,_,_,⟨n,s,hs,h⟩,f,t,hf,hc⟩ := group_input G hG
  refine ⟨Bootstrap.Source.FullGroup s h,inferInstance,Bootstrap.Source.ColumnSpace s h,
    inferInstance,inferInstance,Bootstrap.Source.columnSpace_infinite s h,inferInstance,
    Bootstrap.Source.fullAction_two_transitive s h,?_,
    Bootstrap.Source.inputInFull s h hs f t hc,Bootstrap.Source.inputInFull_injective s h hs f t hc hf⟩
  intro x
  exact Bootstrap.Source.fullAction_stabilizer_fg s h x

end FiniteAlgebraicEnvelopes

section
namespace FiniteAlgebraicEnvelopes.Bootstrap.Source
variable {G : Type*} [Group G] {n : ℕ} (s : Fin n → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word n => evalWord s w=1))

instance steinberg_finitelyPresented : Group.IsFinitelyPresented (Steinberg.Group (Fin 6) (R s h (ZMod 2))) :=
  steinberg_finitePresentation_of_free s h (ZMod 2)

instance affine_finitelyPresented :
    Group.IsFinitelyPresented (AffineAction.Group (R:=R s h (ZMod 2)) (V:=BigAlgebra s h (ZMod 2))) :=
  Enveloping.affine_finitePresentation (bigGenerators s h (ZMod 2))
    (bigGenerators_finite s h (ZMod 2)) (bigGenerators_generate s h (ZMod 2))

instance full_finitelyPresented : Group.IsFinitelyPresented (FullGroup s h) := by
  let := MappingTorus.torus_finitelyPresented (affineTransition s h)
  exact Group.IsFinitelyPresented.equiv (affineTorusEquivalence s h)

end FiniteAlgebraicEnvelopes.Bootstrap.Source

namespace FiniteAlgebraicEnvelopes
/-- The source's complete action envelope, in a small universe. -/
theorem input_finite_action_envelope {G : Type*} [Group G] (hG : HasDecidableWordProblem G) :
    ∃ (Γ : Type) (_ : Group Γ) (X : Type) (_ : MulAction Γ X),
      Group.IsFinitelyPresented Γ ∧ Countable X ∧ Infinite X ∧ FaithfulSMul Γ X ∧
      (∀ x₁ x₂ y₁ y₂ : X, x₁≠x₂ → y₁≠y₂ → ∃ g : Γ, g • x₁=y₁ ∧ g • x₂=y₂) ∧
      (∀ x : X, Group.FG (MulAction.stabilizer Γ x)) ∧
      ∃ f : G →* Γ, Function.Injective f := by
  obtain ⟨H,_,_,⟨n,s,hs,h⟩,f,t,hf,hc⟩ := group_input G hG
  refine ⟨Bootstrap.Source.FullGroup s h,inferInstance,Bootstrap.Source.ColumnSpace s h,
    inferInstance,inferInstance,inferInstance,Bootstrap.Source.columnSpace_infinite s h,inferInstance,
    Bootstrap.Source.fullAction_two_transitive s h,?_,
    Bootstrap.Source.inputInFull s h hs f t hc,Bootstrap.Source.inputInFull_injective s h hs f t hc hf⟩
  intro x
  exact Bootstrap.Source.fullAction_stabilizer_fg s h x

end FiniteAlgebraicEnvelopes
end

namespace FiniteAlgebraicEnvelopes

section
universe u
namespace LiftedAction
variable {Γ X : Type*} [Group Γ] [MulAction Γ X]

@[instance_reducible] def action : MulAction (ULift.{u} Γ) (ULift.{u} X) where
  smul g x := ⟨g.down • x.down⟩
  one_smul x := by cases x; exact congrArg ULift.up (one_smul Γ _)
  mul_smul g h x := by cases x; exact congrArg ULift.up (mul_smul g.down h.down _)

attribute [local instance] action

@[simp] lemma down_smul (g : ULift.{u} Γ) (x : ULift.{u} X) : (g • x).down=g.down • x.down := rfl

instance faithful [FaithfulSMul Γ X] : FaithfulSMul (ULift.{u} Γ) (ULift.{u} X) where
  eq_of_smul_eq_smul := by
    intro g h he
    apply ULift.ext
    apply eq_of_smul_eq_smul (α:=X)
    intro x
    exact congrArg ULift.down (he (ULift.up x))

def stabilizerEquivalence (x : ULift.{u} X) :
    MulAction.stabilizer (ULift.{u} Γ) x ≃* MulAction.stabilizer Γ x.down where
  toFun g := ⟨g.val.down,by
    have hg := g.property
    change (g.val • x)=x at hg
    exact congrArg ULift.down hg⟩
  invFun g := ⟨ULift.up g.val,by
    change ULift.up (g.val • x.down)=x
    rw [show g.val • x.down=x.down from g.property]⟩
  left_inv g := by apply Subtype.ext; rfl
  right_inv g := by apply Subtype.ext; rfl
  map_mul' g h := rfl

end LiftedAction

/-- Manuscript Theorem 1.2, with the exact frozen universe and action requirements. -/
theorem envelope (G : Type u) [Group G] [Group.FG G]
    (hG : HasDecidableWordProblem G) : HasActionEnvelope G := by
  obtain ⟨Γ,hΓ,X,hX,hfp,hcount,hinf,hfaith,htwo,hstab,f,hf⟩ := input_finite_action_envelope hG
  let : MulAction (ULift.{u} Γ) (ULift.{u} X) := LiftedAction.action
  let : Group.IsFinitelyPresented (ULift.{u} Γ) :=
    Group.IsFinitelyPresented.equiv (MulEquiv.ulift.symm : Γ ≃* ULift.{u} Γ)
  refine ⟨ULift.{u} Γ,inferInstance,ULift.{u} X,inferInstance,inferInstance,inferInstance,
    inferInstance,LiftedAction.faithful,?_,?_,(MulEquiv.ulift.symm.toMonoidHom).comp f,
    MulEquiv.ulift.symm.injective.comp hf⟩
  · intro x₁ x₂ y₁ y₂ hx hy
    obtain ⟨g,hg₁,hg₂⟩ := htwo x₁.down x₂.down y₁.down y₂.down
      (fun h => hx (ULift.ext _ _ h)) (fun h => hy (ULift.ext _ _ h))
    refine ⟨ULift.up g,?_,?_⟩
    · apply ULift.ext; exact hg₁
    · apply ULift.ext; exact hg₂
  · intro x
    let := hstab x.down
    let e : MulAction.stabilizer Γ x.down ≃* MulAction.stabilizer (ULift.{u} Γ) x :=
      (LiftedAction.stabilizerEquivalence x).symm
    exact Group.fg_of_surjective (f:=e.toMonoidHom) (show Function.Surjective e.toMonoidHom from e.surjective)

open scoped commutatorElement

/-- The original input, not merely its auxiliary double, embeds in the actual elementary part.
The ring and kernel-annihilating coefficient transition are constructed from its algorithmic WP. -/
theorem input_elementary {G : Type*} [Group G] (hG : HasDecidableWordProblem G) :
    ∃ (R : Type) (_ : Ring R) (ψ : R →ₙ+* R), Function.Injective ψ ∧
      (∀ z : Steinberg.Group (Fin 6) R, Steinberg.matrixMap z=1 → Steinberg.coefficientMap ψ z=1) ∧
      ∃ f : G →* Steinberg.ElementaryGroup R, Function.Injective f := by
  classical
  obtain ⟨H,_,_,⟨n,s,hs,h⟩,f,t,hf,hcom⟩ := group_input G hG
  obtain ⟨R,_,ψ,hψ,hker,ν,hν⟩ := Bootstrap.Source.kernelRing s h hs
  have hc (g : G) : ⁅(ν.comp f) (g,g),ν t⁆=(ν.comp f) (g,1) := by
    change ⁅ν (f (g,g)),ν t⁆=ν (f (g,1))
    rw [←map_commutatorElement]
    apply congrArg ν
    exact hcom g
  refine ⟨R,inferInstance,ψ,hψ,hker,
    Steinberg.elementaryEmbedding (ν.comp f) (ν t) hc,?_⟩
  exact Steinberg.elementaryEmbedding_injective _ (hν.comp hf) _ hc

end

/-- The original input embeds in the constructed Steinberg mapping torus.
This does not yet assert finite presentation or simplicity. -/
theorem input_steinberg_torus {G : Type*} [Group G] (hG : HasDecidableWordProblem G) :
    ∃ (R : Type) (_ : Ring R) (ψ : R →ₙ+* R), Function.Injective ψ ∧
      (∀ z : Steinberg.Group (Fin 6) R, Steinberg.matrixMap z=1 → Steinberg.coefficientMap ψ z=1) ∧
      ∃ f : G →* SequentialLimit.Torus (Steinberg.coefficientMap (ι:=Fin 6) ψ), Function.Injective f := by
  obtain ⟨R,_,ψ,hψ,hker,f,hf⟩ := input_elementary hG
  let e := Steinberg.limitEquivalence ψ hker
  let j := SequentialLimit.of (Steinberg.elementaryTransition ψ) 0
  let k : G →* SequentialLimit.Limit (Steinberg.coefficientMap (ι:=Fin 6) ψ) :=
    e.symm.toMonoidHom.comp (j.comp f)
  have hk : Function.Injective k := e.symm.injective.comp
    ((SequentialLimit.of_injective _ (Steinberg.elementaryTransition_injective ψ hψ) 0).comp hf)
  exact ⟨R,inferInstance,ψ,hψ,hker,SemidirectProduct.inl.comp k,SemidirectProduct.inl_injective.comp hk⟩

end FiniteAlgebraicEnvelopes

namespace FiniteAlgebraicEnvelopes.TypeAAction
universe u v
attribute [local instance] Classical.propDecidable
open scoped Pointwise

/-- Unordered two-element subsets, without an ordering or repetitions. -/
def Pairs (X : Type v) := {s : Finset X // s.card=2}

variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]

@[instance_reducible] def pairAction : MulAction Γ (Pairs X) where
  smul g s := ⟨g • s.val,(Finset.card_smul_finset g s.val).trans s.property⟩
  one_smul s := by apply Subtype.ext; exact one_smul _ _
  mul_smul g h s := by apply Subtype.ext; exact mul_smul _ _ _

attribute [local instance] pairAction

lemma pairs_pretransitive
    (htwo : ∀ x₁ x₂ y₁ y₂ : X, x₁ ≠ x₂ → y₁ ≠ y₂ →
      ∃ g : Γ, g • x₁ = y₁ ∧ g • x₂ = y₂) :
    MulAction.IsPretransitive Γ (Pairs X) := by
  refine ⟨?_⟩
  intro s t
  obtain ⟨a,b,hab,hs⟩ := Finset.card_eq_two.mp s.property
  obtain ⟨c,d,hcd,ht⟩ := Finset.card_eq_two.mp t.property
  obtain ⟨g,hg,hg'⟩ := htwo a b c d hab hcd
  refine ⟨g,?_⟩
  apply Subtype.ext
  change g • s.val = t.val
  rw [hs,ht]
  simp [Finset.smul_finset_insert,Finset.smul_finset_singleton,hg,hg']

lemma pairs_single_orbit
    (htwo : ∀ x₁ x₂ y₁ y₂ : X, x₁ ≠ x₂ → y₁ ≠ y₂ →
      ∃ g : Γ, g • x₁ = y₁ ∧ g • x₂ = y₂) :
    Subsingleton (MulAction.orbitRel.Quotient Γ (Pairs X)) :=
  (MulAction.pretransitive_iff_subsingleton_quotient Γ (Pairs X)).mp (pairs_pretransitive htwo)

lemma pairs_finite_orbits
    (htwo : ∀ x₁ x₂ y₁ y₂ : X, x₁ ≠ x₂ → y₁ ≠ y₂ →
      ∃ g : Γ, g • x₁ = y₁ ∧ g • x₂ = y₂) :
    Finite (MulAction.orbitRel.Quotient Γ (Pairs X)) := by
  let := pairs_single_orbit htwo
  infer_instance

/-- Type-(A) action hypotheses. -/
def Hypotheses (Γ : Type u) [Group Γ] (X : Type v) [MulAction Γ X] : Prop :=
  Group.IsFinitelyPresented Γ ∧ Nonempty X ∧ Countable X ∧ FaithfulSMul Γ X ∧
  (∀ x : X, Group.FG (MulAction.stabilizer Γ x)) ∧
  Finite (MulAction.orbitRel.Quotient Γ (Pairs X))

theorem envelope_hypotheses (G : Type u) [Group G] [Group.FG G]
    (hG : HasDecidableWordProblem G) :
    ∃ (Γ : Type u) (_ : Group Γ) (X : Type u) (_ : MulAction Γ X),
      Hypotheses Γ X ∧ ∃ f : G →* Γ, Function.Injective f := by
  obtain ⟨Γ,hΓ,X,hX,hfp,hcount,hinf,hfaith,htwo,hstab,f,hf⟩ := envelope G hG
  exact ⟨Γ,hΓ,X,hX,⟨hfp,inferInstance,hcount,hfaith,hstab,pairs_finite_orbits htwo⟩,f,hf⟩

end FiniteAlgebraicEnvelopes.TypeAAction

end

end OAI
