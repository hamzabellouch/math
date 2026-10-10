import OAI.GroupTheory.BooneHigman.Affine
import OAI.GroupTheory.BooneHigman.AlgebraPresentations

namespace OAI

noncomputable section

/-!
Affine module presentations, stabilized actions, and finite stabilizers.
-/

namespace FiniteAlgebraicEnvelopes.MatrixModule
open scoped BigOperators
variable {R V ι : Type*} [Ring R] [AddCommGroup V] [Module R V] [Fintype ι] [DecidableEq ι]

def applyMatrix (A : Matrix ι ι R) (v : ι → V) : ι → V := fun i => ∑ j, A i j • v j

omit [DecidableEq ι] in
@[simp] theorem applyMatrix_zero (v : ι → V) : applyMatrix (0 : Matrix ι ι R) v=0 := by
  funext i
  simp [applyMatrix]

omit [DecidableEq ι] in
theorem applyMatrix_add (A B : Matrix ι ι R) (v : ι → V) :
    applyMatrix (A+B) v=applyMatrix A v+applyMatrix B v := by
  funext i
  simp [applyMatrix,add_smul,Finset.sum_add_distrib]

omit [DecidableEq ι] in
theorem applyMatrix_sub (A B : Matrix ι ι R) (v : ι → V) :
    applyMatrix (A-B) v=applyMatrix A v-applyMatrix B v := by
  funext i
  simp [applyMatrix,sub_smul,Finset.sum_sub_distrib]

@[simp] theorem applyMatrix_one (v : ι → V) : applyMatrix (1 : Matrix ι ι R) v=v := by
  funext i
  simp [applyMatrix,Matrix.one_apply,ite_smul]

omit [DecidableEq ι] in
theorem applyMatrix_mul (A B : Matrix ι ι R) (v : ι → V) :
    applyMatrix (A*B) v=applyMatrix A (applyMatrix B v) := by
  funext i
  simp only [applyMatrix,Matrix.mul_apply,Finset.sum_smul,Finset.smul_sum,mul_smul]
  exact Finset.sum_comm

omit [DecidableEq ι] in
theorem applyMatrix_vec_add (A : Matrix ι ι R) (v w : ι → V) :
    applyMatrix A (v+w)=applyMatrix A v+applyMatrix A w := by
  funext i
  simp [applyMatrix,smul_add,Finset.sum_add_distrib]

@[simp] theorem applyMatrix_singleVec (A : Matrix ι ι R) (j : ι) (v : V) (i : ι) :
    applyMatrix A (Pi.single j v) i=A i j • v := by
  simp [applyMatrix,Pi.single_apply,smul_ite]

@[simp] theorem applyMatrix_single (i j : ι) (r : R) (v : ι → V) :
    applyMatrix (Matrix.single i j r) v=Pi.single i (r • v j) := by
  funext c
  by_cases hc : c=i
  · subst c
    simp [applyMatrix,Matrix.single_apply]
  · simp [applyMatrix,hc,Ne.symm hc]

def unitsAddEquiv (g : (Matrix ι ι R)ˣ) : (ι → V) ≃+ (ι → V) where
  toFun := applyMatrix g.val
  invFun := applyMatrix g.inv
  left_inv v := by rw [←applyMatrix_mul,g.inv_val,applyMatrix_one]
  right_inv v := by rw [←applyMatrix_mul,g.val_inv,applyMatrix_one]
  map_add' := applyMatrix_vec_add g.val

def unitsAction : (Matrix ι ι R)ˣ →* MulAut (Multiplicative (ι → V)) where
  toFun g := AddEquiv.toMultiplicative (unitsAddEquiv g)
  map_one' := by
    apply MulEquiv.ext
    intro v
    apply Multiplicative.toAdd.injective
    exact applyMatrix_one _
  map_mul' g h := by
    apply MulEquiv.ext
    intro v
    apply Multiplicative.toAdd.injective
    exact applyMatrix_mul _ _ _

@[simp] theorem unitsAction_apply (g : (Matrix ι ι R)ˣ) (v : Multiplicative (ι → V)) :
    (unitsAction g v).toAdd=applyMatrix g.val v.toAdd := rfl

/-- In particular the literal Steinberg action depends only on its elementary matrix. -/
theorem steinberg_action :
    (unitsAction (V:=V)).comp (Steinberg.matrixMap (ι:=Fin 6) (R:=R))=AffineAction.action := by
  apply PresentedGroup.ext
  rintro ⟨⟨⟨a,b⟩,hab⟩,r⟩
  change unitsAction (Steinberg.matrixMap (Steinberg.root a b hab r))=AffineAction.action (Steinberg.root a b hab r)
  rw [Steinberg.matrixMap_root,AffineAction.action_root]
  apply MulEquiv.ext
  intro v
  apply Multiplicative.toAdd.injective
  change applyMatrix (1+Matrix.single a b r) v.toAdd=(AffineAction.elementary a b hab r v).toAdd
  rw [applyMatrix_add,applyMatrix_one,applyMatrix_single]
  exact (AffineAction.elementary_column a b hab r v.toAdd).symm

end FiniteAlgebraicEnvelopes.MatrixModule

section
namespace FiniteAlgebraicEnvelopes.MatrixModule
variable {R V ι : Type*} [Ring R] [AddCommGroup V] [Module R V] [Fintype ι] [DecidableEq ι]

def columnMap (f : V →+ V) (v : ι → V) : ι → V := fun i => f (v i)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem columnMap_add (f : V →+ V) (v w : ι → V) :
    columnMap f (v+w)=columnMap f v+columnMap f w := by funext i; exact map_add f _ _

theorem columnMap_matrix (f : V →+ V) (ψ : R →ₙ+* R)
    (hf : ∀ r v, f (r • v)=ψ r • f v) (A : Matrix ι ι R) (v : ι → V) :
    columnMap f (applyMatrix A v)=applyMatrix (matrixNonunitalMap ψ A) (columnMap f v) := by
  funext i
  simp only [columnMap,applyMatrix,map_sum,hf]
  rfl

theorem columnMap_corrected (f : V →+ V) (ψ : R →ₙ+* R)
    (hf : ∀ r v, f (r • v)=ψ r • f v) (A : Matrix ι ι R) (v : ι → V) :
    columnMap f (applyMatrix A v)=applyMatrix (correctedMap (matrixNonunitalMap ψ) A) (columnMap f v) := by
  change _=applyMatrix (1+matrixNonunitalMap ψ (A-1)) (columnMap f v)
  rw [applyMatrix_add,applyMatrix_one,←columnMap_matrix f ψ hf,←columnMap_add]
  rw [applyMatrix_sub,applyMatrix_one,add_sub_cancel]
end FiniteAlgebraicEnvelopes.MatrixModule

namespace FiniteAlgebraicEnvelopes.NonunitalTensor
open scoped TensorProduct
variable {k B : Type*} [CommRing k] [Ring B] [Algebra k B]

theorem coefficient_compatible (f : B →ₙₐ[k] B) (r : Enveloping.Coeff k B) (b : B) :
    f (r • b)=coefficientRing f r • f b := by
  induction r using TensorProduct.inductionOn with
  | add r s hr hs => simp only [add_smul,map_add,hr,hs]
  | tmul a c =>
    rw [←MulOpposite.op_unop c]
    change f (Enveloping.act k B (a⊗ₜ[k] MulOpposite.op c.unop) b)=
      Enveloping.act k B (f a⊗ₜ[k] MulOpposite.op (f c.unop)) (f b)
    simp only [Enveloping.act_tmul,map_mul]

end FiniteAlgebraicEnvelopes.NonunitalTensor
end

namespace FiniteAlgebraicEnvelopes.MatrixModule
variable {R V ι : Type*} [Ring R] [AddCommGroup V] [Module R V] [Fintype ι] [DecidableEq ι]

/-- A detector after the coefficient map detects every entry of a matrix difference. -/
theorem correctedMatrix_eq_one (ψ : R →ₙ+* R) (b : V)
    (hb : ∀ r : R, ψ r • b=0 → r=0) (A : Matrix ι ι R)
    (hA : ∀ j : ι, applyMatrix (correctedMap (matrixNonunitalMap ψ) A)
      (Pi.single j b)=Pi.single j b) : A=1 := by
  have he (j : ι) : applyMatrix (matrixNonunitalMap ψ (A-1)) (Pi.single j b)=0 := by
    have hh := hA j
    change applyMatrix (1+matrixNonunitalMap ψ (A-1)) (Pi.single j b)=Pi.single j b at hh
    rw [applyMatrix_add,applyMatrix_one] at hh
    exact add_left_cancel (hh.trans (add_zero _).symm)
  apply sub_eq_zero.mp
  ext i j
  apply hb
  simpa using congrFun (he j) i

/-- In particular a corrected unit acting trivially on all columns was already the identity. -/
theorem correctedUnits_eq_one (ψ : R →ₙ+* R) (b : V)
    (hb : ∀ r : R, ψ r • b=0 → r=0) (A : (Matrix (Fin 6) (Fin 6) R)ˣ)
    (hA : ∀ v : Multiplicative (Fin 6 → V), unitsAction (Steinberg.correctedUnits ψ A) v=v) : A=1 := by
  apply Units.ext
  apply correctedMatrix_eq_one ψ b hb
  intro j
  exact congrArg Multiplicative.toAdd (hA (Multiplicative.ofAdd (Pi.single j b)))

end FiniteAlgebraicEnvelopes.MatrixModule

section
namespace FiniteAlgebraicEnvelopes.SequentialLimit
variable {Q : Type*} [Group Q] (f : Monoid.End Q)

def stage (j : ℕ) : Set (Limit f) := Set.range (of f j)

theorem stage_mono {i j : ℕ} (hij : i≤j) : stage f i ⊆ stage f j := by
  rintro _ ⟨x,rfl⟩
  exact ⟨transition f i j hij x,of_transition f i j hij x⟩

theorem next_marker_not_mem (hf : Function.Injective f) {w : Q} (hw : w∉Set.range f) (j : ℕ) :
    of f (j+1) w∉stage f j := by
  rintro ⟨x,hx⟩
  apply hw
  refine ⟨x,of_injective f hf (j+1) ?_⟩
  exact (of_succ f j x).trans hx

theorem stage_strict (hf : Function.Injective f) {w : Q} (hw : w∉Set.range f) (j : ℕ) :
    stage f j ⊂ stage f (j+1) := by
  rw [Set.ssubset_def]
  refine ⟨stage_mono f (Nat.le_succ j),?_⟩
  intro hh
  exact next_marker_not_mem f hf hw j (hh ⟨w,rfl⟩)

theorem marker_ne (hf : Function.Injective f) {w : Q} (hw : w∉Set.range f) {i j : ℕ} (hij : i<j) :
    of f i w≠of f j w := by
  intro he
  have ht : transition f i j (Nat.le_of_lt hij) w=w :=
    of_injective f hf j ((of_transition f i j (Nat.le_of_lt hij) w).trans he)
  have hn : j-i=(j-i-1)+1 := by omega
  change (f^(j-i)) w=w at ht
  rw [hn,pow_succ'] at ht
  exact hw ⟨(f^(j-i-1)) w,ht⟩

theorem markers_injective (hf : Function.Injective f) {w : Q} (hw : w∉Set.range f) :
    Function.Injective (fun j : ℕ => of f j w) := by
  intro i j he
  by_contra hn
  rcases lt_or_gt_of_ne hn with hij|hji
  · exact marker_ne f hf hw hij he
  · exact marker_ne f hf hw hji he.symm

theorem infinite_of_marker (hf : Function.Injective f) {w : Q} (hw : w∉Set.range f) : Infinite (Limit f) :=
  Infinite.of_injective _ (markers_injective f hf hw)

instance countable_limit [Countable Q] : Countable (Limit f) := by
  unfold Limit DirectLimit
  infer_instance
end FiniteAlgebraicEnvelopes.SequentialLimit

namespace FiniteAlgebraicEnvelopes.ColumnLimit
variable {B : Type*} [Ring B] (φ : B →ₙ+* B)

def transition : Monoid.End (Multiplicative (Fin 6 → B)) where
  toFun x := Multiplicative.ofAdd (fun i => φ (x.toAdd i))
  map_one' := by apply Multiplicative.toAdd.injective; funext i; exact map_zero φ
  map_mul' x y := by apply Multiplicative.toAdd.injective; funext i; exact map_add φ _ _

theorem transition_injective (hφ : Function.Injective φ) : Function.Injective (transition φ) := by
  intro x y he
  apply Multiplicative.toAdd.injective
  funext i
  exact hφ (congrArg (fun v : Multiplicative (Fin 6 → B) => v.toAdd i) he)

theorem one_not_range (hφ1 : φ 1≠1) : (1:B)∉Set.range φ := by
  rintro ⟨x,hx⟩
  apply hφ1
  have he : φ 1*φ x=φ x := by rw [←map_mul,one_mul]
  rwa [hx,mul_one] at he

def marker : Multiplicative (Fin 6 → B) := Multiplicative.ofAdd (fun i => if i=0 then 1 else 0)

theorem marker_not_range (hφ1 : φ 1≠1) : marker (B:=B)∉Set.range (transition φ) := by
  rintro ⟨x,hx⟩
  apply one_not_range φ hφ1
  refine ⟨x.toAdd 0,?_⟩
  exact congrArg (fun v : Multiplicative (Fin 6 → B) => v.toAdd 0) hx

theorem limit_infinite (hφ : Function.Injective φ) (hφ1 : φ 1≠1) :
    Infinite (SequentialLimit.Limit (transition φ)) :=
  SequentialLimit.infinite_of_marker _ (transition_injective φ hφ) (marker_not_range φ hφ1)

end FiniteAlgebraicEnvelopes.ColumnLimit
end

section
namespace FiniteAlgebraicEnvelopes.SequentialLimit
variable {A B C : Type*} [Group A] [Group B] [Group C]
variable (f : Monoid.End A) (g : Monoid.End B) (h : Monoid.End C)

theorem exists_common_stage₂ (x : Limit f) (y : Limit g) :
    ∃ i a b, x=of f i a ∧ y=of g i b := by
  obtain ⟨i,a,rfl⟩ := DirectLimit.exists_eq_mk (transition f) x
  obtain ⟨j,b,rfl⟩ := DirectLimit.exists_eq_mk (transition g) y
  exact ⟨max i j,transition f i (max i j) (le_max_left _ _) a,
    transition g j (max i j) (le_max_right _ _) b,
    (of_transition f _ _ _ _).symm,(of_transition g _ _ _ _).symm⟩

theorem exists_common_stage₃ (x : Limit f) (y : Limit g) (z : Limit h) :
    ∃ i a b c, x=of f i a ∧ y=of g i b ∧ z=of h i c := by
  obtain ⟨i,a,b,rfl,rfl⟩ := exists_common_stage₂ f g x y
  obtain ⟨j,c,rfl⟩ := DirectLimit.exists_eq_mk (transition h) z
  exact ⟨max i j,transition f i (max i j) (le_max_left _ _) a,
    transition g i (max i j) (le_max_left _ _) b,
    transition h j (max i j) (le_max_right _ _) c,
    (of_transition f _ _ _ _).symm,(of_transition g _ _ _ _).symm,(of_transition h _ _ _ _).symm⟩
end FiniteAlgebraicEnvelopes.SequentialLimit

namespace FiniteAlgebraicEnvelopes.LimitAction
open SequentialLimit
variable {Q V : Type*} [Group Q] [Group V]
variable (α : Q →* MulAut V) (f : Monoid.End Q) (g : Monoid.End V)
variable (hc : ∀ x v, g (α x v)=α (f x) (g v))

include hc
theorem compatible_pow (n : ℕ) (x : Q) (v : V) :
    (g^n) (α x v)=α ((f^n) x) ((g^n) v) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ',pow_succ']
    exact (congrArg g ih).trans (hc _ _)

def applyLimit : Limit f → Limit g → Limit g :=
  DirectLimit.map₂ (transition f) (transition g) (transition g) (fun _ x v => α x v)
    (fun i j _ x v => compatible_pow α f g hc (j-i) x v)

@[simp] theorem applyLimit_of (i : ℕ) (x : Q) (v : V) :
    applyLimit α f g hc (of f i x) (of g i v)=of g i (α x v) := by
  change DirectLimit.map₂ (transition f) (transition g) (transition g) (fun _ x v => α x v) _ ⟦⟨i,x⟩⟧ ⟦⟨i,v⟩⟧=⟦⟨i,α x v⟩⟧
  exact DirectLimit.map₂_def (transition f) (transition g) (transition g)
    (fun _ x v => α x v) (fun i j _ x v => compatible_pow α f g hc (j-i) x v) i x v

@[simp] theorem applyLimit_one (v : Limit g) : applyLimit α f g hc 1 v=v := by
  obtain ⟨i,v,rfl⟩ := DirectLimit.exists_eq_mk (transition g) v
  change applyLimit α f g hc 1 (of g i v)=of g i v
  rw [←map_one (of f i),applyLimit_of,map_one]
  rfl

theorem applyLimit_mul (x y : Limit f) (v : Limit g) :
    applyLimit α f g hc (x*y) v=applyLimit α f g hc x (applyLimit α f g hc y v) := by
  obtain ⟨i,x,y,v,rfl,rfl,rfl⟩ := exists_common_stage₃ f f g x y v
  rw [←map_mul,applyLimit_of,applyLimit_of,applyLimit_of,map_mul]
  rfl

theorem applyLimit_mul_vec (x : Limit f) (v w : Limit g) :
    applyLimit α f g hc x (v*w)=applyLimit α f g hc x v*applyLimit α f g hc x w := by
  obtain ⟨i,x,v,w,rfl,rfl,rfl⟩ := exists_common_stage₃ f g g x v w
  rw [←map_mul,applyLimit_of,applyLimit_of,applyLimit_of,map_mul,map_mul]

def action : Limit f →* MulAut (Limit g) where
  toFun x := {
    toFun := applyLimit α f g hc x
    invFun := applyLimit α f g hc x⁻¹
    left_inv v := by rw [←applyLimit_mul,inv_mul_cancel,applyLimit_one]
    right_inv v := by rw [←applyLimit_mul,mul_inv_cancel,applyLimit_one]
    map_mul' := applyLimit_mul_vec α f g hc x }
  map_one' := by apply MulEquiv.ext; exact applyLimit_one α f g hc
  map_mul' x y := by apply MulEquiv.ext; exact applyLimit_mul α f g hc x y

@[simp] theorem action_of (i : ℕ) (x : Q) (v : V) :
    action α f g hc (of f i x) (of g i v)=of g i (α x v) := applyLimit_of α f g hc i x v

/-- Detection after one transition suffices for faithfulness on the direct limit. -/
theorem action_injective (hg : Function.Injective g)
    (hd : ∀ x : Q, (∀ v : V, α (f x) v=v) → x=1) : Function.Injective (action α f g hc) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm _ bot_le
  intro x hx
  change x=1
  change action α f g hc x=1 at hx
  obtain ⟨i,x,rfl⟩ := DirectLimit.exists_eq_mk (transition f) x
  change action α f g hc (of f i x)=1 at hx
  change of f i x=1
  have hx1 : x=1 := hd x (by
    intro v
    have he := DFunLike.congr_fun hx (of g (i+1) v)
    rw [←of_succ f i x,action_of] at he
    exact of_injective g hg (i+1) he)
  rw [hx1,map_one]

end FiniteAlgebraicEnvelopes.LimitAction
end

section
namespace FiniteAlgebraicEnvelopes.MatrixModule
variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]

def elementaryAction : Steinberg.ElementaryGroup R →* MulAut (Multiplicative (Fin 6 → V)) :=
  (unitsAction (V:=V)).comp (Steinberg.ElementaryGroup R).subtype

@[simp] theorem elementaryAction_quotient (x : Steinberg.Group (Fin 6) R) :
    elementaryAction (V:=V) (Steinberg.elementaryQuotient x)=AffineAction.action x :=
  DFunLike.congr_fun (steinberg_action (R:=R) (V:=V)) x
end FiniteAlgebraicEnvelopes.MatrixModule

namespace FiniteAlgebraicEnvelopes.NonunitalTensor
open SequentialLimit
variable {k B : Type*} [CommRing k] [Ring B] [Algebra k B]
variable (φ : B →ₙₐ[k] B)

abbrev LinearGroup := Steinberg.ElementaryGroup (Enveloping.Coeff k B)
abbrev Columns := Multiplicative (Fin 6 → B)

def linearAction : LinearGroup (k:=k) (B:=B) →* MulAut (Columns (B:=B)) := MatrixModule.elementaryAction

def linearStep : Monoid.End (LinearGroup (k:=k) (B:=B)) := Steinberg.elementaryTransition (coefficientRing φ)
def columnStep : Monoid.End (Columns (B:=B)) := ColumnLimit.transition (φ : B →ₙ+* B)

theorem linear_column_compatible (x : LinearGroup (k:=k) (B:=B)) (v : Columns (B:=B)) :
    columnStep φ (linearAction x v)=linearAction (linearStep φ x) (columnStep φ v) := by
  apply Multiplicative.toAdd.injective
  exact MatrixModule.columnMap_corrected φ.toAddMonoidHom (coefficientRing φ)
    (coefficient_compatible φ) x.val.val v.toAdd

def limitAction : Limit (linearStep φ) →* MulAut (Limit (columnStep φ)) :=
  LimitAction.action linearAction (linearStep φ) (columnStep φ) (linear_column_compatible φ)

theorem limitAction_injective (hφ : Function.Injective φ) (b : B)
    (hd : ∀ r : Enveloping.Coeff k B, Enveloping.act k B (coefficientRing φ r) b=0 → r=0) :
    Function.Injective (limitAction φ) := by
  apply LimitAction.action_injective _ _ _ _ (ColumnLimit.transition_injective _ hφ)
  intro x hx
  apply Subtype.ext
  exact MatrixModule.correctedUnits_eq_one (coefficientRing φ) b hd x.val hx

end FiniteAlgebraicEnvelopes.NonunitalTensor
end

namespace FiniteAlgebraicEnvelopes.MatrixModule
variable {R V W : Type*} [Ring R] [AddCommGroup V] [AddCommGroup W] [Module R V] [Module R W]

def columnEquiv (e : V ≃ₗ[R] W) : Multiplicative (Fin 6 → V) ≃* Multiplicative (Fin 6 → W) :=
  AddEquiv.toMultiplicative (LinearEquiv.piCongrRight (fun _ : Fin 6 => e)).toAddEquiv

theorem columnEquiv_action (e : V ≃ₗ[R] W) (x : Steinberg.Group (Fin 6) R)
    (v : Multiplicative (Fin 6 → V)) :
    columnEquiv e (AffineAction.action x v)=AffineAction.action x (columnEquiv e v) := by
  rw [←elementaryAction_quotient,←elementaryAction_quotient]
  apply Multiplicative.toAdd.injective
  funext i
  change e (∑ j, (Steinberg.matrixMap x).val i j • v.toAdd j)=
    ∑ j, (Steinberg.matrixMap x).val i j • e (v.toAdd j)
  simp

def affineEquiv (e : V ≃ₗ[R] W) : AffineAction.Group (R:=R) (V:=V) ≃* AffineAction.Group (R:=R) (V:=W) :=
  SemidirectProduct.congr (columnEquiv e) (MulEquiv.refl _) (by
    intro x
    apply MulEquiv.ext
    intro v
    exact columnEquiv_action e x v)

end FiniteAlgebraicEnvelopes.MatrixModule

namespace FiniteAlgebraicEnvelopes.Enveloping
variable {B : Type*} [Ring B] [Algebra (ZMod 2) B]

/-- The manuscript cyclic-module and finite relative-presentation lemmas assembled.
The Steinberg finite-presentation premise is precisely the separate cited theorem. -/
theorem affine_finitePresentation (S : Set B) (hS : S.Finite) (hgen : Algebra.adjoin (ZMod 2) S=⊤)
    [Group.IsFinitelyPresented (Steinberg.Group (Fin 6) (Coeff (ZMod 2) B))] :
    Group.IsFinitelyPresented (AffineAction.Group (R:=Coeff (ZMod 2) B) (V:=B)) := by
  classical
  let T := AlgebraGenerators.envelopingGenerators S
  have hT : T.Finite := AlgebraGenerators.envelopingGenerators_finite hS
  let F : Finset (Coeff (ZMod 2) B) := insert 1 hT.toFinset
  have hF1 : (1 : Coeff (ZMod 2) B) ∈ F := Finset.mem_insert_self _ _
  have hF : Subring.closure (↑F : Set (Coeff (ZMod 2) B))=⊤ := by
    apply top_unique
    rw [←AlgebraGenerators.envelopingGenerators_generate hgen]
    apply Subring.closure_mono
    intro x hx
    exact Finset.mem_insert_of_mem (by simpa using hx)
  have hD := hS.image (difference (ZMod 2) B)
  let D := hD.toFinset
  have hDset : (↑D : Set (Coeff (ZMod 2) B))=difference (ZMod 2) B '' S := hD.coe_toFinset
  have hDrel : Submodule.span (Coeff (ZMod 2) B) (↑D : Set (Coeff (ZMod 2) B))=relations (k:=ZMod 2) S := by
    rw [hDset]
    rfl
  let := FiniteAffine.affine_finitelyPresented F D hF1 hF
  let e : (Coeff (ZMod 2) B ⧸ Submodule.span (Coeff (ZMod 2) B) (↑D : Set (Coeff (ZMod 2) B))) ≃ₗ[Coeff (ZMod 2) B] B :=
    (Submodule.quotEquivOfEq _ _ hDrel).trans (quotientEquiv S hgen)
  exact Group.IsFinitelyPresented.equiv (MatrixModule.affineEquiv e)

end FiniteAlgebraicEnvelopes.Enveloping

namespace FiniteAlgebraicEnvelopes.LimitAction
open SequentialLimit
variable {Q V : Type*} [Group Q] [Group V]
variable (α : Q →* MulAut V) (f : Monoid.End Q) (g : Monoid.End V)
variable (hc : ∀ x v, g (α x v)=α (f x) (g v))

/-- One step into the simple-algebra image gives transitivity in the limit. -/
theorem transitive_nonone
    (ht : ∀ v w : V, v≠1 → w≠1 → ∃ x : Q, α x (g v)=g w)
    (v w : Limit g) (hv : v≠1) (hw : w≠1) :
    ∃ x : Limit f, action α f g hc x v=w := by
  obtain ⟨i,v,w,rfl,rfl⟩ := exists_common_stage₂ g g v w
  have hv1 : v≠1 := by intro he; exact hv (he ▸ map_one _)
  have hw1 : w≠1 := by intro he; exact hw (he ▸ map_one _)
  obtain ⟨x,hx⟩ := ht v w hv1 hw1
  refine ⟨of f (i+1) x,?_⟩
  rw [←of_succ g i v,action_of,hx,of_succ]

/-- The stage shift intertwines the actual linear limit actions. -/
theorem action_shift (x : Limit f) (v : Limit g) :
    action α f g hc (shift f x) (shift g v)=shift g (action α f g hc x v) := by
  obtain ⟨i,x,v,rfl,rfl⟩ := exists_common_stage₂ f g x v
  rw [shift_apply_of,shift_apply_of,action_of,action_of,shift_apply_of]

theorem action_shift_inv (x : Limit f) (v : Limit g) :
    action α f g hc ((shift f)⁻¹ x) ((shift g)⁻¹ v)=(shift g)⁻¹ (action α f g hc x v) := by
  apply (shift g).injective
  simpa using (action_shift α f g hc ((shift f)⁻¹ x) ((shift g)⁻¹ v)).symm

theorem action_shift_zpow (n : ℤ) (x : Limit f) (v : Limit g) :
    action α f g hc (((shift f)^n) x) (((shift g)^n) v)=((shift g)^n) (action α f g hc x v) := by
  induction n using Int.induction_on generalizing x v with
  | zero => simp
  | succ n ih =>
    rw [zpow_add,zpow_add,zpow_one,zpow_one]
    change action α f g hc (((shift f)^(n:ℤ)) (shift f x)) (((shift g)^(n:ℤ)) (shift g v)) = _
    rw [ih,action_shift]
    rfl
  | pred n ih =>
    rw [sub_eq_add_neg,zpow_add,zpow_add,zpow_neg_one,zpow_neg_one]
    change action α f g hc (((shift f)^(-(n:ℤ))) ((shift f)⁻¹ x)) (((shift g)^(-(n:ℤ))) ((shift g)⁻¹ v)) = _
    rw [ih,action_shift_inv]
    rfl

def torusAction : Torus f →* MulAut (Limit g) :=
  SemidirectProduct.lift (action α f g hc) (SequentialLimit.action g) (by
    intro n
    ext x v
    have he := action_shift_zpow α f g hc n.toAdd x (((shift g)^n.toAdd)⁻¹ v)
    change action α f g hc (((shift f)^n.toAdd) x) v=
      ((shift g)^n.toAdd) (action α f g hc x (((shift g)^n.toAdd)⁻¹ v))
    simpa only [MulAut.apply_inv_self] using he)

@[simp] theorem torusAction_apply (a : Torus f) (v : Limit g) :
    torusAction α f g hc a v=action α f g hc a.left (((shift g)^a.right.toAdd) v) := rfl

@[simp] theorem torusAction_inl (x : Limit f) :
    torusAction α f g hc (SemidirectProduct.inl x)=action α f g hc x := by
  simp [torusAction]

@[simp] theorem shift_pow_of (i n : ℕ) (v : V) :
    ((shift g)^n) (of g i v)=of g (i+n) v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change shift g (((shift g)^n) (of g i v))=of g (i+(n+1)) v
    rw [ih,shift_apply_of]
    rfl

/-- A finite-stage linear element cannot be a strictly advancing shift. -/
theorem ne_positive_shift (hg : Function.Injective g) {w : V} (hw : w∉Set.range g)
    (x : Limit f) (n : ℕ) (hn : 0<n) : action α f g hc x≠(shift g)^n := by
  obtain ⟨i,q,rfl⟩ := DirectLimit.exists_eq_mk (transition f) x
  intro he
  have hv := DFunLike.congr_fun he (of g i w)
  change action α f g hc (of f i q) (of g i w)=((shift g)^n) (of g i w) at hv
  rw [action_of,shift_pow_of] at hv
  have hm : of g (i+n) w∈stage g i := ⟨α q w,hv⟩
  have hm' := stage_mono g (show i ≤ i + n - 1 from by omega) hm
  have heq : i+n=(i+n-1)+1 := by omega
  rw [heq] at hm'
  exact next_marker_not_mem g hg hw (i+n-1) hm'

theorem shift_exponent_zero (hg : Function.Injective g) {w : V} (hw : w∉Set.range g)
    (x : Limit f) (z : ℤ) (he : action α f g hc x=(shift g)^z) : z=0 := by
  cases z with
  | ofNat n =>
    cases n with
    | zero => rfl
    | succ n =>
      exact False.elim (ne_positive_shift α f g hc hg hw x (n+1) (Nat.succ_pos _) (by
        change action α f g hc x=(shift g)^((n+1 : ℕ):ℤ) at he
        rwa [zpow_natCast] at he))
  | negSucc n =>
    have hi := congrArg Inv.inv he
    have hi' : action α f g hc x⁻¹=(shift g)^(n+1) := by
      simpa only [←map_inv,zpow_negSucc,inv_inv] using hi
    exact False.elim (ne_positive_shift α f g hc hg hw x⁻¹ (n+1) (Nat.succ_pos _) hi')

theorem torusAction_injective (hα : Function.Injective (action α f g hc))
    (hg : Function.Injective g) {w : V} (hw : w∉Set.range g) :
    Function.Injective (torusAction α f g hc) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm _ bot_le
  intro a ha
  change a=1
  have he : action α f g hc a.left * (shift g)^a.right.toAdd=1 := ha
  have hz : a.right.toAdd=0 := shift_exponent_zero α f g hc hg hw a.left⁻¹ a.right.toAdd (by
    rw [map_inv]
    exact (inv_eq_of_mul_eq_one_right he))
  have hr : a.right=1 := Multiplicative.toAdd.injective hz
  have hl : a.left=1 := hα (by simpa [hz] using he)
  exact SemidirectProduct.ext hl hr

def affineStep : Monoid.End (V ⋊[α] Q) :=
  SemidirectProduct.map g f (by intro x; ext v; exact hc x v)

@[simp] theorem affineStep_left (a : V ⋊[α] Q) : (affineStep α f g hc a).left=g a.left := rfl
@[simp] theorem affineStep_right (a : V ⋊[α] Q) : (affineStep α f g hc a).right=f a.right := rfl

@[simp] theorem affineStep_pow_left (n : ℕ) (a : V ⋊[α] Q) :
    (((affineStep α f g hc)^n) a).left=(g^n) a.left := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ',pow_succ']
    change g ((((affineStep α f g hc)^n) a).left)=g ((g^n) a.left)
    rw [ih]

@[simp] theorem affineStep_pow_right (n : ℕ) (a : V ⋊[α] Q) :
    (((affineStep α f g hc)^n) a).right=(f^n) a.right := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ',pow_succ']
    change f ((((affineStep α f g hc)^n) a).right)=f ((f^n) a.right)
    rw [ih]

abbrev AffineLimit := (Limit g) ⋊[action α f g hc] Limit f

def affineStage (i : ℕ) : (V ⋊[α] Q) →* AffineLimit α f g hc :=
  SemidirectProduct.map (of g i) (of f i) (by intro x; ext v; exact (action_of α f g hc i x v).symm)

def affineLimitMap : Limit (affineStep α f g hc) →* AffineLimit α f g hc :=
  lift (affineStep α f g hc) (affineStage α f g hc)
    (compatible_of_succ _ _ (by intro i a; ext <;> exact of_succ _ i _))

@[simp] theorem affineLimitMap_of (i : ℕ) (a : V ⋊[α] Q) :
    affineLimitMap α f g hc (of (affineStep α f g hc) i a)=affineStage α f g hc i a := rfl

private theorem pow_map_one_later {W : Type*} [Group W] (p : Monoid.End W)
    (i j m : ℕ) (hij : i ≤ j) (hjm : j ≤ m) (x : W) (hx : (p^(j-i)) x=1) :
    (p^(m-i)) x=1 := by
  rw [show m-i=(m-j)+(j-i) by omega,pow_add]
  change (p^(m-j)) ((p^(j-i)) x)=1
  rw [hx,map_one]

theorem affineLimitMap_injective : Function.Injective (affineLimitMap α f g hc) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm _ bot_le
  intro x hx
  change x=1
  obtain ⟨i,a,rfl⟩ := DirectLimit.exists_eq_mk (transition (affineStep α f g hc)) x
  change affineStage α f g hc i a=1 at hx
  have hv : of g i a.left=1 := congrArg SemidirectProduct.left hx
  have hq : of f i a.right=1 := congrArg SemidirectProduct.right hx
  obtain ⟨j,hij,hj⟩ := (DirectLimit.exists_eq_one (G:=fun _ : ℕ => V) (f:=transition g) ⟨i,a.left⟩).mp hv
  obtain ⟨k,hik,hk⟩ := (DirectLimit.exists_eq_one (G:=fun _ : ℕ => Q) (f:=transition f) ⟨i,a.right⟩).mp hq
  apply (DirectLimit.exists_eq_one (G:=fun _ : ℕ => V ⋊[α] Q) (f:=transition (affineStep α f g hc)) ⟨i,a⟩).mpr
  refine ⟨max j k,le_trans hij (le_max_left _ _),?_⟩
  apply SemidirectProduct.ext
  · exact (affineStep_pow_left α f g hc (max j k-i) a).trans
      (pow_map_one_later g i j (max j k) hij (le_max_left _ _) a.left hj)
  · exact (affineStep_pow_right α f g hc (max j k-i) a).trans
      (pow_map_one_later f i k (max j k) hik (le_max_right _ _) a.right hk)

theorem affineLimitMap_surjective : Function.Surjective (affineLimitMap α f g hc) := by
  intro a
  obtain ⟨i,v,q,hv,hq⟩ := exists_common_stage₂ g f a.left a.right
  refine ⟨of (affineStep α f g hc) i ⟨v,q⟩,?_⟩
  exact SemidirectProduct.ext hv.symm hq.symm

def affineLimitEquivalence : Limit (affineStep α f g hc) ≃* AffineLimit α f g hc :=
  MulEquiv.ofBijective (affineLimitMap α f g hc) ⟨affineLimitMap_injective α f g hc,affineLimitMap_surjective α f g hc⟩

end FiniteAlgebraicEnvelopes.LimitAction

end

end OAI
