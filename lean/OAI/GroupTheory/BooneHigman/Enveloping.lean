import OAI.GroupTheory.BooneHigman.Affine

namespace OAI


/-!
Tensor-enveloping algebra actions, simplicity, and elementary row control.
-/


namespace FiniteAlgebraicEnvelopes.Enveloping
open scoped TensorProduct
variable (k B : Type*) [CommRing k] [Ring B] [Algebra k B]
abbrev Coeff := B ⊗[k] Bᵐᵒᵖ

/-- Right multiplication, with its order correctly reversed. -/
def right : Bᵐᵒᵖ →ₐ[k] Module.End k B where
  toFun b := LinearMap.mulRight k b.unop
  map_one' := by ext a; simp
  map_mul' b c := by ext a; simp [mul_assoc]
  map_zero' := by ext a; simp
  map_add' b c := by ext a; simp [mul_add]
  commutes' r := by ext a; simp [Algebra.smul_def,Algebra.commutes]

/-- The true enveloping-ring action on the algebra. -/
def representation : Coeff k B →ₐ[k] Module.End k B :=
  Algebra.TensorProduct.lift (Algebra.lmul k B) (right k B) (by
    intro a b
    ext x
    exact (mul_assoc a x b.unop).symm)

instance module : Module (Coeff k B) B := Module.compHom B (representation k B).toRingHom

@[simp] theorem tmul_smul (a b m : B) :
    (a ⊗ₜ[k] MulOpposite.op b : Coeff k B) • m = a*m*b := by
  change representation k B (a ⊗ₜ[k] MulOpposite.op b) m = _
  simp [representation,right,mul_assoc]

def eval : Coeff k B →ₗ[Coeff k B] B := LinearMap.toSpanSingleton (Coeff k B) B 1
theorem eval_apply (r : Coeff k B) : eval k B r = r • (1:B) := rfl
@[simp] theorem eval_tmul (a b : B) : eval k B (a ⊗ₜ[k] MulOpposite.op b) = a*b := by simp [eval_apply]

def difference (b : B) : Coeff k B := b ⊗ₜ[k] (1:Bᵐᵒᵖ) - (1:B) ⊗ₜ[k] MulOpposite.op b

@[simp] theorem difference_zero : difference k B 0 = 0 := by simp [difference]
@[simp] theorem difference_one : difference k B 1 = 0 := by simp [difference]
theorem difference_add (b c : B) : difference k B (b+c) = difference k B b + difference k B c := by
  simp only [difference,TensorProduct.add_tmul,MulOpposite.op_add,TensorProduct.tmul_add]
  abel
theorem difference_mul (b c : B) : difference k B (b*c) =
    (b ⊗ₜ[k] (1:Bᵐᵒᵖ)) * difference k B c +
    ((1:B) ⊗ₜ[k] MulOpposite.op c) * difference k B b := by
  simp only [difference,mul_sub,Algebra.TensorProduct.tmul_mul_tmul,one_mul,mul_one,
    ← MulOpposite.op_mul]
  abel
@[simp] theorem difference_algebraMap (r : k) : difference k B (algebraMap k B r) = 0 := by
  simp [difference,Algebra.algebraMap_eq_smul_one,TensorProduct.smul_tmul,TensorProduct.tmul_smul]

variable {k B}
/-- The generators of the kernel, exactly d_y=y⊗1−1⊗yᵒᵖ. -/
def relations (Y : Set B) : Submodule (Coeff k B) (Coeff k B) :=
  Submodule.span (Coeff k B) (difference k B '' Y)

/-- The product identity propagates the kernel generators through the whole algebra. -/
theorem difference_mem (Y : Set B) (hgen : Algebra.adjoin k Y = ⊤) (b : B) :
    difference k B b ∈ relations (k:=k) Y := by
  have hb : b ∈ Algebra.adjoin k Y := by rw [hgen]; trivial
  induction hb using Algebra.adjoin_induction with
  | mem b hb => exact Submodule.subset_span ⟨b,hb,rfl⟩
  | algebraMap r => simp
  | add b c _ _ hb hc => rw [difference_add]; exact Submodule.add_mem _ hb hc
  | mul b c _ _ hb hc =>
    rw [difference_mul]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hc) (Submodule.smul_mem _ _ hb)

theorem relations_le_kernel (Y : Set B) : relations (k:=k) Y ≤ (eval k B).ker := by
  apply Submodule.span_le.mpr
  rintro _ ⟨b,hb,rfl⟩
  change eval k B (difference k B b) = 0
  simp only [difference,map_sub]
  simp only [← MulOpposite.op_one,eval_tmul,mul_one,one_mul,sub_self]

/-- Every tensor is congruent to its value tensored with one. -/
theorem reduce_tensor (Y : Set B) (hgen : Algebra.adjoin k Y = ⊤) (r : Coeff k B) :
    r - (eval k B r ⊗ₜ[k] (1:Bᵐᵒᵖ)) ∈ relations (k:=k) Y := by
  induction r using TensorProduct.inductionOn with
  | tmul a b =>
    have hb := difference_mem Y hgen b.unop
    have h := Submodule.smul_mem (relations (k:=k) Y) (a ⊗ₜ[k] (1:Bᵐᵒᵖ)) hb
    have hev : eval k B (a ⊗ₜ[k] b) = a*b.unop := by
      simpa only [MulOpposite.op_unop] using eval_tmul k B a b.unop
    have he : a ⊗ₜ[k] b - (eval k B (a ⊗ₜ[k] b) ⊗ₜ[k] (1:Bᵐᵒᵖ)) =
        -((a ⊗ₜ[k] (1:Bᵐᵒᵖ)) * difference k B b.unop) := by
      simp only [difference,mul_sub,Algebra.TensorProduct.tmul_mul_tmul,one_mul,mul_one,
        MulOpposite.op_unop,neg_sub,hev]
    rw [he]
    exact Submodule.neg_mem _ h
  | add r s hr hs =>
    simpa only [map_add,TensorProduct.add_tmul,add_sub_add_comm] using Submodule.add_mem _ hr hs

theorem kernel_eq (Y : Set B) (hgen : Algebra.adjoin k Y = ⊤) :
    (eval k B).ker = relations (k:=k) Y := by
  apply le_antisymm
  · intro r hr
    have h := reduce_tensor Y hgen r
    have hz : eval k B r = 0 := hr
    simpa [hz] using h
  · exact relations_le_kernel Y

theorem eval_surjective : Function.Surjective (eval k B) := by
  intro b
  exact ⟨b ⊗ₜ[k] (1:Bᵐᵒᵖ),by simpa using eval_tmul k B b 1⟩

/-- The cyclic-module lemma, with no assumed tensor action identities. -/
noncomputable def quotientEquiv (Y : Set B) (hgen : Algebra.adjoin k Y = ⊤) :
    (Coeff k B ⧸ relations (k:=k) Y) ≃ₗ[Coeff k B] B := by
  let f := (relations (k:=k) Y).liftQ (eval k B) (relations_le_kernel Y)
  apply LinearEquiv.ofBijective f
  constructor
  · intro x y hxy
    obtain ⟨r,rfl⟩ := Submodule.Quotient.mk_surjective (relations (k:=k) Y) x
    obtain ⟨s,rfl⟩ := Submodule.Quotient.mk_surjective (relations (k:=k) Y) y
    apply (Submodule.Quotient.eq _).mpr
    rw [← kernel_eq Y hgen]
    change eval k B (r-s) = 0
    change eval k B r = eval k B s at hxy
    rw [map_sub,hxy,sub_self]
  · intro b
    obtain ⟨r,hr⟩ := eval_surjective (k:=k) (B:=B) b
    exact ⟨Submodule.Quotient.mk r,hr⟩

section Simple
variable {A : Type*} [Ring A] [Algebra k A] [IsSimpleRing A]

/-- The coefficients that can be reached from one input form a two-sided ideal;
    unitality of the inclusion into B is deliberately not required. -/
def reachable (i : A →ₙₐ[k] B) (u : A) : TwoSidedIdeal A :=
  TwoSidedIdeal.mk' {d | ∃ r : Coeff k B, r • i u = i d}
    (by exact ⟨(0 : Coeff k B), by simpa only [map_zero] using (zero_smul (Coeff k B) (i u))⟩)
    (by
      rintro x y ⟨r,hr⟩ ⟨s,hs⟩
      exact ⟨r+s,by rw [add_smul,hr,hs,map_add]⟩)
    (by
      rintro x ⟨r,hr⟩
      exact ⟨-r,by rw [neg_smul,hr,map_neg]⟩)
    (by
      rintro x y ⟨r,hr⟩
      refine ⟨(i x ⊗ₜ[k] (1:Bᵐᵒᵖ))*r,?_⟩
      rw [mul_smul,hr]
      simp only [← MulOpposite.op_one,tmul_smul,mul_one,map_mul])
    (by
      rintro x y ⟨r,hr⟩
      refine ⟨((1:B) ⊗ₜ[k] MulOpposite.op (i y))*r,?_⟩
      rw [mul_smul,hr,tmul_smul,one_mul,map_mul])

/-- Simplicity supplies every desired row operation. -/
theorem coefficient_control (i : A →ₙₐ[k] B) (u d : A) (hu : u ≠ 0) :
    ∃ r : Coeff k B, r • i u = i d := by
  have huI : u ∈ reachable i u := by
    simp only [reachable,TwoSidedIdeal.mem_mk',Set.mem_ofPred_eq]
    exact ⟨1,one_smul _ _⟩
  have hI : reachable i u ≠ ⊥ := by
    intro h
    rw [h] at huI
    exact hu (by simpa using huI)
  have htop : reachable i u = ⊤ := (eq_bot_or_eq_top _).resolve_left hI
  have hd : d ∈ reachable i u := by rw [htop]; trivial
  simpa only [reachable,TwoSidedIdeal.mem_mk',Set.mem_ofPred_eq] using hd
end Simple

end FiniteAlgebraicEnvelopes.Enveloping


namespace FiniteAlgebraicEnvelopes.RowControl
open Enveloping
variable {k A B : Type*} [CommRing k] [Ring A] [Ring B]
  [Algebra k A] [Algebra k B] [IsSimpleRing A]

def act (g : Steinberg.Group (Fin 6) (Coeff k B)) (v : Fin 6 → B) : Fin 6 → B :=
  (AffineAction.action g (Multiplicative.ofAdd v)).toAdd

@[simp] theorem act_one (v : Fin 6 → B) : act (k:=k) 1 v = v := by simp [act]
theorem act_mul (g h : Steinberg.Group (Fin 6) (Coeff k B)) (v : Fin 6 → B) :
    act (g*h) v = act g (act h v) := by simp [act]
@[simp] theorem act_root (a b : Fin 6) (hab : a ≠ b) (r : Coeff k B) (v : Fin 6 → B) :
    act (Steinberg.root a b hab r) v = fun j => if j=a then v j + r • v b else v j := by
  funext j
  simp [act]

def Related (i : A →ₙₐ[k] B) (v w : Fin 6 → A) : Prop :=
  ∃ g : Steinberg.Group (Fin 6) (Coeff k B), act g (i ∘ v) = i ∘ w

omit [IsSimpleRing A] in
theorem Related.refl (i : A →ₙₐ[k] B) (v : Fin 6 → A) : Related i v v := ⟨1,act_one _⟩
omit [IsSimpleRing A] in
theorem Related.trans {i : A →ₙₐ[k] B} {u v w : Fin 6 → A}
    (huv : Related i u v) (hvw : Related i v w) : Related i u w := by
  obtain ⟨g,hg⟩ := huv
  obtain ⟨h,hh⟩ := hvw
  exact ⟨h*g,by rw [act_mul,hg,hh]⟩
omit [IsSimpleRing A] in
theorem Related.symm {i : A →ₙₐ[k] B} {v w : Fin 6 → A}
    (h : Related i v w) : Related i w v := by
  obtain ⟨g,hg⟩ := h
  refine ⟨g⁻¹,?_⟩
  rw [← hg,← act_mul,inv_mul_cancel,act_one]

/-- A genuine Steinberg element sets any nonpivot row to the desired value. -/
theorem set_row (i : A →ₙₐ[k] B) (v : Fin 6 → A) (j l : Fin 6)
    (hj : v j ≠ 0) (hl : l ≠ j) (a : A) : Related i v (Function.update v l a) := by
  obtain ⟨r,hr⟩ := coefficient_control i (v j) (a-v l) hj
  refine ⟨Steinberg.root l j hl r,?_⟩
  rw [act_root]
  funext b
  by_cases hb : b=l
  · subst b
    simp [hr]

  · simp [hb]

/-- Eliminate any finite set of rows around a fixed nonzero pivot. -/
theorem set_rows (i : A →ₙₐ[k] B) (v w : Fin 6 → A) (j : Fin 6)
    (hj : v j ≠ 0) (s : Finset (Fin 6)) (hs : j ∉ s) :
    Related i v (fun a => if a ∈ s then w a else v a) := by
  induction s using Finset.induction_on with
  | empty => simpa using Related.refl i v
  | @insert a s ha ih =>
    have hjs : j ∉ s := fun h => hs (Finset.mem_insert_of_mem h)
    have hja : j ≠ a := fun h => hs (by simp [h])
    have hvj : (if j ∈ s then w j else v j) ≠ 0 := by simpa [hjs] using hj
    have hstep := set_row i (fun b => if b ∈ s then w b else v b) j a hvj hja.symm (w a)
    have he : Function.update (fun b => if b ∈ s then w b else v b) a (w a) =
        fun b => if b ∈ insert a s then w b else v b := by
      funext b
      by_cases hb : b=a
      · subst b; simp
      · simp [hb]
    rw [he] at hstep
    exact (ih hjs).trans hstep

/-- Every nonzero vector in the simple-algebra image reaches the same standard column. -/
theorem normalize (i : A →ₙₐ[k] B) (v : Fin 6 → A) (hv : v ≠ 0) :
    Related i v (Pi.single 5 1) := by
  have hex : ∃ j, v j ≠ 0 := by
    by_contra! h
    exact hv (funext h)
  obtain ⟨j,hj⟩ := hex
  have hp : ∃ w : Fin 6 → A, Related i v w ∧ w 5 = 1 := by
    by_cases hj5 : j=5
    · subst j
      let u := Function.update v 0 1
      have h₁ : Related i v u := set_row i v 5 0 hj (by decide) 1
      have hu : u 0 ≠ 0 := by simp [u]
      refine ⟨Function.update u 5 1,h₁.trans (set_row i u 0 5 hu (by decide) 1),?_⟩
      simp
    · refine ⟨Function.update v 5 1,set_row i v j 5 hj (Ne.symm hj5) 1,?_⟩
      simp
  obtain ⟨w,hw,hw5⟩ := hp
  have hwne : w 5 ≠ 0 := by rw [hw5]; exact one_ne_zero
  have hkill := set_rows i w (fun _ => 0) 5 hwne (Finset.univ.erase 5) (by simp)
  have he : (fun a => if a ∈ Finset.univ.erase (5:Fin 6) then (0:A) else w a) =
      Pi.single 5 1 := by
    funext a
    by_cases ha : a=5
    · subst a; simp [hw5]
    · simp [ha]
  rw [he] at hkill
  exact hw.trans hkill

/-- The linear core of two-transitivity, with actual root words. -/
theorem transitive_nonzero (i : A →ₙₐ[k] B) (v w : Fin 6 → A)
    (hv : v ≠ 0) (hw : w ≠ 0) : Related i v w :=
  (normalize i v hv).trans (normalize i w hw).symm
end FiniteAlgebraicEnvelopes.RowControl

end OAI
