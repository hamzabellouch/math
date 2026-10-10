import OAI.Combinatorics.HadwigerCounterexample.RandomBinaryMixing

namespace OAI

/-! # Mixer Product Variables -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix
variable {p : Shape} {n : ℕ} {r : Comp p.g → ℕ}

abbrev Terms (p : Shape) (l : Tag p.g) (r : Comp p.g → ℕ) :=
  Fin p.J × TagStar l × ((Σ e, Fin (r e)) × Bool)
abbrev Parts (p : Shape) (n : ℕ) (r : Comp p.g → ℕ) :=
  ∀ e, Mat (Row p n) (Fin (r e))

def formCol (P : Parts p n r) (l : Tag p.g) (d : MArr p n) :
    Mat (Row p n) (Terms p l r) :=
  Matrix.of (fun i =>
    fun ⟨j,f,⟨e,k⟩,b⟩ =>
      (if b then (d (j,e,f.val))ᵀ * P e else d (j,f.val,e) * P e) i k)

theorem formCol_true (P : Parts p n r) (l : Tag p.g) (d : MArr p n)
    (i j f e k) :
    formCol P l d i (j,f,⟨e,k⟩,true)=((d (j,e,f.val))ᵀ * P e) i k := by simp [formCol]
theorem formCol_false (P : Parts p n r) (l : Tag p.g) (d : MArr p n)
    (i j f e k) :
    formCol P l d i (j,f,⟨e,k⟩,false)=(d (j,f.val,e) * P e) i k := by simp [formCol]

theorem qmix_eq (P Q : Parts p n r) (l : Tag p.g) (d : Draw p n) {x : Profile p n}
    (hx : ∀ e, x e=P e*(Q e)ᵀ) :
    qmix (drawn d) x l=formCol P l d.1 * (formCol Q l d.2.1)ᵀ := by
  classical
  have h (j : Fin p.J) (f : TagStar l) (e) (L R : Moment p n) :
      liftM L R (x e) = L*P e * (R*Q e)ᵀ := by
    rw [liftM_def,hx]
    simp only [Matrix.mul_assoc,transpose_mul]
  ext i k
  let A := formCol P l d.1
  let B := formCol Q l d.2.1
  change _ = ∑ t : Terms p l r, A i t*B k t
  unfold qmix
  simp_rw [Matrix.sum_apply, Fintype.sum_prod_type, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl
    fun e _ => ?_
  simp_rw [Matrix.add_apply,h j f]
  let a := (drawn d).mixL j e f.val
  let b := (drawn d).mixR j e f.val
  let a' := (drawn d).mixL j f.val e
  let b' := (drawn d).mixR j f.val e
  change (∑ t, (aᵀ * P e) i t * (bᵀ * Q e) k t)+
    (∑ t, (a' * P e) i t * (b' * Q e) k t) = _
  rw [←Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun t _ => ?_
  rw [Fintype.sum_bool]; rfl

theorem formCol_add (P : Parts p n r) (l : Tag p.g) (d d' : MArr p n) :
    formCol P l (d+d') = formCol P l d + formCol P l d' := by
  ext i j; rcases j with ⟨j,f,⟨e,k⟩,_|_⟩
  · simp only [Matrix.add_apply, formCol_false,Pi.add_apply,Matrix.add_mul]
  · simp only [Matrix.add_apply, formCol_true,Pi.add_apply,Matrix.add_mul, Matrix.transpose_add]
theorem formCol_smul (P : Parts p n r) (l : Tag p.g) (a : F) (d : MArr p n) :
    formCol P l (a•d) = a • formCol P l d := by
  ext i j; rcases j with ⟨j,f,⟨e,k⟩,_|_⟩
  · simp only [Matrix.smul_apply, formCol_false,Pi.smul_apply,Matrix.smul_mul]
  · simp only [Matrix.smul_apply, formCol_true,Pi.smul_apply,Matrix.smul_mul,
      Matrix.transpose_smul]

variable {U : Type}

/-- Stacked evaluation of all columns on a batch of free directions. -/
def stackL (P Q : Parts p n r) (l : Tag p.g) (W : Mat (Row p n) U) :
    Draw p n →ₗ[F] Mat U (Terms p l r ⊕ Terms p l r) where
  toFun d := Wᵀ * fromCols (formCol P l d.1) (formCol Q l d.2.1)
  map_add' d d' := by
    simp only [Prod.fst_add,Prod.snd_add,formCol_add,mul_fromCols, Matrix.mul_add]
    ext i j; cases j <;> rfl
  map_smul' v d := by
    simp only [Prod.smul_fst,Prod.smul_snd,formCol_smul,mul_fromCols,RingHom.id_apply,
      Matrix.mul_smul]
    ext i j; cases j <;> rfl

variable [Fintype U]

/-- Well away from the profile factors all the formal variables from a given
side can be specified independently. -/
theorem formCol_onto (P : Parts p n r) (l : Tag p.g) (W : Mat (Row p n) U)
    (hw : Function.Injective W.mulVec)
    (hP : ∀ i, Function.Injective (P i).mulVec)
    (h : ∀ i, Disjoint (colSp (P i)) (colSp W))
    (A : Mat U (Terms p l r)) :
    ∃ d : MArr p n, Wᵀ * formCol P l d=A := by
  classical
  let tgt (b : Bool) (j : Fin p.J) (e f : Comp p.g) :
      Mat (Fin (r e)) U :=
    if h : inc f l then Matrix.of (fun k i => A i (j,⟨f,h⟩,⟨e,k⟩,b)) else 0
  have ho (j : Fin p.J) (e f : Comp p.g) :
      ∃ L : Moment p n, (P e)ᵀ * L * W=tgt true j e f ∧
                         (P f)ᵀ * Lᵀ * W=tgt false j f e :=
    prescribe_opposite (inj_fromCols (hP _) hw (h e)) (inj_fromCols hw (hP _) (h f).symm) _ _
  choose D hD hd using ho
  let d : MArr p n := fun ⟨j,e,f⟩ => D j e f
  refine ⟨d,?_⟩
  ext i j
  rcases j with ⟨j,f,⟨e,k⟩,_|_⟩
  · have he : Wᵀ * (D j f e * P e)=(tgt false j e f.val)ᵀ := by
      rw [← hd]; simp only [transpose_mul,transpose_transpose]
    change ∑ q, Wᵀ i q * formCol P l d q (j,f,⟨e,k⟩,false) = _
    simp only [formCol_false]
    change (Wᵀ*(D j f e * P e)) i k=_
    rw [he]; simp [tgt,f.property]
  · have he : Wᵀ*((D j e f)ᵀ*P e)=(tgt true j e f.val)ᵀ := by
      rw [← hD]; simp only [transpose_mul,transpose_transpose]
    change ∑ q, Wᵀ i q * formCol P l d q (j,f,⟨e,k⟩,true) = _
    simp only [formCol_true]
    change (Wᵀ*((D j e f)ᵀ*P e)) i k=_
    rw [he]; simp [tgt,f.property]

theorem stack_surj (P Q : Parts p n r) (l : Tag p.g) (W : Mat (Row p n) U)
    (hw : Function.Injective W.mulVec)
    (hP : ∀ i, Function.Injective (P i).mulVec) (hQ : ∀ i, Function.Injective (Q i).mulVec)
    (h1 : ∀ i, Disjoint (colSp (P i)) (colSp W))
    (h2 : ∀ i, Disjoint (colSp (Q i)) (colSp W)) :
    Function.Surjective (stackL P Q l W) := by
  intro A
  obtain ⟨d,hd⟩ := formCol_onto P l W hw hP h1 A.toCols₁
  obtain ⟨f,hf⟩ := formCol_onto Q l W hw hQ h2 A.toCols₂
  refine ⟨(d,f,0),?_⟩
  change Wᵀ * fromCols (formCol P l d) (formCol Q l f)=_
  rw [mul_fromCols,hd,hf,fromCols_toCols]

end HadwigerCounterexample

end

end OAI
