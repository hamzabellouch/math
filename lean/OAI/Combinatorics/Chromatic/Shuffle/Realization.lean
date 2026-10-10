import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.CellVars
import OAI.Combinatorics.Chromatic.Walls.Pack

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A : I → Type*} [∀ i,DecidableEq (A i)]

abbrev Realization (d : I → ℕ) (s : ∀ i,Finset (A i)) := ∀ i,Fin (d i) ≃ s i

def realizationMap {d : I → ℕ} {s : ∀ i,Finset (A i)} (r : Realization d s) :
    (Σi,Fin (d i)) → (Σi,A i) := fun x => ⟨x.1,r x.1 x.2⟩

omit [Fintype I] [DecidableEq I] [∀ i,DecidableEq (A i)] in
lemma realizationMap_injective {d : I → ℕ} {s : ∀ i,Finset (A i)} (r : Realization d s) :
    Function.Injective (realizationMap r) := by
  exact (Function.Embedding.sigmaMap (Function.Embedding.refl I)
    (fun i => (r i).toEmbedding.trans (Function.Embedding.subtype _))).injective

omit [Fintype I] [DecidableEq I] [∀ i,DecidableEq (A i)] in
lemma rename_realization_independent {d : I → ℕ} {s : ∀ i,Finset (A i)}
    (r t : Realization d s) (f : S d) :
    rename (realizationMap r) f.val = rename (realizationMap t) f.val := by
  let σ : ∀ i,Equiv.Perm (Fin (d i)) := fun i => (r i).trans (t i).symm
  have he : realizationMap t ∘ packAction (fun i => Fin (d i)) σ = realizationMap r := by
    funext ⟨i,x⟩
    change (⟨i,↑(t i (σ i x))⟩ : Σi,A i) = ⟨i,↑(r i x)⟩
    simp [σ]
  rw [← he, ← rename_rename, f.property σ]

noncomputable def valueAt {d : I → ℕ} {s : ∀ i,Finset (A i)}
    (r : Realization d s) (f : S d) : FractionRing (MvPolynomial (Σi,A i) ℚ) :=
  algebraMap _ _ (rename (realizationMap r) f.val)

omit [Fintype I] [DecidableEq I] [∀ i,DecidableEq (A i)] in
lemma valueAt_independent {d : I → ℕ} {s : ∀ i,Finset (A i)}
    (r t : Realization d s) (f : S d) : valueAt r f = valueAt t f := by
  rw [valueAt,valueAt,rename_realization_independent]

noncomputable def defaultRealization {d : I → ℕ} {s : ∀ i,Finset (A i)}
    (h : ∀ i,(s i).card = d i) : Realization d s := fun i =>
  Fintype.equivOfCardEq (by simp [h i])

noncomputable def labeledValue {d : I → ℕ} (f : S d) (s : ∀ i,Finset (A i)) :
    FractionRing (MvPolynomial (Σi,A i) ℚ) :=
  if h : ∀ i,(s i).card = d i then valueAt (defaultRealization h) f else 0

omit [DecidableEq I] [∀ i,DecidableEq (A i)] in
lemma labeledValue_eq {d : I → ℕ} {s : ∀ i,Finset (A i)} (r : Realization d s) (f : S d) :
    labeledValue f s = valueAt r f := by
  have h : ∀ i,(s i).card = d i := by
    intro i
    simpa using (Fintype.card_congr (r i)).symm
  rw [labeledValue, dite_eq_left h, valueAt_independent _ r]

omit [∀ i,DecidableEq (A i)] in
lemma valueAt_shuffle (a : I → I → ℕ) {d e : I → ℕ}
    (s : ∀ i,Finset (A i)) (r : Realization (d+e) s) (f : S d) (g : S e) :
    valueAt r (shufflePolynomial a f g) =
    renameInjFraction (realizationMap r) (realizationMap_injective r) (rawShuffle a f.val g.val) := by
  rw [← shufflePolynomial_eq]
  exact (renameInjFraction_algebraMap (realizationMap r) (realizationMap_injective r)
    (shufflePolynomial a f g).val).symm

end ElementaryPositivity.RawShuffle

namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A : I → Type*} [∀ i,DecidableEq (A i)]

abbrev SizedCut (d : I → ℕ) (s : ∀ i,Finset (A i)) :=
  {p : PackConvolution.Cut s // ∀ i,(PackConvolution.left p i).card = d i}

noncomputable def cutRealizationEquiv {d e : I → ℕ} {s : ∀ i,Finset (A i)}
    (r : Realization (d+e) s) : Cut d e ≃ SizedCut d s :=
  (Equiv.piCongrRight fun i => PackEnumeration.sizedSplitEquiv (r i) (d i)).trans
    Equiv.subtypePiEquivPi.symm

omit [Fintype I] [DecidableEq I] in
@[simp] lemma cutRealizationEquiv_left {d e : I → ℕ} {s : ∀ i,Finset (A i)}
    (r : Realization (d+e) s) (t : Cut d e) (i : I) :
    PackConvolution.left (cutRealizationEquiv r t).val i =
      (t i).val.map (PackEnumeration.embedding (r i)) := rfl
omit [Fintype I] [DecidableEq I] in
@[simp] lemma cutRealizationEquiv_right {d e : I → ℕ} {s : ∀ i,Finset (A i)}
    (r : Realization (d+e) s) (t : Cut d e) (i : I) :
    PackConvolution.right (cutRealizationEquiv r t).val i =
      (t i).valᶜ.map (PackEnumeration.embedding (r i)) := rfl

noncomputable def leftRealization {d e : I → ℕ} {s : ∀ i,Finset (A i)}
    (r : Realization (d+e) s) (t : Cut d e) :
    Realization d (PackConvolution.left (cutRealizationEquiv r t).val) :=
  fun i => (leftEnum t i).trans (PackEnumeration.mapEquiv
    (PackEnumeration.embedding (r i)) (t i).val)

noncomputable def rightRealization {d e : I → ℕ} {s : ∀ i,Finset (A i)}
    (r : Realization (d+e) s) (t : Cut d e) :
    Realization e (PackConvolution.right (cutRealizationEquiv r t).val) :=
  fun i => (rightEnum t i).trans (PackEnumeration.mapEquiv
    (PackEnumeration.embedding (r i)) (t i).valᶜ)

omit [Fintype I] [DecidableEq I] in
lemma leftRealization_map {d e : I → ℕ} {s : ∀ i,Finset (A i)}
    (r : Realization (d+e) s) (t : Cut d e) :
    realizationMap (leftRealization r t) = realizationMap r ∘ leftInput t := rfl
omit [Fintype I] [DecidableEq I] in
lemma rightRealization_map {d e : I → ℕ} {s : ∀ i,Finset (A i)}
    (r : Realization (d+e) s) (t : Cut d e) :
    realizationMap (rightRealization r t) = realizationMap r ∘ rightInput t := rfl

omit [DecidableEq I] in
lemma labeledValue_left {d e : I → ℕ} {s : ∀ i,Finset (A i)}
    (r : Realization (d+e) s) (t : Cut d e) (f : S d) :
    labeledValue f (PackConvolution.left (cutRealizationEquiv r t).val) =
      algebraMap _ (FractionRing (MvPolynomial (Σi,A i) ℚ))
        (rename (realizationMap r) (rename (leftInput t) f.val)) := by
  rw [labeledValue_eq (leftRealization r t),valueAt,leftRealization_map,rename_rename]
omit [DecidableEq I] in
lemma labeledValue_right {d e : I → ℕ} {s : ∀ i,Finset (A i)}
    (r : Realization (d+e) s) (t : Cut d e) (g : S e) :
    labeledValue g (PackConvolution.right (cutRealizationEquiv r t).val) =
      algebraMap _ (FractionRing (MvPolynomial (Σi,A i) ℚ))
        (rename (realizationMap r) (rename (rightInput t) g.val)) := by
  rw [labeledValue_eq (rightRealization r t),valueAt,rightRealization_map,rename_rename]

noncomputable def pairKernel (a : I → I → ℕ) (x y : Σi,A i) :
    FractionRing (MvPolynomial (Σi,A i) ℚ) :=
  let v := algebraMap _ (FractionRing (MvPolynomial (Σi,A i) ℚ)) (diagonal x y)
  v^(a x.1 y.1) / if x.1 = y.1 then v else 1

omit [∀ i,DecidableEq (A i)] in
lemma kernel_formula (a : I → I → ℕ) (s t : ∀ i,Finset (A i)) :
    PackConvolution.kernel (pairKernel a) s t =
      (∏ i,∏ j,∏ x ∈ s i,∏ y ∈ t j,
        (algebraMap _ (FractionRing (MvPolynomial (Σi,A i) ℚ)) (diagonal (⟨i,x⟩ : Σi,A i) ⟨j,y⟩))^(a i j)) /
      (∏ i,∏ x ∈ s i,∏ y ∈ t i,
        algebraMap _ (FractionRing (MvPolynomial (Σi,A i) ℚ)) (diagonal (⟨i,x⟩ : Σi,A i) ⟨i,y⟩)) := by
  simp only [PackConvolution.kernel,pairKernel,Finset.prod_div_distrib]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    exact Finset.prod_comm
  · apply Finset.prod_congr rfl
    intro i hi
    apply Finset.prod_congr rfl
    intro x hx
    rw [Finset.prod_eq_single i]
    · simp
    · intro j hj hji
      simp only [ite_eq_right (Ne.symm hji),Finset.prod_const_one]
    · simp

lemma mapped_cut_kernel (a : I → I → ℕ) {d e : I → ℕ}
    {s : ∀ i,Finset (A i)} (r : Realization (d+e) s) (t : Cut d e) :
    PackConvolution.kernel (pairKernel a)
      (PackConvolution.left (cutRealizationEquiv r t).val)
      (PackConvolution.right (cutRealizationEquiv r t).val) =
    algebraMap _ (FractionRing (MvPolynomial (Σi,A i) ℚ))
      (rename (realizationMap r) (∏ i,∏ j,cutFactor t i j (a i j))) /
    algebraMap _ (FractionRing (MvPolynomial (Σi,A i) ℚ))
      (rename (realizationMap r) (cutDenominator t)) := by
  rw [kernel_formula]
  simp only [cutRealizationEquiv_left,cutRealizationEquiv_right,
    Finset.prod_map,cutFactor,cutDenominator,map_prod,map_pow,diagonal,map_sub,rename_X,pow_one]
  rfl

variable [∀ i,Fintype (A i)]

lemma valueAt_shuffle_sum (a : I → I → ℕ) {d e : I → ℕ}
    {s : ∀ i,Finset (A i)} (r : Realization (d+e) s) (f : S d) (g : S e) :
    valueAt r (shufflePolynomial a f g) =
      ∑ p : SizedCut d s, labeledValue f (PackConvolution.left p.val) *
        labeledValue g (PackConvolution.right p.val) *
          PackConvolution.kernel (pairKernel a)
            (PackConvolution.left p.val) (PackConvolution.right p.val) := by
  classical
  rw [valueAt_shuffle a s r, ← (cutRealizationEquiv r).sum_comp]
  simp only [rawShuffle,map_sum,map_div₀]
  apply Finset.sum_congr rfl
  intro t ht
  rw [labeledValue_left,labeledValue_right,mapped_cut_kernel]
  have hn := renameInjFraction_algebraMap (α := Σi,Fin (d i+e i)) (realizationMap r) (realizationMap_injective r)
    (cutNumerator a t f.val g.val)
  have hd := renameInjFraction_algebraMap (α := Σi,Fin (d i+e i)) (realizationMap r) (realizationMap_injective r)
    (cutDenominator t)
  rw [hn,hd]
  simp only [cutNumerator,map_mul]
  rw [mul_div_assoc]

omit [Fintype I] [DecidableEq I] [∀ i,Fintype (A i)] in
lemma cut_right_card {d e : I → ℕ} {s : ∀ i,Finset (A i)}
    (hs : ∀ i,(s i).card = (d+e) i) (p : SizedCut d s) :
    ∀ i,(PackConvolution.right p.val i).card = e i := by
  intro i
  have h := Finset.card_union_of_disjoint (p.val i).property.1
  rw [(p.val i).property.2, hs i] at h
  have hl := p.property i
  change (p.val i).val.1.card = d i at hl
  change (p.val i).val.2.card = e i
  simp only [Pi.add_apply] at h
  omega

omit [Fintype I] [DecidableEq I] [∀ i,Fintype (A i)] in
lemma cut_card_add {d e : I → ℕ} {s : ∀ i,Finset (A i)} (p : PackConvolution.Cut s)
    (hl : ∀ i,(PackConvolution.left p i).card = d i)
    (hr : ∀ i,(PackConvolution.right p i).card = e i) :
    ∀ i,(s i).card = (d+e) i := by
  intro i
  have h := Finset.card_union_of_disjoint (p i).property.1
  rw [(p i).property.2] at h
  exact h.trans (congrArg₂ (·+·) (hl i) (hr i))

lemma pack_shuffle_sum (a : I → I → ℕ) {d e : I → ℕ}
    (s : ∀ i,Finset (A i)) (f : S d) (g : S e) :
    PackConvolution.shuffle (pairKernel a) (labeledValue f) (labeledValue g) s =
      ∑ p : SizedCut d s, labeledValue f (PackConvolution.left p.val) *
        labeledValue g (PackConvolution.right p.val) *
          PackConvolution.kernel (pairKernel a)
            (PackConvolution.left p.val) (PackConvolution.right p.val) := by
  classical
  unfold PackConvolution.shuffle
  rw [← Fintype.sum_subtype_add_sum_subtype
    (fun p : PackConvolution.Cut s => ∀ i,(PackConvolution.left p i).card = d i)]
  suffices hz : (∑ p : {p : PackConvolution.Cut s //
      ¬ ∀ i,(PackConvolution.left p i).card = d i},
      labeledValue f (PackConvolution.left p.val) * labeledValue g (PackConvolution.right p.val) *
      PackConvolution.kernel (pairKernel a)
        (PackConvolution.left p.val) (PackConvolution.right p.val)) = 0 by
    rw [hz,add_zero]
  apply Finset.sum_eq_zero
  intro p hp
  rw [labeledValue,dite_eq_right p.property,zero_mul,zero_mul]

lemma labeledValue_shuffle (a : I → I → ℕ) {d e : I → ℕ} (f : S d) (g : S e) :
    labeledValue (A := A) (shufflePolynomial a f g) =
      PackConvolution.shuffle (pairKernel a) (labeledValue f) (labeledValue g) := by
  classical
  funext s
  by_cases hs : ∀ i,(s i).card = (d+e) i
  · rw [labeledValue_eq (defaultRealization hs),valueAt_shuffle_sum,pack_shuffle_sum]
  · rw [labeledValue,dite_eq_right hs,PackConvolution.shuffle]
    symm
    apply Finset.sum_eq_zero
    intro p hp
    by_cases hl : ∀ i,(PackConvolution.left p i).card = d i
    · have hr : ¬ ∀ i,(PackConvolution.right p i).card = e i := by
        intro hh
        exact hs (cut_card_add p hl hh)
      simp only [labeledValue,dite_eq_right hr,mul_zero,zero_mul]
    · simp only [labeledValue,dite_eq_right hl,zero_mul,zero_mul]

omit [Fintype I] [DecidableEq I] [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)] in
lemma valueAt_injective {d : I → ℕ} {s : ∀ i,Finset (A i)} (r : Realization d s) :
    Function.Injective (valueAt r) := by
  intro f g h
  apply Subtype.ext
  apply MvPolynomial.rename_injective (realizationMap r) (realizationMap_injective r)
  exact IsFractionRing.injective (MvPolynomial (Σi,A i) ℚ) _ h

omit [DecidableEq I] [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)] in
lemma labeledValue_injective {d : I → ℕ} {s : ∀ i,Finset (A i)} (r : Realization d s) :
    Function.Injective (fun f : S d => labeledValue f s) := by
  intro f g hh
  apply valueAt_injective r
  simpa only [labeledValue_eq r] using hh

def castS {d e : I → ℕ} (h : d=e) (f : S d) : S e := h ▸ f

omit [DecidableEq I] [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)] in
lemma labeledValue_cast {d e : I → ℕ} (h : d=e) (f : S d) :
    labeledValue (A := A) (castS h f) = labeledValue f := by
  subst e
  rfl

theorem shufflePolynomial_assoc (a : I → I → ℕ) {d e b : I → ℕ}
    (f : S d) (g : S e) (h : S b) :
    castS (add_assoc d e b) (shufflePolynomial a (shufflePolynomial a f g) h) =
      shufflePolynomial a f (shufflePolynomial a g h) := by
  classical
  let s : ∀ i,Finset (Fin ((d+(e+b)) i)) := fun _ => Finset.univ
  let r : Realization (d+(e+b)) s := defaultRealization (by intro i; simp [s])
  apply labeledValue_injective r
  dsimp only
  rw [labeledValue_cast,labeledValue_shuffle,labeledValue_shuffle,
    labeledValue_shuffle,labeledValue_shuffle]
  exact congrFun (PackConvolution.shuffle_assoc (pairKernel a)
    (labeledValue f) (labeledValue g) (labeledValue h)) s

end ElementaryPositivity.RawShuffle

end

end OAI
