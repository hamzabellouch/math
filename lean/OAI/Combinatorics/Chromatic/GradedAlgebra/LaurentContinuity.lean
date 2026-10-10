import Mathlib

namespace OAI

section
namespace ElementaryPositivity.LaurentPrecision
open Filter
open scoped LaurentSeries

abbrev Series := LaurentSeries ℚ

def LowerBound (b : ℤ) (f : Series) : Prop := ∀j<b,f.coeff j=0
def Agrees (b : ℤ) (f g : Series) : Prop := ∀j<b,f.coeff j=g.coeff j

lemma lowerBound_iff_orderTop (b : ℤ) (f : Series) :
    LowerBound b f ↔ (b : WithTop ℤ)≤f.orderTop := by
  rw [HahnSeries.le_orderTop_iff_forall]
  simp only [LowerBound,WithTop.coe_lt_coe]

lemma lowerBound_order (f : Series) : LowerBound f.order f :=
  fun _ h=>HahnSeries.coeff_eq_zero_of_lt_order h

lemma lowerBound_mono {a b : ℤ} {f : Series} (h : LowerBound b f) (hab : a≤b) :
    LowerBound a f := fun j hj=>h j (hj.trans_le hab)

lemma lowerBound_zero (b : ℤ) : LowerBound b (0 : Series) := by simp [LowerBound]

lemma lowerBound_add {b : ℤ} {f g : Series} (hf : LowerBound b f) (hg : LowerBound b g) :
    LowerBound b (f+g) := by
  intro j hj
  simp only [HahnSeries.coeff_add,hf j hj,hg j hj,add_zero]

lemma lowerBound_mul {a b : ℤ} {f g : Series} (hf : LowerBound a f) (hg : LowerBound b g) :
    LowerBound (a+b) (f*g) := by
  rw [lowerBound_iff_orderTop] at *
  rw [WithTop.coe_add,HahnSeries.orderTop_mul]
  exact add_le_add hf hg

lemma agrees_iff_sub {b : ℤ} {f g : Series} : Agrees b f g ↔ LowerBound b (f-g) := by
  simp only [Agrees,LowerBound,HahnSeries.coeff_sub,sub_eq_zero]

lemma agrees_refl (b : ℤ) (f : Series) : Agrees b f f := fun _ _=>rfl
lemma agrees_symm {b : ℤ} {f g : Series} (h : Agrees b f g) : Agrees b g f :=
  fun j hj=>(h j hj).symm
lemma agrees_mono {a b : ℤ} {f g : Series} (h : Agrees b f g) (hab : a≤b) :
    Agrees a f g := fun j hj=>h j (hj.trans_le hab)
lemma agrees_add {b : ℤ} {f f' g g' : Series} (hf : Agrees b f f') (hg : Agrees b g g') :
    Agrees b (f+g) (f'+g') := by
  intro j hj
  simp only [HahnSeries.coeff_add,hf j hj,hg j hj]
lemma agrees_neg {b : ℤ} {f g : Series} (h : Agrees b f g) : Agrees b (-f) (-g) := by
  intro j hj
  simp only [HahnSeries.coeff_neg,h j hj]
lemma agrees_sub {b : ℤ} {f f' g g' : Series} (hf : Agrees b f f') (hg : Agrees b g g') :
    Agrees b (f-g) (f'-g') := by
  simpa only [sub_eq_add_neg] using agrees_add hf (agrees_neg hg)

lemma agrees_mul {N a b : ℤ} {f f' g g' : Series}
    (hf : Agrees (N-b) f f') (hg : Agrees (N-a) g g')
    (hf' : LowerBound a f') (hgb : LowerBound b g) :
    Agrees N (f*g) (f'*g') := by
  rw [agrees_iff_sub] at *
  have h₁ := lowerBound_mul hf hgb
  have h₂ := lowerBound_mul hf' hg
  have he : f*g-f'*g'=(f-f')*g+f'*(g-g') := by ring
  rw [he]
  apply lowerBound_add
  · simpa using h₁
  · convert h₂ using 1
    omega

variable {ι : Type*} (l : Filter ι)

def Converges (f : ι → Series) (F : Series) : Prop :=
  ∀N : ℤ,∀ᶠ i in l,Agrees N (f i) F

lemma converges_const (F : Series) : Converges l (fun _=>F) F :=
  fun N=>Eventually.of_forall (fun _=>agrees_refl N F)

lemma Converges.coeff {f : ι → Series} {F : Series} (h : Converges l f F) (j : ℤ) :
    ∀ᶠ i in l,(f i).coeff j=F.coeff j :=
  (h (j+1)).mono (fun _ hi=>hi j (by omega))

lemma Converges.lowerBound {f : ι → Series} {F : Series} (h : Converges l f F)
    (b : ℤ) (hb : LowerBound b F) : ∀ᶠ i in l,LowerBound b (f i) := by
  filter_upwards [h b] with i hi
  intro j hj
  rw [hi j hj,hb j hj]

lemma Converges.add {f g : ι → Series} {F G : Series}
    (hf : Converges l f F) (hg : Converges l g G) :
    Converges l (fun i=>f i+g i) (F+G) := by
  intro N
  filter_upwards [hf N,hg N] with i hi hj
  exact agrees_add hi hj

lemma Converges.neg {f : ι → Series} {F : Series} (hf : Converges l f F) :
    Converges l (fun i=> -f i) (-F) := by
  intro N
  exact (hf N).mono (fun _ hi=>agrees_neg hi)

lemma Converges.sub {f g : ι → Series} {F G : Series}
    (hf : Converges l f F) (hg : Converges l g G) :
    Converges l (fun i=>f i-g i) (F-G) := by
  intro N
  filter_upwards [hf N,hg N] with i hi hj
  exact agrees_sub hi hj

lemma Converges.mul {f g : ι → Series} {F G : Series}
    (hf : Converges l f F) (hg : Converges l g G) :
    Converges l (fun i=>f i*g i) (F*G) := by
  intro N
  filter_upwards [hf (N-G.order),hg (N-F.order),
    hg.lowerBound l G.order (lowerBound_order G)] with i hi hj hb
  exact agrees_mul hi hj (lowerBound_order F) hb

lemma Converges.pow {f : ι → Series} {F : Series} (hf : Converges l f F) (n : ℕ) :
    Converges l (fun i=>f i^n) (F^n) := by
  induction n with
  | zero => simpa using converges_const l 1
  | succ n ih => simpa only [pow_succ] using ih.mul l hf

lemma Converges.sum {α : Type*} (s : Finset α) {f : α → ι → Series} {F : α → Series}
    (h : ∀a∈s,Converges l (f a) (F a)) :
    Converges l (fun i=>∑a∈s,f a i) (∑a∈s,F a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using converges_const l 0
  | @insert a s ha ih =>
    simpa only [Finset.sum_insert ha] using
      (h a (Finset.mem_insert_self _ _)).add l (ih (fun b hb=>h b (Finset.mem_insert_of_mem hb)))

lemma Converges.nat_coeff [NeBot l] {f : ι → Series} {F : Series}
    (hf : Converges l f F) (hpos : ∀ᶠ i in l,∀j,∃n : ℕ,(f i).coeff j=n) :
    ∀j,∃n : ℕ,F.coeff j=n := by
  intro j
  obtain ⟨i,hi,hp⟩:=((hf.coeff l j).and hpos).exists
  rw [←hi]
  exact hp j

end ElementaryPositivity.LaurentPrecision

end

end OAI
