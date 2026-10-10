import OAI.Combinatorics.HadwigerCounterexample.RankSubrectangles

namespace OAI

/-! # Cross Pattern Counting -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Submodule Function Finset
open scoped BigOperators

variable {I J T L : Type} [Fintype I] [Fintype J] [Fintype T] [Fintype L]
  [DecidableEq I] [DecidableEq J] [DecidableEq T] [DecidableEq L]

abbrev Avenue (I J : Type) := Mat (I×J) (I×J)
def interDraw (M : Avenue I J) :=
  ∀ i u v,M (i,u) (i,v)=0

def disperses (f : T → I × J) (g : L → I × J) :=
  ∀ i j,(f i).1≠(g j).1
def arcPeak (M : Avenue I J) (t : ℕ) :=
  ∃ (f g : Fin t→ I × J), disperses f g ∧ Injective (M.submatrix f g).mulVec

def peak (M : Avenue I J) : ℕ := sSup {t | arcPeak M t}

omit [DecidableEq I] [DecidableEq J] in
private theorem peak_bdd (M : Avenue I J) (t : ℕ) (h : arcPeak M t) :
    t≤ Fintype.card (I×J) := by
  obtain ⟨f,g,hg,h⟩ := h
  have hx := ((mrk_inj.mp h).trans (Fintype.card_fin _)).symm
  exact hx.trans_le ((M.rank_submatrix_le f g).trans M.rank_le_card_width)

omit [DecidableEq I] [DecidableEq J] in
theorem real_peak (M : Avenue I J) : arcPeak M (peak M) := by
  classical
  have he : arcPeak M 0 := ⟨Fin.elim0,Fin.elim0,
    fun i => Fin.elim0 i, fun _ _ _ => Subsingleton.elim _ _⟩
  exact Nat.sSup_mem (show Set.Nonempty {t | arcPeak M t} from ⟨0,he⟩)
    ⟨Fintype.card (I×J),fun _ => peak_bdd M _⟩

omit [DecidableEq I] [DecidableEq J] in
theorem peak_le (M : Avenue I J) : peak M ≤ Fintype.card (I×J) :=
  peak_bdd M _ (real_peak M)

omit [DecidableEq I] [DecidableEq J] in
theorem sized_peak (M : Avenue I J) {f : T→I × J} {g : L → I × J}
    (h : disperses f g) : (M.submatrix f g).rank ≤ peak M := by
  classical
  obtain ⟨a,b,hb⟩ := minor_arc (M.submatrix f g)
  let W := {t | arcPeak M t}
  refine le_csSup ⟨Fintype.card (I×J),fun t => peak_bdd M t⟩
    (show (M.submatrix f g).rank∈W from ?_)
  exact ⟨f ∘ a,g ∘ b,fun i j => h _ _,hb⟩

omit [DecidableEq I] [DecidableEq J] in
theorem peak_pos (M : Avenue I J) (h : M≠0) (he : interDraw M) : 1≤peak M := by
  classical
  obtain ⟨⟨x,y⟩,⟨v,w⟩,hx⟩ :
      ∃ i j : I×J,M i j≠0 := by by_contra! hn; exact h (Matrix.ext fun i j => hn i j)
  let f (_ : Unit) := (x,y)
  let g (_ : Unit) := (v,w)
  have hv : disperses f g := fun i j h => hx ((show x=v from h).symm ▸ he x y w)
  have hh := sized_peak M hv
  have h1 : M.submatrix f g=1 := by
    ext i j
    obtain rfl := Subsingleton.elim i j
    rw [Matrix.one_apply_eq]
    exact (bit_cases _).resolve_left hx
  simpa only [h1,Matrix.rank_one,Fintype.card_unit] using hh

abbrev Incident (I J : Type) := Mat J (I×J)
def took (M : Avenue I J) (i : I) : Incident I J × Incident I J :=
  (M.submatrix (fun j => (i,j)) _root_.id, (Mᵀ.submatrix (fun j => (i,j)) _root_.id))

private theorem took_same (A B : Avenue I J) {t : ℕ} (f g : Fin t→ I×J)
    (hA : peak A=t) (hB : peak B=t) (ha : interDraw A) (hb : interDraw B)
    (hd : disperses f g) (hf : Injective (A.submatrix f g).mulVec)
    (hL : ∀ i,took A (f i).1=took B (f i).1)
    (hR : ∀ i,took A (g i).1=took B (g i).1) : A=B := by
  classical
  let touched (x : I) := (∃ i,x=(f i).1)∨∃ i,x=(g i).1
  have he {i : I} (h : touched i) (j : J) (k : I × J) :
      A (i,j) k=B (i,j) k ∧ A k (i,j)=B k (i,j) := by
    have hE : took A i=took B i := by
      rcases h with ⟨i,rfl⟩|⟨i,rfl⟩; exact hL i; exact hR i
    exact ⟨congr_fun (congr_fun (congrArg Prod.fst hE) j) k,
      congr_fun (congr_fun (congrArg Prod.snd hE) j) k⟩
  ext ⟨i,j⟩ ⟨k,l⟩
  by_cases h : i=k
  · subst k; rw [ha,hb]
  by_cases hi : touched i
  · exact (he hi j _).1
  by_cases hj : touched k
  · exact (he hj l _).2
  let u := Sum.elim f (fun _ : Unit => (i,j))
  let v := Sum.elim g (fun _ : Unit => (k,l))
  have ht : disperses u v := by
    rintro (x|x) (y|y) h'
    · exact hd _ _ h'
    · exact hj (Or.inl ⟨_,h'.symm⟩)
    · exact hi (Or.inr ⟨_,h'⟩)
    · exact h h'
  have h1 x y : A (f x) y=B (f x) y :=
    (he (i:=(f x).1) (Or.inl ⟨x,rfl⟩) (f x).2 y).1
  have h2 x y : A x (g y)=B x (g y) :=
    (he (i:=(g y).1) (Or.inr ⟨y,rfl⟩) (g y).2 x).2
  exact border_same A B f g (i,j) (k,l) hf h1 h2 ((sized_peak A ht).trans_eq hA)
    ((sized_peak B ht).trans_eq hB)

private abbrev Bag (I J : Type) := (I × J) × Incident I J × Incident I J
def peakExpense (I J : Type) [Fintype I] [Fintype J] (t : ℕ) :=
  2*t * ((1+2*num J)* num I*num J)

private theorem bagCount :
    num (Bag I J) ≤ bp ((1+2*num J)*num I*num J) := by
  classical
  have hA : num (I×J) ≤ bp (num (I×J)) := by
    let K := I×J
    have h : Fintype.card K <2^(Fintype.card K) := Nat.lt_two_pow_self
    unfold num
    rw [bp_nat]
    exact_mod_cast h.le
  have he {I J : Type} [Fintype I] [Fintype J] : num (I×J)=num I*num J := by
    simp only [num,Fintype.card_prod,Nat.cast_mul]
  unfold Bag
  rw [he, he (I:=Incident ..)]
  simp only [Incident,cast_mat]
  calc num (I×J)* _ ≤ bp (num (I×J))* _ :=
        mul_le_mul_of_nonneg_right hA (mul_nonneg (bp_pos _).le (bp_pos _).le)
       _ = _ := by rw [←bp_add,←bp_add,he]; congr 1; ring

set_option maxHeartbeats 800000 in
theorem price_peak (t : ℕ) :
    nbr (fun M : Avenue I J => interDraw M ∧ peak M=t)≤bp (peakExpense I J t) := by
  classical
  let S := {M : Avenue I J // interDraw M ∧ peak M=t}
  have ht (M : S) : arcPeak M.val t := by
    have hf {A : Avenue I J} {t : ℕ} (h : peak A=t) : arcPeak A t := h ▸ real_peak A
    exact hf M.property.2
  choose f g hD hG using ht
  let P := (Fin t → Bag I J) × (Fin t → Bag I J)
  let e : S→P := fun M => (fun i => (f M i,took M.val (f M i).1),
    fun i => (g M i,took M.val (g M i).1))
  have hf : Injective e := by
    intro A B h
    have h1 (i) : (f A i,took A.val (f A i).1)=(f B i,took B.val (f B i).1) :=
      congr_fun (congrArg Prod.fst h) i
    have h2 (i) : (g A i,took A.val (g A i).1)=(g B i,took B.val (g B i).1) :=
      congr_fun (congrArg Prod.snd h) i
    refine Subtype.ext (took_same A.val B.val (f A) (g A) A.property.2 B.property.2
      A.property.1 B.property.1 (hD A) (hG A) (fun i => ?_) (fun i => ?_))
    · have he : took A.val (f A i).1=took B.val (f B i).1 := congrArg Prod.snd (h1 i)
      rwa [← show f A i=f B i from congrArg Prod.fst (h1 i)] at he
    have he : took A.val (g A i).1=took B.val (g B i).1 := congrArg Prod.snd (h2 i)
    rwa [← show g A i=g B i from congrArg Prod.fst (h2 i)] at he
  rw [nbr_eq_card]
  have hZ : (Fintype.card S:ℝ) ≤ Fintype.card P := by exact_mod_cast Fintype.card_le_of_injective e hf
  apply hZ.trans
  apply le_trans ((show (↑(Fintype.card P):ℝ)=num (Bag I J)^t*num (Bag I J)^t by
    simp [P,num]).le)
  let V := ((1+2*num J)*num I*num J)
  have h1 := @bagCount I J _ _ _ _
  have he := pow_le_pow_left₀ (Nat.cast_nonneg _ : 0 ≤ num (Bag I J)) h1 t
  have hz := bp_mul_nat V t
  rw [← hz] at he
  refine (mul_le_mul he he (pow_nonneg (Nat.cast_nonneg _) _) (bp_pos _).le).trans_eq ?_
  rw [←bp_add]; unfold V peakExpense; congr 1; ring

end HadwigerCounterexample

end

end OAI
