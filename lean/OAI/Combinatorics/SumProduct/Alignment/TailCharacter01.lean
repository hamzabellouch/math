import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.MalcevCharacters01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
noncomputable section
end
 
end

section
 

 

noncomputable section
open scoped BigOperators
namespace TailRefinementCharts
open RationalLattice MalcevCharacters RationalTailCoordinates IntegerHyperplane
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {r n : ℕ} (c : RealCoordinates G (r+n)) (hsk : SecondKind c)
variable (H : Subgroup G)
variable (hH : ∀ g : G, g∈H ↔ ∀ i : Fin (r+n), i.val < r → c.coord g i=0)

def prefixVector (x : Fin (r+n) → ℝ) (i : Fin (r+n)) : ℝ :=
  if i.val < r then x i else 0

def prefixElement (g : G) : G := c.coord.symm (prefixVector (r:=r) (c.coord g))
def tail (g : G) : H := rebuild c H hH (fun i => c.coord g (embed r i))

omit [IsTopologicalGroup G] in
@[simp] lemma prefix_coord (g : G) (i : Fin (r+n)) :
    c.coord (prefixElement c g) i=prefixVector (r:=r) (c.coord g) i := by
  simp [prefixElement]
omit [IsTopologicalGroup G] in
@[simp] lemma tail_coord (g : G) (i : Fin n) :
    c.coord (tail c H hH g).val (embed r i)=c.coord g (embed r i) := by
  simp [tail,rebuild]

include hsk in
omit [IsTopologicalGroup G] in
lemma prefix_product (g : G) : prefixElement c g=
    (List.ofFn (fun i : Fin r => axis c (i.castLE (Nat.le_add_right r n))
      (c.coord g (i.castLE (Nat.le_add_right r n))))).prod := by
  rw [hsk.ordered (prefixElement c g),List.ofFn_add,List.prod_append]
  have hz : (List.ofFn (fun i : Fin n => axis c (Fin.natAdd r i)
      (c.coord (prefixElement c g) (Fin.natAdd r i)))).prod=1 := by
    have he : (fun i : Fin n => axis c (Fin.natAdd r i)
      (c.coord (prefixElement c g) (Fin.natAdd r i)))=fun _ => (1:G) := by
      funext i
      simp [prefixVector]
    rw [he]
    simp
  rw [hz,mul_one]
  congr 1
  apply List.ofFn_inj.mpr
  funext i
  simp [prefixVector,i.isLt]

include hsk in
lemma decompose (g : G) : g=prefixElement c g*(tail c H hH g).val := by
  rw [prefix_product c hsk]
  have ht := (tail_secondKind c H hH hsk).ordered (tail c H hH g)
  have ht' := congrArg Subtype.val ht
  simp only [← H.subtype_apply,map_list_prod,List.map_ofFn] at ht'
  change (tail c H hH g).val=(List.ofFn (fun i : Fin n => (axis (tailCoordinates c H hH) i ((tailCoordinates c H hH).coord (tail c H hH g) i)).val)).prod at ht'
  simp only [axis_val] at ht'
  have hc : ∀ i, (tailCoordinates c H hH).coord (tail c H hH g) i=c.coord g (embed r i) :=
    fun i => tail_coord c H hH g i
  simp_rw [hc] at ht'
  rw [ht']
  conv_lhs => rw [hsk.ordered g,List.ofFn_add,List.prod_append]
  rfl

omit [IsTopologicalGroup G] in
lemma prefix_congr {g h : G} (he : ∀ i : Fin (r+n),i.val < r → c.coord g i=c.coord h i) :
    prefixElement c g=prefixElement c h := by
  unfold prefixElement
  apply congrArg c.coord.symm
  funext i
  unfold prefixVector
  split_ifs with hi
  · exact he i hi
  · rfl

omit [IsTopologicalGroup G] in
lemma prefix_mul_congr (hr : r < r+n) (g h : G) :
    prefixElement c (g*h)=prefixElement c (prefixElement c g*prefixElement c h) := by
  apply prefix_congr c
  exact mul_lower_congr c ⟨r,hr⟩
    (fun i hi => by simp [prefixVector,(show i.val < r from hi)])
    (fun i hi => by simp [prefixVector,(show i.val < r from hi)])

variable (χ : H →* Multiplicative ℝ)
variable (hconj : ∀ (g : G) (x : H), g⁻¹*x.val*g∈H)
variable (hχconj : ∀ (g : G) (x : H), χ ⟨g⁻¹*x.val*g,hconj g x⟩=χ x)

include hsk hχconj in
 

theorem tail_character_mul (hr : r < r+n) (g h : G) :
    (χ (tail c H hH (g*h))).toAdd = (χ (tail c H hH g)).toAdd+
      (χ (tail c H hH h)).toAdd+
      (χ (tail c H hH (prefixElement c g*prefixElement c h))).toAdd := by
  let a:=prefixElement c g
  let b:=prefixElement c h
  let u:=tail c H hH g
  let v:=tail c H hH h
  let e:=tail c H hH (a*b)
  let u':H:=⟨b⁻¹*u.val*b,hconj b u⟩
  have he : tail c H hH (g*h)=e*u'*v := by
    apply Subtype.ext
    have hg := decompose c hsk H hH g
    have hh := decompose c hsk H hH h
    have hab := decompose c hsk H hH (a*b)
    have hgh := decompose c hsk H hH (g*h)
    have hp := prefix_mul_congr c hr g h
    change g=a*u.val at hg
    change h=b*v.val at hh
    change a*b=prefixElement c (a*b)*e.val at hab
    change prefixElement c (g*h)=prefixElement c (a*b) at hp
    rw [hp] at hgh
    change (tail c H hH (g*h)).val=e.val*(b⁻¹*u.val*b)*v.val
    apply mul_left_cancel (a:=prefixElement c (a*b))
    rw [← hgh,hg,hh]
    calc (a*u.val)*(b*v.val)=(a*b)*((b⁻¹*u.val*b)*v.val) := by group
         _ = (prefixElement c (a*b)*e.val)*((b⁻¹*u.val*b)*v.val) := congrArg (fun z => z*((b⁻¹*u.val*b)*v.val)) hab
         _ = _ := by group
  rw [he,χ.map_mul,χ.map_mul]
  change (χ e).toAdd+(χ u').toAdd+(χ v).toAdd=_
  rw [show χ u'=χ u from hχconj b u]
  dsimp [e,u,v,a,b]
  ring

end TailRefinementCharts

namespace BlockSplitCoordinates
open RationalTailCoordinates IntegerHyperplane RationalPolynomialMap
variable {r n : ℕ}

def blockMap (f : (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin (r+n) → ℝ)
    (i : Fin (r+n)) : ℝ :=
  if hi : i.val < r then x i else f (fun j => x (embed r j)) ⟨i.val-r,by omega⟩

@[simp] lemma blockMap_prefix (f : (Fin n → ℝ) → (Fin n → ℝ))
    (x : Fin (r+n) → ℝ) (i : Fin (r+n)) (hi : i.val < r) : blockMap f x i=x i := by
  simp [blockMap,hi]
@[simp] lemma blockMap_embed (f : (Fin n → ℝ) → (Fin n → ℝ))
    (x : Fin (r+n) → ℝ) (i : Fin n) :
    blockMap f x (embed r i)=f (fun j => x (embed r j)) i := by
  simp [blockMap,embed]

lemma blockMap_comp (f g : (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin (r+n) → ℝ) :
    blockMap f (blockMap g x)=blockMap (f ∘ g) x := by
  funext i
  unfold blockMap
  split_ifs with hi
  · rfl
  · congr 2
    funext j
    simp [embed]

lemma blockMap_id (x : Fin (r+n) → ℝ) : blockMap id x=x := by
  funext i
  unfold blockMap
  split_ifs with hi
  · rfl
  · apply congrArg x
    apply Fin.ext
    simp only [embed]
    omega

lemma blockMap_continuous {f : (Fin n → ℝ) → (Fin n → ℝ)} (hf : Continuous f) :
    Continuous (blockMap (r:=r) f) := by
  apply continuous_pi
  intro i
  unfold blockMap
  split_ifs
  · exact continuous_apply _
  · exact (continuous_apply _).comp (hf.comp (continuous_pi (fun _ => continuous_apply _)))

def blockHomeomorph (f : (Fin n → ℝ) ≃ₜ (Fin n → ℝ)) :
    (Fin (r+n) → ℝ) ≃ₜ (Fin (r+n) → ℝ) where
  toFun := blockMap f
  invFun := blockMap f.symm
  left_inv x := by
    rw [blockMap_comp]
    have he : ((f.symm : (Fin n → ℝ) → (Fin n → ℝ))∘f)=id := by
      funext y; exact f.symm_apply_apply y
    rw [he,blockMap_id]
  right_inv x := by
    rw [blockMap_comp]
    have he : ((f : (Fin n → ℝ) → (Fin n → ℝ))∘f.symm)=id := by
      funext y; exact f.apply_symm_apply y
    rw [he,blockMap_id]
  continuous_toFun := blockMap_continuous f.continuous
  continuous_invFun := blockMap_continuous f.symm.continuous

lemma blockMap_polynomial (f : (Fin n → ℝ) → (Fin n → ℝ))
    (hf : ∀ j, IsPolynomial (fun x => f x j)) (i : Fin (r+n)) :
    IsPolynomial (fun x => blockMap f x i) := by
  unfold blockMap
  split_ifs
  · exact coordinate _
  · exact comp (hf _) (fun _ => coordinate _)

lemma splitCoordinates_polynomial (k : Fin (n+1) → ℤ) (p : Fin (n+1)) (i : Fin (n+1)) :
    IsPolynomial (fun x => splitCoordinates k p x i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · change IsPolynomial (fun x => (∑ j,(k j:ℝ)*x j)/(k p:ℝ))
    have hsum : IsPolynomial (fun x : Fin (n+1) → ℝ => ∑ j,(k j:ℝ)*x j) := by
      refine ⟨∑ j,MvPolynomial.C (k j:ℚ)*MvPolynomial.X j,?_⟩
      intro x
      rw [MvPolynomial.eval₂_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [MvPolynomial.eval₂_mul,MvPolynomial.eval₂_C,MvPolynomial.eval₂_X]
      simp
    simpa only [Rat.cast_inv,Rat.cast_intCast,div_eq_mul_inv] using mul hsum (const ((k p:ℚ)⁻¹))
  · exact coordinate _
end BlockSplitCoordinates

namespace TailCharacterRechart
open RationalLattice MalcevCharacters RationalTailCoordinates IntegerHyperplane
open BlockSplitCoordinates TailRefinementCharts RationalPolynomialMap
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {r n : ℕ} (c : RealCoordinates G (r+(n+1)))
variable (k : Fin (n+1) → ℤ) (p : Fin (n+1)) (hp : k p≠0)

def chartHomeomorph : G ≃ₜ (Fin (r+(n+1)) → ℝ) :=
  c.coord.trans (blockHomeomorph (r:=r) (splitHomeomorph k p hp))

omit [IsTopologicalGroup G] in
lemma chart_prefix (g : G) (i : Fin (r+(n+1))) (hi : i.val < r) :
    chartHomeomorph c k p hp g i=c.coord g i := blockMap_prefix _ _ _ hi
omit [IsTopologicalGroup G] in
lemma chart_head (g : G) : chartHomeomorph c k p hp g (embed r 0)=
    form k (fun j => c.coord g (embed r j))/(k p:ℝ) := by
  change blockMap (splitCoordinates k p) (c.coord g) (embed r 0)=_
  rw [blockMap_embed]
  rfl
omit [IsTopologicalGroup G] in
lemma chart_tail (g : G) (i : Fin n) :
    chartHomeomorph c k p hp g (embed r i.succ)=c.coord g (embed r (p.succAbove i)) := by
  change blockMap (splitCoordinates k p) (c.coord g) (embed r i.succ)=_
  rw [blockMap_embed]
  rfl

omit [IsTopologicalGroup G] in
lemma chart_polynomial (i : Fin (r+(n+1))) :
    IsPolynomial (fun x => chartHomeomorph c k p hp (c.coord.symm x) i) := by
  change IsPolynomial (fun x => blockMap (splitCoordinates k p) (c.coord (c.coord.symm x)) i)
  simp only [Homeomorph.apply_symm_apply]
  exact blockMap_polynomial _ (splitCoordinates_polynomial k p) i
omit [IsTopologicalGroup G] in
lemma inverse_polynomial (i : Fin (r+(n+1))) :
    IsPolynomial (fun x => c.coord ((chartHomeomorph c k p hp).symm x) i) := by
  change IsPolynomial (fun x => c.coord (c.coord.symm (blockMap (splitLift k p) x)) i)
  simp only [Homeomorph.apply_symm_apply]
  exact blockMap_polynomial _ (splitLift_polynomial k p) i

omit [IsTopologicalGroup G] in
lemma chart_one (i : Fin (r+(n+1))) : chartHomeomorph c k p hp 1 i=0 := by
  by_cases hi : i.val < r
  · rw [chart_prefix c k p hp 1 i hi,c.one_coord]
  · let a : Fin (n+1):=⟨i.val-r,by omega⟩
    have he : i=embed r a := by apply Fin.ext; simp [a,embed]; omega
    rw [he]
    refine Fin.cases ?_ (fun j => ?_) a
    · rw [chart_head]
      simp [form,c.one_coord]
    · rw [chart_tail,c.one_coord]

variable (hlast : ∀ j : Fin (n+1), p < j → k j=0)
include hlast in
omit [IsTopologicalGroup G] in
lemma old_lower_congr (i : Fin n) {g h : G}
    (he : ∀ j : Fin (r+(n+1)),j < embed r i.succ →
      chartHomeomorph c k p hp g j=chartHomeomorph c k p hp h j)
    (a : Fin (r+(n+1))) (ha : a < embed r (p.succAbove i)) : c.coord g a=c.coord h a := by
  by_cases har : a.val < r
  · rw [← chart_prefix c k p hp g a har,← chart_prefix c k p hp h a har]
    exact he a (by change a.val < r+i.val+1; omega)
  · let a' : Fin (n+1):=⟨a.val-r,by omega⟩
    have ha' : a=embed r a' := by apply Fin.ext; simp [a',embed]; omega
    rw [ha']
    have ht (u : G) : (fun j => c.coord u (embed r j))=
        splitLift k p (fun j => chartHomeomorph c k p hp u (embed r j)) := by
      have hh := splitLift_splitCoordinates k p hp (fun j => c.coord u (embed r j))
      change (fun j => c.coord u (embed r j))=
        splitLift k p (fun j => blockMap (splitCoordinates k p) (c.coord u) (embed r j))
      simp only [blockMap_embed]
      exact hh.symm
    rw [congrFun (ht g) a',congrFun (ht h) a']
    apply splitLift_lower_dep k p hlast i
    · intro j hj
      exact he (embed r j) (Nat.add_lt_add_left hj r)
    · change a.val < r+(p.succAbove i).val at ha
      change a.val-r < (p.succAbove i).val
      omega

def lowerElement (g : G) (i : Fin (r+(n+1))) : G :=
  (chartHomeomorph c k p hp).symm
    (lowerExtend i (fun j => chartHomeomorph c k p hp g ⟨j.val,lt_trans j.isLt i.isLt⟩))

omit [IsTopologicalGroup G] in
lemma lowerElement_coord (g : G) (i j : Fin (r+(n+1))) :
    chartHomeomorph c k p hp (lowerElement c k p hp g i) j=
      if j.val < i.val then chartHomeomorph c k p hp g j else 0 := by
  simp only [lowerElement,Homeomorph.apply_symm_apply,lowerExtend]
  split_ifs <;> rfl
omit [IsTopologicalGroup G] in
lemma lowerElement_below (g : G) (i j : Fin (r+(n+1))) (hj : j < i) :
    chartHomeomorph c k p hp (lowerElement c k p hp g i) j=chartHomeomorph c k p hp g j := by
  rw [lowerElement_coord,ite_eq_left (show j.val < i.val from hj)]
omit [IsTopologicalGroup G] in
lemma lowerElement_at (g : G) (i : Fin (r+(n+1))) :
    chartHomeomorph c k p hp (lowerElement c k p hp g i) i=0 := by
  rw [lowerElement_coord,ite_eq_right (lt_irrefl _)]

omit [IsTopologicalGroup G] in
lemma exists_correction (i : Fin (r+(n+1))) :
    ∃ P : MvPolynomial (Fin i.val ⊕ Fin i.val) ℚ,
      ∀ v : (Fin i.val ⊕ Fin i.val) → ℝ,
      chartHomeomorph c k p hp
        ((chartHomeomorph c k p hp).symm (lowerExtend i (fun j => v (.inl j))) *
         (chartHomeomorph c k p hp).symm (lowerExtend i (fun j => v (.inr j)))) i=
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) v P := by
  have hm : IsPolynomialMap c (fun v : (Fin i.val ⊕ Fin i.val) → ℝ => (chartHomeomorph c k p hp).symm (lowerExtend i (fun j => v (.inl j))) *
      (chartHomeomorph c k p hp).symm (lowerExtend i (fun j => v (.inr j)))) := by
    apply polynomialMap_mul
    all_goals
      intro a
      apply comp (inverse_polynomial c k p hp a)
      intro b
      unfold lowerExtend
      split_ifs
      · exact coordinate _
      · exact zero
  have hres := comp (chart_polynomial c k p hp i) hm
  simpa only [IsPolynomial,Homeomorph.symm_apply_apply] using hres

def correction (i : Fin (r+(n+1))) : MvPolynomial (Fin i.val ⊕ Fin i.val) ℚ :=
  (exists_correction c k p hp i).choose

omit [IsTopologicalGroup G] in
lemma correction_eval (g h : G) (i : Fin (r+(n+1))) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ)
      (Sum.elim (fun j => chartHomeomorph c k p hp g ⟨j.val,lt_trans j.isLt i.isLt⟩)
        (fun j => chartHomeomorph c k p hp h ⟨j.val,lt_trans j.isLt i.isLt⟩))
        (correction c k p hp i)=
    chartHomeomorph c k p hp (lowerElement c k p hp g i*lowerElement c k p hp h i) i :=
  ((exists_correction c k p hp i).choose_spec _).symm

omit [IsTopologicalGroup G] in
lemma prefix_defect (g h : G) (i : Fin (r+(n+1))) (hi : i.val < r) :
    chartHomeomorph c k p hp (g*h) i=chartHomeomorph c k p hp g i+
      chartHomeomorph c k p hp h i+
      chartHomeomorph c k p hp (lowerElement c k p hp g i*lowerElement c k p hp h i) i := by
  have hl (u : G) (j : Fin (r+(n+1))) (hj : j < i) :
      c.coord u j=c.coord (lowerElement c k p hp u i) j := by
    have hjr : j.val < r:=lt_trans hj hi
    rw [← chart_prefix c k p hp u j hjr,← chart_prefix c k p hp _ j hjr,
      lowerElement_below c k p hp u i j hj]
  have hz (u : G) : c.coord (lowerElement c k p hp u i) i=0 := by
    rw [← chart_prefix c k p hp _ i hi,lowerElement_at]
  have he := correction_eq_of_lower_eq c i (hl g) (hl h)
  simp only [hz,sub_zero] at he
  simp only [chart_prefix c k p hp _ i hi]
  linarith only [he]

include hlast in
omit [IsTopologicalGroup G] in
lemma tail_defect (g h : G) (i : Fin n) :
    chartHomeomorph c k p hp (g*h) (embed r i.succ)=
      chartHomeomorph c k p hp g (embed r i.succ)+
      chartHomeomorph c k p hp h (embed r i.succ)+
      chartHomeomorph c k p hp
        (lowerElement c k p hp g (embed r i.succ)*lowerElement c k p hp h (embed r i.succ))
        (embed r i.succ) := by
  have hl (u : G) : ∀ a : Fin (r+(n+1)),a < embed r (p.succAbove i) →
      c.coord u a=c.coord (lowerElement c k p hp u (embed r i.succ)) a :=
    old_lower_congr c k p hp hlast i (fun j hj =>
      (lowerElement_below c k p hp u (embed r i.succ) j hj).symm)
  have hz (u : G) : c.coord (lowerElement c k p hp u (embed r i.succ)) (embed r (p.succAbove i))=0 := by
    rw [← chart_tail c k p hp _ i,lowerElement_at]
  have he := correction_eq_of_lower_eq c (embed r (p.succAbove i)) (hl g) (hl h)
  simp only [hz,sub_zero] at he
  simp only [chart_tail]
  linarith only [he]

variable (hsk : SecondKind c) (H : Subgroup G)
variable (hH : ∀ g : G, g∈H ↔ ∀ i : Fin (r+(n+1)),i.val < r → c.coord g i=0)
variable (χ : H →* Multiplicative ℝ)
variable (hconj : ∀ (g : G) (x : H),g⁻¹*x.val*g∈H)
variable (hχconj : ∀ (g : G) (x : H),χ ⟨g⁻¹*x.val*g,hconj g x⟩=χ x)
variable (hχ : ∀ x : H,(χ x).toAdd=form k ((tailCoordinates c H hH).coord x))

include hχ in
omit [IsTopologicalGroup G] in
lemma chart_head_character (g : G) : chartHomeomorph c k p hp g (embed r 0)=
    (χ (tail c H hH g)).toAdd/(k p:ℝ) := by
  rw [chart_head,hχ]
  congr 2
  funext j
  exact (tail_coord c H hH g j).symm

include hsk hχconj hχ in
lemma head_mul (g h : G) : chartHomeomorph c k p hp (g*h) (embed r 0)=
    chartHomeomorph c k p hp g (embed r 0)+chartHomeomorph c k p hp h (embed r 0)+
    chartHomeomorph c k p hp (prefixElement c g*prefixElement c h) (embed r 0) := by
  simp only [chart_head_character c k p hp H hH χ hχ]
  rw [tail_character_mul c hsk H hH χ hconj hχconj (by omega) g h]
  ring

omit [IsTopologicalGroup G] in
lemma prefix_lower_head (g : G) :
    prefixElement c (lowerElement c k p hp g (embed r 0))=prefixElement c g := by
  apply prefix_congr
  intro i hi
  rw [← chart_prefix c k p hp _ i hi,← chart_prefix c k p hp g i hi,
    lowerElement_below c k p hp g (embed r 0) i (by change i.val < r+0; omega)]

include hsk hχconj hχ in
lemma head_defect (g h : G) : chartHomeomorph c k p hp (g*h) (embed r 0)=
    chartHomeomorph c k p hp g (embed r 0)+chartHomeomorph c k p hp h (embed r 0)+
    chartHomeomorph c k p hp
      (lowerElement c k p hp g (embed r 0)*lowerElement c k p hp h (embed r 0)) (embed r 0) := by
  rw [head_mul c k p hp hsk H hH χ hconj hχconj hχ g h]
  congr 1
  rw [head_mul c k p hp hsk H hH χ hconj hχconj hχ
      (lowerElement c k p hp g (embed r 0)) (lowerElement c k p hp h (embed r 0)),
    lowerElement_at,lowerElement_at,prefix_lower_head,prefix_lower_head,zero_add,zero_add]

include hsk hχconj hχ hlast in
lemma mul_coord (g h : G) (i : Fin (r+(n+1))) :
    chartHomeomorph c k p hp (g*h) i=chartHomeomorph c k p hp g i+
      chartHomeomorph c k p hp h i+
      MvPolynomial.eval₂ (algebraMap ℚ ℝ)
        (Sum.elim (fun j => chartHomeomorph c k p hp g ⟨j.val,lt_trans j.isLt i.isLt⟩)
          (fun j => chartHomeomorph c k p hp h ⟨j.val,lt_trans j.isLt i.isLt⟩))
          (correction c k p hp i) := by
  rw [correction_eval]
  by_cases hi : i.val < r
  · exact prefix_defect c k p hp g h i hi
  · let a : Fin (n+1):=⟨i.val-r,by omega⟩
    have he : i=embed r a := by apply Fin.ext; simp [a,embed]; omega
    rw [he]
    refine Fin.cases ?_ (fun j => ?_) a
    · exact head_defect c k p hp hsk H hH χ hconj hχconj hχ g h
    · exact tail_defect c k p hp hlast g h j

 

def tailCharacterCoordinates : RealCoordinates G (r+(n+1)) where
  coord := chartHomeomorph c k p hp
  one_coord := chart_one c k p hp
  correction := correction c k p hp
  mul_coord := mul_coord c k p hp hlast hsk H hH χ hconj hχconj hχ

end TailCharacterRechart

end
end
end
end

end OAI
