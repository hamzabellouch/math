import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RationalLattice03
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
open _root_.Polynomial _root_.OAI.Polynomial
noncomputable section
namespace RationalLattice
variable {G : Type*} [Group G] [TopologicalSpace G] {n : ℕ}
variable (c : RealCoordinates G n)

theorem powerPolynomial_rational {g : G} (hg : IsRational c g) (i : Fin n) :
    ∃ p : ℚ[X], powerPolynomial c g i = p.map (algebraMap ℚ ℝ) := by
  let h : rationalSubgroup c := ⟨g,hg⟩
  obtain ⟨p,hp⟩ := TriangularDenominators.natpow_polynomial (rationalCoordinates c) h i
  refine ⟨p,Polynomial.eq_of_eval_nat_eq ?_⟩
  intro m
  rw [powerPolynomial_nat]
  have he := congrArg (fun q : ℚ => (q:ℝ)) (hp m)
  change ((p.eval (m:ℚ) : ℚ) : ℝ) = (qcoord c (h^m) i : ℝ) at he
  rw [qcoord_spec] at he
  change ((p.eval (m:ℚ) : ℚ) : ℝ) = c.coord (g^m) i at he
  rw [← he]
  simpa using (Polynomial.eval_map_apply (p:=p) (algebraMap ℚ ℝ) (m:ℚ)).symm

 

theorem realPower_rational {g : G} (hg : IsRational c g) (t : ℚ) :
    IsRational c (realPower c g t) := by
  intro i
  obtain ⟨p,hp⟩ := powerPolynomial_rational c hg i
  refine ⟨p.eval t,?_⟩
  rw [realPower_coord,hp]
  exact (Polynomial.eval_map_apply (p:=p) (algebraMap ℚ ℝ) t).symm

end RationalLattice
end
end
 

 
section
open _root_.Polynomial _root_.OAI.Polynomial
noncomputable section
namespace RationalLattice
variable {G : Type*} [Group G] [TopologicalSpace G] {n : ℕ}
variable (c : RealCoordinates G n)

lemma coord_mul_of_left_zero (g h : G) (i : Fin n)
    (hg : ∀ j : Fin n, j < i → c.coord g j = 0) :
    c.coord (g*h) i = c.coord g i + c.coord h i := by
  have he : (Sum.elim (fun j : Fin i.val => c.coord g ⟨j.val,lt_trans j.isLt i.isLt⟩)
      (fun j : Fin i.val => c.coord h ⟨j.val,lt_trans j.isLt i.isLt⟩)) =
      (Sum.elim (fun j : Fin i.val => c.coord 1 ⟨j.val,lt_trans j.isLt i.isLt⟩)
      (fun j : Fin i.val => c.coord h ⟨j.val,lt_trans j.isLt i.isLt⟩)) := by
    funext a
    cases a with
    | inl j => simp only [Sum.elim_inl]; rw [hg _ j.isLt,c.one_coord]
    | inr j => rfl
  have hm := c.mul_coord 1 h i
  rw [one_mul,c.one_coord,zero_add] at hm
  rw [c.mul_coord,he]
  linarith

lemma coord_mul_of_right_zero (g h : G) (i : Fin n)
    (hh : ∀ j : Fin n, j < i → c.coord h j = 0) :
    c.coord (g*h) i = c.coord g i + c.coord h i := by
  have he : (Sum.elim (fun j : Fin i.val => c.coord g ⟨j.val,lt_trans j.isLt i.isLt⟩)
      (fun j : Fin i.val => c.coord h ⟨j.val,lt_trans j.isLt i.isLt⟩)) =
      (Sum.elim (fun j : Fin i.val => c.coord g ⟨j.val,lt_trans j.isLt i.isLt⟩)
      (fun j : Fin i.val => c.coord 1 ⟨j.val,lt_trans j.isLt i.isLt⟩)) := by
    funext a
    cases a with
    | inl j => rfl
    | inr j => simp only [Sum.elim_inr]; rw [hh _ j.isLt,c.one_coord]
  have hm := c.mul_coord g 1 i
  rw [mul_one,c.one_coord,add_zero] at hm
  rw [c.mul_coord,he]
  linarith

lemma realPower_coord_of_lower_zero (g : G) (i : Fin n)
    (hg : ∀ j : Fin n, j < i → c.coord g j = 0) (t : ℝ) :
    c.coord (realPower c g t) i = t * c.coord g i := by
  have hp : powerPolynomial c g i = X * C (c.coord g i) := by
    apply Polynomial.eq_of_eval_nat_eq
    intro m
    rw [powerPolynomial_nat]
    simp only [Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_C]
    induction m with
    | zero => simp [c.one_coord]
    | succ m ih => rw [pow_succ,coord_mul_of_right_zero c _ _ i hg,ih]; push_cast; ring
  rw [realPower_coord,hp]
  simp only [Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_C]

def basisElement (i : Fin n) : G := c.coord.symm (Pi.single i 1)
def basisFlow (i : Fin n) (t : ℝ) : G := realPower c (basisElement c i) t

lemma basisFlow_continuous (i : Fin n) : Continuous (basisFlow c i) :=
  realPower_continuous c _
@[simp] lemma basisFlow_zero (i : Fin n) : basisFlow c i 0 = 1 := realPower_zero c _
lemma basisFlow_add (i : Fin n) (s t : ℝ) :
    basisFlow c i (s+t) = basisFlow c i s * basisFlow c i t := realPower_add c _ _ _
lemma basisFlow_neg (i : Fin n) (t : ℝ) : basisFlow c i (-t) = (basisFlow c i t)⁻¹ :=
  realPower_neg c _ _

lemma basisFlow_coord (i j : Fin n) (hji : j ≤ i) (t : ℝ) :
    c.coord (basisFlow c i t) j = if j=i then t else 0 := by
  classical
  have hzero (k : Fin n) (hk : k < j) : c.coord (basisElement c i) k = 0 := by
    have hki : k ≠ i := ne_of_lt (lt_of_lt_of_le hk hji)
    simp [basisElement,hki]
  change c.coord (realPower c (basisElement c i) t) j = _
  rw [realPower_coord_of_lower_zero c _ j hzero]
  simp only [basisElement,Homeomorph.apply_symm_apply,Pi.single_apply]
  split_ifs <;> simp_all

 
def peel (g : G) : ℕ → G
  | 0 => g
  | k+1 => if h : k<n then
      basisFlow c ⟨k,h⟩ (-c.coord (peel g k) ⟨k,h⟩) * peel g k
    else peel g k

lemma peel_continuous [IsTopologicalGroup G] (k : ℕ) : Continuous (fun g => peel c g k) := by
  induction k with
  | zero => exact continuous_id
  | succ k ih =>
    simp only [peel]
    split_ifs with h
    · exact ((basisFlow_continuous c _).comp ((continuous_apply _).comp
        (c.coord.continuous.comp ih)).neg).mul ih
    · exact ih

lemma peel_zero_coordinates (g : G) (k : ℕ) :
    ∀ i : Fin n, i.val < k → c.coord (peel c g k) i = 0 := by
  induction k with
  | zero => intro i hi; omega
  | succ k ih =>
    intro i hi
    by_cases hk : k<n
    · rw [peel,dite_eq_left hk]
      rw [coord_mul_of_left_zero c _ _ i (by
        intro j hj
        rw [basisFlow_coord c _ j (show j.val ≤ k from by change j.val < i.val at hj; omega)]
        simp [show j ≠ (⟨k,hk⟩:Fin n) from fun h => by have := congrArg Fin.val h; change j.val < i.val at hj; dsimp at this; omega])]
      by_cases hik : i.val < k
      · rw [ih i hik,basisFlow_coord c _ i (show i.val ≤ k from by omega)]
        simp [show i ≠ (⟨k,hk⟩:Fin n) from fun h => by have := congrArg Fin.val h; dsimp at this; omega]
      · have he : i = (⟨k,hk⟩:Fin n) := Fin.ext (show i.val = k from by omega)
        subst i
        rw [basisFlow_coord c _ _ le_rfl]
        simp
    · rw [peel,dite_eq_right hk]
      exact ih i (by omega)

lemma peel_dimension (g : G) : peel c g n = 1 := by
  apply c.coord.injective
  funext i
  rw [peel_zero_coordinates c g n i i.isLt,c.one_coord]

def expCoordinates (g : G) (i : Fin n) : ℝ := c.coord (peel c g i.val) i

def tailProduct (x : Fin n → ℝ) (k : ℕ) : G :=
  ((List.ofFn (fun i => basisFlow c i (x i))).drop k).prod

def expProduct (x : Fin n → ℝ) : G := tailProduct c x 0

lemma tailProduct_dimension (x : Fin n → ℝ) : tailProduct c x n = 1 := by
  have h := List.drop_length (l := List.ofFn (fun i => basisFlow c i (x i)))
  simp only [List.length_ofFn] at h
  simp only [tailProduct,h,List.prod_nil]

lemma tailProduct_step (x : Fin n → ℝ) (k : ℕ) (hk : k<n) :
    tailProduct c x k = basisFlow c ⟨k,hk⟩ (x ⟨k,hk⟩) * tailProduct c x (k+1) := by
  unfold tailProduct
  rw [List.drop_eq_getElem_cons (by simpa using hk),List.prod_cons,List.getElem_ofFn]

lemma tailProduct_lower (x : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    ∀ i : Fin n, i.val < k → c.coord (tailProduct c x k) i = 0 := by
  induction hk using Nat.decreasingInduction with
  | self => intro i hi; rw [tailProduct_dimension,c.one_coord]
  | of_succ k hk ih =>
    intro i hi
    rw [tailProduct_step c x k hk,coord_mul_of_left_zero c _ _ i (by
      intro j hj
      rw [basisFlow_coord c _ j (show j.val ≤ k from by change j.val < i.val at hj; omega)]
      rw [ite_eq_right (fun h => by have := congrArg Fin.val h; change j.val < i.val at hj; dsimp at this; omega)])]
    rw [basisFlow_coord c _ i (show i.val ≤ k from by omega),ih i (by omega)]
    rw [ite_eq_right (fun h => by have := congrArg Fin.val h; dsimp at this; omega),zero_add]

lemma tailProduct_coord (x : Fin n → ℝ) (i : Fin n) :
    c.coord (tailProduct c x i.val) i = x i := by
  rw [tailProduct_step c x i.val i.isLt,coord_mul_of_left_zero c _ _ i (by
    intro j hj
    rw [basisFlow_coord c i j (le_of_lt hj),ite_eq_right (ne_of_lt hj)])]
  rw [basisFlow_coord c i i le_rfl,ite_eq_left rfl,
    tailProduct_lower c x (i.val+1) i.isLt i (Nat.lt_succ_self _),add_zero]

lemma peel_expProduct (x : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    peel c (expProduct c x) k = tailProduct c x k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hkn : k<n := by omega
    rw [peel,dite_eq_left hkn,ih (by omega)]
    rw [tailProduct_coord c x ⟨k,hkn⟩,tailProduct_step c x k hkn,basisFlow_neg]
    exact inv_mul_cancel_left _ _

lemma expCoordinates_expProduct (x : Fin n → ℝ) : expCoordinates c (expProduct c x) = x := by
  funext i
  rw [expCoordinates,peel_expProduct c x i.val (Nat.le_of_lt i.isLt),tailProduct_coord]

lemma tailProduct_expCoordinates (g : G) (k : ℕ) (hk : k ≤ n) :
    tailProduct c (expCoordinates c g) k = peel c g k := by
  induction hk using Nat.decreasingInduction with
  | self => rw [tailProduct_dimension,peel_dimension]
  | of_succ k hk ih =>
    rw [tailProduct_step c _ k hk,ih,expCoordinates,peel,dite_eq_left hk,basisFlow_neg]
    exact mul_inv_cancel_left _ _

lemma expProduct_expCoordinates (g : G) : expProduct c (expCoordinates c g) = g := by
  simpa only [expProduct,peel] using tailProduct_expCoordinates c g 0 (Nat.zero_le n)

lemma expCoordinates_continuous [IsTopologicalGroup G] : Continuous (expCoordinates c) := by
  apply continuous_pi
  intro i
  exact (continuous_apply i).comp (c.coord.continuous.comp (peel_continuous c i.val))

lemma expProduct_continuous [IsTopologicalGroup G] : Continuous (expProduct c) := by
  change Continuous (fun x : Fin n → ℝ => (List.ofFn (fun i => basisFlow c i (x i))).prod)
  simp only [List.ofFn_eq_map]
  exact continuous_list_prod _ (fun i _ => (basisFlow_continuous c i).comp (continuous_apply i))

 

def secondKindHomeomorph [IsTopologicalGroup G] : G ≃ₜ (Fin n → ℝ) where
  toFun := expCoordinates c
  invFun := expProduct c
  left_inv := expProduct_expCoordinates c
  right_inv := expCoordinates_expProduct c
  continuous_toFun := expCoordinates_continuous c
  continuous_invFun := expProduct_continuous c

end RationalLattice
end
end
 

 
section
noncomputable section
namespace MalcevPrefixQuotient
open RationalLattice
variable {G : Type*} [Group G] [TopologicalSpace G] {n r : ℕ}
variable (c : RealCoordinates G n) (hr : r ≤ n)

include hr in
 

lemma prefix_eq_iff (g h : G) :
    (∀ i : Fin n, i.val < r → c.coord g i = c.coord h i) ↔
    (∀ i : Fin n, i.val < r → c.coord (g⁻¹*h) i = 0) := by
  constructor
  · intro he i hi
    have haux : ∀ m : ℕ, ∀ hm : m < r, c.coord (g⁻¹*h) ⟨m,lt_of_lt_of_le hm hr⟩ = 0 := by
      intro m
      induction m using Nat.strong_induction_on with
      | h m ih =>
        intro hm
        let j : Fin n := ⟨m,lt_of_lt_of_le hm hr⟩
        have hd : ∀ u : Fin n, u < j → c.coord (g⁻¹*h) u = 0 := by
          intro u hu
          exact ih u.val hu (lt_trans hu hm)
        have hc := coord_mul_of_right_zero c g (g⁻¹*h) j hd
        rw [mul_inv_cancel_left] at hc
        have he' := he j hm
        linarith
    exact haux i.val hi
  · intro hd i hi
    have hc := coord_mul_of_right_zero c g (g⁻¹*h) i (fun u hu => hd u (lt_trans hu hi))
    rw [mul_inv_cancel_left,hd i hi,add_zero] at hc
    exact hc.symm

variable (N : Subgroup G)
variable (hN : ∀ g : G, g ∈ N ↔ ∀ i : Fin n, i.val < r → c.coord g i = 0)
include hr hN in
lemma eq_coset_iff (g h : G) :
    (QuotientGroup.mk g : G ⧸ N) = QuotientGroup.mk h ↔
    ∀ i : Fin n, i.val < r → c.coord g i = c.coord h i := by
  rw [QuotientGroup.eq,hN]
  exact (prefix_eq_iff c hr g h).symm

def embed (i : Fin r) : Fin n := ⟨i.val,lt_of_lt_of_le i.isLt hr⟩
def lift (x : Fin r → ℝ) (i : Fin n) : ℝ := if h : i.val < r then x ⟨i.val,h⟩ else 0
@[simp] lemma lift_embed (x : Fin r → ℝ) (i : Fin r) : lift x (embed hr i) = x i := by
  simp [lift,embed,i.isLt]
lemma lift_continuous : Continuous (lift (n:=n) (r:=r)) := by
  apply continuous_pi
  intro i
  unfold lift
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

def coordinates (x : G ⧸ N) (i : Fin r) : ℝ := Quotient.lift (fun g : G => c.coord g (embed hr i))
  (by
    intro g h he
    exact ((prefix_eq_iff c hr g h).mpr ((hN _).mp (QuotientGroup.leftRel_apply.mp he))) (embed hr i) i.isLt) x

@[simp] lemma coordinates_mk (g : G) (i : Fin r) :
    coordinates c hr N hN (QuotientGroup.mk g) i = c.coord g (embed hr i) := rfl

def represent (x : Fin r → ℝ) : G := c.coord.symm (lift x)
def rebuild (x : Fin r → ℝ) : G ⧸ N := QuotientGroup.mk (represent c x)

lemma coordinates_rebuild (x : Fin r → ℝ) : coordinates c hr N hN (rebuild c N x) = x := by
  funext i
  simp [rebuild,represent,coordinates_mk]
lemma rebuild_coordinates (x : G ⧸ N) : rebuild c N (coordinates c hr N hN x) = x := by
  induction x using Quotient.inductionOn with | h g =>
    apply (eq_coset_iff c hr N hN _ _).mpr
    intro i hi
    simp [represent,lift,hi,embed]
lemma coordinates_continuous : Continuous (coordinates c hr N hN) := by
  rw [(QuotientGroup.isQuotientMap_mk N).continuous_iff]
  apply continuous_pi
  intro i
  change Continuous (fun g : G => c.coord g (embed hr i))
  exact (continuous_apply (embed hr i)).comp c.coord.continuous
lemma rebuild_continuous : Continuous (rebuild c (r:=r) N) :=
  QuotientGroup.continuous_mk.comp (c.coord.symm.continuous.comp lift_continuous)

def homeomorph : (G ⧸ N) ≃ₜ (Fin r → ℝ) where
  toFun := coordinates c hr N hN
  invFun := rebuild c N
  left_inv := rebuild_coordinates c hr N hN
  right_inv := coordinates_rebuild c hr N hN
  continuous_toFun := coordinates_continuous c hr N hN
  continuous_invFun := rebuild_continuous c N

variable [N.Normal]

 

def quotientChart : RealCoordinates (G ⧸ N) r where
  coord := homeomorph c hr N hN
  one_coord i := c.one_coord _
  correction i := c.correction (embed hr i)
  mul_coord g h i := by
    induction g using Quotient.inductionOn with | h g =>
      induction h using Quotient.inductionOn with | h h =>
        exact c.mul_coord g h (embed hr i)

end MalcevPrefixQuotient

end
end
end
end
end

end OAI
