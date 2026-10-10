import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.CubePolynomials01
import OAI.Combinatorics.SumProduct.Alignment.MalcevWeighted01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
noncomputable section
end
end

end

section

 

section
 

 
noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial
open scoped BigOperators
namespace Polynomial
open scoped _root_.Polynomial
lemma natDegree_le_of_taylor_sub (p : ℝ[X]) (d : ℕ)
    (hp : ∀ t : ℝ,(_root_.Polynomial.taylor t p-p).natDegree ≤ d) : p.natDegree ≤ d+1 := by
  have he : _root_.Polynomial.hasseDeriv (d+1) p=_root_.Polynomial.C (p.coeff (d+1)) := by
    apply Polynomial.funext
    intro t
    have h:=_root_.Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hp t) (Nat.lt_succ_self d))
    rw [_root_.Polynomial.coeff_sub,_root_.Polynomial.taylor_coeff] at h
    simpa only [_root_.Polynomial.eval_C] using sub_eq_zero.mp h
  have hd:=congrArg Polynomial.natDegree he
  rw [_root_.Polynomial.natDegree_hasseDeriv,_root_.Polynomial.natDegree_C] at hd
  omega
end Polynomial

namespace CubePolynomials
open CubeFaces
variable {G : Type*} [Group G]
lemma real_polynomial_mem (H : Filtration G) (A : Multiplicative ℝ →* G)
    (e k : ℕ) (hA : ∀ t : ℝ,A (Multiplicative.ofAdd t)∈H.level (e+k))
    (p : ℝ[X]) (hp : p.natDegree ≤ e) :
    (fun t : ℝ=>A (Multiplicative.ofAdd (p.eval t)))∈polynomials H k := by
  induction e generalizing k p with
  | zero =>
    have he : p=C (p.coeff 0) := eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero hp)
    rw [he]
    simp only [eval_C]
    exact const_mem (by simpa using hA (p.coeff 0))
  | succ e ih =>
    apply mem_of_derivatives
    · intro t
      exact H.antitone (Nat.le_add_left k (e+1)) (hA (p.eval t))
    · intro t
      let q:=taylor t p-p
      have hq : q.natDegree ≤ e := by
        by_cases hp0 : p=0
        · simp [q,hp0]
        by_cases hq0 : q=0
        · simp [hq0]
        have hd : q.degree < p.degree :=
          degree_sub_lt_right (degree_taylor p t) hp0 (leadingCoeff_taylor t p)
        have hd':q.natDegree < p.natDegree := (natDegree_lt_natDegree_iff hq0).mpr hd
        omega
      have hA' : ∀ t : ℝ,A (Multiplicative.ofAdd t)∈H.level (e+(k+1)) := by
        simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hA
      convert ih (k+1) hA' q hq using 1
      funext x
      change (A (Multiplicative.ofAdd (p.eval x)))⁻¹*A (Multiplicative.ofAdd (p.eval (x+t)))=
        A (Multiplicative.ofAdd (q.eval x))
      rw [← map_inv,← map_mul]
      congr 1
      apply Multiplicative.toAdd.injective
      simp [q,taylor_apply,eval_comp]
      ring
end CubePolynomials

namespace RationalLattice
open CubeFaces CubePolynomials MalcevCharacters
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G n)

omit [IsTopologicalGroup G] in
lemma prefix_zero_inv (g : G) (i : Fin n)
    (hz : ∀ j : Fin n,j < i → c.coord g j=0) :
    ∀ j : Fin n,j < i → c.coord g⁻¹ j=0 := by
  intro j hj
  have hh:=coord_mul_of_right_zero c g⁻¹ g j (fun l hl=>hz l (lt_trans hl hj))
  rw [inv_mul_cancel,c.one_coord,hz j hj,add_zero] at hh
  exact hh.symm

omit [IsTopologicalGroup G] in
lemma coord_inv_of_prefix_zero (g : G) (i : Fin n)
    (hz : ∀ j : Fin n,j < i → c.coord g j=0) : c.coord g⁻¹ i= -c.coord g i := by
  have hh:=coord_mul_of_right_zero c g⁻¹ g i hz
  rw [inv_mul_cancel,c.one_coord] at hh
  linarith

omit [IsTopologicalGroup G] in
lemma tail_coord_natDegree (H : Filtration G) (w : Fin n → ℕ)
    (hH : ∀ k (g : G),g∈H.level k ↔ ∀ i : Fin n,w i < k → c.coord g i=0)
    (i : Fin n) (d k : ℕ) (hdk : w i < k+d+1)
    (f : ℝ → G) (hf : f∈polynomials H k)
    (hz : ∀ t (j : Fin n),j < i → c.coord (f t) j=0)
    (p : ℝ[X]) (hp : ∀ t,p.eval t=c.coord (f t) i) : p.natDegree ≤ d := by
  induction d generalizing k f p with
  | zero =>
    have hw : w i < k+1 := by omega
    by_cases h : w i < k
    · have he : p=0 := by
        apply Polynomial.funext
        intro t
        rw [eval_zero,hp]
        exact (hH k (f t)).mp (eval_mem hf t) i h
      simp [he]
    · 
      have hq (t : ℝ) : taylor t p-p=0 := by
        apply Polynomial.funext
        intro x
        simp only [eval_sub,taylor_apply,eval_comp,eval_add,eval_X,eval_C,eval_zero,hp]
        have hh: c.coord ((f x)⁻¹*f (x+t)) i=0 :=
          (hH (k+1) _).mp (eval_mem (derivative_mem hf t) x) i hw
        rw [coord_mul_of_left_zero c _ _ i (prefix_zero_inv c _ i (hz x)),
          coord_inv_of_prefix_zero c _ i (hz x)] at hh
        linarith
      have he : p=C (p.eval 0) := by
        apply Polynomial.funext
        intro t
        have hh:=congrArg (fun q : ℝ[X]=>q.eval 0) (hq t)
        simp only [eval_sub,taylor_apply,eval_comp,eval_add,eval_X,eval_C,zero_add,eval_zero] at hh
        simpa only [eval_C] using sub_eq_zero.mp hh
      rw [he,natDegree_C]
  | succ d ih =>
    apply natDegree_le_of_taylor_sub
    intro t
    let f' : ℝ → G:=fun x=>(f x)⁻¹*f (x+t)
    have hf' : f'∈polynomials H (k+1) := derivative_mem hf t
    have hz' (x : ℝ) (j : Fin n) (hj : j < i) : c.coord (f' x) j=0 := by
      change c.coord ((f x)⁻¹*f (x+t)) j=0
      rw [coord_mul_of_left_zero c _ _ j (fun l hl=>prefix_zero_inv c _ i (hz x) l (lt_trans hl hj)),
        prefix_zero_inv c _ i (hz x) j hj,hz (x+t) j hj]
      simp
    apply ih (k+1) (by omega) f' hf' hz' (taylor t p-p)
    intro x
    simp only [eval_sub,taylor_apply,eval_comp,eval_add,eval_X,eval_C,hp,f']
    rw [coord_mul_of_left_zero c _ _ i (prefix_zero_inv c _ i (hz x)),
      coord_inv_of_prefix_zero c _ i (hz x)]
    ring

end RationalLattice
end
 
end

section
 

noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial
open scoped BigOperators
namespace RationalLattice
open CubeFaces CubePolynomials MalcevCharacters
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G n) (hsk : SecondKind c)

lemma prod_ofFn_suffix {M : Type*} [Monoid M] {n : ℕ} (f : Fin n → M) (k : ℕ) :
    (List.ofFn (fun i=>if k ≤ i.val then f i else 1)).prod=((List.ofFn f).drop k).prod := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k =>
      rw [List.ofFn_succ,List.ofFn_succ]
      simpa using ih (fun i=>f i.succ) k

def suffixCoords (x : Fin n → ℝ) (k : ℕ) (i : Fin n) : ℝ := if k ≤ i.val then x i else 0

lemma suffixCoords_zero (x : Fin n → ℝ) : suffixCoords x 0=x := by
  funext i
  simp [suffixCoords]

def suffixGroup (x : Fin n → ℝ) (k : ℕ) : G := c.coord.symm (suffixCoords x k)

include hsk in
omit [IsTopologicalGroup G] in
lemma suffixGroup_eq_prod (x : Fin n → ℝ) (k : ℕ) :
    suffixGroup c x k=((List.ofFn (fun i=>axis c i (x i))).drop k).prod := by
  rw [hsk.ordered (suffixGroup c x k)]
  simp only [suffixGroup,Homeomorph.apply_symm_apply,suffixCoords]
  have he (i : Fin n) : axis c i (if k ≤ i.val then x i else 0)=
      if k ≤ i.val then axis c i (x i) else 1 := by split_ifs  <;> simp
  simp only [he]
  exact prod_ofFn_suffix _ _

include hsk in
omit [IsTopologicalGroup G] in
lemma suffixGroup_succ (x : Fin n → ℝ) (k : ℕ) (hk : k < n) :
    suffixGroup c x k=axis c ⟨k,hk⟩ (x ⟨k,hk⟩)*suffixGroup c x (k+1) := by
  rw [suffixGroup_eq_prod c hsk x k,suffixGroup_eq_prod c hsk x (k+1),
    List.drop_eq_getElem_cons (by simpa using hk),List.prod_cons,List.getElem_ofFn]

include hsk in
omit [IsTopologicalGroup G] in
lemma axis_polynomial_mem (H : Filtration G) (w : Fin n → ℕ)
    (hH : ∀ k (g : G),g∈H.level k ↔ ∀ i : Fin n,w i  <  k → c.coord g i=0)
    (i : Fin n) (p : ℝ[X]) (hp : p.natDegree  ≤  w i) :
    (fun t : ℝ=>axis c i (p.eval t))∈polynomials H 0 := by
  let A : Multiplicative ℝ →* G :=
    { toFun := fun t=>axis c i t.toAdd
      map_one' := axis_zero c i
      map_mul' := fun t u=>hsk.axis_add i t.toAdd u.toAdd }
  exact real_polynomial_mem H A (w i) 0
    (by intro t; exact MalcevWeightedCoordinates.axis_mem_level c H w hH i t) p hp

include hsk in
omit [IsTopologicalGroup G] in
theorem coordinate_natDegree (H : Filtration G) (w : Fin n → ℕ)
    (hH : ∀ k (g : G),g∈H.level k ↔ ∀ i : Fin n,w i  <  k → c.coord g i=0)
    (f : ℝ → G) (hf : f∈polynomials H 0)
    (p : Fin n → ℝ[X]) (hp : ∀ t i,(p i).eval t=c.coord (f t) i) :
    ∀ i,(p i).natDegree  ≤  w i := by
  have hmem : ∀ k,(fun t : ℝ=>suffixGroup c (c.coord (f t)) k)∈polynomials H 0 := by
    intro k
    induction k with
    | zero => simpa only [suffixGroup,suffixCoords_zero,Homeomorph.symm_apply_apply] using hf
    | succ k ih =>
      by_cases hk : k < n
      · let i : Fin n:=⟨k,hk⟩
        have hd : (p i).natDegree  ≤  w i := by
          apply tail_coord_natDegree c H w hH i (w i) 0 (by omega)
            (fun t=>suffixGroup c (c.coord (f t)) k) ih
          · intro t j hj
            simp only [suffixGroup,Homeomorph.apply_symm_apply,suffixCoords]
            rw [ite_eq_right (by change j.val < k at hj; omega)]
          · intro t
            simpa only [suffixGroup,Homeomorph.apply_symm_apply,suffixCoords,i,le_refl,ite_true] using hp t i
        have ha:=axis_polynomial_mem c hsk H w hH i (p i) hd
        have hh: (fun t : ℝ=>suffixGroup c (c.coord (f t)) (k+1))=
            (fun t=>axis c i ((p i).eval t))⁻¹*(fun t=>suffixGroup c (c.coord (f t)) k) := by
          funext t
          change _=(axis c i ((p i).eval t))⁻¹*suffixGroup c (c.coord (f t)) k
          rw [suffixGroup_succ c hsk _ k hk,hp]
          simp [i]
        rw [hh]
        exact (polynomials H 0).mul_mem ((polynomials H 0).inv_mem ha) ih
      · have hh : (fun t : ℝ=>suffixGroup c (c.coord (f t)) (k+1))=1 := by
          funext t
          apply c.coord.injective
          funext j
          simp only [suffixGroup,Homeomorph.apply_symm_apply,suffixCoords,Pi.one_apply,c.one_coord]
          rw [ite_eq_right (by have:=j.isLt; omega)]
        rw [hh]
        exact (polynomials H 0).one_mem
  intro i
  apply tail_coord_natDegree c H w hH i (w i) 0 (by omega)
    (fun t=>suffixGroup c (c.coord (f t)) i.val) (hmem i.val)
  · intro t j hj
    simp only [suffixGroup,Homeomorph.apply_symm_apply,suffixCoords]
    rw [ite_eq_right (by change j.val < i.val at hj; omega)]
  · intro t
    simpa only [suffixGroup,Homeomorph.apply_symm_apply,suffixCoords,le_refl,ite_true] using hp t i

end RationalLattice

end
end
end

end OAI
