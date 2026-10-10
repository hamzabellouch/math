import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RationalLattice14
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
noncomputable section
open scoped BigOperators
end
 
end

section
 

 

noncomputable section
namespace RationalLattice.WeightedLawChart
open WeightedPolynomial
variable {K : Type*} [Group K] [TopologicalSpace K] {n : ℕ}
variable (e : K ≃ₜ (Fin n → ℝ)) (he : e 1=0)
variable (w : Fin n → ℕ) (hw : ∀ i,0<w i) (hmono : Monotone w)

def law (x : (Fin n ⊕ Fin n) → ℝ) : Fin n → ℝ :=
  e (e.symm (fun j=>x (Sum.inl j))*e.symm (fun j=>x (Sum.inr j)))
def difference (x : (Fin n ⊕ Fin n) → ℝ) (i : Fin n) : ℝ:=
  law e x i-x (Sum.inl i)-x (Sum.inr i)

include he in
lemma difference_left (y : Fin n → ℝ) (i : Fin n) :
    difference e (Sum.elim (fun _=>0) y) i=0 := by
  have h0 : e.symm 0=1:=e.symm_apply_eq.mpr he.symm
  change e (e.symm 0*e.symm y) i-0-y i=0
  simp [h0]
include he in
lemma difference_right (x : Fin n → ℝ) (i : Fin n) :
    difference e (Sum.elim x (fun _=>0)) i=0 := by
  have h0 : e.symm 0=1:=e.symm_apply_eq.mpr he.symm
  change e (e.symm x*e.symm 0) i-x i-0=0
  simp [h0]

def extend (i : Fin n) (z : (Fin i.val ⊕ Fin i.val) → ℝ) :
    (Fin n ⊕ Fin n) → ℝ:=Sum.elim
      (fun j=>if h : j.val < i.val then z (Sum.inl ⟨j.val,h⟩) else 0)
      (fun j=>if h : j.val < i.val then z (Sum.inr ⟨j.val,h⟩) else 0)

def restrict (i : Fin n) (z : (Fin n ⊕ Fin n) → ℝ) :
    (Fin i.val ⊕ Fin i.val) → ℝ:=Sum.elim
      (fun j=>z (Sum.inl ⟨j.val,lt_trans j.isLt i.isLt⟩))
      (fun j=>z (Sum.inr ⟨j.val,lt_trans j.isLt i.isLt⟩))

lemma extend_polynomial (i : Fin n) (j : Fin n ⊕ Fin n) :
    RationalPolynomialMap.IsPolynomial (fun x=>extend i x j) := by
  cases j with
  | inl j =>
    by_cases h : j.val < i.val
    · simp only [extend,Sum.elim_inl,dite_eq_left h]
      exact RationalPolynomialMap.coordinate _
    · simp only [extend,Sum.elim_inl,dite_eq_right h]
      simpa only [Rat.cast_zero] using RationalPolynomialMap.const 0
  | inr j =>
    by_cases h : j.val < i.val
    · simp only [extend,Sum.elim_inr,dite_eq_left h]
      exact RationalPolynomialMap.coordinate _
    · simp only [extend,Sum.elim_inr,dite_eq_right h]
      simpa only [Rat.cast_zero] using RationalPolynomialMap.const 0

variable (hpoly : ∀ i,RationalPolynomialMap.IsPolynomial (fun x=>law e x i))
variable (hweight : ∀ i,IsWeighted (Sum.elim w w) (w i) (fun x=>law e x i))

include hpoly in
lemma difference_polynomial (i : Fin n) :
    RationalPolynomialMap.IsPolynomial (fun x=>difference e x i) :=
  RationalPolynomialMap.sub (RationalPolynomialMap.sub (hpoly i)
    (RationalPolynomialMap.coordinate _)) (RationalPolynomialMap.coordinate _)

include he hw hmono hweight in
lemma difference_restrict (i : Fin n) (x : (Fin n ⊕ Fin n) → ℝ) :
    difference e x i=difference e (extend i (restrict i x)) i := by
  have hh:=((hweight i).sub (IsWeighted.coordinate (Sum.elim w w) (Sum.inl i))).sub
    (IsWeighted.coordinate (Sum.elim w w) (Sum.inr i))
  obtain ⟨p,hp,hpval⟩:=hh
  change ∀ x,difference e x i=MvPolynomial.eval x p at hpval
  rw [hpval,hpval]
  apply mixed_eval_congr hw hw p hp
  · intro y
    rw [← hpval,difference_left e he]
  · intro y
    rw [← hpval,difference_right e he]
  · intro j hj
    cases j with
    | inl j =>
      have hij : j.val < i.val := by
        by_contra h
        have hh:=hmono (show i≤j by omega)
        change w j<w i at hj
        omega
      simp only [extend,Sum.elim_inl,Sum.elim_inr,dite_eq_left hij,restrict]
    | inr j =>
      have hij : j.val < i.val := by
        by_contra h
        have hh:=hmono (show i≤j by omega)
        change w j<w i at hj
        omega
      simp only [extend,Sum.elim_inl,Sum.elim_inr,dite_eq_left hij,restrict]

include hpoly in
lemma exists_correction (i : Fin n) :
    ∃ P : MvPolynomial (Fin i.val ⊕ Fin i.val) ℚ,
      ∀ x,difference e (extend i x) i=MvPolynomial.eval₂ (algebraMap ℚ ℝ) x P :=
  RationalPolynomialMap.comp (difference_polynomial e hpoly i) (extend_polynomial i)

 

def realCoordinates : RealCoordinates K n where
  coord:=e
  one_coord i:=congrFun he i
  correction i:=(exists_correction e hpoly i).choose
  mul_coord g h i:=by
    let x:=(Sum.elim (e g) (e h))
    have hh:=difference_restrict e he w hw hmono hweight i x
    rw [(exists_correction e hpoly i).choose_spec] at hh
    have ha : difference e x i=e (g*h) i-e g i-e h i := by simp [difference,law,x]
    rw [ha] at hh
    change e (g*h) i=e g i+e h i+MvPolynomial.eval₂ _ (restrict i x) _
    linarith

end RationalLattice.WeightedLawChart
end
 
end

section
 

 

noncomputable section
open scoped BigOperators
namespace RationalLattice.PolynomialArrays
open WeightedPolynomial MalcevCharacters
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n q : ℕ} (c : RealCoordinates G n) (hsk : SecondKind c)
variable (A : CubeFaces.Filtration G) (w : Fin n → ℕ)
variable (hA : ∀ k (g : G),g∈A.level k ↔ ∀ i : Fin n,w i<k → c.coord g i=0)

def IsArray (f : (Fin q → ℝ) → G) : Prop :=
  ∀ i,IsWeighted (fun _ : Fin q=>1) (w i) (fun u=>canonicalLog c (f u) i)

omit [IsTopologicalGroup G] in
lemma one_array : IsArray c w (fun _ : Fin q → ℝ=>(1:G)) := by
  intro i
  simpa only [canonicalLog_one,Pi.zero_apply] using IsWeighted.const (fun _ : Fin q=>1) (w i) 0

include hsk hA in
lemma mul_array {f g : (Fin q → ℝ) → G} (hf : IsArray c w f) (hg : IsArray c w g) :
    IsArray c w (fun u=>f u*g u) := by
  intro i
  have hs (j : Fin n ⊕ Fin n) :
      IsWeighted (fun _ : Fin q=>1) (Sum.elim w w j)
        (fun u=>Sum.elim (canonicalLog c (f u)) (canonicalLog c (g u)) j) := by
    cases j with
    | inl j=>exact hf j
    | inr j=>exact hg j
  have hh:=(log_multiplication_weighted c hsk A w hA i).comp hs
  simpa only [Sum.elim_inl,Sum.elim_inr,canonicalExp_log] using hh

omit [IsTopologicalGroup G] in
lemma log_inv (g : G) : canonicalLog c g⁻¹= -canonicalLog c g := by
  have hh:=canonicalLog_realPower c g (-1)
  rw [show (-1:ℝ)=((-1:ℤ):ℝ) by simp,realPower_int] at hh
  simpa using hh

omit [IsTopologicalGroup G] in
lemma inv_array {f : (Fin q → ℝ) → G} (hf : IsArray c w f) :
    IsArray c w (fun u=>(f u)⁻¹) := by
  intro i
  have hh:=(hf i).smul (-1)
  simpa only [log_inv,Pi.neg_apply,neg_one_mul] using hh

 

def group : Subgroup ((Fin q → ℝ) → G) where
  carrier:=IsArray c w
  one_mem':=one_array c w
  mul_mem':=mul_array c hsk A w hA
  inv_mem':=inv_array c w

omit [IsTopologicalGroup G] in
lemma constant (g : G) : IsArray c w (fun _ : Fin q → ℝ=>g) :=
  fun _=>IsWeighted.const _ _ _

lemma affine_weighted (b : ℝ) (v : Fin q → ℝ) :
    IsWeighted (fun _ : Fin q=>1) 1 (fun u=>b+∑ j,v j*u j) :=
  (IsWeighted.const _ _ b).add (IsWeighted.sum Finset.univ (fun j _=>
    (IsWeighted.coordinate (fun _ : Fin q=>1) j).smul (v j)))

variable (hw : ∀ i,0<w i)
include hw in
omit [IsTopologicalGroup G] in
lemma power_affine (g : G) (b : ℝ) (v : Fin q → ℝ) :
    IsArray c w (fun u=>realPower c g (b+∑ j,v j*u j)) := by
  intro i
  have hh:=((affine_weighted b v).mono (hw i)).smul (canonicalLog c g i)
  simpa only [canonicalLog_realPower,Pi.smul_apply,smul_eq_mul,mul_comm] using hh

include hsk hA hw in
 

lemma source_array (g x : G) (b : ℝ) (v : Fin q → ℝ) :
    IsArray c w (fun u=>realPower c g (b+∑ j,v j*u j)*x) :=
  mul_array c hsk A w hA (power_affine c w hw g b v) (constant c w x)

omit [IsTopologicalGroup G] in
lemma translate_array {f : (Fin q → ℝ) → G} (hf : IsArray c w f) (v : Fin q → ℝ) :
    IsArray c w (fun u=>f (u+v)) := by
  intro i
  exact (hf i).comp (fun j=>(IsWeighted.coordinate (fun _ : Fin q=>1) j).add
    (IsWeighted.const _ _ (v j)))

 
def shift (v : Fin q → ℝ) : group (q:=q) c hsk A w hA ≃* group (q:=q) c hsk A w hA where
  toFun f:=⟨fun u=>f.val (u+v),translate_array c w f.property v⟩
  invFun f:=⟨fun u=>f.val (u-v),by
    change IsArray c w (fun u=>f.val (u-v))
    have hh:=translate_array c w f.property (-v)
    simpa only [sub_eq_add_neg] using hh⟩
  left_inv f:=by apply Subtype.ext; funext u; simp
  right_inv f:=by apply Subtype.ext; funext u; simp
  map_mul' f g:=rfl

lemma shift_continuous (v : Fin q → ℝ) : Continuous (shift c hsk A w hA v) := by
  apply Continuous.subtype_mk
  exact continuous_pi (fun u=>(continuous_apply (u+v)).comp continuous_subtype_val)

 
def lattice (Γ : Subgroup G) : Subgroup (group (q:=q) c hsk A w hA) where
  carrier:=fun f=>∀ z : Fin q → ℤ,f.val (fun j=>(z j:ℝ))∈Γ
  one_mem':=fun _=>Γ.one_mem
  mul_mem':=fun hf hg z=>Γ.mul_mem (hf z) (hg z)
  inv_mem':=fun hf z=>Γ.inv_mem (hf z)

lemma shift_lattice (Γ : Subgroup G) (v : Fin q → ℤ) (f : group (q:=q) c hsk A w hA) :
    shift c hsk A w hA (fun j=>(v j:ℝ)) f∈lattice c hsk A w hA Γ ↔
      f∈lattice c hsk A w hA Γ := by
  constructor
  · intro hf z
    have hh:=hf (z-v)
    change f.val (fun j=>((z-v) j:ℝ)+(v j:ℝ))∈Γ at hh
    simpa only [Pi.sub_apply,Int.cast_sub,Pi.add_apply,sub_add_cancel] using hh
  · intro hf z
    have hh:=hf (z+v)
    change f.val (fun j=>(z j:ℝ)+(v j:ℝ))∈Γ
    simpa only [Pi.add_apply,Int.cast_add] using hh

end RationalLattice.PolynomialArrays
end
 

end
end

end OAI
