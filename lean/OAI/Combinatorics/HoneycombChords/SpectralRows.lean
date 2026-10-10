import OAI.Combinatorics.HoneycombChords.Reflection
import OAI.Combinatorics.HoneycombChords.RowExchange

namespace OAI

/-!
# Spectral monodromy rows and boundary exchange identities

Formalized from *Uniform marked polygon estimates and sharp finite bridge moments*
(OpenAI, September 26, 2026).
-/

section
namespace CriticalHoneycomb.Transfer.RowExchange
open Reflection Reflection.Fusion
open scoped Matrix BigOperators
lemma local_source_fusion (u : ℝ) (hm : Q (u-L)≠0) (hu : Q u≠0) (hp : Q (u+L)≠0)
    (s t : Spin) : localBackward (spectralR (u+L)) (spectralR (u-L)) s t*sourceW=
      sourceW*block (spectralR u) s t := by
  ext ⟨a,b⟩ j
  simp only [Matrix.mul_apply,Fintype.sum_prod_type,localBackward,Matrix.kronecker,Matrix.kroneckerMap,block,Matrix.sum_apply,Matrix.of_apply,Finset.sum_mul]
  have hh:=source_bulk_fusion u hm hu hp a b s j t
  unfold fusionProduct fusionLift at hh
  convert hh using 1
  apply Finset.sum_congr rfl;intro x hx
  apply Finset.sum_congr rfl;intro y hy
  apply Finset.sum_congr rfl;intro z hz
  ring
lemma local_source_quotient_fusion (u : ℝ) (hm : Q (u-L)≠0) (hu : Q u≠0) (hp : Q (u+L)≠0)
    (s t : Spin) : sourceWbarᵀ*localForward (spectralR (u+L)) (spectralR (u-L)) s t=
      block (spectralR u) s t*sourceWbarᵀ := by
  have hh:=congrArg Matrix.conjTranspose (local_source_fusion u hm hu hp t s)
  simpa only [Matrix.conjTranspose_mul,sourceW_conjTranspose,
    localBackward_conjTranspose _ _ (spectralR_hermitian _) (spectralR_hermitian _),
    block_conjTranspose _ (spectralR_hermitian _)] using hh
noncomputable def exactSites (n : ℕ) (ξ : Fin n→ℝ) (u : ℝ) : Fin n→Local :=
  fun i=>spectralR (u+ξ i)

theorem source_row_fusion (n : ℕ) (ξ : Fin n→ℝ) (u : ℝ)
    (hm : ∀ i,Q ((u-L)+ξ i)≠0) (hu : ∀ i,Q (u+ξ i)≠0)
    (hp : ∀ i,Q ((u+L)+ξ i)≠0) (s t : Space n) :
    backward n (exactSites n ξ (u+L)) (exactSites n ξ (u-L)) s t*sourceW=
      sourceW*row n (exactSites n ξ u) s t := by
  apply row_fusion
  intro i a b
  have em : (u+ξ i)-L=(u-L)+ξ i := by ring
  have ep : (u+ξ i)+L=(u+L)+ξ i := by ring
  simpa only [exactSites,em,ep] using local_source_fusion (u+ξ i)
    (by simpa only [em] using hm i) (hu i) (by simpa only [ep] using hp i) a b

theorem source_row_quotient_fusion (n : ℕ) (ξ : Fin n→ℝ) (u : ℝ)
    (hm : ∀ i,Q ((u-L)+ξ i)≠0) (hu : ∀ i,Q (u+ξ i)≠0)
    (hp : ∀ i,Q ((u+L)+ξ i)≠0) (s t : Space n) :
    sourceWbarᵀ*forward n (exactSites n ξ (u+L)) (exactSites n ξ (u-L)) s t=
      row n (exactSites n ξ u) s t*sourceWbarᵀ := by
  apply row_quotient_fusion
  intro i a b
  have em : (u+ξ i)-L=(u-L)+ξ i := by ring
  have ep : (u+ξ i)+L=(u+L)+ξ i := by ring
  simpa only [exactSites,em,ep] using local_source_quotient_fusion (u+ξ i)
    (by simpa only [em] using hm i) (hu i) (by simpa only [ep] using hp i) a b
end CriticalHoneycomb.Transfer.RowExchange

end

section
namespace CriticalHoneycomb.Transfer.Reflection
open Fusion
open scoped Matrix
lemma reflected_Q (u : ℝ) : Q (b-u)=Q u := by
  have e1 : Real.pi/4+(b-u)=Real.pi-(b+u) := by unfold b;ring
  have e2 : b+(b-u)=Real.pi-(Real.pi/4+u) := by unfold b;ring
  simp [Q,sine,e1,e2,Real.sin_pi_sub,mul_comm]
lemma reflected_A (u : ℝ) : coeffA (b-u)=coeffH u := by
  simp [coeffA,coeffH]
lemma reflected_H (u : ℝ) : coeffH (b-u)=coeffA u := rfl
lemma reflected_V (u : ℝ) : coeffV (b-u)=coeffV u := by
  simp [coeffV,mul_comm]
lemma reflected_C (u : ℝ) : coeffC (b-u)=coeffD u := by
  have ee : Real.pi/4-(b-u)=u-L := by unfold b L;ring
  simp [coeffC,coeffD,ee]
lemma reflected_D (u : ℝ) : coeffD (b-u)=coeffC u := by
  have ee : (b-u)-L=Real.pi/4-u := by unfold b L;ring
  simp [coeffC,coeffD,ee]
def spinValue (a : Fin 3) : ℤ := 1-(a.val:ℤ)
lemma spinValue_rev (a : Fin 3) : spinValue a.rev = -spinValue a := by
  fin_cases a <;> norm_num [spinValue]
private lemma crossingCrossingComponent00 (u : ℝ) (c d : Fin 3) :
    spectralR (b-u) (0,0) (c,d)=
      phase^(spinValue c-spinValue 0)*spectralR u ((0:Fin 3).rev,d) (c.rev,0) := by
  fin_cases c <;> fin_cases d <;>
    simp [spectralR,bulkNumerator,reflected_Q,reflected_C,spinValue,Fin.rev]

private lemma crossingCrossingComponent01 (u : ℝ) (c d : Fin 3) :
    spectralR (b-u) (0,1) (c,d)=
      phase^(spinValue c-spinValue 0)*spectralR u ((0:Fin 3).rev,d) (c.rev,1) := by
  fin_cases c <;> fin_cases d <;>
    simp [spectralR,bulkNumerator,reflected_Q,reflected_A,reflected_V,spinValue,Fin.rev]
  all_goals { have hn : phase ≠ 0 := point_ne_zero _
              field_simp [hn]  }
private lemma crossingCrossingComponent02 (u : ℝ) (c d : Fin 3) :
    spectralR (b-u) (0,2) (c,d)=
      phase^(spinValue c-spinValue 0)*spectralR u ((0:Fin 3).rev,d) (c.rev,2) := by
  fin_cases c <;> fin_cases d <;>
    simp [spectralR,bulkNumerator,reflected_Q,reflected_H,
      reflected_C,reflected_D,spinValue,Fin.rev,
      div_eq_mul_inv]
  all_goals { have hn : phase ≠ 0 := point_ne_zero _
              field_simp [hn] <;> ring }
private lemma crossingCrossingComponent10 (u : ℝ) (c d : Fin 3) :
    spectralR (b-u) (1,0) (c,d)=
      phase^(spinValue c-spinValue 1)*spectralR u ((1:Fin 3).rev,d) (c.rev,0) := by
  fin_cases c <;> fin_cases d <;>
    simp [spectralR,bulkNumerator,reflected_Q,reflected_A,reflected_V,spinValue,Fin.rev,
      div_eq_mul_inv]
  all_goals { have hn : phase ≠ 0 := point_ne_zero _
              field_simp [hn]  }
private lemma crossingCrossingComponent11 (u : ℝ) (c d : Fin 3) :
    spectralR (b-u) (1,1) (c,d)=
      phase^(spinValue c-spinValue 1)*spectralR u ((1:Fin 3).rev,d) (c.rev,1) := by
  fin_cases c <;> fin_cases d <;>
    simp [spectralR,bulkNumerator,reflected_Q,reflected_H,
      spinValue,Fin.rev,
      div_eq_mul_inv]
  all_goals { have hn : phase ≠ 0 := point_ne_zero _
              field_simp [hn]  }
private lemma crossingCrossingComponent12 (u : ℝ) (c d : Fin 3) :
    spectralR (b-u) (1,2) (c,d)=
      phase^(spinValue c-spinValue 1)*spectralR u ((1:Fin 3).rev,d) (c.rev,2) := by
  fin_cases c <;> fin_cases d <;>
    simp [spectralR,bulkNumerator,reflected_Q,reflected_A,reflected_V,spinValue,Fin.rev]
  all_goals { have hn : phase ≠ 0 := point_ne_zero _
              field_simp [hn]  }
private lemma crossingCrossingComponent20 (u : ℝ) (c d : Fin 3) :
    spectralR (b-u) (2,0) (c,d)=
      phase^(spinValue c-spinValue 2)*spectralR u ((2:Fin 3).rev,d) (c.rev,0) := by
  fin_cases c <;> fin_cases d <;>
    simp [spectralR,bulkNumerator,reflected_Q,reflected_H,
      reflected_C,reflected_D,spinValue,Fin.rev,
      div_eq_mul_inv]
  all_goals { have hn : phase ≠ 0 := point_ne_zero _
              field_simp [hn] <;> ring }
private lemma crossingCrossingComponent21 (u : ℝ) (c d : Fin 3) :
    spectralR (b-u) (2,1) (c,d)=
      phase^(spinValue c-spinValue 2)*spectralR u ((2:Fin 3).rev,d) (c.rev,1) := by
  fin_cases c <;> fin_cases d <;>
    simp [spectralR,bulkNumerator,reflected_Q,reflected_A,reflected_V,spinValue,Fin.rev,
      div_eq_mul_inv]
  all_goals { have hn : phase ≠ 0 := point_ne_zero _
              field_simp [hn]  }
private lemma crossingCrossingComponent22 (u : ℝ) (c d : Fin 3) :
    spectralR (b-u) (2,2) (c,d)=
      phase^(spinValue c-spinValue 2)*spectralR u ((2:Fin 3).rev,d) (c.rev,2) := by
  fin_cases c <;> fin_cases d <;>
    simp [spectralR,bulkNumerator,reflected_Q,reflected_C,spinValue,Fin.rev]


theorem source_crossing (u : ℝ) (i j k l : Fin 3) :
    spectralR (b-u) (i,j) (k,l)=
      phase^(spinValue k-spinValue i)*spectralR u (i.rev,l) (k.rev,j) := by
  fin_cases i <;> fin_cases j
  · exact crossingCrossingComponent00 u k l
  · exact crossingCrossingComponent01 u k l
  · exact crossingCrossingComponent02 u k l
  · exact crossingCrossingComponent10 u k l
  · exact crossingCrossingComponent11 u k l
  · exact crossingCrossingComponent12 u k l
  · exact crossingCrossingComponent20 u k l
  · exact crossingCrossingComponent21 u k l
  · exact crossingCrossingComponent22 u k l
end CriticalHoneycomb.Transfer.Reflection

end

section
namespace CriticalHoneycomb.BoundaryJet
open TrivSqZeroExt
abbrev Jet := DualNumber (DualNumber ℂ)
noncomputable def C : ℂ →+* Jet := (inlHom (R := DualNumber ℂ) (M := DualNumber ℂ)).comp (inlHom (R := ℂ) (M := ℂ))
noncomputable def eL : Jet := inr 1
noncomputable def eR : Jet := inl (inr 1)
noncomputable def base (a : Jet) : ℂ := a.fst.fst
noncomputable def left (a : Jet) : ℂ := a.snd.fst
noncomputable def right (a : Jet) : ℂ := a.fst.snd
noncomputable def both (a : Jet) : ℂ := a.snd.snd
lemma jet_ext (a b : Jet) (h₀ : base a=base b) (h₁ : left a=left b)
    (h₂ : right a=right b) (h₃ : both a=both b) : a=b := by
  apply TrivSqZeroExt.ext
  · exact TrivSqZeroExt.ext h₀ h₂
  · exact TrivSqZeroExt.ext h₁ h₃
@[simp] lemma base_mul (a b : Jet) : base (a*b)=base a*base b := rfl
@[simp] lemma left_mul (a b : Jet) : left (a*b)=base a*left b+left a*base b := by
  simp [left,base,smul_eq_mul]
@[simp] lemma right_mul (a b : Jet) : right (a*b)=base a*right b+right a*base b := by
  simp [right,base,smul_eq_mul]
@[simp] lemma both_mul (a b : Jet) : both (a*b)=base a*both b+left a*right b+
    right a*left b+both a*base b := by
  simp [both,base,left,right,smul_eq_mul]
  ring
@[simp] lemma base_add (a b : Jet) : base (a+b)=base a+base b := rfl
@[simp] lemma left_add (a b : Jet) : left (a+b)=left a+left b := rfl
@[simp] lemma right_add (a b : Jet) : right (a+b)=right a+right b := rfl
@[simp] lemma both_add (a b : Jet) : both (a+b)=both a+both b := rfl
@[simp] lemma base_C (a : ℂ) : base (C a)=a := rfl
@[simp] lemma left_C (a : ℂ) : left (C a)=0 := rfl
@[simp] lemma right_C (a : ℂ) : right (C a)=0 := rfl
@[simp] lemma both_C (a : ℂ) : both (C a)=0 := rfl
@[simp] lemma eL_sq : eL^2=0 := by simp [eL,pow_two]
@[simp] lemma eR_sq : eR^2=0 := by
  apply jet_ext <;> simp [eR,pow_two,base,left,right,both,smul_eq_mul]
noncomputable def form (a b c d : ℂ) : Jet := C a+eL*C b+eR*C c+eL*eR*C d
@[simp] lemma base_form (a b c d : ℂ) : base (form a b c d)=a := by simp [form,base,eL,eR,C]
@[simp] lemma left_form (a b c d : ℂ) : left (form a b c d)=b := by simp [form,left,eL,eR,C,smul_eq_mul]
@[simp] lemma right_form (a b c d : ℂ) : right (form a b c d)=c := by simp [form,right,eL,eR,C,smul_eq_mul]
@[simp] lemma both_form (a b c d : ℂ) : both (form a b c d)=d := by simp [form,both,eL,eR,C,smul_eq_mul]
lemma form_coords (a : Jet) : form (base a) (left a) (right a) (both a)=a := by
  apply jet_ext <;> simp
noncomputable def baseAdd : Jet →+ ℂ := {toFun := base, map_zero' := rfl, map_add' := base_add}
noncomputable def leftAdd : Jet →+ ℂ := {toFun := left, map_zero' := rfl, map_add' := left_add}
noncomputable def rightAdd : Jet →+ ℂ := {toFun := right, map_zero' := rfl, map_add' := right_add}
noncomputable def bothAdd : Jet →+ ℂ := {toFun := both, map_zero' := rfl, map_add' := both_add}
lemma base_sum {ι : Type*} (s : Finset ι) (f : ι→Jet) : base (∑ i∈s,f i)=∑ i∈s,base (f i) :=
  map_sum baseAdd f s
lemma left_sum {ι : Type*} (s : Finset ι) (f : ι→Jet) : left (∑ i∈s,f i)=∑ i∈s,left (f i) :=
  map_sum leftAdd f s
lemma right_sum {ι : Type*} (s : Finset ι) (f : ι→Jet) : right (∑ i∈s,f i)=∑ i∈s,right (f i) :=
  map_sum rightAdd f s
lemma both_sum {ι : Type*} (s : Finset ι) (f : ι→Jet) : both (∑ i∈s,f i)=∑ i∈s,both (f i) :=
  map_sum bothAdd f s
end CriticalHoneycomb.BoundaryJet

end

section

namespace CriticalHoneycomb.Transfer.SpectralFamily
open Reflection RowExchange BoundaryJet
open scoped Matrix BigOperators
noncomputable def K0 (t : ℝ) (p : Pair) : ℂ :=
  phase^(spinValue p.2.rev)*boundary0 t p.1 p.2.rev
noncomputable def K1 (t : ℝ) (p : Pair) : ℂ :=
  phase^(spinValue p.2.rev)*boundary1 t p.1 p.2.rev

noncomputable def K (e : Jet) (t : ℝ) (p : Pair) : Jet := C (K0 t p)+e*C (K1 t p)
noncomputable def bulkRows (N : ℕ) (ξ : Fin N→ℝ) (u : ℝ)
    (s t : Space N) : Matrix Pair Pair ℂ :=
  forward N (exactSites N ξ u) (exactSites N ξ (b-u)) s t

noncomputable def T (N : ℕ) (ξ : Fin N→ℝ) (u : ℝ) :
    Matrix (Space N) (Space N) Jet := fun s t=>
  ∑ p : Pair,∑ q : Pair,K eL (b-u) p*C (bulkRows N ξ u s t p q)*K eR u q
noncomputable def coefficient (N : ℕ) (ξ : Fin N→ℝ) (u : ℝ) (i j : Bool) :
    Matrix (Space N) (Space N) ℂ := fun s t=>
  ∑ p : Pair,∑ q : Pair,(if i then K1 (b-u) p else K0 (b-u) p)*
    bulkRows N ξ u s t p q*(if j then K1 u q else K0 u q)
lemma K_left (u : ℝ) (p : Pair) : K eL u p=form (K0 u p) (K1 u p) 0 0 := by
  apply jet_ext <;> simp [K,form,base,left,right,both,C,eL,eR,smul_eq_mul]
lemma K_right (u : ℝ) (p : Pair) : K eR u p=form (K0 u p) 0 (K1 u p) 0 := by
  apply jet_ext <;> simp [K,form,base,left,right,both,C,eL,eR,smul_eq_mul]

theorem T_coefficients (N : ℕ) (ξ : Fin N→ℝ) (u : ℝ) (s t : Space N) :
    T N ξ u s t=form (coefficient N ξ u false false s t)
      (coefficient N ξ u true false s t) (coefficient N ξ u false true s t)
      (coefficient N ξ u true true s t) := by
  apply jet_ext <;>
    simp [T,coefficient,base_sum,left_sum,right_sum,both_sum,K_left,K_right,
      base_mul,left_mul,right_mul,both_mul]

def Nonsingular (N : ℕ) (ξ : Fin N→ℝ) (u : ℝ) : Prop :=
  sine (gamma+u)≠0 ∧ sine (gamma+(b-u))≠0 ∧
    ∀ i, Q (u+ξ i)≠0 ∧ Q ((b-u)+ξ i)≠0

def GlobalSpectralCommutation : Prop :=
  ∀ N (ξ : Fin N→ℝ) (u v : ℝ), Nonsingular N ξ u→Nonsingular N ξ v→
    Commute (T N ξ u) (T N ξ v)

def GlobalSpectralFusion : Prop :=
  ∀ N (ξ : Fin N→ℝ) (i : Fin N) (u : ℝ),
    (u=L-ξ i ∨ u=L+ξ i)→Nonsingular N ξ (u-L)→
    Nonsingular N ξ (u+L)→Nonsingular N ξ u→
      T N ξ (u-L)*T N ξ (u+L)=T N ξ u
end CriticalHoneycomb.Transfer.SpectralFamily

end

section
namespace CriticalHoneycomb.Transfer.Reflection
open scoped Matrix BigOperators
lemma point_reflected_mul (t : ℝ) : point t*point (b-t)-root^6=0 := by
  rw [←point_add,add_sub_cancel,root_pow]

  unfold b
  ring_nf
lemma alphaMinus_C_poly (t y : ℝ) (h : Q (t-y)≠0) :
    alphaMinus t y*(coeffC (t-y)/Q (t-y)) =
      (root^6*(point y)^2+root^10*(point t)^2)*
      (root^4*(point y)^2+root^12*(point t)^2) := by
  have hh:=congrFun (congrFun (rminus_scaled t y h) (0,0)) (0,0)
  simpa [spectralR,bulkNumerator,rNumerator,smul_eq_mul,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using hh
lemma alphaMinus_H_poly (t y : ℝ) (h : Q (t-y)≠0) :
    alphaMinus t y*(coeffH (t-y)/Q (t-y)) =
      (root^4+root^12)*point t*point y*((point t)^2-(point y)^2) := by
  have hh:=congrFun (congrFun (rminus_scaled t y h) (0,2)) (1,1)
  simp only [Matrix.smul_apply,smul_eq_mul,spectralR,bulkNumerator,rNumerator,
    Fin.val_zero,Fin.val_one,show (2:Fin 3).val=2 from rfl] at hh
  rw [div_eq_mul_inv,phase_inv] at hh
  have hn : -root^12≠0 := neg_ne_zero.mpr (pow_ne_zero _ root_ne_zero)
  apply mul_right_cancel₀ hn
  linear_combination hh
lemma alphaMinus_V_poly (t y : ℝ) (h : Q (t-y)≠0) :
    alphaMinus t y*(coeffV (t-y)/Q (t-y)) =
      (root^6*(point y)^2+root^10*(point t)^2)*((point t)^2-(point y)^2) := by
  have hh:=congrFun (congrFun (rminus_scaled t y h) (0,1)) (0,1)
  simpa [spectralR,bulkNumerator,rNumerator,smul_eq_mul,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using hh
lemma alphaMinus_A_poly (t y : ℝ) (h : Q (t-y)≠0) :
    alphaMinus t y*(coeffA (t-y)/Q (t-y)) =
      (root^4+root^12)*point t*point y*(root^6*(point y)^2+root^10*(point t)^2) := by
  have hh:=congrFun (congrFun (rminus_scaled t y h) (0,1)) (1,0)
  simpa [spectralR,bulkNumerator,rNumerator,smul_eq_mul,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using hh
lemma alphaMinus_poly (t y : ℝ) (h : Q (t-y)≠0) :
    alphaMinus t y=(root^4*(point t)^2+root^12*(point y)^2)*
      (root^6*(point t)^2+root^10*(point y)^2) := by
  have hh:=congrFun (congrFun (rminus_scaled t y h) (1,1)) (1,1)
  simpa [spectralR,bulkNumerator,rNumerator,smul_eq_mul,h] using hh
lemma source_swap_constant_scalar (t : ℝ) (h : Q (t-(b-t))≠0)
    (ht : sine (gamma+t)≠0) (hy : sine (gamma+(b-t))≠0) :
    (coeffC (t-(b-t))/Q (t-(b-t)))*(sine (gamma-t)/sine (gamma+t))+
      coeffH (t-(b-t))/Q (t-(b-t)) = sine (gamma-(b-t))/sine (gamma+(b-t)) := by
  have hh:=swap_constant_algebra root (point t) (point (b-t)) root_constraint (point_reflected_mul t)
  rw [←alphaMinus_C_poly t (b-t) h,←alphaMinus_H_poly t (b-t) h,
    ←alphaMinus_poly t (b-t) h,←beta_k t ht,←beta_k (b-t) hy,
    ←beta_polynomial t,←beta_polynomial (b-t)] at hh
  apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero
    (alphaMinus_ne_zero t (b-t) h) (beta_ne_zero t ht)) (beta_ne_zero (b-t) hy))
  linear_combination hh
lemma source_swap_linear_scalar (t : ℝ) (h : Q (t-(b-t))≠0)
    (ht : sine (gamma+t)≠0) (hy : sine (gamma+(b-t))≠0) :
    ((coeffV (t-(b-t))/Q (t-(b-t)))+(coeffA (t-(b-t))/Q (t-(b-t))))*
      (sine (2*t)/sine (gamma+t)) = sine (2*(b-t))/sine (gamma+(b-t)) := by
  have hh:=swap_linear_algebra root (point t) (point (b-t)) root_constraint (point_reflected_mul t)
  rw [←alphaMinus_V_poly t (b-t) h,←alphaMinus_A_poly t (b-t) h,
    ←alphaMinus_poly t (b-t) h,←beta_l t ht,←beta_l (b-t) hy,
    ←beta_polynomial t,←beta_polynomial (b-t)] at hh
  apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero
    (alphaMinus_ne_zero t (b-t) h) (beta_ne_zero t ht)) (beta_ne_zero (b-t) hy))
  linear_combination hh
end CriticalHoneycomb.Transfer.Reflection

end

section
namespace CriticalHoneycomb.Transfer.SpectralFamily
open Reflection BoundaryJet
open scoped Matrix BigOperators
private lemma boundarySwapPhaseFourRelation : phase^4+1=0 := by
  rw [phase_eq,←pow_mul]
  exact root_constraint
lemma source_K0_swap (t : ℝ) (h : Q (t-(b-t))≠0)
    (ht : sine (gamma+t)≠0) (hy : sine (gamma+(b-t))≠0) :
    spectralR (t-(b-t)) *ᵥ K0 t = fun p => K0 (b-t) (p.2,p.1) := by
  have hc:=source_swap_constant_scalar t h ht hy
  have hp:=boundarySwapPhaseFourRelation
  have hn : phase≠0 := point_ne_zero _
  funext ⟨a,b'⟩
  fin_cases a <;> fin_cases b' <;>
    simp [Matrix.mulVec,dotProduct,Fintype.sum_prod_type,Fin.sum_univ_three,
      spectralR,bulkNumerator,K0,boundary0,spinValue,Fin.rev]
  all_goals field_simp [h,ht,hy,hn] at hc ⊢
  · linear_combination phase^2*hc + sine (gamma+(b-t))*sine (gamma-t)*coeffD (t-(b-t))*hp
  · linear_combination sine (gamma-t)*coeffH (t-(b-t))*hp
  · linear_combination phase^2*hc + sine (gamma+(b-t))*sine (gamma-t)*coeffD (t-(b-t))*hp
lemma source_K1_swap (t : ℝ) (h : Q (t-(b-t))≠0)
    (ht : sine (gamma+t)≠0) (hy : sine (gamma+(b-t))≠0) :
    spectralR (t-(b-t)) *ᵥ K1 t = fun p => K1 (b-t) (p.2,p.1) := by
  have hc:=source_swap_linear_scalar t h ht hy
  funext ⟨a,b'⟩
  fin_cases a <;> fin_cases b' <;>
    simp [Matrix.mulVec,dotProduct,Fintype.sum_prod_type,Fin.sum_univ_three,
      spectralR,bulkNumerator,K1,boundary1,spinValue,Fin.rev,div_eq_mul_inv]
  all_goals
    have hn : phase≠0 := point_ne_zero _
    field_simp [h,ht,hy,hn] at hc ⊢
    linear_combination hc
end CriticalHoneycomb.Transfer.SpectralFamily

end

section

namespace CriticalHoneycomb.Transfer.ClosedFourRow
open scoped Matrix BigOperators
section
variable {α ι k k' : Type*} [CommSemiring k] [CommSemiring k']
  [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]
omit [Fintype α] [DecidableEq α] [DecidableEq ι] in
lemma map_forwardPair (f : k →+* k') (M N : Row α ι k) (s t : ι) :
    (forwardPair M N s t).map f =
      forwardPair (fun s t => (M s t).map f) (fun s t => (N s t).map f) s t := by
  ext p q
  simp [forwardPair,Matrix.map_apply,Matrix.sum_apply,map_sum,
    Matrix.kronecker,Matrix.kroneckerMap]
omit [Fintype α] [DecidableEq α] [DecidableEq ι] in
lemma map_backwardPair (f : k →+* k') (M N : Row α ι k) (s t : ι) :
    (backwardPair M N s t).map f =
      backwardPair (fun s t => (M s t).map f) (fun s t => (N s t).map f) s t := by
  ext p q
  simp [backwardPair,Matrix.map_apply,Matrix.sum_apply,map_sum,
    Matrix.kronecker,Matrix.kroneckerMap]
omit [DecidableEq α] [DecidableEq ι] in
lemma map_pair_exchange (f : k →+* k') (F : Matrix (α×α) (α×α) k)
    (M N : Row α ι k)
    (h : ∀ s t, F * forwardPair M N s t = backwardPair M N s t * F) :
    ∀ s t, F.map f * forwardPair (fun s t => (M s t).map f)
        (fun s t => (N s t).map f) s t =
      backwardPair (fun s t => (M s t).map f)
        (fun s t => (N s t).map f) s t * F.map f := by
  intro s t
  have hh := congrArg (fun P : Matrix (α×α) (α×α) k => P.map f) (h s t)
  simpa only [Matrix.map_mul,map_forwardPair,map_backwardPair] using hh
omit [Fintype α] in
lemma map_auxBC (f : k →+* k') (F : Matrix (α×α) (α×α) k) :
    (auxBC F).map f = auxBC (F.map f) := by
  ext p q
  simp only [auxBC,Matrix.map_apply,Matrix.one_apply,map_mul]
  split_ifs <;> simp_all
omit [Fintype α] in
lemma map_auxAC (f : k →+* k') (F : Matrix (α×α) (α×α) k) :
    (auxAC F).map f = auxAC (F.map f) := by
  ext p q
  simp only [auxAC,Matrix.map_apply,Matrix.one_apply,map_mul]
  split_ifs <;> simp_all
omit [Fintype α] in
lemma map_auxBD (f : k →+* k') (F : Matrix (α×α) (α×α) k) :
    (auxBD F).map f = auxBD (F.map f) := by
  ext p q
  simp only [auxBD,Matrix.map_apply,Matrix.one_apply,map_mul]
  split_ifs <;> simp_all
omit [Fintype α] in
lemma map_auxAD (f : k →+* k') (F : Matrix (α×α) (α×α) k) :
    (auxAD F).map f = auxAD (F.map f) := by
  ext p q
  simp only [auxAD,Matrix.map_apply,Matrix.one_apply,map_mul]
  split_ifs <;> simp_all
lemma map_auxTrain (f : k →+* k') (F₁ F₂ F₃ F₄ : Matrix (α×α) (α×α) k) :
    (auxTrain F₁ F₂ F₃ F₄).map f =
      auxTrain (F₁.map f) (F₂.map f) (F₃.map f) (F₄.map f) := by
  simp only [auxTrain,Matrix.map_mul,map_auxAD,map_auxBD,map_auxAC,map_auxBC]
omit [Fintype α] [DecidableEq α] in
lemma square_zero_tensor (f : k →+* k') (e : k') (he : e*e=0)
    (a₀ a₁ b₀ b₁ : α×α → k) :
    tensorBoundary (fun p => f (a₀ p)+e*f (a₁ p)) (fun p => f (b₀ p)+e*f (b₁ p)) =
      fun p => f (tensorBoundary a₀ b₀ p)+
        e*f ((tensorBoundary a₁ b₀+tensorBoundary a₀ b₁) p) := by
  funext p
  simp only [tensorBoundary,Pi.add_apply,map_add,map_mul]
  calc
    _ = f (a₀ (p.1,p.2.1))*f (b₀ (p.2.2.1,p.2.2.2))+
          e*(f (a₁ (p.1,p.2.1))*f (b₀ (p.2.2.1,p.2.2.2))+
            f (a₀ (p.1,p.2.1))*f (b₁ (p.2.2.1,p.2.2.2)))+
          (e*e)*(f (a₁ (p.1,p.2.1))*f (b₁ (p.2.2.1,p.2.2.2))) := by ring
    _ = _ := by rw [he,zero_mul,add_zero]
omit [DecidableEq ι] in
lemma map_right_jet (f : k →+* k') (U : Matrix ι ι k) (r₀ r₁ : ι → k)
    (h₀ : U *ᵥ r₀=r₀) (h₁ : U *ᵥ r₁=r₁) (e : k') :
    U.map f *ᵥ (fun p => f (r₀ p)+ e*f (r₁ p)) =
      fun p => f (r₀ p)+e*f (r₁ p) := by
  have h₀' : U.map f *ᵥ (f ∘ r₀)=f ∘ r₀ := by
    funext p
    rw [←RingHom.map_mulVec,h₀]
    rfl
  have h₁' : U.map f *ᵥ (f ∘ r₁)=f ∘ r₁ := by
    funext p
    rw [←RingHom.map_mulVec,h₁]
    rfl
  change U.map f *ᵥ ((f ∘ r₀)+e • (f ∘ r₁)) = (f ∘ r₀)+e • (f ∘ r₁)
  rw [Matrix.mulVec_add,Matrix.mulVec_smul,h₀',h₁']
omit [DecidableEq ι] in
lemma map_left_jet (f : k →+* k') (U : Matrix ι ι k) (l₀ l₁ : ι → k)
    (h₀ : l₀ ᵥ* U=l₀) (h₁ : l₁ ᵥ* U=l₁) (e : k') :
    (fun p => f (l₀ p)+ e*f (l₁ p)) ᵥ* U.map f =
      fun p => f (l₀ p)+e*f (l₁ p) := by
  have h₀' : (f ∘ l₀) ᵥ* U.map f=f ∘ l₀ := by
    funext p
    rw [←RingHom.map_vecMul,h₀]
    rfl
  have h₁' : (f ∘ l₁) ᵥ* U.map f=f ∘ l₁ := by
    funext p
    rw [←RingHom.map_vecMul,h₁]
    rfl
  change ((f ∘ l₀)+e • (f ∘ l₁)) ᵥ* U.map f = (f ∘ l₀)+e • (f ∘ l₁)
  rw [Matrix.add_vecMul,Matrix.smul_vecMul,h₀',h₁']
end
end CriticalHoneycomb.Transfer.ClosedFourRow

end

section
namespace CriticalHoneycomb.Transfer.SpectralFamily
open Reflection RowExchange BoundaryJet ClosedFourRow
open scoped Matrix BigOperators
noncomputable def JRow (N : ℕ) (ξ : Fin N→ℝ) (u : ℝ) : Row Spin (Space N) Jet :=
  fun s t => (row N (exactSites N ξ u) s t).map C
lemma forward_JRow (N : ℕ) (ξ : Fin N→ℝ) (u v : ℝ) (s t : Space N) :
    forwardPair (JRow N ξ u) (JRow N ξ v) s t =
      (forward N (exactSites N ξ u) (exactSites N ξ v) s t).map C := by
  funext p q
  simp only [forwardPair,JRow,forward,Matrix.map_apply,Matrix.sum_apply,map_sum,Matrix.kronecker,Matrix.kroneckerMap,Matrix.of_apply,map_mul]
lemma T_closePair (N : ℕ) (ξ : Fin N→ℝ) (u : ℝ) :
    T N ξ u = closePair (forwardPair (JRow N ξ u) (JRow N ξ (b-u)))
      (K eL (b-u)) (K eR u) := by
  funext s t
  simp only [T,closePair,forward_JRow,bulkRows,Matrix.map_apply]
lemma backward_JRow (N : ℕ) (ξ : Fin N→ℝ) (u v : ℝ) (s t : Space N) :
    backwardPair (JRow N ξ u) (JRow N ξ v) s t =
      (backward N (exactSites N ξ u) (exactSites N ξ v) s t).map C := by
  funext p q
  simp only [backwardPair,JRow,backward,Matrix.map_apply,Matrix.sum_apply,map_sum,Matrix.kronecker,Matrix.kroneckerMap,Matrix.of_apply,map_mul]
end CriticalHoneycomb.Transfer.SpectralFamily

end

section
namespace CriticalHoneycomb.Transfer.Reflection
open scoped Matrix
private lemma transposeCrossingTransposeCrossing00 (u : ℝ) (c d : Fin 3) :
    spectralR (b-u) (c,d) (0,0)=
      phase^(spinValue d-spinValue 0)*spectralR u (0,d.rev) (c,(0:Fin 3).rev) := by
  fin_cases c <;> fin_cases d <;>
    simp [spectralR,bulkNumerator,reflected_Q,reflected_C,spinValue,Fin.rev]

private lemma transposeCrossingTransposeCrossing01 (u : ℝ) (c d : Fin 3) :
    spectralR (b-u) (c,d) (0,1)=
      phase^(spinValue d-spinValue 1)*spectralR u (0,d.rev) (c,(1:Fin 3).rev) := by
  fin_cases c <;> fin_cases d <;>
    simp [spectralR,bulkNumerator,reflected_Q,reflected_A,reflected_V,spinValue,Fin.rev,div_eq_mul_inv]
  all_goals { have hn : phase ≠ 0 := point_ne_zero _
              field_simp [hn]  }
private lemma transposeCrossingTransposeCrossing02 (u : ℝ) (c d : Fin 3) :
    spectralR (b-u) (c,d) (0,2)=
      phase^(spinValue d-spinValue 2)*spectralR u (0,d.rev) (c,(2:Fin 3).rev) := by
  fin_cases c <;> fin_cases d <;>
    simp [spectralR,bulkNumerator,reflected_Q,reflected_H,
      reflected_C,reflected_D,spinValue,Fin.rev,div_eq_mul_inv]
  all_goals { have hn : phase ≠ 0 := point_ne_zero _
              field_simp [hn] <;> ring }
private lemma transposeCrossingTransposeCrossing10 (u : ℝ) (c d : Fin 3) :
    spectralR (b-u) (c,d) (1,0)=
      phase^(spinValue d-spinValue 0)*spectralR u (1,d.rev) (c,(0:Fin 3).rev) := by
  fin_cases c <;> fin_cases d <;>
    simp [spectralR,bulkNumerator,reflected_Q,reflected_A,reflected_V,spinValue,Fin.rev]
  all_goals { have hn : phase ≠ 0 := point_ne_zero _
              field_simp [hn]  }
private lemma transposeCrossingTransposeCrossing11 (u : ℝ) (c d : Fin 3) :
    spectralR (b-u) (c,d) (1,1)=
      phase^(spinValue d-spinValue 1)*spectralR u (1,d.rev) (c,(1:Fin 3).rev) := by
  fin_cases c <;> fin_cases d <;>
    simp [spectralR,bulkNumerator,reflected_Q,reflected_H,
      spinValue,Fin.rev,div_eq_mul_inv]
  all_goals { have hn : phase ≠ 0 := point_ne_zero _
              field_simp [hn]  }
private lemma transposeCrossingTransposeCrossing12 (u : ℝ) (c d : Fin 3) :
    spectralR (b-u) (c,d) (1,2)=
      phase^(spinValue d-spinValue 2)*spectralR u (1,d.rev) (c,(2:Fin 3).rev) := by
  fin_cases c <;> fin_cases d <;>
    simp [spectralR,bulkNumerator,reflected_Q,reflected_A,reflected_V,spinValue,Fin.rev,div_eq_mul_inv]
  all_goals { have hn : phase ≠ 0 := point_ne_zero _
              field_simp [hn]  }
private lemma transposeCrossingTransposeCrossing20 (u : ℝ) (c d : Fin 3) :
    spectralR (b-u) (c,d) (2,0)=
      phase^(spinValue d-spinValue 0)*spectralR u (2,d.rev) (c,(0:Fin 3).rev) := by
  fin_cases c <;> fin_cases d <;>
    simp [spectralR,bulkNumerator,reflected_Q,reflected_H,
      reflected_C,reflected_D,spinValue,Fin.rev,div_eq_mul_inv]
  all_goals { have hn : phase ≠ 0 := point_ne_zero _
              field_simp [hn] <;> ring }
private lemma transposeCrossingTransposeCrossing21 (u : ℝ) (c d : Fin 3) :
    spectralR (b-u) (c,d) (2,1)=
      phase^(spinValue d-spinValue 1)*spectralR u (2,d.rev) (c,(1:Fin 3).rev) := by
  fin_cases c <;> fin_cases d <;>
    simp [spectralR,bulkNumerator,reflected_Q,reflected_A,reflected_V,spinValue,Fin.rev]
  all_goals { have hn : phase ≠ 0 := point_ne_zero _
              field_simp [hn]  }
private lemma transposeCrossingTransposeCrossing22 (u : ℝ) (c d : Fin 3) :
    spectralR (b-u) (c,d) (2,2)=
      phase^(spinValue d-spinValue 2)*spectralR u (2,d.rev) (c,(2:Fin 3).rev) := by
  fin_cases c <;> fin_cases d <;>
    simp [spectralR,bulkNumerator,reflected_Q,reflected_C,spinValue,Fin.rev]


lemma source_transpose_crossing (u : ℝ) (i j k l : Fin 3) :
    spectralR (b-u) (k,l) (i,j)=
      phase^(spinValue l-spinValue j)*spectralR u (i,l.rev) (k,j.rev) := by
  fin_cases i <;> fin_cases j
  · exact transposeCrossingTransposeCrossing00 u k l
  · exact transposeCrossingTransposeCrossing01 u k l
  · exact transposeCrossingTransposeCrossing02 u k l
  · exact transposeCrossingTransposeCrossing10 u k l
  · exact transposeCrossingTransposeCrossing11 u k l
  · exact transposeCrossingTransposeCrossing12 u k l
  · exact transposeCrossingTransposeCrossing20 u k l
  · exact transposeCrossingTransposeCrossing21 u k l
  · exact transposeCrossingTransposeCrossing22 u k l
end CriticalHoneycomb.Transfer.Reflection

end

section
namespace CriticalHoneycomb.Transfer.Reflection
open TrivSqZeroExt
open scoped Matrix
abbrev Scalar := DualNumber ℂ
noncomputable def pairMatrix {ι : Type*} (A B : Matrix ι ι ℂ) : Matrix ι ι Scalar :=
  fun p q=>⟨A p q,B p q⟩
lemma pairMatrix_mul {ι : Type*} [Fintype ι] (A B C D : Matrix ι ι ℂ) :
    pairMatrix A B*pairMatrix C D=pairMatrix (A*C) (A*D+B*C) := by
  funext p q
  apply TrivSqZeroExt.ext
  · simp only [Matrix.mul_apply,TrivSqZeroExt.fst_sum]
    rfl
  · simp only [Matrix.mul_apply,TrivSqZeroExt.snd_sum]
    have hh (i : ι) : snd (pairMatrix A B p i * pairMatrix C D i q)=
        A p i*D i q+B p i*C i q := by
      exact DualNumber.snd_mul (R:=ℂ) (pairMatrix A B p i) (pairMatrix C D i q)
    simp only [hh,Finset.sum_add_distrib]
    rfl
lemma pairMatrix_transpose {ι : Type*} (A B : Matrix ι ι ℂ) :
    (pairMatrix A B)ᵀ=pairMatrix (Matrix.transpose A) (Matrix.transpose B) := rfl
noncomputable def bulkJet (u : ℝ) : Matrix Pair Pair Scalar := pairMatrix (spectralR u) 0

noncomputable def boundaryJet (t : ℝ) : Matrix (Fin 3) (Fin 3) Scalar :=
  pairMatrix (boundary0 t) (boundary1 t)
noncomputable def jetSlot1 (M : Matrix (Fin 3) (Fin 3) Scalar) : Matrix Pair Pair Scalar :=
  fun p q=>if p.2=q.2 then M p.1 q.1 else 0
noncomputable def jetSlot2 (M : Matrix (Fin 3) (Fin 3) Scalar) : Matrix Pair Pair Scalar :=
  fun p q=>if p.1=q.1 then M p.2 q.2 else 0
lemma jetSlot1_pair (A B : Matrix (Fin 3) (Fin 3) ℂ) :
    jetSlot1 (pairMatrix A B)=pairMatrix (slot1 A) (slot1 B) := by
  ext p q : 2 <;> by_cases h : p.2=q.2 <;> simp [jetSlot1,slot1,pairMatrix,h]
lemma jetSlot2_pair (A B : Matrix (Fin 3) (Fin 3) ℂ) :
    jetSlot2 (pairMatrix A B)=pairMatrix (slot2 A) (slot2 B) := by
  ext p q : 2 <;> by_cases h : p.1=q.1 <;> simp [jetSlot2,slot2,pairMatrix,h]

theorem source_reflection (t y : ℝ)
    (hm : Q (t-y)≠0) (hp : Q (t+y)≠0)
    (ht : sine (gamma+t)≠0) (hy : sine (gamma+y)≠0) :
    bulkJet (t-y)*jetSlot1 (boundaryJet t)*(bulkJet (t+y))ᵀ*jetSlot2 (boundaryJet y)=
    jetSlot2 (boundaryJet y)*bulkJet (t+y)*jetSlot1 (boundaryJet t)*(bulkJet (t-y))ᵀ := by
  simp only [bulkJet,boundaryJet,jetSlot1_pair,jetSlot2_pair,pairMatrix_transpose,
    Matrix.transpose_zero,pairMatrix_mul,Matrix.zero_mul,Matrix.mul_zero,
    zero_add,add_zero,Matrix.add_mul]
  rw [source_reflection_constant t y hm hp ht hy]
  have hh := source_reflection_linear t y hm hp ht hy
  rw [add_comm] at hh
  rw [hh]
end CriticalHoneycomb.Transfer.Reflection

end

section
namespace CriticalHoneycomb.Transfer.Reflection.Fusion
lemma sourceWbar_reverse (d e j : Fin 3) :
    sourceWbar (e.rev,d.rev) j=sourceWbar (d,e) j.rev := by
  fin_cases d <;> fin_cases e <;> fin_cases j <;> rfl
lemma sourceWbar_spin (d e j : Fin 3) (h : sourceWbar (d,e) j≠0) :
    spinValue d+spinValue e=spinValue j := by
  fin_cases d <;> fin_cases e <;> fin_cases j <;>
    simp_all [sourceWbar,spinValue]

lemma sourceWbar_crossing_phase (b d e j : Fin 3) :
    phase^(spinValue d)*phase^(spinValue e-spinValue b)*sourceWbar (e.rev,d.rev) j=
      phase^(spinValue j.rev-spinValue b)*sourceWbar (d,e) j.rev := by
  rw [sourceWbar_reverse]
  by_cases h : sourceWbar (d,e) j.rev=0
  · simp [h]
  · have hs := sourceWbar_spin d e j.rev h
    have hn : phase≠0 := point_ne_zero _
    rw [←zpow_add₀ hn]
    congr 2
    omega
lemma sum_fin_rev {M : Type*} [AddCommMonoid M] (f : Fin 3→M) :
    (∑ j : Fin 3,f j.rev)=∑ j : Fin 3,f j := by
  exact Equiv.sum_comp Fin.revPerm f
end CriticalHoneycomb.Transfer.Reflection.Fusion

end

section
namespace CriticalHoneycomb.Transfer.Reflection
open scoped Matrix BigOperators
abbrev Spin3 := Fin 3
noncomputable def boundaryVector (A : Matrix Spin3 Spin3 ℂ) (p : Pair) : ℂ :=
  phase^(spinValue p.2.rev)*A p.1 p.2.rev
noncomputable def crossedBC (R : Matrix Pair Pair ℂ) (A B : Matrix Spin3 Spin3 ℂ)
    (i m j n : Spin3) : ℂ :=
  ∑ p,∑ q,R (m,j) (p,q)*boundaryVector A (i,p)*boundaryVector B (q,n)
noncomputable def crossedADt (R : Matrix Pair Pair ℂ) (A B : Matrix Spin3 Spin3 ℂ)
    (i m j n : Spin3) : ℂ :=
  ∑ p,∑ q,R (p,q) (i,n)*boundaryVector A (p,m)*boundaryVector B (j,q)
noncomputable def unbend (V : Spin3→Spin3→Spin3→Spin3→ℂ) : Matrix Pair Pair ℂ := fun p q=>
  phase^(-spinValue q.1-spinValue q.2)*V p.1 q.1.rev p.2 q.2.rev
lemma phase_cancellation (a c d : ℤ) :
    phase^(-a-c)*phase^(d+a)*phase^(-d)*phase^c=1 := by
  have hn : phase≠0:=point_ne_zero _
  rw [←zpow_add₀ hn,←zpow_add₀ hn,←zpow_add₀ hn]
  convert zpow_zero phase using 1 ; congr 1 ; ring
lemma sandwich12 (A B : Matrix Spin3 Spin3 ℂ) (R : Matrix Pair Pair ℂ) (i j m n : Spin3) :
    (slot1 A*R*slot2 B) (i,j) (m,n)=
      ∑ p,∑ q,A i p*R (p,j) (m,q)*B q n := by
  simp only [Matrix.mul_apply,Fintype.sum_prod_type,slot1,slot2]
  simp only [ite_mul,mul_ite,zero_mul,mul_zero,Finset.mem_univ,ite_true,
    Finset.sum_ite_eq,Finset.sum_mul]
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [Finset.sum_comm]
lemma sandwich21 (A B : Matrix Spin3 Spin3 ℂ) (R : Matrix Pair Pair ℂ) (i j m n : Spin3) :
    (slot2 B*R*slot1 A) (i,j) (m,n)=
      ∑ p,∑ q,B j q*R (i,q) (p,n)*A p m := by
  simp only [Matrix.mul_apply,Fintype.sum_prod_type,slot1,slot2]
  simp only [ite_mul,mul_ite,zero_mul,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true,
    Finset.sum_mul]
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true]

lemma unbend_BC (u : ℝ) (A B : Matrix Spin3 Spin3 ℂ) :
    unbend (crossedBC (spectralR (b-u)) A B)=slot1 A*(spectralR u)ᵀ*slot2 B := by
  ext ⟨i,j⟩ ⟨m,n⟩
  rw [sandwich12]
  simp only [unbend,crossedBC,Finset.mul_sum]
  rw [←CriticalHoneycomb.Transfer.Reflection.Fusion.sum_fin_rev (fun p : Spin3=>
    ∑ q : Spin3,phase^(-spinValue m-spinValue n)*
      (spectralR (b-u) (m.rev,j) (p,q)*boundaryVector A (i,p)*boundaryVector B (q,n.rev)))]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  rw [source_crossing]
  simp only [boundaryVector,spinValue_rev,Fin.rev_rev,Matrix.transpose_apply]
  calc
    _=(phase^(-spinValue m-spinValue n)*phase^(-spinValue p+spinValue m)*
      phase^(spinValue p)*phase^(spinValue n))*
      (A i p*spectralR u (m,q) (p,j)*B q n) := by ring_nf
    _=_ := by
      have hh:=phase_cancellation (spinValue m) (spinValue n) (-spinValue p)
      simp only [neg_neg] at hh
      rw [hh,one_mul]
lemma unbend_ADt (u : ℝ) (A B : Matrix Spin3 Spin3 ℂ) :
    unbend (crossedADt (spectralR (b-u)) A B)=slot2 B*spectralR u*slot1 A := by
  ext ⟨i,j⟩ ⟨m,n⟩
  rw [sandwich21]
  simp only [unbend,crossedADt,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [←CriticalHoneycomb.Transfer.Reflection.Fusion.sum_fin_rev (fun q : Spin3=>
    phase^(-spinValue m-spinValue n)*
      (spectralR (b-u) (p,q) (i,n.rev)*boundaryVector A (p,m.rev)*boundaryVector B (j,q)))]
  apply Finset.sum_congr rfl
  intro q hq
  rw [source_transpose_crossing]
  simp only [boundaryVector,spinValue_rev,Fin.rev_rev]
  calc
    _=(phase^(-spinValue m-spinValue n)*phase^(-spinValue q+spinValue n)*
      phase^(spinValue q)*phase^(spinValue m))*
      (B j q*spectralR u (i,q) (p,n)*A p m) := by ring_nf
    _=_ := by
      have hh:=phase_cancellation (spinValue n) (spinValue m) (-spinValue q)
      have he : -spinValue m-spinValue n = -spinValue n-spinValue m := by ring
      simp only [neg_neg] at hh
      rw [he,hh,one_mul]
end CriticalHoneycomb.Transfer.Reflection

end

section
namespace CriticalHoneycomb.Transfer.Reflection
open scoped Matrix
lemma source_flip_transpose (u : ℝ) (i j k l : Fin 3) :
    spectralR u (i.rev,j.rev) (k.rev,l.rev)=spectralR u (k,l) (i,j) := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [spectralR,bulkNumerator,Fin.rev]
lemma source_spin (u : ℝ) (i j k l : Fin 3)
    (h : spectralR u (i,j) (k,l)≠0) :
    spinValue i+spinValue j=spinValue k+spinValue l := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp_all [spectralR,bulkNumerator,spinValue]
lemma source_phase_conservation (u : ℝ) (i j k l : Fin 3) :
    phase^(spinValue i+spinValue j)*spectralR u (i,j) (k,l)=
      phase^(spinValue k+spinValue l)*spectralR u (i,j) (k,l) := by
  by_cases h : spectralR u (i,j) (k,l)=0
  · simp [h]
  · rw [source_spin u i j k l h]
end CriticalHoneycomb.Transfer.Reflection

end

section
namespace CriticalHoneycomb.Transfer.Reflection
open scoped Matrix BigOperators
noncomputable def actAC (R : Matrix Pair Pair ℂ) (V : Spin3→Spin3→Spin3→Spin3→ℂ)
    (i m j n : Spin3) : ℂ := ∑ p,∑ q,R (i,j) (p,q)*V p m q n
noncomputable def actBDt (R : Matrix Pair Pair ℂ) (V : Spin3→Spin3→Spin3→Spin3→ℂ)
    (i m j n : Spin3) : ℂ := ∑ p,∑ q,R (p,q) (m,n)*V i p j q
lemma unbend_injective : Function.Injective unbend := by
  intro V W h
  funext i m j n
  have hh:=congrFun (congrFun h (i,j)) (m.rev,n.rev)
  simp only [unbend,Fin.rev_rev] at hh
  exact mul_left_cancel₀ (zpow_ne_zero _ (point_ne_zero _)) hh
lemma unbend_add (V W : Spin3→Spin3→Spin3→Spin3→ℂ) :
    unbend (V+W)=unbend V+unbend W := by
  ext p q
  simp [unbend,mul_add]
lemma unbend_AC (R : Matrix Pair Pair ℂ) (V : Spin3→Spin3→Spin3→Spin3→ℂ) :
    unbend (actAC R V)=R*unbend V := by
  ext ⟨i,j⟩ ⟨m,n⟩
  simp only [unbend,actAC,Matrix.mul_apply,Fintype.sum_prod_type,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  ring
lemma unbend_BDt (u : ℝ) (V : Spin3→Spin3→Spin3→Spin3→ℂ) :
    unbend (actBDt (spectralR u) V)=unbend V*(spectralR u)ᵀ := by
  ext ⟨i,j⟩ ⟨m,n⟩
  simp only [unbend,actBDt,Matrix.mul_apply,Matrix.transpose_apply,Fintype.sum_prod_type,
    Finset.mul_sum]
  rw [←Fusion.sum_fin_rev (fun p : Spin3=>∑ q : Spin3,
    phase^(-spinValue m-spinValue n)*(spectralR u (p,q) (m.rev,n.rev)*V i p j q))]
  apply Finset.sum_congr rfl
  intro p hp
  rw [←Fusion.sum_fin_rev (fun q : Spin3=>
    phase^(-spinValue m-spinValue n)*(spectralR u (p.rev,q) (m.rev,n.rev)*V i p.rev j q))]
  apply Finset.sum_congr rfl
  intro q hq
  rw [source_flip_transpose]
  by_cases h : spectralR u (m,n) (p,q)=0
  · simp [h]
  · have hs:=source_spin u m n p q h
    have he : -spinValue m-spinValue n = -spinValue p-spinValue q := by omega
    rw [he]
    ring

theorem source_boundary_pair_constant (t y : ℝ)
    (hm : Q (t-y)≠0) (hp : Q (t+y)≠0)
    (ht : sine (gamma+t)≠0) (hy : sine (gamma+y)≠0) :
    actAC (spectralR (t-y))
      (crossedBC (spectralR (b-(t+y))) (boundary0 t) (boundary0 y))=
    actBDt (spectralR (t-y))
      (crossedADt (spectralR (b-(t+y))) (boundary0 t) (boundary0 y)) := by
  apply unbend_injective
  rw [unbend_AC,unbend_BDt,unbend_BC,unbend_ADt]
  simpa only [mul_assoc] using source_reflection_constant t y hm hp ht hy

theorem source_boundary_pair_linear (t y : ℝ)
    (hm : Q (t-y)≠0) (hp : Q (t+y)≠0)
    (ht : sine (gamma+t)≠0) (hy : sine (gamma+y)≠0) :
    actAC (spectralR (t-y))
      (crossedBC (spectralR (b-(t+y))) (boundary1 t) (boundary0 y))+
    actAC (spectralR (t-y))
      (crossedBC (spectralR (b-(t+y))) (boundary0 t) (boundary1 y))=
    actBDt (spectralR (t-y))
      (crossedADt (spectralR (b-(t+y))) (boundary1 t) (boundary0 y))+
    actBDt (spectralR (t-y))
      (crossedADt (spectralR (b-(t+y))) (boundary0 t) (boundary1 y)) := by
  apply unbend_injective
  rw [unbend_add,unbend_add,unbend_AC,unbend_AC,unbend_BDt,unbend_BDt,
      unbend_BC,unbend_BC,unbend_ADt,unbend_ADt]
  simpa only [mul_assoc] using source_reflection_linear t y hm hp ht hy
end CriticalHoneycomb.Transfer.Reflection

end

section

namespace CriticalHoneycomb.Transfer
open scoped Matrix

noncomputable def angle : ℝ := Real.pi / 8
noncomputable def bigAngle : ℝ := 3 * angle
noncomputable def sine2 : ℝ := Real.sin (2 * angle)
noncomputable def denominator (u : ℝ) : ℝ :=
  Real.sin (2 * angle + u) * Real.sin (bigAngle + u)

noncomputable def a (u : ℝ) : ℝ :=
  sine2 * Real.sin (bigAngle - u) / denominator u
noncomputable def h (u : ℝ) : ℝ :=
  sine2 * Real.sin u / denominator u
noncomputable def v (u : ℝ) : ℝ :=
  Real.sin (bigAngle - u) * Real.sin u / denominator u
noncomputable def c (u : ℝ) : ℝ :=
  Real.sin (bigAngle - u) * Real.sin (2 * angle - u) / denominator u
noncomputable def d (u : ℝ) : ℝ :=
  Real.sin u * Real.sin (u - angle) / denominator u

noncomputable def phase : ℂ := Complex.exp ((2 * angle : ℝ) * Complex.I)

noncomputable def blockOne (u : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(v u : ℂ), (a u : ℂ); (a u : ℂ), (v u : ℂ)]

noncomputable def blockZero (u : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![(d u : ℂ), (h u : ℂ) / phase, (c u : ℂ) + (d u : ℂ) / phase^2;
     (h u : ℂ) * phase, 1, (h u : ℂ) / phase;
     (c u : ℂ) + (d u : ℂ) * phase^2, (h u : ℂ) * phase, (d u : ℂ)]

lemma sine_product (x u : ℝ) :
    Real.sin (x+u) * Real.sin (x-u) = (Real.sin x)^2 - (Real.sin u)^2 := by
  rw [Real.sin_add, Real.sin_sub]
  nlinarith [Real.sin_sq_add_cos_sq x, Real.sin_sq_add_cos_sq u,
    mul_nonneg (sq_nonneg (Real.sin x)) (sq_nonneg (Real.sin u))]

lemma c_as_denominator (u : ℝ) : c u = denominator (-u) / denominator u := by
  unfold c denominator
  simp only [← sub_eq_add_neg]
  rw [mul_comm (Real.sin (bigAngle-u))]

lemma c_unitary (u : ℝ) (hp : denominator u ≠ 0) (hm : denominator (-u) ≠ 0) :
    c u * c (-u) = 1 := by
  rw [c_as_denominator, c_as_denominator, neg_neg]
  field_simp

lemma h_conjugate_c (u : ℝ) (hp : denominator u ≠ 0) (hm : denominator (-u) ≠ 0) :
    h u + c u * h (-u) = 0 := by
  rw [c_as_denominator]
  unfold h
  rw [Real.sin_neg]
  field_simp
  ; ring

lemma denominator_product (u : ℝ) :
    denominator u * denominator (-u) =
      Real.sin (bigAngle-u) * Real.sin (bigAngle+u) * (sine2^2 - (Real.sin u)^2) := by
  unfold denominator sine2
  simp only [← sub_eq_add_neg]
  calc
    _ = (Real.sin (2*angle+u) * Real.sin (2*angle-u)) *
      (Real.sin (bigAngle-u) * Real.sin (bigAngle+u)) := by ring
    _ = _ := by rw [sine_product]; ring

lemma one_diagonal (u : ℝ) (hp : denominator u ≠ 0) (hm : denominator (-u) ≠ 0) :
    v u * v (-u) + a u * a (-u) = 1 := by
  unfold v a
  simp only [sub_neg_eq_add, Real.sin_neg]
  field_simp
  nlinarith only [denominator_product u]

lemma one_offdiagonal (u : ℝ) (hp : denominator u ≠ 0) (hm : denominator (-u) ≠ 0) :
    v u * a (-u) + a u * v (-u) = 0 := by
  unfold v a
  simp only [sub_neg_eq_add, Real.sin_neg]
  field_simp
  ; ring

lemma sin_bigAngle : Real.sin bigAngle = Real.cos angle := by
  rw [show bigAngle = Real.pi/2 - angle by unfold bigAngle angle; ring,
    Real.sin_pi_div_two_sub]

lemma cos_bigAngle : Real.cos bigAngle = Real.sin angle := by
  rw [show bigAngle = Real.pi/2 - angle by unfold bigAngle angle; ring,
    Real.cos_pi_div_two_sub]

lemma cos_two_angle : Real.cos (2*angle) = sine2 := by
  unfold sine2
  rw [show 2*angle = Real.pi/4 by unfold angle; ring,
    Real.cos_pi_div_four, Real.sin_pi_div_four]

lemma mixed_sine_identity (u : ℝ) :
    Real.sin (2*angle-u) * Real.sin (bigAngle-u) * Real.sin (u+angle) +
      Real.sin (2*angle+u) * Real.sin (bigAngle+u) * Real.sin (u-angle) =
        sine2^2 * Real.sin u := by
  rw [Real.sin_sub, Real.sin_sub, Real.sin_add, Real.sin_add, Real.sin_add,
    Real.sin_sub, sin_bigAngle, cos_bigAngle, cos_two_angle]
  change (sine2 * Real.cos u - sine2 * Real.sin u) *
      (Real.cos angle * Real.cos u - Real.sin angle * Real.sin u) *
      (Real.sin u * Real.cos angle + Real.cos u * Real.sin angle) +
    (sine2 * Real.cos u + sine2 * Real.sin u) *
      (Real.cos angle * Real.cos u + Real.sin angle * Real.sin u) *
      (Real.sin u * Real.cos angle - Real.cos u * Real.sin angle) = _
  have h₁ : (Real.cos angle)^2 - (Real.sin angle)^2 = sine2 := by
    have hh := Real.cos_two_mul angle
    rw [cos_two_angle] at hh
    nlinarith only [Real.sin_sq_add_cos_sq angle, hh]
  have h₂ : 2 * Real.sin angle * Real.cos angle = sine2 := (Real.sin_two_mul angle).symm
  linear_combination
    2*sine2*Real.sin u*(Real.cos u)^2 * h₁ +
    sine2*Real.sin u*((Real.sin u)^2-(Real.cos u)^2) * h₂ +
    sine2^2*Real.sin u * Real.sin_sq_add_cos_sq u

lemma zero_mixed (u : ℝ) (hp : denominator u ≠ 0) (hm : denominator (-u) ≠ 0) :
    h u * h (-u) + c u * d (-u) + c (-u) * d u = 0 := by
  unfold h c d
  simp only [Real.sin_neg, sub_neg_eq_add]
  rw [show -u-angle = -(u+angle) by ring, Real.sin_neg]
  field_simp
  have ht := mixed_sine_identity u
  have ht' := congrArg (fun t : ℝ => t * Real.sin u) ht
  nlinarith only [ht']

lemma blockOne_unitary (u : ℝ) (hp : denominator u ≠ 0) (hm : denominator (-u) ≠ 0) :
    blockOne u * (blockOne (-u)).transpose = 1 := by
  have hd : (v u:ℂ)*v (-u)+(a u:ℂ)*a (-u)=1 := by
    exact_mod_cast one_diagonal u hp hm
  have ho : (v u:ℂ)*a (-u)+(a u:ℂ)*v (-u)=0 := by
    exact_mod_cast one_offdiagonal u hp hm
  ext i j
  fin_cases i <;> fin_cases j <;>
    first
    | simpa [blockOne, Matrix.mul_apply, Fin.sum_univ_two, add_comm] using hd
    | simpa [blockOne, Matrix.mul_apply, Fin.sum_univ_two, add_comm] using ho

lemma phase_sq : phase^2 = Complex.I := by
  unfold phase
  rw [← Complex.exp_nat_mul]
  convert Complex.exp_pi_div_two_mul_I using 1
  push_cast
  unfold angle
  push_cast
  ring_nf

lemma phase_ne_zero : phase ≠ 0 := Complex.exp_ne_zero _

lemma phase_inv : phase⁻¹ = -phase * Complex.I := by
  apply mul_left_cancel₀ phase_ne_zero
  rw [mul_inv_cancel₀ phase_ne_zero]
  calc
    1 = -phase^2 * Complex.I := by rw [phase_sq]; simp
    _ = phase * (-phase * Complex.I) := by ring

lemma blockZero_unitary (u : ℝ) (hp : denominator u ≠ 0) (hm : denominator (-u) ≠ 0) :
    blockZero u * (blockZero (-u)).transpose = 1 := by
  have hcc : (c u:ℂ)*c (-u)=1 := by exact_mod_cast c_unitary u hp hm
  have hhc : (h u:ℂ)+(c u:ℂ)*h (-u)=0 := by exact_mod_cast h_conjugate_c u hp hm
  have hhcr : (h (-u):ℂ)+(c (-u):ℂ)*h u=0 := by
    have hh := h_conjugate_c (-u) hm (by simpa using hp)
    simpa using congrArg (fun t : ℝ => (t:ℂ)) hh
  have hmix : (h u:ℂ)*h (-u)+(c u:ℂ)*d (-u)+(c (-u):ℂ)*d u=0 := by
    exact_mod_cast zero_mixed u hp hm
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [blockZero, Matrix.mul_apply, Fin.sum_univ_three, div_eq_mul_inv,
      inv_pow, phase_inv, phase_sq, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
    (try ring_nf) <;> (try simp only [phase_sq, Complex.I_sq]) <;> (try ring_nf) <;>
      (try simp only [Complex.I_sq])
  all_goals first
    | linear_combination hcc - Complex.I * hmix
    | linear_combination hcc + Complex.I * hmix
    | linear_combination hmix
    | linear_combination (-phase * Complex.I) * hhc
    | linear_combination (-phase * Complex.I) * hhcr
    | linear_combination phase * hhc
    | linear_combination phase * hhcr

end CriticalHoneycomb.Transfer

end

section
namespace CriticalHoneycomb.Transfer.Reflection
open scoped Matrix
lemma angle_double : 2*Transfer.angle=Real.pi/4 := by unfold Transfer.angle;ring
lemma bigAngle_binding : Transfer.bigAngle=b := by unfold Transfer.bigAngle Transfer.angle b;ring
lemma angle_binding : Transfer.angle=L := rfl
lemma denominator_binding (u : ℝ) : (Transfer.denominator u : ℂ)=Q u := by
  simp only [Transfer.denominator,angle_double,bigAngle_binding,Q,sine,Complex.ofReal_mul]
lemma phase_binding : Transfer.phase=phase := by
  unfold Transfer.phase
  rw [angle_double]
  rfl
lemma normA (u : ℝ) : (Q u)⁻¹*coeffA u=(Transfer.a u : ℂ) := by
  simp only [Transfer.a,Transfer.sine2,angle_double,bigAngle_binding,coeffA,S,sine,
    Complex.ofReal_mul,Complex.ofReal_inv,denominator_binding,div_eq_mul_inv]
  ring
lemma normH (u : ℝ) : (Q u)⁻¹*coeffH u=(Transfer.h u : ℂ) := by
  simp only [Transfer.h,Transfer.sine2,angle_double,coeffH,S,sine,
    Complex.ofReal_mul,Complex.ofReal_inv,denominator_binding,div_eq_mul_inv]
  ring
lemma normV (u : ℝ) : (Q u)⁻¹*coeffV u=(Transfer.v u : ℂ) := by
  simp only [Transfer.v,bigAngle_binding,coeffV,sine,
    Complex.ofReal_mul,Complex.ofReal_inv,denominator_binding,div_eq_mul_inv]
  ring
lemma normC (u : ℝ) : (Q u)⁻¹*coeffC u=(Transfer.c u : ℂ) := by
  simp only [Transfer.c,angle_double,bigAngle_binding,coeffC,sine,
    Complex.ofReal_mul,Complex.ofReal_inv,denominator_binding,div_eq_mul_inv]
  ring
lemma normD (u : ℝ) : (Q u)⁻¹*coeffD u=(Transfer.d u : ℂ) := by
  simp only [Transfer.d,angle_binding,coeffD,sine,
    Complex.ofReal_mul,Complex.ofReal_inv,denominator_binding,div_eq_mul_inv]
  ring

noncomputable def normalizedR (u : ℝ) : Matrix Pair Pair ℂ := fun p q=>
  let a := Transfer.a u
  let h := Transfer.h u
  let v := Transfer.v u
  let c := Transfer.c u
  let d := Transfer.d u
  match p.1.val, p.2.val, q.1.val, q.2.val with
  | 0, 0, 0, 0 => c
  | 2, 2, 2, 2 => c
  | 0, 1, 0, 1 => v
  | 1, 0, 1, 0 => v
  | 2, 1, 2, 1 => v
  | 1, 2, 1, 2 => v
  | 0, 1, 1, 0 => a
  | 1, 0, 0, 1 => a
  | 2, 1, 1, 2 => a
  | 1, 2, 2, 1 => a
  | 0, 2, 0, 2 => d
  | 0, 2, 1, 1 => h/Transfer.phase
  | 0, 2, 2, 0 => c+d/Transfer.phase^2
  | 1, 1, 0, 2 => h*Transfer.phase
  | 1, 1, 1, 1 => 1
  | 1, 1, 2, 0 => h/Transfer.phase
  | 2, 0, 0, 2 => c+d*Transfer.phase^2
  | 2, 0, 1, 1 => h*Transfer.phase
  | 2, 0, 2, 0 => d
  | _, _, _, _ => 0

private lemma unitarityNormalization00 (u : ℝ) (hQ : Q u≠0) (c d : Fin 3) :
    spectralR u (0,0) (c,d)=normalizedR u (0,0) (c,d) := by
  have he : (Q u)⁻¹*Q u=1 := inv_mul_cancel₀ hQ
  fin_cases c <;> fin_cases d <;>
    simp [spectralR,bulkNumerator,normalizedR,←normC u,]
private lemma unitarityNormalization01 (u : ℝ) (hQ : Q u≠0) (c d : Fin 3) :
    spectralR u (0,1) (c,d)=normalizedR u (0,1) (c,d) := by
  have he : (Q u)⁻¹*Q u=1 := inv_mul_cancel₀ hQ
  fin_cases c <;> fin_cases d <;>
    simp [spectralR,bulkNumerator,normalizedR,←normA u,←normV u,
      ]
private lemma unitarityNormalization02 (u : ℝ) (hQ : Q u≠0) (c d : Fin 3) :
    spectralR u (0,2) (c,d)=normalizedR u (0,2) (c,d) := by
  have he : (Q u)⁻¹*Q u=1 := inv_mul_cancel₀ hQ
  fin_cases c <;> fin_cases d <;>
    simp [spectralR,bulkNumerator,normalizedR,←normH u,←normC u,←normD u,phase_binding,div_eq_mul_inv] <;> ring
private lemma unitarityNormalization10 (u : ℝ) (hQ : Q u≠0) (c d : Fin 3) :
    spectralR u (1,0) (c,d)=normalizedR u (1,0) (c,d) := by
  have he : (Q u)⁻¹*Q u=1 := inv_mul_cancel₀ hQ
  fin_cases c <;> fin_cases d <;>
    simp [spectralR,bulkNumerator,normalizedR,←normA u,←normV u,
      ]
private lemma unitarityNormalization11 (u : ℝ) (hQ : Q u≠0) (c d : Fin 3) :
    spectralR u (1,1) (c,d)=normalizedR u (1,1) (c,d) := by
  have he : (Q u)⁻¹*Q u=1 := inv_mul_cancel₀ hQ
  fin_cases c <;> fin_cases d <;>
    simp [spectralR,bulkNumerator,normalizedR,←normH u,phase_binding,div_eq_mul_inv,he] <;> ring
private lemma unitarityNormalization12 (u : ℝ) (hQ : Q u≠0) (c d : Fin 3) :
    spectralR u (1,2) (c,d)=normalizedR u (1,2) (c,d) := by
  have he : (Q u)⁻¹*Q u=1 := inv_mul_cancel₀ hQ
  fin_cases c <;> fin_cases d <;>
    simp [spectralR,bulkNumerator,normalizedR,←normA u,←normV u,
      ]
private lemma unitarityNormalization20 (u : ℝ) (hQ : Q u≠0) (c d : Fin 3) :
    spectralR u (2,0) (c,d)=normalizedR u (2,0) (c,d) := by
  have he : (Q u)⁻¹*Q u=1 := inv_mul_cancel₀ hQ
  fin_cases c <;> fin_cases d <;>
    simp [spectralR,bulkNumerator,normalizedR,←normH u,←normC u,←normD u,phase_binding,] <;> ring
private lemma unitarityNormalization21 (u : ℝ) (hQ : Q u≠0) (c d : Fin 3) :
    spectralR u (2,1) (c,d)=normalizedR u (2,1) (c,d) := by
  have he : (Q u)⁻¹*Q u=1 := inv_mul_cancel₀ hQ
  fin_cases c <;> fin_cases d <;>
    simp [spectralR,bulkNumerator,normalizedR,←normA u,←normV u,
      ]
private lemma unitarityNormalization22 (u : ℝ) (hQ : Q u≠0) (c d : Fin 3) :
    spectralR u (2,2) (c,d)=normalizedR u (2,2) (c,d) := by
  have he : (Q u)⁻¹*Q u=1 := inv_mul_cancel₀ hQ
  fin_cases c <;> fin_cases d <;>
    simp [spectralR,bulkNumerator,normalizedR,←normC u,]
lemma spectralR_normalized (u : ℝ) (hQ : Q u≠0) : spectralR u=normalizedR u := by
  ext ⟨a,b⟩ ⟨c,d⟩
  fin_cases a <;> fin_cases b
  · exact unitarityNormalization00 u hQ c d
  · exact unitarityNormalization01 u hQ c d
  · exact unitarityNormalization02 u hQ c d
  · exact unitarityNormalization10 u hQ c d
  · exact unitarityNormalization11 u hQ c d
  · exact unitarityNormalization12 u hQ c d
  · exact unitarityNormalization20 u hQ c d
  · exact unitarityNormalization21 u hQ c d
  · exact unitarityNormalization22 u hQ c d
private lemma unitarityUnitary0000 (u : ℝ) (hp : Transfer.denominator u≠0)
    (hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (0,0) (0,0)=
      (1:Matrix Pair Pair ℂ) (0,0) (0,0) := by
  have hh : (Transfer.c u:ℂ)*Transfer.c (-u)=1 := by
    exact_mod_cast Transfer.c_unitary u hp hm
  simpa [Matrix.one_apply,normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,Fin.sum_univ_two,Transfer.blockOne,Transfer.blockZero] using hh

private lemma unitarityUnitary0001 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (0,0) (0,1)=
      (1:Matrix Pair Pair ℂ) (0,0) (0,1) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary0002 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (0,0) (0,2)=
      (1:Matrix Pair Pair ℂ) (0,0) (0,2) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary0010 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (0,0) (1,0)=
      (1:Matrix Pair Pair ℂ) (0,0) (1,0) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary0011 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (0,0) (1,1)=
      (1:Matrix Pair Pair ℂ) (0,0) (1,1) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary0012 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (0,0) (1,2)=
      (1:Matrix Pair Pair ℂ) (0,0) (1,2) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary0020 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (0,0) (2,0)=
      (1:Matrix Pair Pair ℂ) (0,0) (2,0) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary0021 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (0,0) (2,1)=
      (1:Matrix Pair Pair ℂ) (0,0) (2,1) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary0022 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (0,0) (2,2)=
      (1:Matrix Pair Pair ℂ) (0,0) (2,2) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary00 (u : ℝ) (hp : Transfer.denominator u≠0)
    (hm : Transfer.denominator (-u)≠0) (c d : Fin 3) :
    (normalizedR u*(normalizedR (-u)).transpose) (0,0) (c,d)=
      (1:Matrix Pair Pair ℂ) (0,0) (c,d) := by
  fin_cases c <;> fin_cases d
  · exact unitarityUnitary0000 u hp hm
  · exact unitarityUnitary0001 u hp hm
  · exact unitarityUnitary0002 u hp hm
  · exact unitarityUnitary0010 u hp hm
  · exact unitarityUnitary0011 u hp hm
  · exact unitarityUnitary0012 u hp hm
  · exact unitarityUnitary0020 u hp hm
  · exact unitarityUnitary0021 u hp hm
  · exact unitarityUnitary0022 u hp hm

private lemma unitarityUnitary0100 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (0,1) (0,0)=
      (1:Matrix Pair Pair ℂ) (0,1) (0,0) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary0101 (u : ℝ) (hp : Transfer.denominator u≠0)
    (hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (0,1) (0,1)=
      (1:Matrix Pair Pair ℂ) (0,1) (0,1) := by
  have hh := congrFun (congrFun (Transfer.blockOne_unitary u hp hm) (0:Fin 2)) (0:Fin 2)
  simpa [Matrix.one_apply,normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,Fin.sum_univ_two,Transfer.blockOne,Transfer.blockZero] using hh

private lemma unitarityUnitary0102 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (0,1) (0,2)=
      (1:Matrix Pair Pair ℂ) (0,1) (0,2) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary0110 (u : ℝ) (hp : Transfer.denominator u≠0)
    (hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (0,1) (1,0)=
      (1:Matrix Pair Pair ℂ) (0,1) (1,0) := by
  have hh := congrFun (congrFun (Transfer.blockOne_unitary u hp hm) (0:Fin 2)) (1:Fin 2)
  simpa [Matrix.one_apply,normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,Fin.sum_univ_two,Transfer.blockOne,Transfer.blockZero] using hh

private lemma unitarityUnitary0111 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (0,1) (1,1)=
      (1:Matrix Pair Pair ℂ) (0,1) (1,1) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary0112 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (0,1) (1,2)=
      (1:Matrix Pair Pair ℂ) (0,1) (1,2) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary0120 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (0,1) (2,0)=
      (1:Matrix Pair Pair ℂ) (0,1) (2,0) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary0121 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (0,1) (2,1)=
      (1:Matrix Pair Pair ℂ) (0,1) (2,1) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary0122 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (0,1) (2,2)=
      (1:Matrix Pair Pair ℂ) (0,1) (2,2) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary01 (u : ℝ) (hp : Transfer.denominator u≠0)
    (hm : Transfer.denominator (-u)≠0) (c d : Fin 3) :
    (normalizedR u*(normalizedR (-u)).transpose) (0,1) (c,d)=
      (1:Matrix Pair Pair ℂ) (0,1) (c,d) := by
  fin_cases c <;> fin_cases d
  · exact unitarityUnitary0100 u hp hm
  · exact unitarityUnitary0101 u hp hm
  · exact unitarityUnitary0102 u hp hm
  · exact unitarityUnitary0110 u hp hm
  · exact unitarityUnitary0111 u hp hm
  · exact unitarityUnitary0112 u hp hm
  · exact unitarityUnitary0120 u hp hm
  · exact unitarityUnitary0121 u hp hm
  · exact unitarityUnitary0122 u hp hm

private lemma unitarityUnitary0200 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (0,2) (0,0)=
      (1:Matrix Pair Pair ℂ) (0,2) (0,0) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary0201 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (0,2) (0,1)=
      (1:Matrix Pair Pair ℂ) (0,2) (0,1) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary0202 (u : ℝ) (hp : Transfer.denominator u≠0)
    (hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (0,2) (0,2)=
      (1:Matrix Pair Pair ℂ) (0,2) (0,2) := by
  have hh := congrFun (congrFun (Transfer.blockZero_unitary u hp hm) (0:Fin 3)) (0:Fin 3)
  simpa [Matrix.one_apply,normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,Fin.sum_univ_two,Transfer.blockOne,Transfer.blockZero] using hh

private lemma unitarityUnitary0210 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (0,2) (1,0)=
      (1:Matrix Pair Pair ℂ) (0,2) (1,0) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary0211 (u : ℝ) (hp : Transfer.denominator u≠0)
    (hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (0,2) (1,1)=
      (1:Matrix Pair Pair ℂ) (0,2) (1,1) := by
  have hh := congrFun (congrFun (Transfer.blockZero_unitary u hp hm) (0:Fin 3)) (1:Fin 3)
  simpa [Matrix.one_apply,normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,Fin.sum_univ_two,Transfer.blockOne,Transfer.blockZero] using hh

private lemma unitarityUnitary0212 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (0,2) (1,2)=
      (1:Matrix Pair Pair ℂ) (0,2) (1,2) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary0220 (u : ℝ) (hp : Transfer.denominator u≠0)
    (hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (0,2) (2,0)=
      (1:Matrix Pair Pair ℂ) (0,2) (2,0) := by
  have hh := congrFun (congrFun (Transfer.blockZero_unitary u hp hm) (0:Fin 3)) (2:Fin 3)
  simpa [Matrix.one_apply,normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,Fin.sum_univ_two,Transfer.blockOne,Transfer.blockZero] using hh

private lemma unitarityUnitary0221 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (0,2) (2,1)=
      (1:Matrix Pair Pair ℂ) (0,2) (2,1) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary0222 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (0,2) (2,2)=
      (1:Matrix Pair Pair ℂ) (0,2) (2,2) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary02 (u : ℝ) (hp : Transfer.denominator u≠0)
    (hm : Transfer.denominator (-u)≠0) (c d : Fin 3) :
    (normalizedR u*(normalizedR (-u)).transpose) (0,2) (c,d)=
      (1:Matrix Pair Pair ℂ) (0,2) (c,d) := by
  fin_cases c <;> fin_cases d
  · exact unitarityUnitary0200 u hp hm
  · exact unitarityUnitary0201 u hp hm
  · exact unitarityUnitary0202 u hp hm
  · exact unitarityUnitary0210 u hp hm
  · exact unitarityUnitary0211 u hp hm
  · exact unitarityUnitary0212 u hp hm
  · exact unitarityUnitary0220 u hp hm
  · exact unitarityUnitary0221 u hp hm
  · exact unitarityUnitary0222 u hp hm

private lemma unitarityUnitary1000 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (1,0) (0,0)=
      (1:Matrix Pair Pair ℂ) (1,0) (0,0) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary1001 (u : ℝ) (hp : Transfer.denominator u≠0)
    (hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (1,0) (0,1)=
      (1:Matrix Pair Pair ℂ) (1,0) (0,1) := by
  have hh := congrFun (congrFun (Transfer.blockOne_unitary u hp hm) (1:Fin 2)) (0:Fin 2)
  simpa [Matrix.one_apply,normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,Fin.sum_univ_two,Transfer.blockOne,Transfer.blockZero] using hh

private lemma unitarityUnitary1002 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (1,0) (0,2)=
      (1:Matrix Pair Pair ℂ) (1,0) (0,2) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary1010 (u : ℝ) (hp : Transfer.denominator u≠0)
    (hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (1,0) (1,0)=
      (1:Matrix Pair Pair ℂ) (1,0) (1,0) := by
  have hh := congrFun (congrFun (Transfer.blockOne_unitary u hp hm) (1:Fin 2)) (1:Fin 2)
  simpa [Matrix.one_apply,normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,Fin.sum_univ_two,Transfer.blockOne,Transfer.blockZero] using hh

private lemma unitarityUnitary1011 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (1,0) (1,1)=
      (1:Matrix Pair Pair ℂ) (1,0) (1,1) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary1012 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (1,0) (1,2)=
      (1:Matrix Pair Pair ℂ) (1,0) (1,2) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary1020 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (1,0) (2,0)=
      (1:Matrix Pair Pair ℂ) (1,0) (2,0) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary1021 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (1,0) (2,1)=
      (1:Matrix Pair Pair ℂ) (1,0) (2,1) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary1022 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (1,0) (2,2)=
      (1:Matrix Pair Pair ℂ) (1,0) (2,2) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary10 (u : ℝ) (hp : Transfer.denominator u≠0)
    (hm : Transfer.denominator (-u)≠0) (c d : Fin 3) :
    (normalizedR u*(normalizedR (-u)).transpose) (1,0) (c,d)=
      (1:Matrix Pair Pair ℂ) (1,0) (c,d) := by
  fin_cases c <;> fin_cases d
  · exact unitarityUnitary1000 u hp hm
  · exact unitarityUnitary1001 u hp hm
  · exact unitarityUnitary1002 u hp hm
  · exact unitarityUnitary1010 u hp hm
  · exact unitarityUnitary1011 u hp hm
  · exact unitarityUnitary1012 u hp hm
  · exact unitarityUnitary1020 u hp hm
  · exact unitarityUnitary1021 u hp hm
  · exact unitarityUnitary1022 u hp hm

private lemma unitarityUnitary1100 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (1,1) (0,0)=
      (1:Matrix Pair Pair ℂ) (1,1) (0,0) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary1101 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (1,1) (0,1)=
      (1:Matrix Pair Pair ℂ) (1,1) (0,1) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary1102 (u : ℝ) (hp : Transfer.denominator u≠0)
    (hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (1,1) (0,2)=
      (1:Matrix Pair Pair ℂ) (1,1) (0,2) := by
  have hh := congrFun (congrFun (Transfer.blockZero_unitary u hp hm) (1:Fin 3)) (0:Fin 3)
  simpa [Matrix.one_apply,normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,Fin.sum_univ_two,Transfer.blockOne,Transfer.blockZero] using hh

private lemma unitarityUnitary1110 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (1,1) (1,0)=
      (1:Matrix Pair Pair ℂ) (1,1) (1,0) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary1111 (u : ℝ) (hp : Transfer.denominator u≠0)
    (hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (1,1) (1,1)=
      (1:Matrix Pair Pair ℂ) (1,1) (1,1) := by
  have hh := congrFun (congrFun (Transfer.blockZero_unitary u hp hm) (1:Fin 3)) (1:Fin 3)
  simpa [Matrix.one_apply,normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,Fin.sum_univ_two,Transfer.blockOne,Transfer.blockZero] using hh

private lemma unitarityUnitary1112 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (1,1) (1,2)=
      (1:Matrix Pair Pair ℂ) (1,1) (1,2) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary1120 (u : ℝ) (hp : Transfer.denominator u≠0)
    (hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (1,1) (2,0)=
      (1:Matrix Pair Pair ℂ) (1,1) (2,0) := by
  have hh := congrFun (congrFun (Transfer.blockZero_unitary u hp hm) (1:Fin 3)) (2:Fin 3)
  simpa [Matrix.one_apply,normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,Fin.sum_univ_two,Transfer.blockOne,Transfer.blockZero] using hh

private lemma unitarityUnitary1121 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (1,1) (2,1)=
      (1:Matrix Pair Pair ℂ) (1,1) (2,1) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary1122 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (1,1) (2,2)=
      (1:Matrix Pair Pair ℂ) (1,1) (2,2) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary11 (u : ℝ) (hp : Transfer.denominator u≠0)
    (hm : Transfer.denominator (-u)≠0) (c d : Fin 3) :
    (normalizedR u*(normalizedR (-u)).transpose) (1,1) (c,d)=
      (1:Matrix Pair Pair ℂ) (1,1) (c,d) := by
  fin_cases c <;> fin_cases d
  · exact unitarityUnitary1100 u hp hm
  · exact unitarityUnitary1101 u hp hm
  · exact unitarityUnitary1102 u hp hm
  · exact unitarityUnitary1110 u hp hm
  · exact unitarityUnitary1111 u hp hm
  · exact unitarityUnitary1112 u hp hm
  · exact unitarityUnitary1120 u hp hm
  · exact unitarityUnitary1121 u hp hm
  · exact unitarityUnitary1122 u hp hm

private lemma unitarityUnitary1200 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (1,2) (0,0)=
      (1:Matrix Pair Pair ℂ) (1,2) (0,0) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary1201 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (1,2) (0,1)=
      (1:Matrix Pair Pair ℂ) (1,2) (0,1) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary1202 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (1,2) (0,2)=
      (1:Matrix Pair Pair ℂ) (1,2) (0,2) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary1210 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (1,2) (1,0)=
      (1:Matrix Pair Pair ℂ) (1,2) (1,0) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary1211 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (1,2) (1,1)=
      (1:Matrix Pair Pair ℂ) (1,2) (1,1) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary1212 (u : ℝ) (hp : Transfer.denominator u≠0)
    (hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (1,2) (1,2)=
      (1:Matrix Pair Pair ℂ) (1,2) (1,2) := by
  have hh := congrFun (congrFun (Transfer.blockOne_unitary u hp hm) (0:Fin 2)) (0:Fin 2)
  simpa [Matrix.one_apply,normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,Fin.sum_univ_two,Transfer.blockOne,Transfer.blockZero] using hh

private lemma unitarityUnitary1220 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (1,2) (2,0)=
      (1:Matrix Pair Pair ℂ) (1,2) (2,0) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary1221 (u : ℝ) (hp : Transfer.denominator u≠0)
    (hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (1,2) (2,1)=
      (1:Matrix Pair Pair ℂ) (1,2) (2,1) := by
  have hh := congrFun (congrFun (Transfer.blockOne_unitary u hp hm) (0:Fin 2)) (1:Fin 2)
  simpa [Matrix.one_apply,normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,Fin.sum_univ_two,Transfer.blockOne,Transfer.blockZero] using hh

private lemma unitarityUnitary1222 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (1,2) (2,2)=
      (1:Matrix Pair Pair ℂ) (1,2) (2,2) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary12 (u : ℝ) (hp : Transfer.denominator u≠0)
    (hm : Transfer.denominator (-u)≠0) (c d : Fin 3) :
    (normalizedR u*(normalizedR (-u)).transpose) (1,2) (c,d)=
      (1:Matrix Pair Pair ℂ) (1,2) (c,d) := by
  fin_cases c <;> fin_cases d
  · exact unitarityUnitary1200 u hp hm
  · exact unitarityUnitary1201 u hp hm
  · exact unitarityUnitary1202 u hp hm
  · exact unitarityUnitary1210 u hp hm
  · exact unitarityUnitary1211 u hp hm
  · exact unitarityUnitary1212 u hp hm
  · exact unitarityUnitary1220 u hp hm
  · exact unitarityUnitary1221 u hp hm
  · exact unitarityUnitary1222 u hp hm

private lemma unitarityUnitary2000 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (2,0) (0,0)=
      (1:Matrix Pair Pair ℂ) (2,0) (0,0) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary2001 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (2,0) (0,1)=
      (1:Matrix Pair Pair ℂ) (2,0) (0,1) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary2002 (u : ℝ) (hp : Transfer.denominator u≠0)
    (hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (2,0) (0,2)=
      (1:Matrix Pair Pair ℂ) (2,0) (0,2) := by
  have hh := congrFun (congrFun (Transfer.blockZero_unitary u hp hm) (2:Fin 3)) (0:Fin 3)
  simpa [Matrix.one_apply,normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,Fin.sum_univ_two,Transfer.blockOne,Transfer.blockZero] using hh

private lemma unitarityUnitary2010 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (2,0) (1,0)=
      (1:Matrix Pair Pair ℂ) (2,0) (1,0) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary2011 (u : ℝ) (hp : Transfer.denominator u≠0)
    (hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (2,0) (1,1)=
      (1:Matrix Pair Pair ℂ) (2,0) (1,1) := by
  have hh := congrFun (congrFun (Transfer.blockZero_unitary u hp hm) (2:Fin 3)) (1:Fin 3)
  simpa [Matrix.one_apply,normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,Fin.sum_univ_two,Transfer.blockOne,Transfer.blockZero] using hh

private lemma unitarityUnitary2012 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (2,0) (1,2)=
      (1:Matrix Pair Pair ℂ) (2,0) (1,2) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary2020 (u : ℝ) (hp : Transfer.denominator u≠0)
    (hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (2,0) (2,0)=
      (1:Matrix Pair Pair ℂ) (2,0) (2,0) := by
  have hh := congrFun (congrFun (Transfer.blockZero_unitary u hp hm) (2:Fin 3)) (2:Fin 3)
  simpa [Matrix.one_apply,normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,Fin.sum_univ_two,Transfer.blockOne,Transfer.blockZero] using hh

private lemma unitarityUnitary2021 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (2,0) (2,1)=
      (1:Matrix Pair Pair ℂ) (2,0) (2,1) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary2022 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (2,0) (2,2)=
      (1:Matrix Pair Pair ℂ) (2,0) (2,2) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary20 (u : ℝ) (hp : Transfer.denominator u≠0)
    (hm : Transfer.denominator (-u)≠0) (c d : Fin 3) :
    (normalizedR u*(normalizedR (-u)).transpose) (2,0) (c,d)=
      (1:Matrix Pair Pair ℂ) (2,0) (c,d) := by
  fin_cases c <;> fin_cases d
  · exact unitarityUnitary2000 u hp hm
  · exact unitarityUnitary2001 u hp hm
  · exact unitarityUnitary2002 u hp hm
  · exact unitarityUnitary2010 u hp hm
  · exact unitarityUnitary2011 u hp hm
  · exact unitarityUnitary2012 u hp hm
  · exact unitarityUnitary2020 u hp hm
  · exact unitarityUnitary2021 u hp hm
  · exact unitarityUnitary2022 u hp hm

private lemma unitarityUnitary2100 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (2,1) (0,0)=
      (1:Matrix Pair Pair ℂ) (2,1) (0,0) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary2101 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (2,1) (0,1)=
      (1:Matrix Pair Pair ℂ) (2,1) (0,1) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary2102 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (2,1) (0,2)=
      (1:Matrix Pair Pair ℂ) (2,1) (0,2) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary2110 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (2,1) (1,0)=
      (1:Matrix Pair Pair ℂ) (2,1) (1,0) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary2111 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (2,1) (1,1)=
      (1:Matrix Pair Pair ℂ) (2,1) (1,1) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary2112 (u : ℝ) (hp : Transfer.denominator u≠0)
    (hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (2,1) (1,2)=
      (1:Matrix Pair Pair ℂ) (2,1) (1,2) := by
  have hh := congrFun (congrFun (Transfer.blockOne_unitary u hp hm) (1:Fin 2)) (0:Fin 2)
  simpa [Matrix.one_apply,normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,Fin.sum_univ_two,Transfer.blockOne,Transfer.blockZero] using hh

private lemma unitarityUnitary2120 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (2,1) (2,0)=
      (1:Matrix Pair Pair ℂ) (2,1) (2,0) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary2121 (u : ℝ) (hp : Transfer.denominator u≠0)
    (hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (2,1) (2,1)=
      (1:Matrix Pair Pair ℂ) (2,1) (2,1) := by
  have hh := congrFun (congrFun (Transfer.blockOne_unitary u hp hm) (1:Fin 2)) (1:Fin 2)
  simpa [Matrix.one_apply,normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,Fin.sum_univ_two,Transfer.blockOne,Transfer.blockZero] using hh

private lemma unitarityUnitary2122 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (2,1) (2,2)=
      (1:Matrix Pair Pair ℂ) (2,1) (2,2) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary21 (u : ℝ) (hp : Transfer.denominator u≠0)
    (hm : Transfer.denominator (-u)≠0) (c d : Fin 3) :
    (normalizedR u*(normalizedR (-u)).transpose) (2,1) (c,d)=
      (1:Matrix Pair Pair ℂ) (2,1) (c,d) := by
  fin_cases c <;> fin_cases d
  · exact unitarityUnitary2100 u hp hm
  · exact unitarityUnitary2101 u hp hm
  · exact unitarityUnitary2102 u hp hm
  · exact unitarityUnitary2110 u hp hm
  · exact unitarityUnitary2111 u hp hm
  · exact unitarityUnitary2112 u hp hm
  · exact unitarityUnitary2120 u hp hm
  · exact unitarityUnitary2121 u hp hm
  · exact unitarityUnitary2122 u hp hm

private lemma unitarityUnitary2200 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (2,2) (0,0)=
      (1:Matrix Pair Pair ℂ) (2,2) (0,0) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary2201 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (2,2) (0,1)=
      (1:Matrix Pair Pair ℂ) (2,2) (0,1) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary2202 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (2,2) (0,2)=
      (1:Matrix Pair Pair ℂ) (2,2) (0,2) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary2210 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (2,2) (1,0)=
      (1:Matrix Pair Pair ℂ) (2,2) (1,0) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary2211 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (2,2) (1,1)=
      (1:Matrix Pair Pair ℂ) (2,2) (1,1) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary2212 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (2,2) (1,2)=
      (1:Matrix Pair Pair ℂ) (2,2) (1,2) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary2220 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (2,2) (2,0)=
      (1:Matrix Pair Pair ℂ) (2,2) (2,0) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary2221 (u : ℝ) (_hp : Transfer.denominator u≠0)
    (_hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (2,2) (2,1)=
      (1:Matrix Pair Pair ℂ) (2,2) (2,1) := by
  simp [normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,]

private lemma unitarityUnitary2222 (u : ℝ) (hp : Transfer.denominator u≠0)
    (hm : Transfer.denominator (-u)≠0) :
    (normalizedR u*(normalizedR (-u)).transpose) (2,2) (2,2)=
      (1:Matrix Pair Pair ℂ) (2,2) (2,2) := by
  have hh : (Transfer.c u:ℂ)*Transfer.c (-u)=1 := by
    exact_mod_cast Transfer.c_unitary u hp hm
  simpa [Matrix.one_apply,normalizedR,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,Fin.sum_univ_two,Transfer.blockOne,Transfer.blockZero] using hh

private lemma unitarityUnitary22 (u : ℝ) (hp : Transfer.denominator u≠0)
    (hm : Transfer.denominator (-u)≠0) (c d : Fin 3) :
    (normalizedR u*(normalizedR (-u)).transpose) (2,2) (c,d)=
      (1:Matrix Pair Pair ℂ) (2,2) (c,d) := by
  fin_cases c <;> fin_cases d
  · exact unitarityUnitary2200 u hp hm
  · exact unitarityUnitary2201 u hp hm
  · exact unitarityUnitary2202 u hp hm
  · exact unitarityUnitary2210 u hp hm
  · exact unitarityUnitary2211 u hp hm
  · exact unitarityUnitary2212 u hp hm
  · exact unitarityUnitary2220 u hp hm
  · exact unitarityUnitary2221 u hp hm
  · exact unitarityUnitary2222 u hp hm
theorem spectral_unitarity (u : ℝ) (hp : Q u≠0) (hm : Q (-u)≠0) :
    spectralR u*(spectralR (-u)).transpose=1 := by
  rw [spectralR_normalized u hp,spectralR_normalized (-u) hm]
  have hpr : Transfer.denominator u≠0 := by
    intro h;apply hp;rw [←denominator_binding,h];simp
  have hmr : Transfer.denominator (-u)≠0 := by
    intro h;apply hm;rw [←denominator_binding,h];simp
  ext ⟨a,b⟩ ⟨c,d⟩
  fin_cases a <;> fin_cases b
  · exact unitarityUnitary00 u hpr hmr c d
  · exact unitarityUnitary01 u hpr hmr c d
  · exact unitarityUnitary02 u hpr hmr c d
  · exact unitarityUnitary10 u hpr hmr c d
  · exact unitarityUnitary11 u hpr hmr c d
  · exact unitarityUnitary12 u hpr hmr c d
  · exact unitarityUnitary20 u hpr hmr c d
  · exact unitarityUnitary21 u hpr hmr c d
  · exact unitarityUnitary22 u hpr hmr c d
end CriticalHoneycomb.Transfer.Reflection

end

section
namespace CriticalHoneycomb.Transfer.Reflection
open scoped Matrix BigOperators
abbrev FourVector := Spin3→Spin3→Spin3→Spin3→ℂ
noncomputable def actAD (R : Matrix Pair Pair ℂ) (V : FourVector)
    (i m j n : Spin3) : ℂ := (R*ᵥ(fun p : Pair=>V p.1 m j p.2)) (i,n)
noncomputable def actBD (R : Matrix Pair Pair ℂ) (V : FourVector)
    (i m j n : Spin3) : ℂ := (R*ᵥ(fun p : Pair=>V i p.1 j p.2)) (m,n)
noncomputable def actBC (R : Matrix Pair Pair ℂ) (V : FourVector)
    (i m j n : Spin3) : ℂ := (R*ᵥ(fun p : Pair=>V i p.1 p.2 n)) (m,j)
noncomputable def pairVector (A B : Matrix Spin3 Spin3 ℂ) : FourVector :=
  fun i m j n=>boundaryVector A (i,m)*boundaryVector B (j,n)
lemma actBD_transpose (R : Matrix Pair Pair ℂ) (V : FourVector) :
    actBD Rᵀ V=actBDt R V := by
  funext i m j n
  simp only [actBD,actBDt,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,Matrix.transpose_apply]
lemma BC_pairVector (R : Matrix Pair Pair ℂ) (A B : Matrix Spin3 Spin3 ℂ) :
    actBC R (pairVector A B)=crossedBC R A B := by
  funext i m j n
  simp only [actBC,crossedBC,pairVector,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,mul_assoc]
lemma ADt_pairVector (R : Matrix Pair Pair ℂ) (A B : Matrix Spin3 Spin3 ℂ) :
    actAD Rᵀ (pairVector A B)=crossedADt R A B := by
  funext i m j n
  simp only [actAD,crossedADt,pairVector,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,
    Matrix.transpose_apply,mul_assoc]
lemma actAD_comp (R S : Matrix Pair Pair ℂ) (V : FourVector) :
    actAD R (actAD S V)=actAD (R*S) V := by
  funext i m j n
  exact congrFun (Matrix.mulVec_mulVec (fun p : Pair=>V p.1 m j p.2) R S) (i,n)
lemma actBD_comp (R S : Matrix Pair Pair ℂ) (V : FourVector) :
    actBD R (actBD S V)=actBD (R*S) V := by
  funext i m j n
  exact congrFun (Matrix.mulVec_mulVec (fun p : Pair=>V i p.1 j p.2) R S) (m,n)
lemma actAD_one (V : FourVector) : actAD 1 V=V := by
  funext i m j n
  simp [actAD]
lemma actBD_one (V : FourVector) : actBD 1 V=V := by
  funext i m j n
  simp [actBD]
lemma actAD_add (R : Matrix Pair Pair ℂ) (V W : FourVector) :
    actAD R (V+W)=actAD R V+actAD R W := by
  funext i m j n
  simp [actAD,Matrix.mulVec,dotProduct,mul_add,Finset.sum_add_distrib]
lemma actBD_add (R : Matrix Pair Pair ℂ) (V W : FourVector) :
    actBD R (V+W)=actBD R V+actBD R W := by
  funext i m j n
  simp [actBD,Matrix.mulVec,dotProduct,mul_add,Finset.sum_add_distrib]
lemma actBC_add (R : Matrix Pair Pair ℂ) (V W : FourVector) :
    actBC R (V+W)=actBC R V+actBC R W := by
  funext i m j n
  simp [actBC,Matrix.mulVec,dotProduct,mul_add,Finset.sum_add_distrib]
lemma actAC_add (R : Matrix Pair Pair ℂ) (V W : FourVector) :
    actAC R (V+W)=actAC R V+actAC R W := by
  funext i m j n
  simp [actAC,mul_add,Finset.sum_add_distrib]

noncomputable def fourExchanges (t y : ℝ) (V : FourVector) : FourVector :=
  actAD (spectralR (-(b-(t+y))))
    (actBD (spectralR (-(t-y)))
      (actAC (spectralR (t-y)) (actBC (spectralR (b-(t+y))) V)))

theorem source_boundary_invariant_constant (t y : ℝ)
    (hm : Q (t-y)≠0) (hp : Q (t+y)≠0)
    (hnm : Q (-(t-y))≠0) (hnp : Q (-(b-(t+y)))≠0)
    (ht : sine (gamma+t)≠0) (hy : sine (gamma+y)≠0) :
    fourExchanges t y (pairVector (boundary0 t) (boundary0 y))=pairVector (boundary0 t) (boundary0 y) := by
  have hU₁ : spectralR (-(t-y))*(spectralR (t-y))ᵀ=1 := by
    simpa only [neg_neg] using spectral_unitarity (-(t-y)) hnm (by simpa only [neg_neg] using hm)
  have hU₂ : spectralR (-(b-(t+y)))*(spectralR (b-(t+y)))ᵀ=1 := by
    simpa only [neg_neg] using spectral_unitarity (-(b-(t+y))) hnp
      (by simpa only [neg_neg,reflected_Q] using hp)
  have hI : actAC (spectralR (t-y)) (actBC (spectralR (b-(t+y))) (pairVector (boundary0 t) (boundary0 y)))=
      actBD (spectralR (t-y))ᵀ (actAD (spectralR (b-(t+y)))ᵀ (pairVector (boundary0 t) (boundary0 y))) := by
    simpa only [actBC_add,actAC_add,actAD_add,actBD_add,BC_pairVector,
      ADt_pairVector,actBD_transpose] using source_boundary_pair_constant t y hm hp ht hy
  unfold fourExchanges
  rw [hI,actBD_comp,hU₁,actBD_one,actAD_comp,hU₂,actAD_one]

theorem source_boundary_invariant_linear (t y : ℝ)
    (hm : Q (t-y)≠0) (hp : Q (t+y)≠0)
    (hnm : Q (-(t-y))≠0) (hnp : Q (-(b-(t+y)))≠0)
    (ht : sine (gamma+t)≠0) (hy : sine (gamma+y)≠0) :
    fourExchanges t y (pairVector (boundary1 t) (boundary0 y)+pairVector (boundary0 t) (boundary1 y))=(pairVector (boundary1 t) (boundary0 y)+pairVector (boundary0 t) (boundary1 y)) := by
  have hU₁ : spectralR (-(t-y))*(spectralR (t-y))ᵀ=1 := by
    simpa only [neg_neg] using spectral_unitarity (-(t-y)) hnm (by simpa only [neg_neg] using hm)
  have hU₂ : spectralR (-(b-(t+y)))*(spectralR (b-(t+y)))ᵀ=1 := by
    simpa only [neg_neg] using spectral_unitarity (-(b-(t+y))) hnp
      (by simpa only [neg_neg,reflected_Q] using hp)
  have hI : actAC (spectralR (t-y)) (actBC (spectralR (b-(t+y))) (pairVector (boundary1 t) (boundary0 y)+pairVector (boundary0 t) (boundary1 y)))=
      actBD (spectralR (t-y))ᵀ (actAD (spectralR (b-(t+y)))ᵀ (pairVector (boundary1 t) (boundary0 y)+pairVector (boundary0 t) (boundary1 y))) := by
    simpa only [actBC_add,actAC_add,actAD_add,actBD_add,BC_pairVector,
      ADt_pairVector,actBD_transpose] using source_boundary_pair_linear t y hm hp ht hy
  unfold fourExchanges
  rw [hI,actBD_comp,hU₁,actBD_one,actAD_comp,hU₂,actAD_one]
end CriticalHoneycomb.Transfer.Reflection

end

section
namespace CriticalHoneycomb.Transfer.Reflection
open scoped Matrix BigOperators
noncomputable def pair4 (V W : FourVector) : ℂ :=
  ∑ i,∑ m,∑ j,∑ n,V i m j n*W i m j n
lemma pair4_AD (V W : FourVector) : pair4 V W=
    ∑ m,∑ j,(fun p : Pair=>V p.1 m j p.2) ⬝ᵥ (fun p : Pair=>W p.1 m j p.2) := by
  simp only [pair4,dotProduct,Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl;intro m hm
  rw [Finset.sum_comm]
lemma pair4_BD (V W : FourVector) : pair4 V W=
    ∑ i,∑ j,(fun p : Pair=>V i p.1 j p.2) ⬝ᵥ (fun p : Pair=>W i p.1 j p.2) := by
  simp only [pair4,dotProduct,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl;intro i hi
  rw [Finset.sum_comm]
lemma pair4_AC (V W : FourVector) : pair4 V W=
    ∑ m,∑ n,(fun p : Pair=>V p.1 m p.2 n) ⬝ᵥ (fun p : Pair=>W p.1 m p.2 n) := by
  simp only [pair4,dotProduct,Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl;intro m hm
  simp_rw [Finset.sum_comm (s:=Finset.univ) (t:=Finset.univ) (f:=fun j n : Spin3=> V _ m j n*W _ m j n)]
  rw [Finset.sum_comm]
lemma pair4_BC (V W : FourVector) : pair4 V W=
    ∑ i,∑ n,(fun p : Pair=>V i p.1 p.2 n) ⬝ᵥ (fun p : Pair=>W i p.1 p.2 n) := by
  simp only [pair4,dotProduct,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl;intro i hi
  simp_rw [Finset.sum_comm (s:=Finset.univ) (t:=Finset.univ) (f:=fun j n : Spin3=> V i _ j n*W i _ j n)]
  rw [Finset.sum_comm]
lemma dot_pair_cancel (R S : Matrix Pair Pair ℂ) (h : Rᵀ*S=1) (x y : Pair→ℂ) :
    (R*ᵥx) ⬝ᵥ (S*ᵥy)=x ⬝ᵥ y := by
  rw [Matrix.dotProduct_mulVec,←Matrix.vecMul_transpose,Matrix.vecMul_vecMul,h,Matrix.vecMul_one]
lemma pair4_AD_cancel (R S : Matrix Pair Pair ℂ) (h : Rᵀ*S=1) (V W : FourVector) :
    pair4 (actAD R V) (actAD S W)=pair4 V W := by
  rw [pair4_AD,pair4_AD]
  apply Finset.sum_congr rfl;intro m hm
  apply Finset.sum_congr rfl;intro j hj
  exact dot_pair_cancel R S h _ _
lemma pair4_BD_cancel (R S : Matrix Pair Pair ℂ) (h : Rᵀ*S=1) (V W : FourVector) :
    pair4 (actBD R V) (actBD S W)=pair4 V W := by
  rw [pair4_BD,pair4_BD]
  apply Finset.sum_congr rfl;intro i hi
  apply Finset.sum_congr rfl;intro j hj
  exact dot_pair_cancel R S h _ _
lemma pair4_AC_cancel (R S : Matrix Pair Pair ℂ) (h : Rᵀ*S=1) (V W : FourVector) :
    pair4 (actAC R V) (actAC S W)=pair4 V W := by
  rw [pair4_AC,pair4_AC]
  apply Finset.sum_congr rfl;intro m hm
  apply Finset.sum_congr rfl;intro n hn
  simpa only [Matrix.mulVec,dotProduct,Fintype.sum_prod_type,actAC] using dot_pair_cancel R S h
    (fun p : Pair=>V p.1 m p.2 n) (fun p : Pair=>W p.1 m p.2 n)
lemma pair4_BC_cancel (R S : Matrix Pair Pair ℂ) (h : Rᵀ*S=1) (V W : FourVector) :
    pair4 (actBC R V) (actBC S W)=pair4 V W := by
  rw [pair4_BC,pair4_BC]
  apply Finset.sum_congr rfl;intro i hi
  apply Finset.sum_congr rfl;intro n hn
  exact dot_pair_cancel R S h _ _
lemma spectral_transpose_unitarity (u : ℝ) (hu : Q u≠0) (hn : Q (-u)≠0) :
    (spectralR (-u))ᵀ*spectralR u=1 :=
  mul_eq_one_comm.mp (spectral_unitarity u hu hn)

theorem four_exchanges_pair (t y : ℝ) (V W : FourVector)
    (hm : Q (t-y)≠0) (hp : Q (t+y)≠0)
    (hnm : Q (-(t-y))≠0) (hnp : Q (-(b-(t+y)))≠0) :
    pair4 (fourExchanges (b-t) (b-y) V) (fourExchanges t y W)=pair4 V W := by
  have e₁ : (b-t)-(b-y)=-(t-y) := by ring
  have e₂ : b-((b-t)+(b-y))=-(b-(t+y)) := by ring
  have hp' : Q (b-(t+y))≠0 := by simpa only [reflected_Q] using hp
  simp only [fourExchanges,e₁,e₂,neg_neg]
  rw [pair4_AD_cancel _ _ (by simpa only [neg_neg] using spectral_transpose_unitarity (-(b-(t+y))) hnp (by simpa only [neg_neg] using hp')),
      pair4_BD_cancel _ _ (by simpa only [neg_neg] using spectral_transpose_unitarity (-(t-y)) hnm (by simpa only [neg_neg] using hm)),
      pair4_AC_cancel _ _ (spectral_transpose_unitarity (t-y) hm hnm),
      pair4_BC_cancel _ _ (spectral_transpose_unitarity (b-(t+y)) hp' hnp)]

theorem source_left_covector_constant (t y : ℝ) (W : FourVector)
    (hm : Q (t-y)≠0) (hp : Q (t+y)≠0)
    (hnm : Q (-(t-y))≠0) (hnp : Q (-(b-(t+y)))≠0)
    (ht : sine (gamma+(b-t))≠0) (hy : sine (gamma+(b-y))≠0) :
    pair4 (pairVector (boundary0 (b-t)) (boundary0 (b-y))) (fourExchanges t y W)=pair4 (pairVector (boundary0 (b-t)) (boundary0 (b-y))) W := by
  have e₁ : (b-t)-(b-y)=-(t-y) := by ring
  have e₂ : b-((b-t)+(b-y))=-(b-(t+y)) := by ring
  have hsum : Q ((b-t)+(b-y))≠0 := by
    rw [←reflected_Q ((b-t)+(b-y)),e₂]
    exact hnp
  have hn : Q (-(b-((b-t)+(b-y))))≠0 := by
    simpa only [e₂,neg_neg,reflected_Q] using hp
  have hleft:=source_boundary_invariant_constant (b-t) (b-y)
    (by simpa only [e₁] using hnm) hsum
    (by simpa only [e₁,neg_neg] using hm) hn ht hy
  have h:=four_exchanges_pair t y (pairVector (boundary0 (b-t)) (boundary0 (b-y))) W hm hp hnm hnp
  rw [hleft] at h
  exact h

theorem source_left_covector_linear (t y : ℝ) (W : FourVector)
    (hm : Q (t-y)≠0) (hp : Q (t+y)≠0)
    (hnm : Q (-(t-y))≠0) (hnp : Q (-(b-(t+y)))≠0)
    (ht : sine (gamma+(b-t))≠0) (hy : sine (gamma+(b-y))≠0) :
    pair4 ((pairVector (boundary1 (b-t)) (boundary0 (b-y))+pairVector (boundary0 (b-t)) (boundary1 (b-y)))) (fourExchanges t y W)=pair4 ((pairVector (boundary1 (b-t)) (boundary0 (b-y))+pairVector (boundary0 (b-t)) (boundary1 (b-y)))) W := by
  have e₁ : (b-t)-(b-y)=-(t-y) := by ring
  have e₂ : b-((b-t)+(b-y))=-(b-(t+y)) := by ring
  have hsum : Q ((b-t)+(b-y))≠0 := by
    rw [←reflected_Q ((b-t)+(b-y)),e₂]
    exact hnp
  have hn : Q (-(b-((b-t)+(b-y))))≠0 := by
    simpa only [e₂,neg_neg,reflected_Q] using hp
  have hleft:=source_boundary_invariant_linear (b-t) (b-y)
    (by simpa only [e₁] using hnm) hsum
    (by simpa only [e₁,neg_neg] using hm) hn ht hy
  have h:=four_exchanges_pair t y ((pairVector (boundary1 (b-t)) (boundary0 (b-y))+pairVector (boundary0 (b-t)) (boundary1 (b-y)))) W hm hp hnm hnp
  rw [hleft] at h
  exact h
end CriticalHoneycomb.Transfer.Reflection

end

section

namespace CriticalHoneycomb.Transfer.ClosedFourRow
open Reflection
open scoped Matrix BigOperators
noncomputable def flatten4 (V : FourVector) : Aux Spin3 → ℂ :=
  fun p => V p.1 p.2.1 p.2.2.1 p.2.2.2
noncomputable def unflatten4 (v : Aux Spin3 → ℂ) : FourVector :=
  fun a b c d => v (a,b,c,d)
lemma flatten_unflatten (v : Aux Spin3 → ℂ) : flatten4 (unflatten4 v)=v := rfl
lemma flatten_add (V W : FourVector) : flatten4 (V+W)=flatten4 V+flatten4 W := rfl
lemma flattenBC (R : Matrix Pair Pair ℂ) (V : FourVector) :
    auxBC R *ᵥ flatten4 V = flatten4 (actBC R V) := by
  funext ⟨a,b,c,d⟩
  simp [auxBC,flatten4,actBC,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,
    Matrix.one_apply,mul_ite,ite_mul]
lemma flattenAC (R : Matrix Pair Pair ℂ) (V : FourVector) :
    auxAC R *ᵥ flatten4 V = flatten4 (actAC R V) := by
  funext ⟨a,b,c,d⟩
  simp [auxAC,flatten4,actAC,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,
    Matrix.one_apply,mul_ite,ite_mul]
lemma flattenBD (R : Matrix Pair Pair ℂ) (V : FourVector) :
    auxBD R *ᵥ flatten4 V = flatten4 (actBD R V) := by
  funext ⟨a,b,c,d⟩
  simp [auxBD,flatten4,actBD,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,
    Matrix.one_apply,mul_ite,ite_mul]
lemma flattenAD (R : Matrix Pair Pair ℂ) (V : FourVector) :
    auxAD R *ᵥ flatten4 V = flatten4 (actAD R V) := by
  funext ⟨a,b,c,d⟩
  simp [auxAD,flatten4,actAD,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,
    Matrix.one_apply,mul_ite,ite_mul]
noncomputable def exactTrain (t y : ℝ) : Matrix (Aux Spin3) (Aux Spin3) ℂ :=
  auxTrain (spectralR (b-(t+y))) (spectralR (t-y))
    (spectralR (-(t-y))) (spectralR (-(b-(t+y))))
lemma exactTrain_action (t y : ℝ) (V : FourVector) :
    exactTrain t y *ᵥ flatten4 V = flatten4 (fourExchanges t y V) := by
  simp only [exactTrain,auxTrain,←Matrix.mulVec_mulVec,flattenBC,flattenAC,flattenBD,
    flattenAD,fourExchanges]
lemma pair4_flatten (V W : FourVector) :
    pair4 V W = flatten4 V ⬝ᵥ flatten4 W := by
  simp [pair4,flatten4,dotProduct,Fintype.sum_prod_type]

theorem exactTrain_right_constant (t y : ℝ)
    (hm : Q (t-y)≠0) (hp : Q (t+y)≠0)
    (hnm : Q (-(t-y))≠0) (hnp : Q (-(b-(t+y)))≠0)
    (ht : sine (gamma+t)≠0) (hy : sine (gamma+y)≠0) :
    exactTrain t y *ᵥ flatten4 (pairVector (boundary0 t) (boundary0 y)) =
      flatten4 (pairVector (boundary0 t) (boundary0 y)) := by
  rw [exactTrain_action,source_boundary_invariant_constant t y hm hp hnm hnp ht hy]
theorem exactTrain_right_linear (t y : ℝ)
    (hm : Q (t-y)≠0) (hp : Q (t+y)≠0)
    (hnm : Q (-(t-y))≠0) (hnp : Q (-(b-(t+y)))≠0)
    (ht : sine (gamma+t)≠0) (hy : sine (gamma+y)≠0) :
    exactTrain t y *ᵥ flatten4
      (pairVector (boundary1 t) (boundary0 y)+pairVector (boundary0 t) (boundary1 y)) =
    flatten4 (pairVector (boundary1 t) (boundary0 y)+pairVector (boundary0 t) (boundary1 y)) := by
  rw [exactTrain_action,source_boundary_invariant_linear t y hm hp hnm hnp ht hy]
lemma vecMul_eq_of_pair4 (t y : ℝ) (V : FourVector)
    (h : ∀ W, pair4 V (fourExchanges t y W)=pair4 V W) :
    flatten4 V ᵥ* exactTrain t y = flatten4 V := by
  funext p
  have hh := h (unflatten4 (Pi.single p 1))
  rw [pair4_flatten,pair4_flatten,←exactTrain_action,flatten_unflatten,
    Matrix.dotProduct_mulVec,dotProduct_single_one,dotProduct_single_one] at hh
  exact hh

theorem exactTrain_left_constant (t y : ℝ)
    (hm : Q (t-y)≠0) (hp : Q (t+y)≠0)
    (hnm : Q (-(t-y))≠0) (hnp : Q (-(b-(t+y)))≠0)
    (ht : sine (gamma+(b-t))≠0) (hy : sine (gamma+(b-y))≠0) :
    flatten4 (pairVector (boundary0 (b-t)) (boundary0 (b-y))) ᵥ* exactTrain t y =
      flatten4 (pairVector (boundary0 (b-t)) (boundary0 (b-y))) := by
  apply vecMul_eq_of_pair4
  intro W
  exact source_left_covector_constant t y W hm hp hnm hnp ht hy
theorem exactTrain_left_linear (t y : ℝ)
    (hm : Q (t-y)≠0) (hp : Q (t+y)≠0)
    (hnm : Q (-(t-y))≠0) (hnp : Q (-(b-(t+y)))≠0)
    (ht : sine (gamma+(b-t))≠0) (hy : sine (gamma+(b-y))≠0) :
    flatten4 (pairVector (boundary1 (b-t)) (boundary0 (b-y))+
      pairVector (boundary0 (b-t)) (boundary1 (b-y))) ᵥ* exactTrain t y =
    flatten4 (pairVector (boundary1 (b-t)) (boundary0 (b-y))+
      pairVector (boundary0 (b-t)) (boundary1 (b-y))) := by
  apply vecMul_eq_of_pair4
  intro W
  exact source_left_covector_linear t y W hm hp hnm hnp ht hy
end CriticalHoneycomb.Transfer.ClosedFourRow

end

end OAI
