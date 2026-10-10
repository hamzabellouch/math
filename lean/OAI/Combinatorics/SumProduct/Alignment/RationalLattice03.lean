import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RationalLattice02
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
open _root_.Polynomial _root_.OAI.Polynomial
noncomputable section
end
end
 

 
section
open _root_.Polynomial _root_.OAI.Polynomial
noncomputable section
namespace RationalLattice
variable {G : Type*} [Group G] [TopologicalSpace G] {n : ℕ}
variable (c : RealCoordinates G n)

 
lemma realPower_mem_of_coordinates (H : Subgroup G) (I : Set (Fin n))
    (hH : ∀ g : G, g ∈ H ↔ ∀ i ∈ I, c.coord g i = 0)
    {g : G} (hg : g ∈ H) (t : ℝ) : realPower c g t ∈ H := by
  apply (hH _).mpr
  intro i hi
  rw [realPower_coord]
  have hp : powerPolynomial c g i = 0 := by
    apply Polynomial.eq_of_eval_nat_eq
    intro m
    rw [powerPolynomial_nat,Polynomial.eval_zero]
    exact (hH (g^m)).mp (H.pow_mem hg m) i hi
  simp [hp]

def characterPower (χ : G →* Multiplicative ℝ) (g : G) : ℝ →+ ℝ where
  toFun t := Multiplicative.toAdd (χ (realPower c g t))
  map_zero' := by simp
  map_add' s t := by rw [realPower_add,map_mul]; rfl

lemma character_realPower (χ : G →* Multiplicative ℝ) (hχ : Continuous χ)
    (g : G) (t : ℝ) :
    Multiplicative.toAdd (χ (realPower c g t)) = t * Multiplicative.toAdd (χ g) := by
  have hc : Continuous (characterPower c χ g) := hχ.comp (realPower_continuous c g)
  have h := map_real_smul (characterPower c χ g) hc t 1
  simpa [characterPower] using h

include c in
 

theorem character_kernel_pathConnected (χ : G →* Multiplicative ℝ) (hχ : Continuous χ) :
    IsPathConnected (χ.ker : Set G) := by
  refine ⟨1,χ.ker.one_mem,?_⟩
  intro g hg
  let p : Path (1:G) g :=
    { toFun := fun t => realPower c g t
      continuous_toFun := (realPower_continuous c g).comp continuous_subtype_val
      source' := by simp
      target' := by simp }
  refine ⟨p,?_⟩
  intro t
  change χ (realPower c g t) = 1
  apply Multiplicative.toAdd.injective
  rw [character_realPower c χ hχ]
  change χ g = 1 at hg
  simp [hg]

 
theorem character_kernel_inter_pathConnected (χ : G →* Multiplicative ℝ)
    (hχ : Continuous χ) (H : Subgroup G) (I : Set (Fin n))
    (hH : ∀ g : G, g ∈ H ↔ ∀ i ∈ I, c.coord g i = 0) :
    IsPathConnected ((H ⊓ χ.ker : Subgroup G) : Set G) := by
  refine ⟨1,(H ⊓ χ.ker).one_mem,?_⟩
  intro g hg
  let p : Path (1:G) g :=
    { toFun := fun t => realPower c g t
      continuous_toFun := (realPower_continuous c g).comp continuous_subtype_val
      source' := by simp
      target' := by simp }
  refine ⟨p,?_⟩
  intro t
  refine ⟨realPower_mem_of_coordinates c H I hH hg.1 t,?_⟩
  change χ (realPower c g t) = 1
  apply Multiplicative.toAdd.injective
  rw [character_realPower c χ hχ]
  have hg' : χ g = 1 := hg.2
  simp [hg']

end RationalLattice
end
end
 

 
section
open _root_.Polynomial _root_.OAI.Polynomial
noncomputable section
namespace RationalLattice
variable {G : Type*} [Group G] [TopologicalSpace G] {n : ℕ}
variable (c : RealCoordinates G n)

lemma parameterEval_continuous (P : MvPolynomial (Fin n) ℚ) :
    Continuous (fun x : Fin n → ℝ => parameterEval x P) := by
  simpa only [parameterEval,MvPolynomial.coe_eval₂Hom,MvPolynomial.eval₂_eq_eval_map] using
    (MvPolynomial.continuous_eval (P.map (algebraMap ℚ ℝ)))

lemma paramPoly_continuous (P : ParamPoly n) :
    Continuous (fun v : (Fin n → ℝ) × ℝ => P.eval₂ (parameterEval v.1) v.2) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.eval₂_add,Pi.add_apply] using hp.fun_add hq
  | monomial i a =>
    simpa only [Polynomial.eval₂_monomial,Pi.mul_apply,Pi.pow_apply,Function.comp_apply] using
      ((parameterEval_continuous a).comp continuous_fst).fun_mul (continuous_snd.fun_pow i)

 

theorem realPower_joint_continuous : Continuous (fun v : G × ℝ => realPower c v.1 v.2) := by
  have h (v : G × ℝ) : realPower c v.1 v.2 =
      c.coord.symm (fun i => (universalPowerPolynomial c i).eval₂
        (parameterEval (c.coord v.1)) v.2) := by
    apply c.coord.injective
    funext i
    simp [realPower_coord_universal]
  simp_rw [h]
  apply c.coord.symm.continuous.comp
  apply continuous_pi
  intro i
  exact (paramPoly_continuous _).comp ((c.coord.continuous.comp continuous_fst).prodMk continuous_snd)

include c in
 

theorem contractible_of_realPower_closed (S : Set G) (h1 : (1:G) ∈ S)
    (hS : ∀ g ∈ S, ∀ t : ℝ, realPower c g t ∈ S) : ContractibleSpace S := by
  apply (contractible_iff_id_nullhomotopic S).mpr
  refine ⟨⟨1,h1⟩,⟨?_⟩⟩
  refine
    { toFun := fun v => ⟨realPower c v.2.val (1-(v.1:ℝ)),hS _ v.2.property _⟩
      continuous_toFun := ?_
      map_zero_left := ?_
      map_one_left := ?_ }
  · apply Continuous.subtype_mk
    exact (realPower_joint_continuous c).comp
      ((continuous_subtype_val.comp continuous_snd).prodMk
        (continuous_const.sub (continuous_subtype_val.comp continuous_fst)))
  · intro g
    apply Subtype.ext
    simp
  · intro g
    apply Subtype.ext
    simp

include c in
 
theorem character_kernel_contractible (χ : G →* Multiplicative ℝ) (hχ : Continuous χ) :
    ContractibleSpace χ.ker := by
  apply contractible_of_realPower_closed c (χ.ker:Set G) χ.ker.one_mem
  intro g hg t
  change χ (realPower c g t) = 1
  apply Multiplicative.toAdd.injective
  rw [character_realPower c χ hχ]
  change χ g = 1 at hg
  simp [hg]

 

theorem character_kernel_inter_contractible (χ : G →* Multiplicative ℝ)
    (hχ : Continuous χ) (H : Subgroup G) (I : Set (Fin n))
    (hH : ∀ g : G, g ∈ H ↔ ∀ i ∈ I, c.coord g i = 0) :
    ContractibleSpace ↥(H ⊓ χ.ker) := by
  apply contractible_of_realPower_closed c ((H ⊓ χ.ker : Subgroup G):Set G) (H ⊓ χ.ker).one_mem
  intro g hg t
  refine ⟨realPower_mem_of_coordinates c H I hH hg.1 t,?_⟩
  change χ (realPower c g t) = 1
  apply Multiplicative.toAdd.injective
  rw [character_realPower c χ hχ]
  have hg' : χ g = 1 := hg.2
  simp [hg']

end RationalLattice

namespace RationalLattice
variable {G : Type*} [Group G] [TopologicalSpace G] {n : ℕ}
variable (c : RealCoordinates G n) (H : Subgroup G) (I : Set (Fin n))
variable (hH : ∀ g : G, g ∈ H ↔ ∀ i ∈ I, c.coord g i = 0)

def subgroupRealPower (g : H) (t : ℝ) : H :=
  ⟨realPower c g t,realPower_mem_of_coordinates c H I hH g.property t⟩

lemma subgroupRealPower_continuous (g : H) : Continuous (subgroupRealPower c H I hH g) :=
  (realPower_continuous c g).subtype_mk _

lemma subgroupRealPower_zero (g : H) : subgroupRealPower c H I hH g 0 = 1 := by
  apply Subtype.ext
  exact realPower_zero c g
lemma subgroupRealPower_one (g : H) : subgroupRealPower c H I hH g 1 = g := by
  apply Subtype.ext
  exact realPower_one c g
lemma subgroupRealPower_add (g : H) (s t : ℝ) :
    subgroupRealPower c H I hH g (s+t) =
      subgroupRealPower c H I hH g s * subgroupRealPower c H I hH g t := by
  apply Subtype.ext
  exact realPower_add c g s t

def subgroupCharacterPower (χ : H →* Multiplicative ℝ) (g : H) : ℝ →+ ℝ where
  toFun t := Multiplicative.toAdd (χ (subgroupRealPower c H I hH g t))
  map_zero' := by rw [subgroupRealPower_zero,map_one]; rfl
  map_add' s t := by rw [subgroupRealPower_add,map_mul]; rfl

lemma character_subgroupRealPower (χ : H →* Multiplicative ℝ) (hχ : Continuous χ)
    (g : H) (t : ℝ) :
    Multiplicative.toAdd (χ (subgroupRealPower c H I hH g t)) =
      t * Multiplicative.toAdd (χ g) := by
  have hc : Continuous (subgroupCharacterPower c H I hH χ g) :=
    hχ.comp (subgroupRealPower_continuous c H I hH g)
  have he := map_real_smul (subgroupCharacterPower c H I hH χ g) hc t 1
  simpa [subgroupCharacterPower,subgroupRealPower_one] using he

include hH in
lemma realPower_mem_mapped_kernel (χ : H →* Multiplicative ℝ) (hχ : Continuous χ)
    {g : G} (hg : g ∈ χ.ker.map H.subtype) (t : ℝ) :
    realPower c g t ∈ χ.ker.map H.subtype := by
  obtain ⟨u,hu,rfl⟩ := hg
  refine ⟨subgroupRealPower c H I hH u t,?_,rfl⟩
  change χ (subgroupRealPower c H I hH u t) = 1
  apply Multiplicative.toAdd.injective
  rw [character_subgroupRealPower c H I hH χ hχ]
  change χ u = 1 at hu
  simp [hu]

include hH in
 

theorem lower_kernel_inter_contractible (χ : H →* Multiplicative ℝ)
    (hχ : Continuous χ) (K : Subgroup G) (J : Set (Fin n))
    (hK : ∀ g : G, g ∈ K ↔ ∀ i ∈ J, c.coord g i = 0) :
    ContractibleSpace ↥(K ⊓ χ.ker.map H.subtype) := by
  apply contractible_of_realPower_closed c
    ((K ⊓ χ.ker.map H.subtype : Subgroup G):Set G) (K ⊓ χ.ker.map H.subtype).one_mem
  intro g hg t
  exact ⟨realPower_mem_of_coordinates c K J hK hg.1 t,
    realPower_mem_mapped_kernel c H I hH χ hχ hg.2 t⟩

end RationalLattice
end
end
 

 
section
open _root_.Polynomial _root_.OAI.Polynomial
noncomputable section
namespace TriangularDenominators
variable {G : Type*} [Group G] {n : ℕ}
lemma substitute_eval {ι : Type*} (P : MvPolynomial ι ℚ) (p : ι → ℚ[X]) (t : ℚ) :
    (MvPolynomial.eval₂ C p P).eval t = MvPolynomial.eval (fun i => (p i).eval t) P := by
  have h := MvPolynomial.eval₂_comp_left (Polynomial.evalRingHom t) C p P
  have hc : (Polynomial.evalRingHom t).comp C = RingHom.id ℚ := by ext; simp
  rw [hc] at h
  exact h

 
theorem natpow_polynomial (c : Coordinates G n) (g : G) (i : Fin n) :
    ∃ p : ℚ[X], ∀ m : ℕ, p.eval (m:ℚ) = c.coord (g^m) i := by
  have aux : ∀ l : ℕ, ∀ hl : l<n, ∃ p : ℚ[X],
      ∀ m : ℕ, p.eval (m:ℚ) = c.coord (g^m) ⟨l,hl⟩ := by
    intro l
    induction l using Nat.strong_induction_on with
    | h l ih =>
      intro hl
      choose p hp using (fun j : Fin l => ih j.val j.isLt (lt_trans j.isLt hl))
      let x : (Fin l ⊕ Fin l) → ℚ[X] := Sum.elim p
        (fun j => C (c.coord g ⟨j.val,lt_trans j.isLt hl⟩))
      let Q : ℚ[X] := C (c.coord g ⟨l,hl⟩) +
        MvPolynomial.eval₂ C x (c.correction ⟨l,hl⟩)
      obtain ⟨P,hP0,hP⟩ := Polynomial.exists_antidifference Q
      refine ⟨P,?_⟩
      intro m
      induction m with
      | zero => simpa [c.one_coord] using hP0
      | succ m hm =>
        have he := congrArg (Polynomial.eval (m : ℚ)) hP
        simp only [Polynomial.eval_sub,Polynomial.eval_comp,Polynomial.eval_add,
          Polynomial.eval_one,Polynomial.eval_X] at he
        have hx : (fun a => (x a).eval (m : ℚ)) =
            Sum.elim (fun j => c.coord (g^m) ⟨j.val,lt_trans j.isLt hl⟩)
              (fun j => c.coord g ⟨j.val,lt_trans j.isLt hl⟩) := by
          funext j
          cases j with
          | inl j => exact hp j m
          | inr j => simp [x]
        simp only [Q,Polynomial.eval_add,Polynomial.eval_C,substitute_eval,hx] at he
        rw [pow_succ,c.mul_coord]
        rw [Nat.cast_succ,add_comm (m:ℚ) 1]
        linarith
  exact aux i.val i.isLt
end TriangularDenominators

end
end
end
end
end

end OAI
