import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RationalLattice05
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
open scoped BigOperators
noncomputable section
namespace IntegerHyperplane
variable {n : ℕ}

def form (k : Fin n → ℤ) : (Fin n → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ i, (k i : ℝ) * x i
  map_add' x y := by simp [mul_add,Finset.sum_add_distrib]
  map_smul' r x := by simp [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring

 
def generator (k : Fin n → ℤ) (p j : Fin n) : Fin n → ℤ :=
  k p • Pi.single j 1 - k j • Pi.single p 1

def realGenerator (k : Fin n → ℤ) (p j : Fin n) : Fin n → ℝ := fun i => generator k p j i

lemma realGenerator_eq (k : Fin n → ℤ) (p j : Fin n) :
    realGenerator k p j = (k p : ℝ) • Pi.single j 1 - (k j : ℝ) • Pi.single p 1 := by
  classical
  ext i
  simp [realGenerator,generator,Pi.single_apply]

lemma generator_mem (k : Fin n → ℤ) (p j : Fin n) : realGenerator k p j ∈ (form k).ker := by
  classical
  change form k (realGenerator k p j) = 0
  rw [realGenerator_eq,map_sub,map_smul,map_smul]
  simp [form,Pi.single_apply,mul_comm]

lemma decomposition (k : Fin n → ℤ) {p : Fin n} (hp : k p ≠ 0)
    (x : Fin n → ℝ) :
    (∑ j, (x j / (k p : ℝ)) • realGenerator k p j) =
      x - (form k x / (k p : ℝ)) • Pi.single p 1 := by
  classical
  have hpR : (k p : ℝ) ≠ 0 := by exact_mod_cast hp
  ext i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, realGenerator_eq,
    Pi.sub_apply, Pi.single_apply]
  by_cases hi : i = p
  · subst i
    simp only [↓reduceIte, mul_one]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    have hfirst : ∑ j : Fin n, x j / (k p : ℝ) * ((k p : ℝ) * if p = j then 1 else 0) = x p := by
      simp [mul_ite,hpR]
    rw [hfirst]
    congr 1
    change (∑ j, x j / (k p : ℝ) * (k j : ℝ)) = (∑ j, (k j : ℝ) * x j) / (k p : ℝ)
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    ring
  · simp only [hi, ↓reduceIte, mul_zero, sub_zero]
    simp [mul_ite,hpR]

 

theorem kernel_span (k : Fin n → ℤ) {p : Fin n} (hp : k p ≠ 0) :
    (form k).ker = Submodule.span ℝ (Set.range (realGenerator k p)) := by
  apply le_antisymm
  · intro x hx
    have he := decomposition k hp x
    have hx0 : form k x = 0 := hx
    rw [hx0, zero_div,zero_smul,sub_zero] at he
    rw [← he]
    apply Submodule.sum_mem
    intro j _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j,rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact generator_mem k p j

lemma generator_bound (k : Fin n → ℤ) (A : ℝ) (hA : 0 ≤ A)
    (hk : ∀ i, |(k i : ℝ)| ≤ A) (p j i : Fin n) :
    |(generator k p j i : ℝ)| ≤ A := by
  classical
  by_cases hj : j = p
  · subst j; simpa [generator] using hA
  · by_cases hij : i = j
    · subst i
      simpa [generator,Pi.single_apply,hj] using hk p
    · by_cases hip : i = p
      · subst i
        simpa [generator,Pi.single_apply,Ne.symm hj] using hk j
      · simpa [generator,Pi.single_apply,hij,hip] using hA

theorem form_surjective (k : Fin n → ℤ) {p : Fin n} (hp : k p ≠ 0) :
    Function.Surjective (form k) := by
  classical
  intro y
  refine ⟨Pi.single p (y / (k p : ℝ)), ?_⟩
  have hpR : (k p : ℝ) ≠ 0 := by exact_mod_cast hp
  simp only [form,LinearMap.coe_mk,AddHom.coe_mk,Pi.single_apply]
  simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  field_simp

 
theorem kernel_finrank (k : Fin n → ℤ) (hk : k ≠ 0) :
    Module.finrank ℝ (form k).ker = n-1 := by
  classical
  obtain ⟨p,hp⟩ : ∃ p, k p ≠ 0 := by
    by_contra! h
    exact hk (funext h)
  have hr : (form k).range = ⊤ := LinearMap.range_eq_top.mpr (form_surjective k hp)
  have h := LinearMap.finrank_range_add_finrank_ker (form k)
  rw [hr] at h
  simp at h
  omega

end IntegerHyperplane
end
end
 

 
section
open scoped BigOperators
noncomputable section
namespace IntegerHyperplane
variable {n : ℕ}

def lift (k : Fin (n+1) → ℤ) (p : Fin (n+1)) (x : Fin n → ℝ) : Fin (n+1) → ℝ :=
  p.insertNth (-(∑ j, (k (p.succAbove j):ℝ)*x j)/(k p:ℝ)) x

@[simp] lemma lift_succAbove (k : Fin (n+1) → ℤ) (p : Fin (n+1))
    (x : Fin n → ℝ) (j : Fin n) : lift k p x (p.succAbove j) = x j :=
  Fin.insertNth_apply_succAbove _ _ _ _

@[simp] lemma lift_pivot (k : Fin (n+1) → ℤ) (p : Fin (n+1)) (x : Fin n → ℝ) :
    lift k p x p = -(∑ j, (k (p.succAbove j):ℝ)*x j)/(k p:ℝ) :=
  Fin.insertNth_apply_same _ _ _

lemma form_lift (k : Fin (n+1) → ℤ) (p : Fin (n+1)) (hp : k p ≠ 0) (x : Fin n → ℝ) :
    form k (lift k p x) = 0 := by
  change (∑ j, (k j:ℝ)*lift k p x j) = 0
  rw [Fin.sum_univ_succAbove _ p,lift_pivot]
  simp only [lift_succAbove]
  have hpR : (k p:ℝ) ≠ 0 := by exact_mod_cast hp
  field_simp
  ring

lemma lift_remove (k : Fin (n+1) → ℤ) (p : Fin (n+1)) (hp : k p ≠ 0)
    (x : Fin (n+1) → ℝ) (hx : form k x = 0) : lift k p (p.removeNth x) = x := by
  funext i
  rcases Fin.eq_self_or_eq_succAbove p i with he | ⟨j,he⟩
  · subst i
    rw [lift_pivot]
    have he := Fin.sum_univ_succAbove (fun j => (k j:ℝ)*x j) p
    change (∑ j, (k j:ℝ)*x j) = 0 at hx
    have hpR : (k p:ℝ) ≠ 0 := by exact_mod_cast hp
    apply (div_eq_iff hpR).mpr
    change -(∑ j, (k (p.succAbove j):ℝ)*x (p.succAbove j)) = x p*(k p:ℝ)
    linarith
  · subst i
    exact lift_succAbove k p (p.removeNth x) j

lemma lift_continuous (k : Fin (n+1) → ℤ) (p : Fin (n+1)) : Continuous (lift k p) := by
  apply continuous_pi
  intro i
  rcases Fin.eq_self_or_eq_succAbove p i with he | ⟨j,he⟩
  · subst i
    simp only [lift_pivot]
    apply Continuous.div_const
    apply Continuous.neg
    exact continuous_finsetSum _ (fun j _ => continuous_const.mul (continuous_apply j))
  · subst i
    simp only [lift_succAbove]
    exact continuous_apply j

lemma lift_zero (k : Fin (n+1) → ℤ) (p : Fin (n+1)) : lift k p 0 = 0 := by
  funext i
  rcases Fin.eq_self_or_eq_succAbove p i with he | ⟨j,he⟩ <;> subst i <;> simp

lemma lift_polynomial (k : Fin (n+1) → ℤ) (p : Fin (n+1)) (i : Fin (n+1)) :
    RationalPolynomialMap.IsPolynomial (fun x => lift k p x i) := by
  rcases Fin.eq_self_or_eq_succAbove p i with he | ⟨j,he⟩
  · subst i
    simp only [lift_pivot]
    have hs : RationalPolynomialMap.IsPolynomial (fun x : Fin n → ℝ =>
        ∑ j, (k (p.succAbove j):ℝ)*x j) := by
      have ha (S : Finset (Fin n)) : RationalPolynomialMap.IsPolynomial (fun x : Fin n → ℝ =>
          ∑ j ∈ S, (k (p.succAbove j):ℝ)*x j) := by
        induction S using Finset.induction_on with
        | empty => simpa using RationalPolynomialMap.zero (σ:=Fin n)
        | @insert j S hj ih =>
          simp only [Finset.sum_insert hj]
          apply RationalPolynomialMap.add _ ih
          simpa only [Rat.cast_intCast] using RationalPolynomialMap.mul
            (RationalPolynomialMap.const (σ:=Fin n) (k (p.succAbove j):ℚ))
            (RationalPolynomialMap.coordinate j)
      simpa using ha Finset.univ
    have hm := RationalPolynomialMap.mul (RationalPolynomialMap.neg hs)
      (RationalPolynomialMap.const (σ:=Fin n) ((k p:ℚ)⁻¹))
    simpa only [Rat.cast_inv,Rat.cast_intCast,div_eq_mul_inv] using hm
  · subst i
    simp only [lift_succAbove]
    exact RationalPolynomialMap.coordinate j

 

lemma lift_lower_dep (k : Fin (n+1) → ℤ) (p : Fin (n+1))
    (hlast : ∀ j : Fin (n+1), p < j → k j = 0) (i : Fin n)
    (x y : Fin n → ℝ) (hxy : ∀ j : Fin n, j < i → x j = y j)
    (a : Fin (n+1)) (ha : a < p.succAbove i) : lift k p x a = lift k p y a := by
  rcases Fin.eq_self_or_eq_succAbove p a with he | ⟨j,he⟩
  · subst a
    simp only [lift_pivot]
    congr 2
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j < i
    · rw [hxy j hj]
    · have hk : k (p.succAbove j) = 0 := hlast _
        (lt_of_lt_of_le ha ((Fin.succAboveOrderEmb p).monotone (le_of_not_gt hj)))
      simp [hk]
  · subst a
    simp only [lift_succAbove]
    exact hxy j (Fin.succAbove_lt_succAbove_iff.mp ha)

end IntegerHyperplane

namespace RationalCharacterKernel
open RationalLattice IntegerHyperplane RationalPolynomialMap
variable {G : Type*} [Group G] [TopologicalSpace G] {n : ℕ}
variable (c : RealCoordinates G (n+1)) (χ : G →* Multiplicative ℝ)
variable (k : Fin (n+1) → ℤ) (p : Fin (n+1)) (hp : k p ≠ 0)
variable (hχ : ∀ g : G, Multiplicative.toAdd (χ g) = form k (c.coord g))

def coordinates (g : χ.ker) (i : Fin n) : ℝ := c.coord g.val (p.succAbove i)

include hχ in
lemma form_coord_kernel (g : χ.ker) : form k (c.coord g.val) = 0 := by
  rw [← hχ]
  have hg : χ g.val = 1 := g.property
  rw [hg]
  rfl

include hp hχ in
lemma coord_lift (g : χ.ker) : c.coord g.val = lift k p (coordinates c χ p g) := by
  exact (lift_remove k p hp (c.coord g.val) (form_coord_kernel c χ k hχ g)).symm

def rebuild (x : Fin n → ℝ) : χ.ker :=
  ⟨c.coord.symm (lift k p x),by
    change χ _ = 1
    apply Multiplicative.toAdd.injective
    rw [hχ,c.coord.apply_symm_apply,form_lift k p hp]
    rfl⟩

lemma coordinates_rebuild (x : Fin n → ℝ) :
    coordinates c χ p (rebuild c χ k p hp hχ x) = x := by
  funext i
  simp only [coordinates,rebuild,Homeomorph.apply_symm_apply,lift_succAbove]

lemma rebuild_coordinates (g : χ.ker) :
    rebuild c χ k p hp hχ (coordinates c χ p g) = g := by
  apply Subtype.ext
  apply c.coord.injective
  simp only [rebuild,Homeomorph.apply_symm_apply]
  exact (coord_lift c χ k p hp hχ g).symm

lemma coordinates_continuous : Continuous (coordinates c χ p) := by
  apply continuous_pi
  intro i
  exact (continuous_apply _).comp (c.coord.continuous.comp continuous_subtype_val)

lemma rebuild_continuous : Continuous (rebuild c χ k p hp hχ) := by
  apply Continuous.subtype_mk
  exact c.coord.symm.continuous.comp (lift_continuous k p)

def kernelHomeomorph : χ.ker ≃ₜ (Fin n → ℝ) where
  toFun := coordinates c χ p
  invFun := rebuild c χ k p hp hχ
  left_inv := rebuild_coordinates c χ k p hp hχ
  right_inv := coordinates_rebuild c χ k p hp hχ
  continuous_toFun := coordinates_continuous c χ p
  continuous_invFun := rebuild_continuous c χ k p hp hχ

lemma exists_kernel_correction (i : Fin n) :
    ∃ P : MvPolynomial (Fin i.val ⊕ Fin i.val) ℚ,
    ∀ v : (Fin i.val ⊕ Fin i.val) → ℝ,
      MvPolynomial.eval₂ (algebraMap ℚ ℝ)
        (Sum.elim
          (fun a => lift k p (lowerExtend i (fun j => v (Sum.inl j)))
            ⟨a.val,lt_trans a.isLt (p.succAbove i).isLt⟩)
          (fun a => lift k p (lowerExtend i (fun j => v (Sum.inr j)))
            ⟨a.val,lt_trans a.isLt (p.succAbove i).isLt⟩)) (c.correction (p.succAbove i)) =
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) v P := by
  apply RationalPolynomialMap.eval
  intro a
  cases a with
  | inl a =>
    apply RationalPolynomialMap.comp (lift_polynomial k p _)
    intro j
    unfold lowerExtend
    split_ifs
    · exact RationalPolynomialMap.coordinate _
    · exact RationalPolynomialMap.zero
  | inr a =>
    apply RationalPolynomialMap.comp (lift_polynomial k p _)
    intro j
    unfold lowerExtend
    split_ifs
    · exact RationalPolynomialMap.coordinate _
    · exact RationalPolynomialMap.zero

def kernelCorrection (i : Fin n) : MvPolynomial (Fin i.val ⊕ Fin i.val) ℚ :=
  (exists_kernel_correction c k p i).choose

variable (hlast : ∀ j : Fin (n+1), p < j → k j = 0)

include hp hχ hlast in
lemma kernel_mul_coord (g h : χ.ker) (i : Fin n) :
    coordinates c χ p (g*h) i = coordinates c χ p g i + coordinates c χ p h i +
      MvPolynomial.eval₂ (algebraMap ℚ ℝ)
        (Sum.elim (fun j => coordinates c χ p g ⟨j.val,lt_trans j.isLt i.isLt⟩)
          (fun j => coordinates c χ p h ⟨j.val,lt_trans j.isLt i.isLt⟩)) (kernelCorrection c k p i) := by
  change c.coord (g.val*h.val) (p.succAbove i) = _
  rw [c.mul_coord]
  change coordinates c χ p g i + coordinates c χ p h i + _ = _
  congr 1
  let v : (Fin i.val ⊕ Fin i.val) → ℝ :=
    Sum.elim (fun j => coordinates c χ p g ⟨j.val,lt_trans j.isLt i.isLt⟩)
      (fun j => coordinates c χ p h ⟨j.val,lt_trans j.isLt i.isLt⟩)
  unfold kernelCorrection
  rw [← (exists_kernel_correction c k p i).choose_spec v]
  congr 1
  funext a
  have hl (u : χ.ker) (a : Fin (p.succAbove i).val) :
      c.coord u.val ⟨a.val,lt_trans a.isLt (p.succAbove i).isLt⟩ =
      lift k p (lowerExtend i (fun j => coordinates c χ p u ⟨j.val,lt_trans j.isLt i.isLt⟩))
        ⟨a.val,lt_trans a.isLt (p.succAbove i).isLt⟩ := by
    rw [coord_lift c χ k p hp hχ]
    apply lift_lower_dep k p hlast i
    · intro j hj
      simp [lowerExtend,hj]
    · exact a.isLt
  cases a with
  | inl a => exact hl g a
  | inr a => exact hl h a

 

def kernelCoordinates : RealCoordinates χ.ker n where
  coord := kernelHomeomorph c χ k p hp hχ
  one_coord i := c.one_coord (p.succAbove i)
  correction := kernelCorrection c k p
  mul_coord := kernel_mul_coord c χ k p hp hχ hlast

lemma kernelCoordinates_rational (g : χ.ker) :
    IsRational (kernelCoordinates c χ k p hp hχ hlast) g ↔ IsRational c g.val := by
  constructor
  · intro hg i
    obtain ⟨P,hP⟩ := lift_polynomial k p i
    obtain ⟨q,hq⟩ := eval_rational P (coordinates c χ p g) hg
    refine ⟨q,?_⟩
    rw [hq,← hP]
    exact congrFun (coord_lift c χ k p hp hχ g).symm i
  · intro hg i
    exact hg (p.succAbove i)

end RationalCharacterKernel

end
end
end
end
end

end OAI
