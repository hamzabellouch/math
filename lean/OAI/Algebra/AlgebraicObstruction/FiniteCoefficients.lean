import Mathlib
import OAI.Algebra.FrobeniusObstruction.Obstruction
import OAI.Algebra.AlgebraicObstruction.ImplicitFunction

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction.FormalCorrection
open MvPowerSeries
open scoped Classical
variable {K σ α ι : Type*} [CommRing K] [Fintype α] [Fintype ι]

def coefficientsIn (R : Subalgebra ℤ K) (f : MvPowerSeries σ K) : Prop :=
  ∀ e, coeff e f ∈ R

def restrictCoefficients (R : Subalgebra ℤ K) (f : MvPowerSeries σ K)
    (h : coefficientsIn R f) : MvPowerSeries σ R := fun e => ⟨coeff e f,h e⟩

theorem map_restrictCoefficients (R : Subalgebra ℤ K) (f : MvPowerSeries σ K)
    (h : coefficientsIn R f) : map R.val.toRingHom (restrictCoefficients R f h) = f := by
  ext e; rfl

theorem restrictCoefficients_centered (R : Subalgebra ℤ K) (f : MvPowerSeries σ K)
    (h : coefficientsIn R f) (hf : constantCoeff f = 0) :
    constantCoeff (restrictCoefficients R f h) = 0 := by
  apply Subtype.ext
  exact hf

theorem restrictCoefficients_vanishes (R : Subalgebra ℤ K) (f : MvPowerSeries σ K)
    (h : coefficientsIn R f) {n : ℕ} (hf : Vanishes n f) :
    Vanishes n (restrictCoefficients R f h) := by
  intro e he; apply Subtype.ext; exact hf e he

theorem coefficientsIn_map (R : Subalgebra ℤ K) (f : MvPowerSeries σ R) :
    coefficientsIn R (map R.val.toRingHom f) := fun e => (coeff e f).property

theorem implicit_coefficientsIn (R : Subalgebra ℤ K)
    (L : ι → MvPowerSeries α K) (H : ι → MvPowerSeries (α ⊕ ι) K)
    (hL : ∀ i, constantCoeff (L i) = 0) (hH : ∀ i, Vanishes 2 (H i))
    (hLR : ∀ i, coefficientsIn R (L i)) (hHR : ∀ i, coefficientsIn R (H i))
    (w : ι → MvPowerSeries α K) (hw : ∀ i, constantCoeff (w i) = 0)
    (heq : ∀ i, w i = L i + subst (Sum.elim X w) (H i)) :
    ∀ i, coefficientsIn R (w i) := by
  let LR := fun i => restrictCoefficients R (L i) (hLR i)
  let HR := fun i => restrictCoefficients R (H i) (hHR i)
  obtain ⟨v,⟨hvc,hve⟩,_⟩ := centered_implicit_solution LR HR
    (fun i => restrictCoefficients_centered R _ _ (hL i))
    (fun i => restrictCoefficients_vanishes R _ _ (hH i))
  let vm := fun i => map R.val.toRingHom (v i)
  have hvm : ∀ i, constantCoeff (vm i) = 0 := by
    intro i; simp [vm,constantCoeff_map,hvc]
  have hvarg : ∀ j, constantCoeff (Sum.elim X v j) = 0 := by
    intro j; cases j <;> simp [hvc]
  have hmargument : (fun j => map R.val.toRingHom (Sum.elim X v j)) = Sum.elim X vm := by
    funext j; cases j <;> simp [vm]
  have hvme : ∀ i, vm i = L i + subst (Sum.elim X vm) (H i) := by
    intro i
    have h := congrArg (map R.val.toRingHom) (hve i)
    simpa only [map_add,map_subst (hasSubst_of_constantCoeff_zero hvarg),hmargument,
      LR,HR,map_restrictCoefficients] using h
  obtain ⟨u,_,hu⟩ := centered_implicit_solution L H hL hH
  have hsame : w = vm := (hu w ⟨hw,heq⟩).trans (hu vm ⟨hvm,hvme⟩).symm
  rw [hsame]
  exact fun i => coefficientsIn_map R (v i)

theorem finite_ring_normalized (L : ι → MvPolynomial α K)
    (H : ι → MvPolynomial (α ⊕ ι) K) (constants : Finset K)
    (hL : ∀ i, constantCoeff (L i).toMvPowerSeries = 0)
    (hH : ∀ i, Vanishes 2 (H i).toMvPowerSeries)
    (w : ι → MvPowerSeries α K) (hw : ∀ i, constantCoeff (w i) = 0)
    (heq : ∀ i, w i = (L i).toMvPowerSeries +
      subst (Sum.elim X w) (H i).toMvPowerSeries) :
    ∃ R : Subalgebra ℤ K, Algebra.FiniteType ℤ R ∧
      (∀ c ∈ constants, c ∈ R) ∧ ∀ i, coefficientsIn R (w i) := by
  let s := constants ∪ (Finset.univ.biUnion fun i => (L i).coeffs) ∪
    (Finset.univ.biUnion fun i => (H i).coeffs)
  let R := Algebra.adjoin ℤ (s : Set K)
  have hmem : ∀ c ∈ s, c ∈ R := fun c hc => Algebra.subset_adjoin hc
  refine ⟨R,(Subalgebra.fg_iff_finiteType R).mp (Subalgebra.fg_adjoin_finset s),?_,?_⟩
  · intro c hc; apply hmem; simp [s,hc]
  · apply implicit_coefficientsIn R (fun i => (L i).toMvPowerSeries)
      (fun i => (H i).toMvPowerSeries) hL hH _ _ w hw heq
    · intro i e
      change (L i).coeff e ∈ R
      by_cases hz : (L i).coeff e = 0
      · rw [hz]; exact R.zero_mem
      · apply hmem
        have hc := MvPolynomial.coeff_mem_coeffs e hz
        simp only [s,Finset.mem_union,Finset.mem_biUnion,Finset.mem_univ,true_and]
        exact Or.inl (Or.inr ⟨i,hc⟩)
    · intro i e
      change (H i).coeff e ∈ R
      by_cases hz : (H i).coeff e = 0
      · rw [hz]; exact R.zero_mem
      · apply hmem
        have hc := MvPolynomial.coeff_mem_coeffs e hz
        simp only [s,Finset.mem_union,Finset.mem_biUnion,Finset.mem_univ,true_and]
        exact Or.inr ⟨i,hc⟩

end BoundaryOnly.FormalObstruction.FormalCorrection

namespace BoundaryOnly.FormalObstruction.FormalCorrection
open MvPowerSeries
open scoped Classical
variable {K σ α ι : Type*} [CommRing K] [Fintype α] [Fintype ι]

theorem vanishes_two_of_coeff (f : MvPowerSeries σ K)
    (h0 : coeff 0 f = 0) (h1 : ∀ j, coeff (Finsupp.single j 1) f = 0) :
    Vanishes 2 f := by
  intro e he
  by_cases hz : e.degree = 0
  · have : e = 0 := (Finsupp.degree_eq_zero_iff e).mp hz
    simpa only [this] using h0
  · have hd : e.sum (fun _ n => n) = 1 := by
      change e.degree = 1
      omega
    obtain ⟨j,rfl⟩ := (Finsupp.sum_eq_one_iff e).mp hd
    exact h1 j

def internalJacobian (F : ι → MvPolynomial (α ⊕ ι) K) : Matrix ι ι K :=
  fun i j => (F i).coeff (Finsupp.single (Sum.inr j) 1)

def implicitG (F : ι → MvPolynomial (α ⊕ ι) K) (A : Matrix ι ι K) (i : ι) :
    MvPolynomial (α ⊕ ι) K :=
  MvPolynomial.X (Sum.inr i) - ∑ j, MvPolynomial.C (A i j) * F j

def implicitL (G : ι → MvPolynomial (α ⊕ ι) K) (i : ι) : MvPolynomial α K :=
  ∑ a, MvPolynomial.C ((G i).coeff (Finsupp.single (Sum.inl a) 1)) * MvPolynomial.X a

def implicitH (G : ι → MvPolynomial (α ⊕ ι) K) (i : ι) :
    MvPolynomial (α ⊕ ι) K :=
  G i - ∑ a, MvPolynomial.C ((G i).coeff (Finsupp.single (Sum.inl a) 1)) *
    MvPolynomial.X (Sum.inl a)

omit [Fintype α] in
theorem implicitG_constant [Fintype α] (F : ι → MvPolynomial (α ⊕ ι) K) (A : Matrix ι ι K)
    (hF : ∀ i, (F i).coeff 0 = 0) (i : ι) : (implicitG F A i).coeff 0 = 0 := by
  simp [implicitG,MvPolynomial.coeff_C_mul,hF]

omit [Fintype α] in
theorem implicitG_internal_linear [Fintype α] (F : ι → MvPolynomial (α ⊕ ι) K) (A : Matrix ι ι K)
    (hA : A * internalJacobian F = 1) (i j : ι) :
    (implicitG F A i).coeff (Finsupp.single (Sum.inr j) 1) = 0 := by
  have h := congrArg (fun M : Matrix ι ι K => M i j) hA
  simp only [Matrix.mul_apply,Matrix.one_apply,internalJacobian] at h
  simp only [implicitG,MvPolynomial.coeff_sub,MvPolynomial.coeff_sum,
    MvPolynomial.coeff_sum,MvPolynomial.coeff_C_mul,MvPolynomial.coeff_X,Finsupp.single_left_inj (by decide : (1:ℕ) ≠ 0),
    Sum.inr.injEq,h,sub_self]

omit [Fintype ι] in
theorem implicitL_centered [Fintype ι] (G : ι → MvPolynomial (α ⊕ ι) K) (i : ι) :
    constantCoeff (implicitL G i).toMvPowerSeries = 0 := by
  change (implicitL G i).coeff 0 = 0
  simp [implicitL,MvPolynomial.coeff_C_mul]

omit [Fintype ι] in
theorem implicitH_quadratic [Fintype ι] (G : ι → MvPolynomial (α ⊕ ι) K)
    (h0 : ∀ i, (G i).coeff 0 = 0)
    (h1 : ∀ i j, (G i).coeff (Finsupp.single (Sum.inr j) 1) = 0) (i : ι) :
    Vanishes 2 (implicitH G i).toMvPowerSeries := by
  apply vanishes_two_of_coeff
  · change (implicitH G i).coeff 0 = 0
    simp [implicitH,MvPolynomial.coeff_C_mul,h0]
  · intro j
    change (implicitH G i).coeff (Finsupp.single j 1) = 0
    cases j with
    | inl a =>
      simp [implicitH,MvPolynomial.coeff_C_mul,MvPolynomial.coeff_X,
        Finsupp.single_left_inj (by decide : (1:ℕ) ≠ 0)]
    | inr j =>
      simp [implicitH,MvPolynomial.coeff_C_mul,MvPolynomial.coeff_X,
        Finsupp.single_left_inj (by decide : (1:ℕ) ≠ 0),h1]

theorem polynomial_series_sub (f g : MvPolynomial σ K) :
    (f-g).toMvPowerSeries = f.toMvPowerSeries-g.toMvPowerSeries :=
  map_sub MvPolynomial.coeToMvPowerSeries.ringHom f g

theorem polynomial_series_sum {β : Type*} (s : Finset β) (f : β → MvPolynomial σ K) :
    (∑ b ∈ s, f b).toMvPowerSeries = ∑ b ∈ s, (f b).toMvPowerSeries :=
  map_sum MvPolynomial.coeToMvPowerSeries.ringHom f s

theorem implicitGH_equation (F : ι → MvPolynomial (α ⊕ ι) K) (A : Matrix ι ι K)
    (w : ι → MvPowerSeries α K) (hw : ∀ i, constantCoeff (w i) = 0)
    (hF : ∀ i, subst (Sum.elim X w) (F i).toMvPowerSeries = 0) (i : ι) :
    w i = (implicitL (implicitG F A) i).toMvPowerSeries +
      subst (Sum.elim X w) (implicitH (implicitG F A) i).toMvPowerSeries := by
  have hc : ∀ j, constantCoeff (Sum.elim X w j) = 0 := by
    intro j; cases j <;> simp [hw]
  let hs := hasSubst_of_constantCoeff_zero hc
  have hG : subst (Sum.elim X w) (implicitG F A i).toMvPowerSeries = w i := by
    rw [← substAlgHom_apply hs]
    simp only [implicitG,polynomial_series_sub,polynomial_series_sum,MvPolynomial.coe_mul,
      MvPolynomial.coe_C,MvPolynomial.coe_X,map_sub,map_sum,map_mul,
      substAlgHom_apply,subst_X hs,subst_C,hF,Sum.elim_inr,mul_zero,Finset.sum_const_zero,sub_zero]
  have hlinear : subst (Sum.elim X w)
      (∑ a, MvPolynomial.C ((implicitG F A i).coeff (Finsupp.single (Sum.inl a) 1)) *
        MvPolynomial.X (Sum.inl a)).toMvPowerSeries =
      (implicitL (implicitG F A) i).toMvPowerSeries := by
    rw [← substAlgHom_apply hs]
    simp only [implicitL,polynomial_series_sum,MvPolynomial.coe_mul,MvPolynomial.coe_C,
      MvPolynomial.coe_X,map_sum,map_mul,substAlgHom_apply,subst_X hs,subst_C,Sum.elim_inl]
  rw [implicitH,polynomial_series_sub,subst_sub hs,hG,hlinear]
  abel

theorem finite_ring_nonsingular (F : ι → MvPolynomial (α ⊕ ι) K)
    (hF0 : ∀ i, (F i).coeff 0 = 0)
    (hdet : IsUnit (internalJacobian F).det)
    (constants : Finset K) (w : ι → MvPowerSeries α K)
    (hw : ∀ i, constantCoeff (w i) = 0)
    (hF : ∀ i, subst (Sum.elim X w) (F i).toMvPowerSeries = 0) :
    ∃ R : Subalgebra ℤ K, Algebra.FiniteType ℤ R ∧
      (∀ c ∈ constants, c ∈ R) ∧ ∀ i, coefficientsIn R (w i) := by
  let A := (internalJacobian F)⁻¹
  let G := implicitG F A
  have hA : A * internalJacobian F = 1 := Matrix.nonsing_inv_mul _ hdet
  exact finite_ring_normalized (implicitL G) (implicitH G) constants
    (implicitL_centered G) (implicitH_quadratic G (implicitG_constant F A hF0)
      (implicitG_internal_linear F A hA)) w hw (implicitGH_equation F A w hw hF)

end BoundaryOnly.FormalObstruction.FormalCorrection

namespace BoundaryOnly.FormalObstruction.FormalCorrection
open MvPowerSeries
open scoped Classical
variable {K : Type*} [CommRing K]

structure NonsingularPresentation {σ : Type*} (f : MvPowerSeries σ K) where
  m : ℕ
  F : Fin m → MvPolynomial (σ ⊕ Fin m) K
  w : Fin m → MvPowerSeries σ K
  offset : K
  output : Fin m
  equation : ∀ i, subst (Sum.elim X w) (F i).toMvPowerSeries = 0
  zero : ∀ i, (F i).coeff 0 = 0
  centered : ∀ i, constantCoeff (w i) = 0
  nonsingular : IsUnit (internalJacobian F).det
  represents : f = C offset + w output

theorem NonsingularPresentation.finite_coefficients {σ : Type*} [Fintype σ]
    {f : MvPowerSeries σ K} (D : NonsingularPresentation f) (constants : Finset K) :
    ∃ R : Subalgebra ℤ K, Algebra.FiniteType ℤ R ∧
      (∀ c ∈ constants, c ∈ R) ∧ coefficientsIn R f := by
  let A : Matrix (Fin D.m) (Fin D.m) K := (internalJacobian D.F)⁻¹
  let G := implicitG D.F A
  have hA' := Matrix.nonsing_inv_mul (internalJacobian D.F) D.nonsingular
  have hA : A * internalJacobian D.F = 1 := by
    ext i j
    simpa only [Matrix.one_apply] using congrArg (fun M : Matrix (Fin D.m) (Fin D.m) K => M i j) hA'
  have hH : ∀ i, Vanishes 2 (implicitH G i).toMvPowerSeries :=
    implicitH_quadratic G (implicitG_constant D.F A D.zero) (implicitG_internal_linear D.F A (by
      ext i j
      have h := congrArg (fun M : Matrix (Fin D.m) (Fin D.m) K => M i j) hA
      by_cases hij : i = j
      · simpa only [Matrix.one_apply, ite_eq_left hij] using h
      · simpa only [Matrix.one_apply, ite_eq_right hij] using h))
  obtain ⟨R,hR,hconst,hw⟩ := finite_ring_normalized (implicitL G) (implicitH G)
    (insert D.offset constants) (implicitL_centered G) hH D.w D.centered
      (implicitGH_equation D.F A D.w D.centered D.equation)
  refine ⟨R,hR,fun c hc => hconst c (Finset.mem_insert_of_mem hc),?_⟩
  intro e
  rw [D.represents,map_add]
  apply R.add_mem _ (hw _ e)
  by_cases he : e = 0
  · simpa [he] using hconst D.offset (Finset.mem_insert_self _ _)
  · simp [coeff_C,he]

theorem finite_coefficient_family {κ : Type*} [Fintype κ] {σ : κ → Type*}
    (f : (i : κ) → MvPowerSeries (σ i) K)
    (hf : ∀ i, ∃ R : Subalgebra ℤ K, Algebra.FiniteType ℤ R ∧ coefficientsIn R (f i))
    (constants : Finset K) :
    ∃ R : Subalgebra ℤ K, Algebra.FiniteType ℤ R ∧
      (∀ c ∈ constants, c ∈ R) ∧ ∀ i, coefficientsIn R (f i) := by
  choose R hfg hcoef using hf
  have hgens : ∀ i, ∃ s : Finset K, Algebra.adjoin ℤ (s : Set K) = R i := by
    intro i
    exact (Subalgebra.fg_iff_finiteType (R i)).mpr (hfg i)
  choose s hs using hgens
  let S := constants ∪ Finset.univ.biUnion s
  let A := Algebra.adjoin ℤ (S : Set K)
  have hRA : ∀ i, R i ≤ A := by
    intro i
    rw [← hs i]
    apply Algebra.adjoin_mono
    intro x hx
    change x ∈ S
    simp only [S,Finset.mem_union,Finset.mem_biUnion,Finset.mem_univ,true_and]
    exact Or.inr ⟨i,hx⟩
  refine ⟨A,(Subalgebra.fg_iff_finiteType A).mp (Subalgebra.fg_adjoin_finset S),?_,?_⟩
  · intro c hc
    exact Algebra.subset_adjoin (show c ∈ S by simp [S,hc])
  · exact fun i e => hRA i (hcoef i e)

theorem finite_ring_presentations {κ : Type*} [Fintype κ] {σ : κ → Type*}
    [∀ i, Fintype (σ i)] (f : (i : κ) → MvPowerSeries (σ i) K)
    (D : ∀ i, NonsingularPresentation (f i)) (constants : Finset K) :
    ∃ R : Subalgebra ℤ K, Algebra.FiniteType ℤ R ∧
      (∀ c ∈ constants, c ∈ R) ∧ ∀ i, coefficientsIn R (f i) := by
  apply finite_coefficient_family f _ constants
  intro i
  obtain ⟨R,hR,_,hf⟩ := (D i).finite_coefficients ∅
  exact ⟨R,hR,hf⟩

end BoundaryOnly.FormalObstruction.FormalCorrection

end

end OAI
