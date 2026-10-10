import OAI.Algebra.Determinantal.QuotientFields

namespace OAI

namespace PermanentBorder.AdjugateAlgebra
open Polynomial Matrix Module
variable {K L : Type*} [Field K] [Field L] [Algebra K L] {k : ℕ}

theorem low_coefficients_mem (F : IntermediateField K L)
    (θ : Fin (k+1) → L) (hθ : Function.Injective θ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) L) (hk : 0 < k)
    (P : L[X][X]) (hP : TotalDegreeLE P (k-1))
    (hcoord : ∀ i, (rowBasis θ hθ A hk).repr
      ((Ideal.Quotient.mkₐ L (rowIdeal (pencilBase θ A))) P) i ∈ F) :
    Bivariate.InField F P := by
  intro a b
  by_cases hab : a+b ≤ k-1
  · let i : PlaneIndex (k-1) := ⟨(⟨a,by omega⟩,⟨a+b+1,by omega⟩),by
      change a < a+b+1
      omega⟩
    have h := hcoord i
    rw [rowBasis_repr θ hθ A hk P hP] at h
    change (P.coeff a).coeff (a+b+1-a-1) ∈ F at h
    rwa [show a+b+1-a-1=b by omega] at h
  · rw [hP a b (by omega)]
    exact F.zero_mem

theorem rowEntry_inField (F : IntermediateField K L)
    (θ : Fin (k+1) → L) (hθ : Function.Injective θ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) L) (hk : 0 < k)
    (hθF : ∀ i, θ i ∈ F)
    (hmon : ∀ a d i, (rowBasis θ hθ A hk).repr
      ((Ideal.Quotient.mkₐ L (rowIdeal (pencilBase θ A)))
        (monomial a (monomial d 1))) i ∈ F) (j : Fin (k+1)) :
    Bivariate.InField F (rowEntry (pencilBase θ A) j) := by
  let q := Ideal.Quotient.mkₐ L (rowIdeal (pencilBase θ A))
  let P := rowEntry (pencilBase θ A) j
  let P₀ := rowEntry (pencilBase θ 0) j
  have hP₀ : Bivariate.InField F P₀ := by
    apply (Bivariate.inField_iff_lifts F _).mpr
    refine ⟨rowEntry (pencilBase (fun i => (⟨θ i,hθF i⟩ : F)) 0) j,?_⟩
    rw [map_rowEntry]
    rfl
  have hdeg : TotalDegreeLE (P-P₀) (k-1) := by
    apply TotalDegreeLE.pred_of_top_zero hk
    · exact (totalDegreeLE_rowEntry θ A j).sub (totalDegreeLE_rowEntry θ 0 j)
    · simp only [P,P₀,map_sub,coeff_sub,rowEntry_top,sub_self]
  have hzero : q P = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨j,rfl⟩)
  have hlow : Bivariate.InField F (P-P₀) := by
    apply low_coefficients_mem F θ hθ A hk _ hdeg
    intro i
    change (rowBasis θ hθ A hk).repr (q (P-P₀)) i ∈ F
    rw [map_sub,hzero,zero_sub,map_neg,Finsupp.neg_apply]
    exact F.neg_mem (coordinates_mem F q.toLinearMap (rowBasis θ hθ A hk) hmon P₀ hP₀ i)
  simpa only [sub_add_cancel] using hlow.add hP₀

theorem column_contraction (θ : Fin (k+1) → L)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) L) (j : Fin (k+1)) :
    rowContraction θ A (fun i => A i j) = (pencilMatrix (pencilBase θ A)).det -
      (X + C (X * C (θ j))) * rowEntry (pencilBase θ A) j := by
  classical
  let v : Fin (k+1) → L[X] := Pi.single j 1
  have hv : rowPair (pencilBase θ A) v = rowEntry (pencilBase θ A) j := by
    simp [v,rowPair_eq_sum,Pi.single_apply,apply_ite]
  have hc : (pencilBase θ A).mulVec v =
      (X * C (θ j)) • v + fun i => C (A i j) := by
    funext i
    by_cases hij : i=j
    · subst i
      simp [pencilBase,v,Matrix.mulVec_single]
    · simp [pencilBase,v,Matrix.mulVec_single,hij]
  have hh := X_mul_rowPair (pencilBase θ A) v
  rw [rowPair_neg,hc,rowPair_add,rowPair_smul,hv] at hh
  have hs : (∑ i, v i) = 1 := by simp [v,Pi.single_apply]
  rw [hs,map_one,one_mul] at hh
  change X * rowEntry (pencilBase θ A) j =
    -(C (X*C (θ j)) * rowEntry (pencilBase θ A) j +
      rowContraction θ A (fun i => A i j)) + _ at hh
  linear_combination hh

theorem determinant_mem_rowIdeal (θ : Fin (k+1) → L)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) L) :
    (pencilMatrix (pencilBase θ A)).det ∈ rowIdeal (pencilBase θ A) := by
  have h := column_contraction θ A 0
  have he : (pencilMatrix (pencilBase θ A)).det =
      rowContraction θ A (fun i => A i 0) +
      (X+C (X*C (θ 0))) * rowEntry (pencilBase θ A) 0 := by
    linear_combination -h
  rw [he]
  exact Ideal.add_mem _ (rowContraction_mem θ A _) (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨0,rfl⟩))

end PermanentBorder.AdjugateAlgebra

namespace PermanentBorder.AdjugateAlgebra
open Polynomial Matrix Module
variable {K L : Type*} [Field K] [Field L] [Algebra K L] {k : ℕ}

theorem slopeTrace_eval (θ v : Fin (k+1) → L) (i : Fin (k+1)) :
    (slopeTrace θ v).eval (-θ i) =
      v i * ∏ l ∈ Finset.univ.erase i, (-θ i + θ l) := by
  classical
  simp only [slopeTrace,spectralSlope,Matrix.adjugate_diagonal,
    Matrix.trace,Matrix.diag_apply,Matrix.mul_diagonal,Matrix.map_apply,Matrix.diagonal_apply_eq,
    eval_finsetSum,eval_mul,eval_C,eval_prod,eval_add,eval_X]
  apply Finset.sum_eq_single i
  · intro j _ hji
    have hp : ∏ l ∈ Finset.univ.erase j, (-θ i + θ l) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hji,Finset.mem_univ i⟩)
      simp
    simp [hp]
  · simp

theorem matrix_inField_of_rows (F : IntermediateField K L)
    (θ : Fin (k+1) → L) (hθ : Function.Injective θ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) L)
    (hθF : ∀ i, θ i ∈ F)
    (hdet : Bivariate.InField F (pencilMatrix (pencilBase θ A)).det)
    (hrow : ∀ j, Bivariate.InField F (rowEntry (pencilBase θ A) j)) :
    ∀ i j, A i j ∈ F := by
  classical
  intro i j
  have hlin : Bivariate.InField F (X + C (X * C (θ j))) := by
    rw [map_mul]
    exact (Bivariate.inField_X F).add
      ((Bivariate.inField_C_X F).mul (Bivariate.inField_C_C F _ (hθF j)))
  have hc : Bivariate.InField F (rowContraction θ A (fun l => A l j)) := by
    rw [column_contraction]
    exact hdet.sub (hlin.mul (hrow j))
  have hs : ∀ a, (slopeTrace θ (fun l => A l j)).coeff a ∈ F := by
    intro a
    rw [← rowContraction_top θ A]
    exact scaled_coeff_mem F _ hc k a
  have he := Bivariate.eval_mem F _ hs (-θ i) (F.neg_mem (hθF i))
  rw [slopeTrace_eval] at he
  have hp : (∏ l ∈ Finset.univ.erase i, (-θ i + θ l)) ∈ F := by
    exact F.prod_mem fun l _ => F.add_mem (F.neg_mem (hθF i)) (hθF l)
  have hn : (∏ l ∈ Finset.univ.erase i, (-θ i + θ l)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro l hl hz
    have hei : θ l = θ i := by linear_combination hz
    exact (Finset.mem_erase.mp hl).1 (hθ hei)
  simpa only [mul_div_cancel_right₀ _ hn] using F.div_mem he hp

end PermanentBorder.AdjugateAlgebra

namespace PermanentBorder.Bivariate
open Module Polynomial
universe u
variable {K L R : Type u} [Field K] [Field L] [Algebra K L]
  [Infinite K] [IsAlgClosed L] [CommRing R] [Algebra L R] [Module.Finite L R]

theorem quotient_field_bound (p : K[X][X]) (hp : p ≠ 0)
    (q : L[X][X] →ₐ[L] R) (hq : Function.Surjective q)
    (hpq : q (map (algebraMap K L) p) = 0)
    {n : ℕ} (b : Basis (Fin n) L R) (r s : Fin n → ℕ)
    (hb : ∀ i, b i = q (monomial (r i) (monomial (s i) 1))) :
    ∃ F : IntermediateField K L,
      Algebra.trdeg K F ≤ (finrank L R : Cardinal) ∧
      ∀ a d i, b.repr (q (monomial a (monomial d 1))) i ∈ F := by
  let q' := q.comp (equivalence L).toAlgHom
  let p' := (equivalence K).symm p
  have hp' : p' ≠ 0 := fun h => hp ((equivalence K).symm.injective (h.trans (map_zero _).symm))
  have hq' : Function.Surjective q' := hq.comp (equivalence L).surjective
  have hpq' : q' (MvPolynomial.map (algebraMap K L) p') = 0 := by
    change q (equivalence L (MvPolynomial.map (algebraMap K L) p')) = 0
    rw [equivalence_map, AlgEquiv.apply_symm_apply]
    exact hpq
  have hb' : ∀ i, b i = q' (MvPolynomial.X 0 ^ r i * MvPolynomial.X 1 ^ s i) := by
    intro i
    change b i = q (equivalence L _)
    rw [equivalence_monomial, hb]
  obtain ⟨F,hF,hA,hB,hv⟩ := CurveQuotientParameters.chart_field_bound p' hp' q' hq' hpq' b r s hb'
  refine ⟨F,hF,?_⟩
  intro a d i
  have h := FinitePlaneFrames.monomial_coordinates_mem F q' b hA hB hv a d i
  simpa only [q', AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, equivalence_monomial] using h

end PermanentBorder.Bivariate

namespace PermanentBorder.DeterminantFibers
open Polynomial Module AdjugateAlgebra
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  [Infinite K] [IsAlgClosed L] {k : ℕ}

theorem matrix_field_bound (θ : Fin (k+1) → K) (hθ : Function.Injective θ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) L) (hk : 0 < k)
    (p : K[X][X]) (hp : p ≠ 0)
    (hdet : (pencilMatrix (pencilBase (fun i => algebraMap K L (θ i)) A)).det =
      Bivariate.map (algebraMap K L) p) :
    ∃ F : IntermediateField K L,
      Algebra.trdeg K F ≤ ((k+1).choose 2 : Cardinal) ∧ ∀ i j, A i j ∈ F := by
  classical
  let θ' : Fin (k+1) → L := fun i => algebraMap K L (θ i)
  have hθ' : Function.Injective θ' := (FaithfulSMul.algebraMap_injective K L).comp hθ
  let I := rowIdeal (pencilBase θ' A)
  let q := Ideal.Quotient.mkₐ L I
  have : Module.Finite L (L[X][X] ⧸ I) := finite_row_quotient θ' hθ' A hk
  let b := rowBasis θ' hθ' A hk
  let e := Fintype.equivFin (PlaneIndex (k-1))
  let b' := b.reindex e
  let r : Fin (Fintype.card (PlaneIndex (k-1))) → ℕ := fun i => (e.symm i).val.1.val
  let s : Fin (Fintype.card (PlaneIndex (k-1))) → ℕ :=
    fun i => (e.symm i).val.2.val-(e.symm i).val.1.val-1
  have hb' : ∀ i, b' i = q (monomial (r i) (monomial (s i) 1)) := by
    intro i
    exact (b.reindex_apply e i).trans (rowBasis_apply θ' hθ' A hk (e.symm i))
  have hpq : q (Bivariate.map (algebraMap K L) p) = 0 := by
    rw [← hdet]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (determinant_mem_rowIdeal θ' A)
  obtain ⟨F,hF,hmon⟩ := Bivariate.quotient_field_bound p hp q
    (Ideal.Quotient.mkₐ_surjective L I) hpq b' r s hb'
  have hmon' : ∀ a d i, b.repr (q (monomial a (monomial d 1))) i ∈ F := by
    intro a d i
    have h := hmon a d (e i)
    simpa only [b',Basis.repr_reindex_apply,Equiv.symm_apply_apply] using h
  refine ⟨F,?_,?_⟩
  · rw [row_quotient_finrank θ' hθ' A hk] at hF
    exact hF
  · apply matrix_inField_of_rows F θ' hθ' A
    · intro i
      exact F.algebraMap_mem (θ i)
    · rw [hdet]
      exact Bivariate.inField_map F p
    · exact rowEntry_inField F θ' hθ' A hk (fun i => F.algebraMap_mem (θ i)) hmon'

end PermanentBorder.DeterminantFibers

namespace PermanentBorder.AlgebraicDimension

open Order

variable {R S : Type*} [CommRing R] [CommRing S]

theorem krullDim_le_of_integral (f : R →+* S) (hf : f.IsIntegral) :
    ringKrullDim S ≤ ringKrullDim R := by
  let : Algebra R S := f.toAlgebra
  let : Algebra.IsIntegral R S := ⟨hf⟩
  apply krullDim_le_of_strictMono (PrimeSpectrum.comap f)
  intro I J hIJ
  exact Ideal.IsIntegral.under_lt_under hIJ

universe u

variable {K A : Type u} [Field K] [CommRing A] [Algebra K A]

theorem krullDim_le_of_trdeg_le [Algebra.FiniteType K A] (n : ℕ)
    (h : Algebra.trdeg K A ≤ (n : Cardinal)) :
    ringKrullDim A ≤ n := by
  nontriviality A
  obtain ⟨s, g, hg, hint⟩ := exists_integral_inj_algHom_of_fg K A
  have hs : s ≤ n := by
    have hsn := (trdeg_le_of_injective g hg).trans h
    simpa using hsn
  calc
    ringKrullDim A ≤ ringKrullDim (MvPolynomial (Fin s) K) :=
      krullDim_le_of_integral g.toRingHom hint
    _ = s := by simp
    _ ≤ n := by exact_mod_cast hs

theorem image_dimension_le {F : Type u} [CommRing F] [Algebra K F]
    {N n : ℕ} (f : MvPolynomial (Fin N) K →ₐ[K] F)
    (hF : Algebra.trdeg K F ≤ (n : Cardinal)) :
    ringKrullDim (MvPolynomial (Fin N) K ⧸ RingHom.ker f) ≤ n := by
  apply krullDim_le_of_trdeg_le (K := K) n
  exact (trdeg_le_of_injective
    (Ideal.Quotient.liftₐ (RingHom.ker f) f (fun _ h => h))
    (RingHom.lift_injective_of_ker_le_ideal _ _ le_rfl)).trans hF

end PermanentBorder.AlgebraicDimension

namespace PermanentBorder.AlgebraicDimension
universe u
variable {K A : Type u} [Field K] [CommRing A] [Algebra K A]

theorem krullDim_le_of_field_images [Algebra.FiniteType K A] (n : ℕ)
    (h : ∀ (L : Type u) [Field L] [Algebra K L] (f : A →ₐ[K] L),
      Algebra.trdeg K f.range ≤ (n : Cardinal)) :
    ringKrullDim A ≤ n := by
  nontriviality A
  obtain ⟨s, g, hg, hint⟩ := exists_integral_inj_algHom_of_fg K A
  let R := MvPolynomial (Fin s) K
  let : Algebra R A := g.toRingHom.toAlgebra
  let : Algebra.IsIntegral R A := ⟨hint⟩
  have hg' : (⊥ : Ideal A).comap (algebraMap R A) ≤ (⊥ : Ideal R) := by
    rw [← RingHom.ker_eq_comap_bot]
    exact le_of_eq ((RingHom.injective_iff_ker_eq_bot _).mp hg)
  obtain ⟨q, _, hq, hq0⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
    (⊥ : Ideal R) (⊥ : Ideal A) hg'
  let : q.IsPrime := hq
  let L := FractionRing (A ⧸ q)
  let f : A →ₐ[K] L := (IsScalarTower.toAlgHom K (A ⧸ q) L).comp (Ideal.Quotient.mkₐ K q)
  have hqgi : Function.Injective ((Ideal.Quotient.mk q).comp g.toRingHom) := by
    rw [RingHom.injective_iff_ker_eq_bot]
    change (⊥ : Ideal (A ⧸ q)).comap ((Ideal.Quotient.mk q).comp g.toRingHom) = ⊥
    rw [← Ideal.comap_comap, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact hq0
  have hfg : Function.Injective (f.comp g) :=
    (IsFractionRing.injective (A ⧸ q) L).comp hqgi
  have hrg : Function.Injective (f.rangeRestrict.comp g) := by
    intro x y he
    exact hfg (congrArg Subtype.val he)
  have hs : s ≤ n := by
    have hc := (trdeg_le_of_injective (f.rangeRestrict.comp g) hrg).trans (h L f)
    simpa only [MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fin, Cardinal.lift_natCast,
      Nat.cast_le] using hc
  calc
    ringKrullDim A ≤ ringKrullDim R := krullDim_le_of_integral g.toRingHom hint
    _ = s := by simp [R]
    _ ≤ n := by exact_mod_cast hs

end PermanentBorder.AlgebraicDimension

end OAI
