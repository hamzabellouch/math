import Mathlib.Data.Finsupp.Option
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.ConePrimeLocalization

namespace OAI

namespace SiegelZeros


namespace WeightedTorusJets.W22

open scoped BigOperators
open MvPolynomial

variable {k σ : Type*} [CommRing k]

noncomputable def dehomogenize : MvPolynomial (Option σ) k →+* MvPolynomial σ k :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun o : Option σ => o.elim 1 MvPolynomial.X)

@[simp] theorem dehomogenize_X_none :
    dehomogenize (MvPolynomial.X none : MvPolynomial (Option σ) k) = 1 := by
  simp [dehomogenize]

@[simp] theorem dehomogenize_rename (p : MvPolynomial σ k) :
    dehomogenize (MvPolynomial.rename some p) = p := by
  change MvPolynomial.eval₂Hom MvPolynomial.C
    (fun o : Option σ => o.elim 1 MvPolynomial.X) (MvPolynomial.rename some p) = p
  rw [MvPolynomial.eval₂Hom_rename]
  change MvPolynomial.eval₂ MvPolynomial.C MvPolynomial.X p = p
  exact MvPolynomial.eval₂_eta p

noncomputable def homogenize (p : MvPolynomial σ k) : MvPolynomial (Option σ) k :=
  ∑ i ∈ Finset.range (p.totalDegree + 1),
    MvPolynomial.rename some (MvPolynomial.homogeneousComponent i p) *
      MvPolynomial.X none ^ (p.totalDegree - i)

@[simp] theorem dehomogenize_homogenize (p : MvPolynomial σ k) :
    dehomogenize (homogenize p) = p := by
  simp only [homogenize, map_sum, map_mul, map_pow, dehomogenize_rename,
    dehomogenize_X_none, one_pow, mul_one]
  exact MvPolynomial.sum_homogeneousComponent p

theorem homogenize_isHomogeneous (p : MvPolynomial σ k) :
    (homogenize p).IsHomogeneous p.totalDegree := by
  apply MvPolynomial.IsHomogeneous.sum
  intro i hi
  have hi' : i ≤ p.totalDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hcomponent :=
    (MvPolynomial.homogeneousComponent_isHomogeneous i p).rename_isHomogeneous
      (f := (some : σ → Option σ))
  simpa only [Nat.add_sub_of_le hi'] using
    hcomponent.mul (MvPolynomial.isHomogeneous_X_pow (none : Option σ) (p.totalDegree - i))

theorem homogenize_totalDegree_le (p : MvPolynomial σ k) :
    (homogenize p).totalDegree ≤ p.totalDegree :=
  (homogenize_isHomogeneous p).totalDegree_le

theorem homogenize_ne_zero {p : MvPolynomial σ k} (hp : p ≠ 0) : homogenize p ≠ 0 := by
  intro h
  apply hp
  have := congrArg dehomogenize h
  simpa using this

theorem map_span_homogenize {ι : Type*} (f : ι → MvPolynomial σ k) :
    Ideal.map dehomogenize (Ideal.span (Set.range (fun i => homogenize (f i)))) =
      Ideal.span (Set.range f) := by
  rw [Ideal.map_span]
  congr 1
  ext p
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨q, ⟨i, rfl⟩, hp⟩
    exact ⟨i, (dehomogenize_homogenize (f i)).symm.trans hp⟩
  · rintro ⟨i, rfl⟩
    exact ⟨homogenize (f i), ⟨i, rfl⟩, dehomogenize_homogenize (f i)⟩

end WeightedTorusJets.W22



namespace WeightedTorusJets.W22

variable {k σ : Type*} [CommRing k]

theorem optionExponent_degree (e : Option σ →₀ ℕ) :
    e.degree = e none + e.some.degree := by
  exact e.sum_option_index (fun _ n => n) (fun _ => rfl) (fun _ _ _ => rfl)

@[simp] theorem dehomogenize_monomial (e : Option σ →₀ ℕ) (c : k) :
    dehomogenize (MvPolynomial.monomial e c) = MvPolynomial.monomial e.some c := by
  rw [dehomogenize, MvPolynomial.eval₂Hom_monomial,
    Finsupp.prod_option_index _ _ (by simp) (by intros; simp [pow_add])]
  simp only [Option.elim_none, Option.elim_some, one_pow, one_mul]
  rw [MvPolynomial.monomial_eq]

theorem homogeneous_support_some_injective
    {F : MvPolynomial (Option σ) k} {n : ℕ} (hF : F.IsHomogeneous n) :
    Set.InjOn Finsupp.some (F.support : Set (Option σ →₀ ℕ)) := by
  intro d hd e he hde
  have hddeg : d.degree = n := (hF.degree_eq_sum_deg_support hd).symm
  have hedeg : e.degree = n := (hF.degree_eq_sum_deg_support he).symm
  have hdegree : d.degree = e.degree := hddeg.trans hedeg.symm
  rw [optionExponent_degree, optionExponent_degree, hde] at hdegree
  have hnone : d none = e none := Nat.add_right_cancel hdegree
  apply Finsupp.ext
  intro i
  cases i with
  | none => exact hnone
  | some i => exact congrArg (fun x : σ →₀ ℕ => x i) hde

theorem coeff_dehomogenize_of_isHomogeneous
    {F : MvPolynomial (Option σ) k} {n : ℕ} (hF : F.IsHomogeneous n)
    {e : Option σ →₀ ℕ} (he : e ∈ F.support) :
    (dehomogenize F).coeff e.some = F.coeff e := by
  classical
  conv_lhs => rw [F.as_sum]
  simp only [map_sum, dehomogenize_monomial, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single e]
  · simp
  · intro d hd hde
    have hs : d.some ≠ e.some := fun hs =>
      hde (homogeneous_support_some_injective hF hd he hs)
    simp only [ite_eq_right hs]
  · exact fun h => (h he).elim

theorem dehomogenize_eq_zero_of_isHomogeneous
    {F : MvPolynomial (Option σ) k} {n : ℕ}
    (hF : F.IsHomogeneous n) (hz : dehomogenize F = 0) : F = 0 := by
  apply MvPolynomial.ext
  intro e
  by_cases he : e ∈ F.support
  · simpa only [hz, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using
      (coeff_dehomogenize_of_isHomogeneous hF he).symm
  · simpa only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using
      MvPolynomial.notMem_support_iff.mp he

theorem dehomogenize_injective_on_homogeneous
    {F G : MvPolynomial (Option σ) k} {n : ℕ}
    (hF : F.IsHomogeneous n) (hG : G.IsHomogeneous n)
    (h : dehomogenize F = dehomogenize G) : F = G := by
  apply sub_eq_zero.mp
  apply dehomogenize_eq_zero_of_isHomogeneous (hF.sub hG)
  rw [map_sub, h, sub_self]

end WeightedTorusJets.W22


end SiegelZeros

noncomputable section
open scoped BigOperators

namespace SiegelZeros.W17.ConeLocalLength

section Scaling

variable {k B σ : Type*} [CommRing k] [CommRing B]

theorem eval₂_scale_of_isHomogeneous (F : MvPolynomial σ k) (d : ℕ)
    (hF : F.IsHomogeneous d) (c : k →+* B) (x : σ → B) (t : B) :
    MvPolynomial.eval₂ c (fun i => x i * t) F =
      MvPolynomial.eval₂ c x F * t ^ d := by
  classical
  simp only [MvPolynomial.eval₂_eq, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [mul_pow, Finset.prod_mul_distrib]
  rw [Finset.prod_pow_eq_pow_sum, ← hF.degree_eq_sum_deg_support hm, mul_assoc]

end Scaling

variable (k σ : Type*) [CommRing k]

theorem coneToLaurent_homogeneous (F : ConeRing k σ) (d : ℕ)
    (hF : F.IsHomogeneous d) :
    coneToLaurent k σ F =
      LaurentPolynomial.C (WeightedTorusJets.W22.dehomogenize F) *
        (LaurentPolynomial.T 1 : LaurentChart k σ) ^ d := by
  let x : Option σ → LaurentChart k σ :=
    fun i => LaurentPolynomial.C (i.elim 1 MvPolynomial.X)
  have hscaled : coneToLaurent k σ F =
      MvPolynomial.eval₂ (LaurentPolynomial.C.comp MvPolynomial.C)
        (fun i => x i * LaurentPolynomial.T 1) F := by
    have hv : (fun i : Option σ => i.elim (LaurentPolynomial.T 1 : LaurentChart k σ)
        (fun j => LaurentPolynomial.C (MvPolynomial.X j) * LaurentPolynomial.T 1)) =
        (fun i => x i * LaurentPolynomial.T 1) := by
      funext i
      cases i <;> simp [x]
    change MvPolynomial.eval₂ (LaurentPolynomial.C.comp MvPolynomial.C)
      (fun i : Option σ => i.elim (LaurentPolynomial.T 1)
        (fun j => LaurentPolynomial.C (MvPolynomial.X j) * LaurentPolynomial.T 1)) F = _
    rw [hv]
  rw [hscaled, eval₂_scale_of_isHomogeneous F d hF]
  apply congrArg (fun polynomial : LaurentChart k σ =>
    polynomial * LaurentPolynomial.T 1 ^ d)
  exact (MvPolynomial.hom_eval₂ F MvPolynomial.C LaurentPolynomial.C
    (fun index : Option σ => index.elim 1 MvPolynomial.X)).symm

theorem coneToLaurent_homogenize (f : AffineRing k σ) :
    coneToLaurent k σ (WeightedTorusJets.W22.homogenize f) =
      LaurentPolynomial.C f * (LaurentPolynomial.T 1 : LaurentChart k σ) ^ f.totalDegree := by
  simpa using coneToLaurent_homogeneous k σ (WeightedTorusJets.W22.homogenize f)
    f.totalDegree (WeightedTorusJets.W22.homogenize_isHomogeneous f)

theorem map_homogenized_span_eq_laurent_span {ι : Type*} (f : ι → AffineRing k σ) :
    (Ideal.span (Set.range (fun i => WeightedTorusJets.W22.homogenize (f i)))).map
      (coneToLaurent k σ) =
    (Ideal.span (Set.range f)).map (LaurentPolynomial.C : AffineRing k σ →+* LaurentChart k σ) := by
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change coneToLaurent k σ (WeightedTorusJets.W22.homogenize (f i)) ∈
      (Ideal.span (Set.range f)).map
        (LaurentPolynomial.C : AffineRing k σ →+* LaurentChart k σ)
    rw [coneToLaurent_homogenize]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _
      (Ideal.subset_span (Set.mem_range_self i)))
  · apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change (LaurentPolynomial.C (f i) : LaurentChart k σ) ∈
      (Ideal.span (Set.range (fun j => WeightedTorusJets.W22.homogenize (f j)))).map
        (coneToLaurent k σ)
    apply (Ideal.mul_unit_mem_iff_mem _
      ((LaurentPolynomial.isUnit_T (R := AffineRing k σ) 1).pow (f i).totalDegree)).mp
    rw [← coneToLaurent_homogenize]
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_range_self i))

variable (P : Ideal (AffineRing k σ)) [P.IsPrime]

theorem homogeneous_mem_conePrime_iff (F : ConeRing k σ) (d : ℕ)
    (hF : F.IsHomogeneous d) :
    F ∈ conePrime k σ P ↔ WeightedTorusJets.W22.dehomogenize F ∈ P := by
  change coneAwayToLaurent k σ (algebraMap (ConeRing k σ) (ConeAway k σ) F) ∈
    laurentPrime (AffineRing k σ) P ↔ _
  rw [coneAwayToLaurent_algebraMap, coneToLaurent_homogeneous k σ F d hF,
    Ideal.mul_unit_mem_iff_mem _ ((LaurentPolynomial.isUnit_T 1).pow d)]
  change WeightedTorusJets.W22.dehomogenize F ∈
    (laurentPrime (AffineRing k σ) P).comap (algebraMap (AffineRing k σ) (LaurentChart k σ)) ↔ _
  rw [laurentPrime_comap]

theorem homogenize_mem_conePrime_iff (f : AffineRing k σ) :
    WeightedTorusJets.W22.homogenize f ∈ conePrime k σ P ↔ f ∈ P := by
  simpa using homogeneous_mem_conePrime_iff k σ P
    (WeightedTorusJets.W22.homogenize f) f.totalDegree
    (WeightedTorusJets.W22.homogenize_isHomogeneous f)

end SiegelZeros.W17.ConeLocalLength

end

end OAI
