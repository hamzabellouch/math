import OAI.AlgebraicGeometry.SurfaceCones.KummerProjChart

namespace OAI

noncomputable section

namespace SectionCompletion
variable {k K : Type} [Field k] [Field K] [Algebra k K]
variable (T : ℕ → Submodule k K) [SetLike.GradedMonoid T]
lemma isNoetherianRing_of_finiteType [Algebra.FiniteType k (polynomials T)]
    (hzero : T 0 = LinearMap.range (Algebra.linearMap k K)) :
    IsNoetherianRing (series T) := by
  obtain ⟨σ, hσ, v, d, hd, hv, hgen⟩ := finite_positive_presentation T hzero
  let := hσ
  exact SectionGenerated.isNoetherianRing T v d hd hv hgen

lemma adicComplete_of_finiteType [Algebra.FiniteType k (polynomials T)]
    (hzero : T 0 = LinearMap.range (Algebra.linearMap k K))
    [IsLocalRing (series T)] :
    IsAdicComplete (IsLocalRing.maximalIdeal (series T)) (series T) := by
  obtain ⟨σ, hσ, v, d, hd, hv, hgen⟩ := finite_positive_presentation T hzero
  let := hσ
  exact SectionGenerated.adicComplete T v d hd hv hgen

end SectionCompletion
namespace SectionCompletion
open Polynomial
variable {k K : Type} [Field k] [Field K] [Algebra k K]
variable (T : ℕ → Submodule k K) [SetLike.GradedMonoid T]

/-- The descending coefficient filtration on the graded polynomial algebra. -/
def degreeIdeal (n : ℕ) : Ideal (polynomials T) :=
  ((Ideal.span ({Polynomial.X} : Set K[X])) ^ n).comap (polynomials T).val.toRingHom

lemma mem_degreeIdeal (n : ℕ) (f : polynomials T) :
    f ∈ degreeIdeal T n ↔ ∀ j < n, f.val.coeff j = 0 := by
  change f.val ∈ Ideal.span ({Polynomial.X} : Set K[X]) ^ n ↔ _
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, Polynomial.X_pow_dvd_iff]

lemma degreeIdeal_one_pow_le (n : ℕ) : degreeIdeal T 1 ^ n ≤ degreeIdeal T n := by
  simpa [degreeIdeal] using
    (Ideal.le_comap_pow (K := Ideal.span ({Polynomial.X} : Set K[X]))
      (polynomials T).val.toRingHom n)

lemma monomial_mem_degreeIdeal_one {j : ℕ} (hj : j ≠ 0) (a : K) (ha : a ∈ T j) :
    (⟨monomial j a, (monomial_mem_polynomials T j a).mpr ha⟩ : polynomials T)
      ∈ degreeIdeal T 1 := by
  rw [mem_degreeIdeal]
  intro l hl
  have : l = 0 := by omega
  simp [this, Polynomial.coeff_monomial, hj]

/-- Finite positive homogeneous generation makes the degree and augmentation
filtrations cofinal; this is the estimate used in the manuscript, lines 224–237. -/
lemma degreeIdeal_cofinal {σ : Type} [Fintype σ] (v : σ → K) (d : σ → ℕ)
    (hd : ∀ i, d i ≠ 0) (hv : ∀ i, v i ∈ T (d i))
    (hspan : ∀ j, T j = HomogeneousGeneration.spanPiece v d j)
    (D : ℕ) (hD : 0 < D) (hbound : ∀ i, d i ≤ D) (n : ℕ) :
    degreeIdeal T (n * D) ≤ degreeIdeal T 1 ^ n := by
  classical
  let g (i : σ) : polynomials T :=
    ⟨monomial (d i) (v i), (monomial_mem_polynomials T _ _).mpr (hv i)⟩
  have hg : ∀ i, g i ∈ degreeIdeal T 1 :=
    fun i => monomial_mem_degreeIdeal_one T (hd i) (v i) (hv i)
  have hm (j : ℕ) (hj : n * D ≤ j) (a : K) (ha : a ∈ T j) :
      (⟨monomial j a, (monomial_mem_polynomials T _ _).mpr ha⟩ : polynomials T)
        ∈ degreeIdeal T 1 ^ n := by
    have haspan := ha
    rw [hspan j] at haspan
    induction haspan using Submodule.span_induction with
    | mem a h =>
      obtain ⟨⟨e, he⟩, rfl⟩ := h
      have hsum : n ≤ e.sum (fun _ x => x) := by
        have hw : Finsupp.weight d e ≤ (e.sum (fun _ x => x)) * D := by
          simp only [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul, Finset.sum_mul]
          apply Finset.sum_le_sum
          intro i _
          exact Nat.mul_le_mul_left (e i) (hbound i)
        rw [he] at hw
        exact (Nat.mul_le_mul_right_iff hD).mp (hj.trans hw)
      have hp : e.prod (fun i l => g i ^ l) ∈
          degreeIdeal T 1 ^ (e.sum (fun _ x => x)) := by
        simp only [Finsupp.prod, Finsupp.sum, ← Finset.prod_pow_eq_pow_sum]
        apply Ideal.prod_mem_prod
        intro i _
        exact Ideal.pow_mem_pow (hg i) _
      apply Ideal.pow_le_pow_right hsum
      convert hp using 1
      apply Subtype.ext
      change monomial j (e.prod (fun i l => v i ^ l)) =
        (e.prod (fun i l => g i ^ l)).val
      rw [← he, ← HomogeneousGeneration.monomial_prod v d]
      simp [Finsupp.prod, g]
    | zero =>
      convert (degreeIdeal T 1 ^ n).zero_mem using 1
      exact Subtype.ext (map_zero _)
    | add a b ha₁ hb₁ iha ihb =>
      have ha' : a ∈ T j := by rw [hspan]; exact ha₁
      have hb' : b ∈ T j := by rw [hspan]; exact hb₁
      convert Ideal.add_mem (degreeIdeal T 1 ^ n) (iha ha') (ihb hb') using 1
      exact Subtype.ext (map_add _ _ _)
    | smul c a ha₁ iha =>
      have ha' : a ∈ T j := by rw [hspan]; exact ha₁
      have hc := ((degreeIdeal T 1 ^ n).restrictScalars k).smul_mem c (iha ha')
      change c • (⟨monomial j a, _⟩ : polynomials T) ∈ degreeIdeal T 1 ^ n at hc
      convert hc using 1
      apply Subtype.ext
      ext l
      simp [Polynomial.coeff_monomial, Polynomial.coeff_smul]
  intro f hf
  have hf' := (mem_degreeIdeal T _ f).mp hf
  have hrecon : f = ∑ j ∈ f.val.support,
      (⟨monomial j (f.val.coeff j),
        (monomial_mem_polynomials T _ _).mpr (f.property j)⟩ : polynomials T) := by
    apply Subtype.ext
    change f.val = (polynomials T).val (∑ j ∈ f.val.support,
      (⟨monomial j (f.val.coeff j), _⟩ : polynomials T))
    rw [map_sum]
    exact (Polynomial.sum_monomial_eq f.val).symm
  rw [hrecon]
  apply Ideal.sum_mem
  intro j hj
  apply hm j ?_ _ (f.property j)
  by_contra! hn
  exact (Polynomial.mem_support_iff.mp hj) (hf' j hn)

end SectionCompletion

namespace SectionCompletion
variable {k K : Type} [Field k] [Field K] [Algebra k K]
variable (T : ℕ → Submodule k K) [SetLike.GradedMonoid T]
/-- A finite polynomial truncation of a coefficient-compatible series. -/
def truncation (n : ℕ) (p : series T) : polynomials T :=
  ⟨PowerSeries.trunc n p.val, by
    intro j
    rw [PowerSeries.coeff_trunc]
    split_ifs
    · exact p.property j
    · exact (T j).zero_mem⟩

lemma coeff_truncation (n j : ℕ) (p : series T) :
    (truncation T n p).val.coeff j = if j < n then PowerSeries.coeff j p.val else 0 :=
  PowerSeries.coeff_trunc j n p.val

variable (D : ℕ) (hD : 0 < D)
variable (hc : ∀ n, degreeIdeal T (n * D) ≤ degreeIdeal T 1 ^ n)

include hc in
lemma truncation_sub_mem_pow (p : series T) {n a b : ℕ}
    (ha : n * D ≤ a) (hb : n * D ≤ b) :
    truncation T a p - truncation T b p ∈ degreeIdeal T 1 ^ n := by
  apply hc n
  rw [mem_degreeIdeal]
  intro j hj
  change ((truncation T a p).val - (truncation T b p).val).coeff j = 0
  rw [Polynomial.coeff_sub]
  rw [coeff_truncation, coeff_truncation, ite_eq_left (hj.trans_le ha),
    ite_eq_left (hj.trans_le hb), sub_self]

/-- Truncation at the cofinal degree gives a genuine quotient algebra map. -/
def quotientTruncation (n : ℕ) : series T →ₐ[k] polynomials T ⧸ degreeIdeal T 1 ^ n where
  toFun p := Ideal.Quotient.mk _ (truncation T (n * D) p)
  map_one' := by
    rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    apply hc n
    rw [mem_degreeIdeal]
    intro j hj
    change (PowerSeries.trunc (n * D) (1 : PowerSeries K) - (1 : Polynomial K)).coeff j = 0
    rw [Polynomial.coeff_sub]
    simp [PowerSeries.coeff_trunc, hj, PowerSeries.coeff_one, Polynomial.coeff_one]
  map_mul' p q := by
    rw [← map_mul, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    apply hc n
    rw [mem_degreeIdeal]
    intro j hj
    change (PowerSeries.trunc (n * D) (p.val * q.val) -
      PowerSeries.trunc (n * D) p.val * PowerSeries.trunc (n * D) q.val).coeff j = 0
    rw [Polynomial.coeff_sub]
    rw [PowerSeries.coeff_trunc, ite_eq_left hj, sub_eq_zero]
    simpa only [← Polynomial.coe_mul, Polynomial.coeff_coe] using
      PowerSeries.coeff_mul_eq_coeff_trunc_mul_trunc p.val q.val hj
  map_zero' := by
    change Ideal.Quotient.mk _ (truncation T (n * D) 0) = 0
    have hz : truncation T (n * D) 0 = 0 := by
      apply Subtype.ext
      exact map_zero _
    rw [hz, map_zero]
  map_add' p q := by
    rw [← map_add]
    congr 1
    apply Subtype.ext
    exact map_add _ _ _
  commutes' a := by
    change Ideal.Quotient.mk _ (truncation T (n * D) (algebraMap k (series T) a)) =
      Ideal.Quotient.mk _ (algebraMap k (polynomials T) a)
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    apply hc n
    rw [mem_degreeIdeal]
    intro j hj
    change (PowerSeries.trunc (n * D) (algebraMap k (PowerSeries K) a) -
      algebraMap k (Polynomial K) a).coeff j = 0
    rw [Polynomial.coeff_sub]
    simp [PowerSeries.coeff_trunc, hj, PowerSeries.algebraMap_apply,
      Polynomial.algebraMap_apply, PowerSeries.coeff_C, Polynomial.coeff_C]

lemma quotientTruncation_compatible {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorₐ k (Ideal.pow_le_pow_right hmn)).comp
      (quotientTruncation T D hc n) = quotientTruncation T D hc m := by
  ext p
  change Ideal.Quotient.mk _ (truncation T (n * D) p) =
    Ideal.Quotient.mk _ (truncation T (m * D) p)
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  exact truncation_sub_mem_pow T D hc p (Nat.mul_le_mul_right D hmn) le_rfl

/-- The coefficient ring maps canonically to the vertex-adic completion. -/
def toCompletion : series T →ₐ[k] AdicCompletion (degreeIdeal T 1) (polynomials T) :=
  AdicCompletion.liftAlgHom (degreeIdeal T 1) (quotientTruncation T D hc)
    (fun hmn => quotientTruncation_compatible T D hc hmn)

lemma eval_toCompletion (n : ℕ) (p : series T) :
    AdicCompletion.evalₐ (degreeIdeal T 1) n (toCompletion T D hc p) =
      Ideal.Quotient.mk _ (truncation T (n * D) p) := by
  exact AdicCompletion.evalₐ_liftAlgHom _ _ _ _ _

end SectionCompletion

namespace SmallCM
variable {R : Type} [CommRing R] (I : Ideal R)

lemma completion_eval_compatible {m n : ℕ} (hmn : m ≤ n) (x : AdicCompletion I R) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn) (AdicCompletion.evalₐ I n x) =
      AdicCompletion.evalₐ I m x := by
  refine AdicCompletion.induction_on I R (p := fun y =>
    Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn) (AdicCompletion.evalₐ I n y) =
      AdicCompletion.evalₐ I m y) x ?_
  intro f
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk]
  change Ideal.Quotient.mk (I ^ m) (f.val n) = Ideal.Quotient.mk (I ^ m) (f.val m)
  exact AdicCompletion.Ideal.mk_eq_mk I hmn f

lemma mk_out_completion_eval {m n : ℕ} (hmn : m ≤ n) (x : AdicCompletion I R) :
    Ideal.Quotient.mk (I ^ m) (AdicCompletion.evalₐ I n x).out =
      AdicCompletion.evalₐ I m x := by
  rw [← completion_eval_compatible I hmn x]
  conv_rhs => rw [← Ideal.Quotient.mk_out (AdicCompletion.evalₐ I n x)]
  rw [Ideal.Quotient.factor_mk]

end SmallCM

namespace SectionCompletion
variable {k K : Type} [Field k] [Field K] [Algebra k K]
variable (T : ℕ → Submodule k K) [SetLike.GradedMonoid T]

lemma quotient_coeff_eq {n : ℕ} {a b : polynomials T}
    (h : Ideal.Quotient.mk (degreeIdeal T 1 ^ n) a = Ideal.Quotient.mk _ b)
    {j : ℕ} (hj : j < n) : a.val.coeff j = b.val.coeff j := by
  have hab := (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp h
  have he := (mem_degreeIdeal T n (a - b)).mp (degreeIdeal_one_pow_le T n hab) j hj
  change (a.val - b.val).coeff j = 0 at he
  rwa [Polynomial.coeff_sub, sub_eq_zero] at he

/-- Compatible vertex-adic residues determine each homogeneous coefficient. -/
def fromCompletion (x : AdicCompletion (degreeIdeal T 1) (polynomials T)) : series T :=
  ⟨PowerSeries.mk (fun j => ((AdicCompletion.evalₐ (degreeIdeal T 1) (j + 1) x).out).val.coeff j), by
    intro j
    rw [PowerSeries.coeff_mk]
    exact ((AdicCompletion.evalₐ (degreeIdeal T 1) (j + 1) x).out).property j⟩

lemma coeff_fromCompletion (x : AdicCompletion (degreeIdeal T 1) (polynomials T))
    {j n : ℕ} (hj : j < n) : PowerSeries.coeff j (fromCompletion T x).val =
      ((AdicCompletion.evalₐ (degreeIdeal T 1) n x).out).val.coeff j := by
  simp only [fromCompletion, PowerSeries.coeff_mk]
  apply quotient_coeff_eq T (n := j + 1) _ (Nat.lt_succ_self j)
  rw [Ideal.Quotient.mk_out, SmallCM.mk_out_completion_eval (degreeIdeal T 1) (Nat.succ_le_of_lt hj) x]

variable (D : ℕ) (hD : 0 < D)
variable (hc : ∀ n, degreeIdeal T (n * D) ≤ degreeIdeal T 1 ^ n)

include hD in
lemma from_toCompletion (p : series T) :
    fromCompletion T (toCompletion T D hc p) = p := by
  apply Subtype.ext
  ext j
  rw [coeff_fromCompletion T _ (j := j) (Nat.lt_succ_self j)]
  have hq : Ideal.Quotient.mk (degreeIdeal T 1 ^ (j + 1))
      (AdicCompletion.evalₐ (degreeIdeal T 1) (j + 1) (toCompletion T D hc p)).out =
      Ideal.Quotient.mk _ (truncation T ((j + 1) * D) p) := by
    rw [Ideal.Quotient.mk_out, eval_toCompletion]
  have hh := quotient_coeff_eq T hq (Nat.lt_succ_self j)
  rw [hh, coeff_truncation, ite_eq_left]
  exact (Nat.lt_succ_self j).trans_le (Nat.le_mul_of_pos_right _ hD)

include hD in
lemma to_fromCompletion (x : AdicCompletion (degreeIdeal T 1) (polynomials T)) :
    toCompletion T D hc (fromCompletion T x) = x := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [eval_toCompletion]
  let b := (AdicCompletion.evalₐ (degreeIdeal T 1) (n * D + 1) x).out
  calc
    Ideal.Quotient.mk _ (truncation T (n * D) (fromCompletion T x)) =
        Ideal.Quotient.mk (degreeIdeal T 1 ^ n) b := by
      rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
      apply hc n
      rw [mem_degreeIdeal]
      intro j hj
      change ((truncation T (n * D) (fromCompletion T x)).val - b.val).coeff j = 0
      rw [Polynomial.coeff_sub, coeff_truncation, ite_eq_left hj, sub_eq_zero]
      exact coeff_fromCompletion T x (n := n * D + 1) (hj.trans (Nat.lt_succ_self _))
    _ = AdicCompletion.evalₐ (degreeIdeal T 1) n x :=
      SmallCM.mk_out_completion_eval (degreeIdeal T 1)
        ((Nat.le_mul_of_pos_right n hD).trans (Nat.le_succ _)) x

/-- Literal identification of the graded coefficient completion and the
completion at the positive-degree ideal; no standard grading is assumed. -/
def completionEquiv : series T ≃ₐ[k] AdicCompletion (degreeIdeal T 1) (polynomials T) where
  __ := toCompletion T D hc
  invFun := fromCompletion T
  left_inv := from_toCompletion T D hD hc
  right_inv := to_fromCompletion T D hD hc

end SectionCompletion
namespace SectionCompletion
variable {k K : Type} [Field k] [Field K] [Algebra k K]
variable (T : ℕ → Submodule k K) [SetLike.GradedMonoid T]

lemma mem_degreeIdeal_one (f : polynomials T) :
    f ∈ degreeIdeal T 1 ↔ f.val.coeff 0 = 0 := by
  rw [mem_degreeIdeal]
  simp

lemma degreeIdeal_one_isMaximal
    (hzero : T 0 = LinearMap.range (Algebra.linearMap k K)) :
    (degreeIdeal T 1).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  refine ⟨?_, fun J f hIJ hf hfJ => ?_⟩
  · rw [mem_degreeIdeal_one]
    simp
  · have hc := f.property 0
    rw [hzero, LinearMap.mem_range] at hc
    obtain ⟨a, ha⟩ := hc
    have hsub : f - algebraMap k (polynomials T) a ∈ degreeIdeal T 1 := by
      rw [mem_degreeIdeal_one]
      change (f.val - algebraMap k (Polynomial K) a).coeff 0 = 0
      simp only [Polynomial.coeff_sub, Polynomial.algebraMap_apply, Polynomial.coeff_C,
        ↓reduceIte, sub_eq_zero]
      exact ha.symm
    have ha0 : a ≠ 0 := by
      intro hz
      apply hf
      rw [hz, map_zero, sub_zero] at hsub
      exact hsub
    have hamem : algebraMap k (polynomials T) a ∈ J := by
      simpa only [sub_sub_cancel] using J.sub_mem hfJ (hIJ hsub)
    have hh := J.mul_mem_left (algebraMap k (polynomials T) a⁻¹) hamem
    simpa only [← map_mul, inv_mul_cancel₀ ha0, map_one] using hh


end SectionCompletion

namespace ExplicitCone
open Algebra Polynomial
lemma rationalCone_trdeg : trdeg ℂ (RatFunc L) = 3 := by
  rw [SmallCM.trdeg_fractionRing ℂ L[X] (RatFunc L)]
  have h := trdeg_add_eq ℂ L (A := L[X])
  simpa only [functionField_trdeg, Cardinal.lift_ofNat, Polynomial.trdeg_of_isDomain,
    Cardinal.lift_one, Nat.cast_ofNat, show (2 : Cardinal) + 1 = 3 by norm_num] using h.symm


end ExplicitCone


end

end OAI
