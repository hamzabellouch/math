import Mathlib
import OAI.Combinatorics.SharpRamsey.Geometry.TotalDegreeCombination

namespace OAI

/-! Incidence bounds for rich lines and finite point configurations. -/

section
section
section
open Finset Finsupp
open scoped BigOperators
open MvPolynomial Finsupp
open scoped BigOperators
open MvPolynomial
open scoped BigOperators
open Finset MvPolynomial UniqueFactorizationMonoid
open scoped BigOperators
open Finset MvPolynomial
namespace SharpLogRamsey.RichLinePolynomial
open MvPolynomial Finset
open FlatnessCore NonplaneCertificate
variable {K : Type*} [Field K]
lemma scaled_tangent_dot (g : Option (Fin 2) → K) (a : Fin 2) :
    ∑ i, g i*FlatnessCore.scaledTangent g a i = 0 := by
  simp [FlatnessCore.scaledTangent,Fintype.sum_option,mul_comm]

lemma eval_flatness (F : MvPolynomial (Option (Fin 2)) K) (x : Option (Fin 2) → K)
    (a b : Fin 2) : eval x (FlatnessCore.flatnessPolynomial F a b) =
    LineFlatness.hessian x F
      (FlatnessCore.scaledTangent (fun i => eval x (pderiv i F)) a)
      (FlatnessCore.scaledTangent (fun i => eval x (pderiv i F)) b) := by
  unfold FlatnessCore.flatnessPolynomial LineFlatness.hessian
  simp only [map_sum,map_mul]
  congr 1; ext j
  congr 1; ext i
  have he (a : Fin 2) (i : Option (Fin 2)) :
      eval x (FlatnessCore.scaledTangent (fun i => pderiv i F) a i) =
        FlatnessCore.scaledTangent (fun i => eval x (pderiv i F)) a i := by
    cases i with
    | none => simp [FlatnessCore.scaledTangent]
    | some i => by_cases hi : i = a <;> simp [FlatnessCore.scaledTangent,hi]
  rw [he,he]

theorem family_zero_at_three_lines (F : MvPolynomial (Fin 3) K)
    (x : Fin 3 → K) (v : Fin 3 → Fin 3 → K)
    (h2 : (2 : K) ≠ 0) (hl : ∀ i, LineFlatness.restrictLine x (v i) F = 0)
    (h01 : LinearIndependent K ![v 0,v 1])
    (h02 : LinearIndependent K ![v 0,v 2])
    (h12 : LinearIndependent K ![v 1,v 2]) (idx : Index) :
    eval x (flatFamily F idx) = 0 := by
  let e := idx.1
  let G := renameEquiv K e.symm F
  let y := x ∘ e
  let g := fun i => eval y (pderiv i G)
  have hc (z : Fin 3 → K) : (z ∘ e) ∘ e.symm = z := by ext i; simp
  have hge (i : Option (Fin 2)) : g i = eval x (pderiv (e i) F) := by
    have H := pderiv_rename e.symm.injective (e i) F
    simpa only [g,G,y,renameEquiv_apply,e.symm_apply_apply,eval_rename,hc] using congrArg (eval y) H
  change eval x (renameEquiv K e (flatnessPolynomial G idx.2.1 idx.2.2)) = 0
  rw [renameEquiv_apply,eval_rename,eval_flatness]
  change LineFlatness.hessian y G (FlatnessCore.scaledTangent g idx.2.1)
    (FlatnessCore.scaledTangent g idx.2.2) = 0
  by_cases hn : ∃ i, eval x (pderiv i F) ≠ 0
  · let u := FlatnessCore.scaledTangent g idx.2.1
    let w := FlatnessCore.scaledTangent g idx.2.2
    have hu : ∑ i, eval x (pderiv i F)*(u ∘ e.symm) i = 0 := by
      rw [← e.sum_comp]
      simpa only [Function.comp_apply,e.symm_apply_apply,← hge] using
        scaled_tangent_dot g idx.2.1
    have hw : ∑ i, eval x (pderiv i F)*(w ∘ e.symm) i = 0 := by
      rw [← e.sum_comp]
      simpa only [Function.comp_apply,e.symm_apply_apply,← hge] using
        scaled_tangent_dot g idx.2.2
    have H := LineFlatness.three_lines_tangent_zero F x v h2 hn hl h01 h02 h12
      (u ∘ e.symm) (w ∘ e.symm) hu hw
    simpa only [G,y,LineFlatness.hessian_rename,hc] using H
  · have hg : g = 0 := by
      ext i
      exact not_ne_iff.mp (fun h => hn ⟨e i,hge i ▸ h⟩)
    simp [hg,FlatnessCore.scaledTangent,LineFlatness.hessian]

variable {σ : Type*} [Fintype σ] [DecidableEq σ]
omit [Fintype σ] [DecidableEq σ] in
lemma natDegree_aeval_linear (x : σ → Polynomial K)
    (hx : ∀ i, (x i).natDegree ≤ 1) (F : MvPolynomial σ K) :
    (aeval x F).natDegree ≤ F.totalDegree := by
  conv_lhs => rw [F.as_sum]
  rw [map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro d hd
  rw [aeval_monomial]
  apply (Polynomial.natDegree_mul_le).trans
  simp only [Polynomial.algebraMap_apply,Polynomial.natDegree_C,zero_add]
  calc
    _ ≤ ∑ i ∈ d.support, (x i ^ d i).natDegree := Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ i ∈ d.support, d i := by
      apply Finset.sum_le_sum
      intro i hi
      rw [Polynomial.natDegree_pow]
      simpa [Nat.mul_comm] using Nat.mul_le_mul_right (d i) (hx i)
    _ ≤ F.totalDegree := le_totalDegree hd
omit [Fintype σ] [DecidableEq σ] in

lemma restriction_degree (x v : σ → K) (F : MvPolynomial σ K) :
    (LineFlatness.restrictLine x v F).natDegree ≤ F.totalDegree := by
  apply natDegree_aeval_linear
  intro i
  exact (Polynomial.natDegree_add_le _ _).trans (max_le (by simp)
    ((Polynomial.natDegree_mul_le).trans (by simp)))
omit [Fintype σ] [DecidableEq σ] in

lemma restriction_eval (x v : σ → K) (F : MvPolynomial σ K) (t : K) :
    (LineFlatness.restrictLine x v F).eval t = eval (fun i => x i+v i*t) F := by
  induction F using MvPolynomial.induction_on with
  | C c => simp [LineFlatness.restrictLine]
  | add f g hf hg => simp_all [LineFlatness.restrictLine]
  | mul_X f i hf => simp_all [LineFlatness.restrictLine]
omit [Fintype σ] [DecidableEq σ] in

lemma restriction_zero_of_many (x v : σ → K) (F : MvPolynomial σ K)
    (S : Finset K) (hcard : F.totalDegree < S.card)
    (hzero : ∀ t ∈ S, eval (fun i => x i+v i*t) F = 0) :
    LineFlatness.restrictLine x v F = 0 := by
  by_contra hn
  have H : S.card ≤ (LineFlatness.restrictLine x v F).natDegree := by
    apply Polynomial.card_le_degree_of_subset_roots
    intro t ht
    exact (Polynomial.mem_roots hn).mpr ((restriction_eval x v F t).trans (hzero t ht))
  exact (not_lt_of_ge (H.trans (restriction_degree x v F))) hcard

theorem auxiliary_polynomial {p : ℕ} [CharP K p] [IsAlgClosed K]
    (F : MvPolynomial (Fin 3) K) (hF : F ≠ 0) (hdeg : F.totalDegree < p)
    (hs : Squarefree F) (h2 : (2 : K) ≠ 0)
    (hn : ∀ L : MvPolynomial (Fin 3) K, L ∣ F → L.totalDegree ≤ 1 → IsUnit L) :
    ∃ Q : MvPolynomial (Fin 3) K, IsRelPrime F Q ∧ Q.totalDegree ≤ 3*F.totalDegree ∧
      ∀ (x v : Fin 3 → K) (S : Finset K), 3*F.totalDegree < S.card →
        (∀ t ∈ S, ∃ w : Fin 3 → Fin 3 → K,
          (∀ i, LineFlatness.restrictLine (fun j => x j+v j*t) (w i) F = 0) ∧
          LinearIndependent K ![w 0,w 1] ∧ LinearIndependent K ![w 0,w 2] ∧
          LinearIndependent K ![w 1,w 2]) → LineFlatness.restrictLine x v Q = 0 := by
  obtain ⟨c,hc,hd⟩ := exists_coprime_flat_combination F hF hdeg hs hn
  refine ⟨∑ i, c i • flatFamily F i,hc,hd,?_⟩
  intro x v S hS hpoints
  apply restriction_zero_of_many x v _ S (hd.trans_lt hS)
  intro t ht
  obtain ⟨w,hw,h01,h02,h12⟩ := hpoints t ht
  simp only [map_sum,Algebra.smul_def,MvPolynomial.algebraMap_eq,map_mul,eval_C]
  apply sum_eq_zero
  intro i hi
  rw [family_zero_at_three_lines F _ w h2 hw h01 h02 h12 i,mul_zero]

end SharpLogRamsey.RichLinePolynomial

end

section

section

open scoped BigOperators nonZeroDivisors
open Polynomial Finset
namespace SharpLogRamsey.ParametricBezout

section Fraction
variable {R K : Type*} [CommRing R] [IsDomain R] [NormalizedGCDMonoid R]
  [Field K] [Algebra R K] [IsFractionRing R K]

lemma isCoprime_map_fraction {f g : R[X]} (h : IsRelPrime f g) :
    IsCoprime (f.map (algebraMap R K)) (g.map (algebraMap R K)) := by
  apply isRelPrime_iff_isCoprime.mp
  intro a haf hag
  have ha : a ≠ 0 := by
    intro hz
    rw [hz,zero_dvd_iff] at haf hag
    have hf : f = 0 := (Polynomial.map_injective _ (IsFractionRing.injective R K))
      (by simpa using haf)
    have hg : g = 0 := (Polynomial.map_injective _ (IsFractionRing.injective R K))
      (by simpa using hag)
    rcases h.ne_zero_or_ne_zero with H|H <;> contradiction
  let b : R[X] := IsLocalization.integerNormalization R⁰ a
  have hb : b.primPart.IsPrimitive := Polynomial.isPrimitive_primPart b
  have hab : b.primPart.map (algebraMap R K) ∣ a := by
    have H := Polynomial.map_dvd (algebraMap R K) (Polynomial.primPart_dvd b)
    obtain ⟨c,hc,hbmap⟩ := IsLocalization.integerNormalization_spec R⁰ a
    change b.map (algebraMap R K) = _ at hbmap
    rw [hbmap,Algebra.smul_def,Polynomial.algebraMap_apply] at H
    have hc0 : algebraMap R K c ≠ 0 := by
      intro he
      apply nonZeroDivisors.ne_zero hc
      apply IsFractionRing.injective R K
      simpa using he
    exact (IsUnit.dvd_mul_left (Polynomial.isUnit_C.mpr
      (isUnit_iff_ne_zero.mpr hc0))).mp H
  have hbf := hb.dvd_of_fraction_map_dvd_fraction_map (hab.trans haf)
  have hbg := hb.dvd_of_fraction_map_dvd_fraction_map (hab.trans hag)
  exact Polynomial.isUnit_or_eq_zero_of_isUnit_integerNormalization_primPart ha (h hbf hbg)

include K in
lemma resultant_ne_zero_of_isRelPrime {f g : R[X]} (h : IsRelPrime f g) :
    f.resultant g ≠ 0 := by
  have hc := isCoprime_map_fraction (K := K) h
  have H := Polynomial.resultant_ne_zero _ _ hc
  have hf := Polynomial.natDegree_map_eq_of_injective (IsFractionRing.injective R K) f
  have hg := Polynomial.natDegree_map_eq_of_injective (IsFractionRing.injective R K) g
  rw [hf,hg,Polynomial.resultant_map_map] at H
  exact fun he => H (by rw [he,map_zero])
end Fraction

variable {K : Type*} [CommRing K] [IsDomain K] [NormalizedGCDMonoid K]
omit [IsDomain K] [NormalizedGCDMonoid K] in

lemma natDegree_det_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι K[X]) (d : ι → ℕ)
    (h : ∀ i j, (M i j).natDegree ≤ d j) :
    M.det.natDegree ≤ ∑ j,d j := by
  rw [Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro e he
  apply (Polynomial.natDegree_smul_le _ _).trans
  apply (Polynomial.natDegree_prod_le _ _).trans
  apply sum_le_sum
  intro i hi
  exact h (e i) i

omit [IsDomain K] [NormalizedGCDMonoid K] in

lemma resultant_degree_bound (f g : (K[X])[X]) (Df Dg : ℕ)
    (hf : ∀ i, (f.coeff i).natDegree ≤ Df)
    (hg : ∀ i, (g.coeff i).natDegree ≤ Dg) :
    (f.resultant g).natDegree ≤ f.natDegree*Dg+g.natDegree*Df := by
  calc
    _ ≤ ∑ j : Fin (f.natDegree+g.natDegree),
        j.addCases (fun _ => Dg) (fun _ => Df) := by
      apply natDegree_det_le
      intro i j
      refine Fin.addCases ?_ ?_ j
      · intro j
        simp only [Polynomial.sylvester,Matrix.of_apply,Fin.addCases_left]
        split_ifs <;> simp_all
      · intro j
        simp only [Polynomial.sylvester,Matrix.of_apply,Fin.addCases_right]
        split_ifs <;> simp_all
    _ = _ := by rw [Fin.sum_univ_add]; simp

omit [IsDomain K] [NormalizedGCDMonoid K] in

lemma resultant_eval_zero (f g : (K[X])[X]) (x y : K)
    (hf : (f.map (Polynomial.evalRingHom x)).eval y = 0)
    (hg : (g.map (Polynomial.evalRingHom x)).eval y = 0)
    (hdeg : f.natDegree ≠ 0 ∨ g.natDegree ≠ 0) :
    (f.resultant g).eval x = 0 := by
  obtain ⟨a,b,ha,hb,H⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant f g le_rfl le_rfl hdeg
  have h := congrArg (fun p : (K[X])[X] => (p.map (Polynomial.evalRingHom x)).eval y) H
  simpa [hf,hg] using h.symm

lemma common_points_card_le (f g : (K[X])[X]) (Df Dg : ℕ)
    (hc : IsRelPrime f g)
    (hf : ∀ i, (f.coeff i).natDegree ≤ Df)
    (hg : ∀ i, (g.coeff i).natDegree ≤ Dg)
    (hdeg : f.natDegree ≠ 0 ∨ g.natDegree ≠ 0)
    (S : Finset (K × K)) (hinj : Set.InjOn Prod.fst (S : Set (K × K)))
    (hS : ∀ z ∈ S, (f.map (Polynomial.evalRingHom z.1)).eval z.2 = 0 ∧
      (g.map (Polynomial.evalRingHom z.1)).eval z.2 = 0) :
    S.card ≤ f.natDegree*Dg+g.natDegree*Df := by
  classical
  have hne : f.resultant g ≠ 0 :=
    resultant_ne_zero_of_isRelPrime (K := FractionRing K[X]) hc
  calc
    S.card = (S.image Prod.fst).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (f.resultant g).natDegree := by
      apply Polynomial.card_le_degree_of_subset_roots
      intro x hx
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
      exact (Polynomial.mem_roots hne).mpr (resultant_eval_zero f g z.1 z.2
        (hS z hz).1 (hS z hz).2 hdeg)
    _ ≤ _ := resultant_degree_bound f g Df Dg hf hg
omit [NormalizedGCDMonoid K] in

lemma no_common_point_of_degree_zero (f g : (K[X])[X]) (hc : IsRelPrime f g)
    (hf : f.natDegree = 0) (hg : g.natDegree = 0) (x y : K)
    (hfx : (f.map (Polynomial.evalRingHom x)).eval y = 0)
    (hgx : (g.map (Polynomial.evalRingHom x)).eval y = 0) : False := by
  have hef := Polynomial.eq_C_of_natDegree_eq_zero hf
  have heg := Polynomial.eq_C_of_natDegree_eq_zero hg
  have hfr : (f.coeff 0).IsRoot x := by
    rw [hef] at hfx
    simpa only [Polynomial.map_C, Polynomial.eval_C, Polynomial.coe_evalRingHom, Polynomial.IsRoot] using hfx
  have hgr : (g.coeff 0).IsRoot x := by
    rw [heg] at hgx
    simpa only [Polynomial.map_C, Polynomial.eval_C, Polynomial.coe_evalRingHom, Polynomial.IsRoot] using hgx
  have hfd := map_dvd (Polynomial.C : K[X] →+* (K[X])[X])
    (Polynomial.dvd_iff_isRoot.mpr hfr)
  have hgd := map_dvd (Polynomial.C : K[X] →+* (K[X])[X])
    (Polynomial.dvd_iff_isRoot.mpr hgr)
  have hu : IsUnit (Polynomial.C (Polynomial.X-Polynomial.C x) : (K[X])[X]) := by
    apply hc
    · rwa [← hef] at hfd
    · rwa [← heg] at hgd
  exact Polynomial.not_isUnit_X_sub_C x (Polynomial.isUnit_C.mp hu)

theorem graph_branches_card_le (f g : (K[X])[X]) (Df Dg : ℕ)
    (hc : IsRelPrime f g)
    (hf : ∀ i, (f.coeff i).natDegree ≤ Df)
    (hg : ∀ i, (g.coeff i).natDegree ≤ Dg)
    (hfo : f.natDegree ≤ Df) (hgo : g.natDegree ≤ Dg)
    (S : Finset (K × K)) (hinj : Set.InjOn Prod.fst (S : Set (K × K)))
    (hS : ∀ z ∈ S, (f.map (Polynomial.evalRingHom z.1)).eval z.2 = 0 ∧
      (g.map (Polynomial.evalRingHom z.1)).eval z.2 = 0) :
    S.card ≤ 2*Df*Dg := by
  by_cases hdeg : f.natDegree ≠ 0 ∨ g.natDegree ≠ 0
  · apply (common_points_card_le f g Df Dg hc hf hg hdeg S hinj hS).trans
    nlinarith
  · push Not at hdeg
    have he : S = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact no_common_point_of_degree_zero f g hc hdeg.1 hdeg.2 z.1 z.2
        (hS z hz).1 (hS z hz).2
    simp [he]

end SharpLogRamsey.ParametricBezout

end

section

namespace SharpLogRamsey.GenericCoordinates
open MvPolynomial Finset
open scoped BigOperators
variable {K : Type*} [Field K] [Infinite K]
noncomputable section

lemma exists_eval_ne_zero {σ : Type*} (F : MvPolynomial σ K) (hF : F ≠ 0) :
    ∃ x : σ → K, eval x F ≠ 0 := by
  by_contra! h
  apply hF
  exact MvPolynomial.funext (by simpa using h)

lemma exists_first (T : Finset (Fin 3 → K)) (hT : ∀ v ∈ T, v ≠ 0) :
    ∃ a b : K, ∀ v ∈ T, v 0+a*v 1+b*v 2 ≠ 0 := by
  classical
  let f (v : Fin 3 → K) : MvPolynomial (Fin 2) K :=
    C (v 0)+C (v 1)*X 0+C (v 2)*X 1
  have hf : ∀ v ∈ T, f v ≠ 0 := by
    intro v hv H
    have h0 := congrArg (eval (fun _ => (0:K))) H
    have h1 := congrArg (eval ![1,0]) H
    have h2 := congrArg (eval ![0,1]) H
    simp [f] at h0 h1 h2
    apply hT v hv
    ext i
    fin_cases i <;> simp_all
  obtain ⟨x,hx⟩ := exists_eval_ne_zero (∏ v ∈ T, f v) (Finset.prod_ne_zero_iff.mpr hf)
  refine ⟨x 0,x 1,?_⟩
  intro v hv H
  apply hx
  rw [map_prod]
  apply Finset.prod_eq_zero hv
  simp [f,H,mul_comm]

lemma exists_second (a b : K) (T : Finset (Fin 3 → K))
    (hT : ∀ v ∈ T, v ≠ 0)
    (hk : ∀ v ∈ T, v 0+a*v 1+b*v 2 = 0) :
    ∃ c : K, ∀ v ∈ T, v 1+c*v 2 ≠ 0 := by
  classical
  let f (v : Fin 3 → K) : MvPolynomial Unit K := C (v 1)+C (v 2)*X ()
  have hf : ∀ v ∈ T, f v ≠ 0 := by
    intro v hv H
    have h1 := congrArg (eval (fun _ => (0:K))) H
    have h2 := congrArg (eval (fun _ => (1:K))) H
    simp [f] at h1 h2
    have h0 := hk v hv
    apply hT v hv
    ext i
    fin_cases i <;> simp_all
  obtain ⟨x,hx⟩ := exists_eval_ne_zero (∏ v ∈ T, f v) (Finset.prod_ne_zero_iff.mpr hf)
  refine ⟨x (),?_⟩
  intro v hv H
  apply hx
  rw [map_prod]
  apply Finset.prod_eq_zero hv
  simp [f,H,mul_comm]

def shear (a b c : K) : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K) where
  toFun x := ![x 0+a*x 1+b*x 2, x 1+c*x 2, x 2]
  invFun x := ![x 0-a*x 1+(a*c-b)*x 2, x 1-c*x 2, x 2]
  left_inv x := by ext i; fin_cases i <;> simp ; ring
  right_inv x := by ext i; fin_cases i <;> simp ; ring
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' r x := by ext i; fin_cases i <;> simp <;> ring

abbrev first (a b : K) : (Fin 3 → K) →ₗ[K] K :=
  LinearMap.proj 0+a • LinearMap.proj 1+b • LinearMap.proj 2
omit [Infinite K] in

lemma first_apply (a b : K) (x : Fin 3 → K) : first a b x = x 0+a*x 1+b*x 2 := by simp [first]

def line (x v : Fin 3 → K) : Set (Fin 3 → K) := Set.range (fun r : K => x+r • v)
def direction (t : (Fin 3 → K) →ₗ[K] K) (v : Fin 3 → K) : Fin 3 → K := (t v)⁻¹ • v
def base (t : (Fin 3 → K) →ₗ[K] K) (x v : Fin 3 → K) : Fin 3 → K :=
  x-t x • direction t v
omit [Infinite K] in

lemma map_direction (t : (Fin 3 → K) →ₗ[K] K) (v : Fin 3 → K) (hv : t v ≠ 0) :
    t (direction t v) = 1 := by simp [direction,hv]
omit [Infinite K] in
lemma map_base (t : (Fin 3 → K) →ₗ[K] K) (x v : Fin 3 → K) (hv : t v ≠ 0) :
    t (base t x v) = 0 := by simp [base,map_direction t v hv]
omit [Infinite K] in

lemma line_normalize (t : (Fin 3 → K) →ₗ[K] K) (x v : Fin 3 → K) (hv : t v ≠ 0) :
    line (base t x v) (direction t v) = line x v := by
  ext y
  constructor
  · rintro ⟨r,rfl⟩
    refine ⟨(r-t x)*(t v)⁻¹,?_⟩
    ext i
    simp [base,direction]
    ring
  · rintro ⟨r,rfl⟩
    refine ⟨t x+r*t v,?_⟩
    ext i
    simp [base,direction]
    field_simp
    ; ring

theorem exists_separating_coordinates {ι : Type*} [Fintype ι]
    (x v : ι → Fin 3 → K) (hv : ∀ i, v i ≠ 0)
    (hd : Function.Injective (fun i => line (x i) (v i))) :
    ∃ a b c : K, (∀ i, first a b (v i) ≠ 0) ∧
      Function.Injective (fun i =>
        Polynomial.C ((shear a b c (base (first a b) (x i) (v i))) 1)+
        Polynomial.C ((shear a b c (direction (first a b) (v i))) 1)*Polynomial.X) := by
  classical
  obtain ⟨a,b,hab⟩ := exists_first (Finset.univ.image v) (by
    intro w hw
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hw
    exact hv i)
  have ht : ∀ i, first a b (v i) ≠ 0 := by
    intro i
    exact hab (v i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  let u := fun i => direction (first a b) (v i)
  let z := fun i => base (first a b) (x i) (v i)
  have hdistinct : ∀ i j, i ≠ j → z i ≠ z j ∨ u i ≠ u j := by
    intro i j hij
    by_contra! H
    apply hij
    apply hd
    change line (x i) (v i) = line (x j) (v j)
    rw [← line_normalize (first a b) (x i) (v i) (ht i),
      ← line_normalize (first a b) (x j) (v j) (ht j)]
    exact congrArg₂ line H.1 H.2
  let I := {ij : ι × ι // ij.1 ≠ ij.2}
  let w : I → Fin 3 → K := fun ij =>
    if z ij.val.1 ≠ z ij.val.2 then z ij.val.1-z ij.val.2 else u ij.val.1-u ij.val.2
  have hw : ∀ i, w i ≠ 0 := by
    intro i
    change (if z i.val.1 ≠ z i.val.2 then z i.val.1-z i.val.2 else u i.val.1-u i.val.2) ≠ 0
    by_cases H : z i.val.1 ≠ z i.val.2
    · rw [ite_eq_left H]; exact sub_ne_zero.mpr H
    · rw [ite_eq_right H]; exact sub_ne_zero.mpr ((hdistinct _ _ i.property).resolve_left H)
  have hk : ∀ i, first a b (w i) = 0 := by
    intro i
    change first a b (if z i.val.1 ≠ z i.val.2 then z i.val.1-z i.val.2 else u i.val.1-u i.val.2) = 0
    by_cases H : z i.val.1 ≠ z i.val.2
    · rw [ite_eq_left H,map_sub,map_base _ _ _ (ht _),map_base _ _ _ (ht _),sub_self]
    · rw [ite_eq_right H,map_sub,map_direction _ _ (ht _),map_direction _ _ (ht _),sub_self]
  obtain ⟨c,hc⟩ := exists_second a b (Finset.univ.image w) (by
    intro q hq
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hq
    exact hw i) (by
    intro q hq
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hq
    exact hk i)
  refine ⟨a,b,c,ht,?_⟩
  intro i j H
  by_contra hij
  have h0 := congrArg (fun p : Polynomial K => p.coeff 0) H
  have h1 := congrArg (fun p : Polynomial K => p.coeff 1) H
  simp only [Polynomial.coeff_add,Polynomial.coeff_C,Polynomial.coeff_C_mul,
    Polynomial.coeff_X_zero,mul_zero,add_zero,Polynomial.coeff_X_one,mul_one,
    zero_add,ite_true,ite_false,Nat.one_ne_zero] at h0 h1
  have Hc := hc (w ⟨(i,j),hij⟩) (Finset.mem_image.mpr ⟨⟨(i,j),hij⟩,Finset.mem_univ _,rfl⟩)
  apply Hc
  change (if z i ≠ z j then z i-z j else u i-u j) 1+
    c*(if z i ≠ z j then z i-z j else u i-u j) 2 = 0
  by_cases Hz : z i ≠ z j
  · rw [ite_eq_left Hz]
    change z i 1+c*z i 2 = z j 1+c*z j 2 at h0
    simp only [Pi.sub_apply]
    linear_combination h0
  · rw [ite_eq_right Hz]
    change u i 1+c*u i 2 = u j 1+c*u j 2 at h1
    simp only [Pi.sub_apply]
    linear_combination h1

end
end SharpLogRamsey.GenericCoordinates

end

section

namespace SharpLogRamsey.PolynomialCoordinates
open MvPolynomial
variable {K : Type*} [Field K]
noncomputable section

end
end SharpLogRamsey.PolynomialCoordinates
end
end
end
end

end OAI
