import Mathlib
import OAI.Combinatorics.SharpRamsey.Geometry.Card

namespace OAI

/-! Incidence bounds for rich lines and finite point configurations. -/

section
section
section
section
open scoped BigOperators Classical
open Finset
namespace SharpLogRamsey.Sampling
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable def weight (p : ℝ) (f : V → Bool) : ℝ :=
  ∏ v, if f v then p else 1-p

def selected (f : V → Bool) : Finset V := univ.filter (fun v => f v = true)
omit [DecidableEq V] in

theorem mem_selected (f : V → Bool) (v : V) : v ∈ selected f ↔ f v = true := by
  simp [selected]
omit [DecidableEq V] in

theorem weight_nonneg {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (f : V → Bool) :
    0 ≤ weight p f := by
  apply prod_nonneg
  intro v _
  split <;> linarith

theorem sum_weight (p : ℝ) : ∑ f : V → Bool, weight p f = 1 := by
  simp_rw [weight]
  rw [← Fintype.prod_sum (fun (_v : V) (b : Bool) => if b then p else 1-p)]
  simp

theorem containment_moment (p : ℝ) (A : Finset V) :
    (∑ f : V → Bool, weight p f * (if A ⊆ selected f then 1 else 0)) = p^A.card := by
  have hi (f : V → Bool) :
      (if A ⊆ selected f then (1 : ℝ) else 0) =
        ∏ v : V, if v ∈ A then (if f v then 1 else 0) else 1 := by
    by_cases h : A ⊆ selected f
    · rw [ite_eq_left h]
      symm
      apply prod_eq_one
      intro v _
      by_cases hv : v ∈ A
      · simp [hv, (mem_selected f v).mp (h hv)]
      · simp [hv]
    · rw [ite_eq_right h]
      obtain ⟨v, hv, hfv⟩ := not_subset.mp h
      symm
      apply prod_eq_zero (mem_univ v)
      simp only [mem_selected, Bool.not_eq_true] at hfv
      simp [hv, hfv]
  simp_rw [hi, weight, ← prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (v : V) (b : Bool) =>
    (if b then p else 1-p) * (if v ∈ A then (if b then (1:ℝ) else 0) else 1))]
  calc
    _ = ∏ v : V, if v ∈ A then p else 1 := by
      apply prod_congr rfl
      intro v _
      by_cases hv : v ∈ A <;> simp [hv]
    _ = p^A.card := by simp

noncomputable def count (F : Finset (Finset V)) (S : Finset V) : ℕ :=
  (F.filter (· ⊆ S)).card

theorem family_moment (p : ℝ) (F : Finset (Finset V)) {a : ℕ}
    (hF : ∀ A ∈ F, A.card = a) :
    (∑ f : V → Bool, weight p f * count F (selected f)) = p^a * F.card := by
  have hc (S : Finset V) : (count F S : ℝ) = ∑ A ∈ F, if A ⊆ S then 1 else 0 := by
    simp [count, sum_boole]
  simp_rw [hc, mul_sum]
  rw [sum_comm]
  simp_rw [containment_moment]
  rw [sum_congr rfl (fun A hA => by rw [hF A hA])]
  simp [mul_comm]

theorem size_moment (p : ℝ) :
    (∑ f : V → Bool, weight p f * (selected f).card) = p * Fintype.card V := by
  have hc (f : V → Bool) : ((selected f).card : ℝ) =
      ∑ v : V, if ({v} : Finset V) ⊆ selected f then 1 else 0 := by
    simp [selected, sum_boole]
  simp_rw [hc, mul_sum]
  rw [sum_comm]
  simp_rw [containment_moment]
  simp [mul_comm]

theorem exists_ge_mean {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (X : (V → Bool) → ℝ) : ∃ f, (∑ g, weight p g * X g) ≤ X f := by
  obtain ⟨f, _, hf⟩ := exists_max_image (univ : Finset (V → Bool)) X univ_nonempty
  refine ⟨f, ?_⟩
  calc
    (∑ g, weight p g * X g) ≤ ∑ g, weight p g * X f := by
      exact sum_le_sum (fun g _ => mul_le_mul_of_nonneg_left (hf g (mem_univ g))
        (weight_nonneg hp hp1 g))
    _ = X f := by rw [← sum_mul, sum_weight, one_mul]

end SharpLogRamsey.Sampling

namespace SharpLogRamsey.RichSampling
open Sampling Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable section

lemma moment (p b : ℝ) (A : Finset V) :
    (∑ f : V → Bool, weight p f * b^(A ∩ selected f).card) =
      (1-p+p*b)^A.card := by
  have hi (f : V → Bool) : b^(A ∩ selected f).card =
      ∏ v : V, if v ∈ A ∧ f v = true then b else 1 := by
    rw [← prod_filter]
    simp only [prod_const]
    congr 2
    ext v
    simp [selected]
  simp_rw [hi,weight,← prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (v : V) (a : Bool) =>
    (if a then p else 1-p)*(if v ∈ A ∧ a = true then b else 1))]
  calc
    _ = ∏ v : V, if v ∈ A then 1-p+p*b else 1 := by
      apply prod_congr rfl
      intro v hv
      by_cases H : v ∈ A <;> simp [H] ; ring
    _ = _ := by simp

lemma exp_neg_half_le : Real.exp (-(1/2:ℝ)) ≤ 2/3 := by
  have h := Real.add_one_le_exp (1/2:ℝ)
  have he : Real.exp (-(1/2:ℝ))*Real.exp (1/2:ℝ) = 1 := by rw [← Real.exp_add]; norm_num
  have hm := mul_le_mul_of_nonneg_left h (Real.exp_pos (-(1/2:ℝ))).le
  nlinarith

lemma lower_tail (p M : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (A : Finset V) (hM : M ≤ A.card) :
    (∑ f : V → Bool, weight p f *
      (if ((A ∩ selected f).card : ℝ) ≤ p*M/2 then 1 else 0)) ≤
      Real.exp (-p*M/12) := by
  have hpoint (f : V → Bool) :
      (if ((A ∩ selected f).card : ℝ) ≤ p*M/2 then (1:ℝ) else 0) ≤
        Real.exp (p*M/4)*Real.exp (-(1/2:ℝ))^(A ∩ selected f).card := by
    rw [← Real.exp_nat_mul,← Real.exp_add]
    split_ifs with H
    · rw [Real.one_le_exp_iff]
      linarith
    · exact (Real.exp_pos _).le
  have hb0 : 0 ≤ 1-p+p*Real.exp (-(1/2:ℝ)) :=
    add_nonneg (by linarith) (mul_nonneg hp (Real.exp_pos _).le)
  have hb : 1-p+p*Real.exp (-(1/2:ℝ)) ≤ Real.exp (-p/3) := by
    have H := mul_le_mul_of_nonneg_left exp_neg_half_le hp
    have E := Real.add_one_le_exp (-p/3)
    linarith
  calc
    _ ≤ ∑ f : V → Bool, weight p f *
        (Real.exp (p*M/4)*Real.exp (-(1/2:ℝ))^(A ∩ selected f).card) :=
      sum_le_sum (fun f hf => mul_le_mul_of_nonneg_left (hpoint f) (weight_nonneg hp hp1 f))
    _ = Real.exp (p*M/4)*(1-p+p*Real.exp (-(1/2:ℝ)))^A.card := by
      rw [← moment p (Real.exp (-(1/2:ℝ))) A,mul_sum]
      apply sum_congr rfl
      intro f hf
      ring
    _ ≤ Real.exp (p*M/4)*(Real.exp (-p/3))^A.card :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb0 hb _) (Real.exp_pos _).le
    _ = Real.exp (p*M/4+(A.card:ℝ)*(-p/3)) := by rw [Real.exp_add,Real.exp_nat_mul]
    _ ≤ Real.exp (-p*M/12) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hM hp]

theorem exists_sample [Nonempty V] (p M : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (L : Finset (Finset V)) (hM : ∀ A ∈ L, M ≤ A.card)
    (hprob : (L.card:ℝ)*Real.exp (-p*M/12) < 1/2) :
    ∃ S : Finset V, (S.card:ℝ) ≤ 2*p*Fintype.card V ∧
      ∀ A ∈ L, p*M/2 < ((A ∩ S).card:ℝ) := by
  classical
  let N : ℝ := Fintype.card V
  have hN : 0 < N := by dsimp [N]; exact_mod_cast (Fintype.card_pos (α := V))
  let bad := fun f : V → Bool => ∑ A ∈ L,
    if ((A ∩ selected f).card:ℝ) ≤ p*M/2 then (1:ℝ) else 0
  let X := fun f : V → Bool => ((selected f).card:ℝ)+2*p*N*bad f
  have hb : (∑ f : V → Bool, weight p f*bad f) ≤
      L.card*Real.exp (-p*M/12) := by
    simp only [bad,mul_sum]
    rw [sum_comm]
    calc
      _ ≤ ∑ _A ∈ L, Real.exp (-p*M/12) :=
        sum_le_sum (fun A hA => lower_tail p M hp.le hp1 A (hM A hA))
      _ = _ := by simp
  have hmean : (∑ f, weight p f*X f) < 2*p*N := by
    have he : (∑ f, weight p f*X f) = p*N+2*p*N*(∑ f, weight p f*bad f) := by
      simp only [X,mul_add,sum_add_distrib]
      rw [size_moment,mul_sum]
      congr 1
      apply sum_congr rfl
      intro f hf
      ring
    rw [he]
    have hlt := hb.trans_lt hprob
    have hpos : 0 < p*N := mul_pos hp hN
    nlinarith
  obtain ⟨f,hf⟩ := exists_ge_mean hp.le hp1 (fun f => -X f)
  simp only [mul_neg,Finset.sum_neg_distrib] at hf
  have hX : X f < 2*p*N := by linarith
  have hb0 : 0 ≤ bad f := by apply sum_nonneg; intro A hA; split_ifs <;> norm_num
  refine ⟨selected f,?_,?_⟩
  · have hcoef : 0 ≤ 2*p*N := by positivity
    change ((selected f).card:ℝ) ≤ 2*p*N
    dsimp only [X] at hX
    nlinarith [mul_nonneg hcoef hb0]
  · intro A hA
    by_contra H
    have ha : ((A ∩ selected f).card:ℝ) ≤ p*M/2 := le_of_not_gt H
    have hb1 : 1 ≤ bad f := by
      have H := single_le_sum (s := L) (f := fun B =>
        if ((B ∩ selected f).card:ℝ) ≤ p*M/2 then (1:ℝ) else 0)
        (fun B hB => by split_ifs <;> norm_num) hA
      simpa only [ite_eq_left ha] using H
    have hcoef : 0 ≤ 2*p*N := by positivity
    have hcard : 0 ≤ ((selected f).card:ℝ) := Nat.cast_nonneg _
    dsimp only [X] at hX
    nlinarith [mul_le_mul_of_nonneg_left hb1 hcoef]

end
end SharpLogRamsey.RichSampling

end

section

namespace SharpLogRamsey.Interpolation
open Finset MvPolynomial
open scoped BigOperators
variable {K : Type*} [Field K]
noncomputable section

abbrev Box (n h : ℕ) := Fin n → Fin (h+1)
def exponent {n h : ℕ} (d : Box n h) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (d i).val)

lemma exponent_injective (n h : ℕ) : Function.Injective (exponent (n := n) (h := h)) := by
  intro d e H
  ext i
  exact congrArg (fun f : Fin n →₀ ℕ => f i) H

lemma exponent_degree_le {n h : ℕ} (d : Box n h) : (exponent d).degree ≤ n*h := by
  change (exponent d).sum (fun _ e => e) ≤ n*h
  rw [Finsupp.sum_fintype]
  · calc
      ∑ i, (exponent d) i ≤ ∑ _i : Fin n, h := by
        apply sum_le_sum
        intro i hi
        exact Nat.le_of_lt_succ (d i).isLt
      _ = n*h := by simp
  · simp

lemma monomials_independent (n h : ℕ) :
    LinearIndependent K (fun d : Box n h => monomial (exponent d) (1:K)) :=
  (basisMonomials (Fin n) K).linearIndependent.comp exponent (exponent_injective n h)

theorem exists_vanishing (n h : ℕ) (S : Finset (Fin n → K))
    (hS : S.card < (h+1)^n) :
    ∃ F : MvPolynomial (Fin n) K, F ≠ 0 ∧ F.totalDegree ≤ n*h ∧
      ∀ x ∈ S, eval x F = 0 := by
  classical
  let v : Box n h → (S → K) := fun d x => eval x.val (monomial (exponent d) (1:K))
  have hn : ¬LinearIndependent K v := by
    intro H
    have H' := H.fintype_card_le_finrank
    have he : Fintype.card (Box n h) = (h+1)^n := by simp [Box]
    have hf : Module.finrank K (S → K) = S.card := by simp
    rw [he,hf] at H'
    omega
  obtain ⟨c,hc,d,hd⟩ := Fintype.not_linearIndependent_iff.mp hn
  refine ⟨∑ d, c d • monomial (exponent d) (1:K),?_,?_,?_⟩
  · intro H
    exact hd ((Fintype.linearIndependent_iff.mp (monomials_independent (K := K) n h)) c H d)
  · apply totalDegree_finsetSum_le
    intro d hd
    apply (totalDegree_smul_le _ _).trans
    exact (totalDegree_monomial_le _ _).trans (exponent_degree_le d)
  · intro x hx
    have H := congrFun hc ⟨x,hx⟩
    simpa [v,Algebra.smul_def] using H

end
end SharpLogRamsey.Interpolation

end

namespace SharpLogRamsey.SamplePolynomial
open Finset MvPolynomial AffineIncidence
open scoped BigOperators
variable {K V ι : Type*} [Field K] [Fintype V] [Nonempty V] [Fintype ι]
noncomputable section

lemma degree_le_of_dvd {F G : MvPolynomial (Fin 3) K} (hF : F ≠ 0) (h : G ∣ F) :
    G.totalDegree ≤ F.totalDegree := by
  obtain ⟨H,rfl⟩ := h
  have hG : G ≠ 0 := left_ne_zero_of_mul hF
  have hH : H ≠ 0 := right_ne_zero_of_mul hF
  rw [totalDegree_mul_of_isDomain hG hH]
  omega

omit [Fintype ι] in

lemma squarefree_reduction (F : MvPolynomial (Fin 3) K) (hF : F ≠ 0)
    (x v : ι → Fin 3 → K) (hzero : ∀ i, LineFlatness.restrictLine (x i) (v i) F = 0) :
    ∃ G : MvPolynomial (Fin 3) K, G ≠ 0 ∧ Squarefree G ∧
      G.totalDegree ≤ F.totalDegree ∧
      ∀ i, LineFlatness.restrictLine (x i) (v i) G = 0 := by
  obtain ⟨G,n,hG,hGF,hFG⟩ := exists_squarefree_dvd_pow_of_ne_zero hF
  refine ⟨G,ne_zero_of_dvd_ne_zero hF hGF,hG,degree_le_of_dvd hF hGF,?_⟩
  intro i
  have H := map_dvd (aeval (fun j => Polynomial.C (x i j)+Polynomial.C (v i j)*Polynomial.X)) hFG
  change LineFlatness.restrictLine (x i) (v i) F ∣
    (aeval (fun j => Polynomial.C (x i j)+Polynomial.C (v i j)*Polynomial.X)) (G^n) at H
  rw [hzero i,map_pow] at H
  exact eq_zero_of_pow_eq_zero (zero_dvd_iff.mp H)

theorem exists_polynomial (points : V → Fin 3 → K) (hinj : Function.Injective points)
    (x v : ι → Fin 3 → K) (hv : ∀ i, v i ≠ 0)
    (A : ι → Finset V) (hA : ∀ i a, a ∈ A i → points a ∈ carrier (x i) (v i))
    (p M : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hM : ∀ i, M ≤ (A i).card)
    (hprob : (Fintype.card ι:ℝ)*Real.exp (-p*M/12) < 1/2)
    (h : ℕ) (hsize : 2*p*Fintype.card V < ((h+1)^3:ℕ)) (hdeg : (3*h:ℕ) ≤ p*M/2) :
    ∃ F : MvPolynomial (Fin 3) K, F ≠ 0 ∧ Squarefree F ∧ F.totalDegree ≤ 3*h ∧
      ∀ i, LineFlatness.restrictLine (x i) (v i) F = 0 := by
  classical
  let L := univ.image A
  have hL : (L.card:ℝ)*Real.exp (-p*M/12) < 1/2 := by
    have hc : L.card ≤ Fintype.card ι := (card_image_le).trans_eq (card_univ)
    exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (Real.exp_pos _).le).trans_lt hprob
  obtain ⟨S,hS,hall⟩ := RichSampling.exists_sample p M hp hp1 L
    (by intro B hB; obtain ⟨i,hi,rfl⟩ := mem_image.mp hB; exact hM i) hL
  let T := S.image points
  have hT : T.card < (h+1)^3 := by
    have he : T.card = S.card := card_image_of_injective S hinj
    rw [he]
    exact_mod_cast hS.trans_lt hsize
  obtain ⟨F,hF,hFd,hFT⟩ := Interpolation.exists_vanishing 3 h T hT
  have hzero (i : ι) : LineFlatness.restrictLine (x i) (v i) F = 0 := by
    let B := (A i ∩ S).image points
    let f : K → Fin 3 → K := fun t => x i+t • v i
    let R := B.preimage f (parametrization_injective _ _ (hv i)).injOn
    have hR : R.card = (A i ∩ S).card := by
      rw [card_preimage]
      have he : B.filter (fun y => y ∈ Set.range f) = B := by
        apply filter_eq_self.mpr
        intro y hy
        obtain ⟨a,ha,rfl⟩ := mem_image.mp hy
        exact hA i a (mem_inter.mp ha).1
      rw [he,card_image_of_injective _ hinj]
    have hr : F.totalDegree < R.card := by
      rw [hR]
      have H := (show (3*h:ℕ) ≤ p*M/2 from hdeg).trans_lt (hall (A i) (mem_image.mpr ⟨i,mem_univ i,rfl⟩))
      have H' : 3*h < (A i ∩ S).card := by exact_mod_cast H
      exact hFd.trans_lt H'
    apply RichLinePolynomial.restriction_zero_of_many (x i) (v i) F R hr
    intro t ht
    have H : f t ∈ B := mem_preimage.mp ht
    obtain ⟨a,ha,he⟩ := mem_image.mp H
    have he' : points a = (fun j => x i j+v i j*t) := by
      rw [he]
      ext j
      simp [f,mul_comm]
    rw [← he']
    exact hFT (points a) (mem_image.mpr ⟨a,(mem_inter.mp ha).2,rfl⟩)
  obtain ⟨G,hG,hGs,hGd,hGz⟩ := squarefree_reduction F hF x v hzero
  exact ⟨G,hG,hGs,hGd.trans hFd,hGz⟩

end
end SharpLogRamsey.SamplePolynomial

end

namespace SharpLogRamsey.RichAffineLines
open Finset MvPolynomial AffineIncidence
open scoped BigOperators Classical
variable {K ι : Type*} [Field K] [Infinite K] [IsAlgClosed K] [Fintype ι]
noncomputable section

theorem card_mul_le {q : ℕ} [CharP K q] (h2 : (2:K) ≠ 0)
    (S : Finset (Fin 3 → K)) (hS : S.Nonempty)
    (x v : ι → Fin 3 → K) (hv : ∀ i, v i ≠ 0)
    (hd : Function.Injective (fun i => carrier (x i) (v i)))
    (M Kp h C : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hM : ∀ i, M ≤ (onLine x v S i).card)
    (hcap : ∀ L : MvPolynomial (Fin 3) K, L.totalDegree = 1 →
      (S.filter (fun y => eval y L = 0)).card ≤ Kp)
    (hprob : (Fintype.card ι:ℝ)*Real.exp (-p*M/12) < 1/2)
    (hsize : 2*p*S.card < ((h+1)^3:ℕ)) (hdeg : (3*h:ℕ) ≤ p*M/2)
    (hchar : 3*h < q) (hMD : 18*h < M) (hKM : 8*Kp ≤ M^2)
    (hD : h^2*M ≤ C*S.card) :
    Fintype.card ι*M ≤ (6+72*C)*S.card := by
  classical
  let : Nonempty S := hS.to_subtype
  let A : ι → Finset S := fun i => univ.filter (fun y => y.val ∈ carrier (x i) (v i))
  have hAc (i : ι) : (A i).card = (onLine x v S i).card := by
    apply card_bij (fun y _ => y.val)
    · intro y hy
      exact mem_filter.mpr ⟨y.property,(mem_filter.mp hy).2⟩
    · intro a ha b hb H
      exact Subtype.ext H
    · intro y hy
      exact ⟨⟨y,(mem_filter.mp hy).1⟩,mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hy).2⟩,rfl⟩
  obtain ⟨F,hF,hFs,hFd,hFz⟩ := SamplePolynomial.exists_polynomial
    (fun y : S => y.val) Subtype.val_injective x v hv A
    (fun i y hy => (mem_filter.mp hy).2) p M hp hp1
    (fun i => by rw [Nat.cast_le]; rw [hAc i]; exact hM i) hprob h
    (by simpa only [Fintype.card_coe] using hsize) hdeg
  have H := SurfaceRichLines.card_le F hF (hFd.trans_lt hchar) hFs h2
    x v hv hd hFz S M Kp hM (fun L _ H => hcap L H) (by omega) hKM
  have HM : 0 < M := by omega
  have HM' : 0 < M-3*F.totalDegree := by omega
  have HD' : M ≤ 2*(M-3*F.totalDegree) := by omega
  have H1 : (2*S.card/M)*M ≤ 2*S.card := Nat.div_mul_le_self _ _
  have H2 : (2*S.card/(M-3*F.totalDegree))*M ≤ 4*S.card := by
    calc
      _ ≤ (2*S.card/(M-3*F.totalDegree))*(2*(M-3*F.totalDegree)) := Nat.mul_le_mul_left _ HD'
      _ = 2*((2*S.card/(M-3*F.totalDegree))*(M-3*F.totalDegree)) := by ring
      _ ≤ 2*(2*S.card) := Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _)
      _ = _ := by ring
  have H3 : 8*F.totalDegree^2*M ≤ 72*C*S.card := by
    calc
      _ ≤ 8*(3*h)^2*M := Nat.mul_le_mul_right M (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hFd _))
      _ = 72*(h^2*M) := by ring
      _ ≤ 72*(C*S.card) := Nat.mul_le_mul_left _ hD
      _ = _ := by ring
  have HX := Nat.mul_le_mul_right M H
  nlinarith

end
end SharpLogRamsey.RichAffineLines
end

section

namespace SharpLogRamsey.ProjectiveBaseChange
open scoped BigOperators
open Finset Classical
noncomputable section
variable {K E : Type*} [Field K] [Field E] [Algebra K E] {n : ℕ}

end
end SharpLogRamsey.ProjectiveBaseChange
end
end

end OAI
