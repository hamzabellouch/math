import Mathlib
import OAI.Analysis.SymmetricDomains.PolynomialSignSetProjection2

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.SignElimination
open Set Polynomial
open scoped Classical BigOperators

lemma RationalOn.polynomial_preimage {X Y ι κ : Type*} {c : X → ι → ℝ} {d : Y → κ → ℝ}
    {S : Set X} {g : X → ℝ} (hg : RationalOn c S g) (f : Y → X)
    (q : ι → MvPolynomial κ ℝ)
    (hc : ∀ y i, c (f y) i = MvPolynomial.eval (d y) (q i)) :
    RationalOn d (f ⁻¹' S) (g ∘ f) := by
  obtain ⟨p,r,hr⟩ := hg
  refine ⟨MvPolynomial.eval₂Hom MvPolynomial.C q p,
    MvPolynomial.eval₂Hom MvPolynomial.C q r,fun y hy => ?_⟩
  have hv (p : MvPolynomial ι ℝ) :
      MvPolynomial.eval (d y) (MvPolynomial.eval₂Hom MvPolynomial.C q p) =
        MvPolynomial.eval (c (f y)) p := by
    rw [PolynomialSignSet.eval_substitution]
    exact congrArg (fun v => MvPolynomial.eval v p) (funext (fun i => (hc y i).symm))
  simpa only [hv,Function.comp_apply] using hr (f y) hy

lemma RationalOn.coordinate_preimage {X Y ι κ : Type*} {c : X → ι → ℝ} {d : Y → κ → ℝ}
    {S : Set X} {g : X → ℝ} (hg : RationalOn c S g) (f : Y → X)
    (r : ι → κ) (hc : ∀ y i, c (f y) i = d y (r i)) :
    RationalOn d (f ⁻¹' S) (g ∘ f) :=
  hg.polynomial_preimage f (fun i => MvPolynomial.X (r i)) (by simpa using hc)

lemma eval_eq_sum_range_of_natDegree_le (P : ℝ[X]) (N : ℕ) (hN : P.natDegree ≤ N) (y : ℝ) :
    P.eval y = ∑ k ∈ Finset.range (N+1), P.coeff k * y^k := by
  rw [eval_eq_sum_range]
  apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hN 1))
  intro k hk hkn
  simp only [Finset.mem_range,not_lt] at hkn
  rw [coeff_eq_zero_of_natDegree_lt (by omega),zero_mul]

lemma polynomialSignSet_root_relation {X ι : Type*} {c : X → ι → ℝ}
    {S : Set X} (hS : PolynomialSignSet c S) (P : X → ℝ[X]) (N : ℕ)
    (hP : RationalPolynomialOn c S P) (hd : ∀ x ∈ S, (P x).natDegree ≤ N) :
    PolynomialSignSet (fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1))
      {z | z.1 ∈ S ∧ (P z.1).eval z.2 = 0} := by
  let d := fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1)
  have hT : PolynomialSignSet d (Prod.fst ⁻¹' S) :=
    hS.coordinate_preimage Prod.fst some (by intros; rfl)
  have hy : RationalOn d (Prod.fst ⁻¹' S) (fun z => z.2) := by
    simpa only [MvPolynomial.eval_X, d, Option.elim_none] using
      (RationalOn.polynomial (c := d) (S := Prod.fst ⁻¹' S) (MvPolynomial.X none))
  have hr (k : ℕ) : RationalOn d (Prod.fst ⁻¹' S) (fun z : X × ℝ => (P z.1).coeff k) :=
    (hP k).coordinate_preimage Prod.fst some (by intros; rfl)
  have he : RationalOn d (Prod.fst ⁻¹' S) (fun z : X × ℝ => (P z.1).eval z.2) := by
    apply (RationalOn.sum (Finset.range (N+1)) _ (fun k _ => (hr k).mul (hy.pow k))).congr
    intro z hz
    exact (eval_eq_sum_range_of_natDegree_le (P z.1) N (hd z.1 hz) z.2).symm
  convert he.sign_set hT 0 using 1
  ext z
  simp only [mem_ofPred_eq,mem_inter_iff,mem_preimage,sign_eq_zero_iff]

theorem polynomialSignSet_finite_subrelation {X ι : Type*} {c : X → ι → ℝ}
    {A : Set (X × ℝ)}
    (hA : PolynomialSignSet (fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1)) A) :
    ∃ B : Set (X × ℝ),
      PolynomialSignSet (fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1)) B ∧
      B ⊆ A ∧ (∀ x, {y : ℝ | (x,y) ∈ B}.Finite) ∧
      ∀ x, (∃ y : ℝ, (x,y) ∈ B) ↔ ∃ y : ℝ, (x,y) ∈ A := by
  classical
  obtain ⟨s,W,hW⟩ := hA.finite_sign_description
  let Q : s → X → ℝ[X] := fun p x =>
    ((MvPolynomial.optionEquivLeft ℝ ι) p.val).map (MvPolynomial.eval (c x))
  let d : s → ℕ := fun p => ((MvPolynomial.optionEquivLeft ℝ ι) p.val).natDegree
  have hQ (p : s) : RationalPolynomialOn c univ (Q p) := by
    intro k
    simpa only [Q,coeff_map] using RationalOn.polynomial
      (((MvPolynomial.optionEquivLeft ℝ ι) p.val).coeff k)
  have hd (p : s) (x : X) (_hx : x ∈ (univ : Set X)) : (Q p x).natDegree ≤ d p := natDegree_map_le
  let T := fun J : Finset s => (univ : Set X) ∩ {x | ∀ a, Q a x ≠ 0 ↔ a ∈ J}
  have hT (J : Finset s) : PolynomialSignSet c (T J) :=
    polynomialSignSet_nonzero_mask PolynomialSignSet.univ d Q hQ hd J
  let P := fun (J : Finset s) x => ∏ a : J, Q a.val x
  let N := fun J : Finset s => ∑ a : J, d a.val
  have hp (J : Finset s) : RationalPolynomialOn c (T J) (P J) :=
    RationalPolynomialOn.prod Finset.univ _ (fun a _ => (hQ a.val).mono inter_subset_left)
  have hpn (J : Finset s) (x : X) (hx : x ∈ T J) : P J x ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun a _ => (hx.2 a.val).mpr a.property)
  have hpd (J : Finset s) (x : X) (hx : x ∈ T J) : (P J x).natDegree ≤ N J :=
    (natDegree_prod_le _ _).trans (Finset.sum_le_sum (fun a _ => hd a.val x hx.1))
  let U := fun (J : Finset s) (n : Fin (N J+1)) => T J ∩
    {x | P J x ≠ 0 ∧ (P J x).natDegree = n.val}
  have hU (J : Finset s) (n : Fin (N J+1)) : PolynomialSignSet c (U J n) :=
    degree_stratum_signSet (hT J) (P J) (N J) n (hp J) (hpd J)
  let R := fun (J : Finset s) x => P J x * criticalSampler (P J x)
  have hrs (J : Finset s) (x : X) (hx : x ∈ T J) : R J x ≠ 0 ∧
      ∀ y : ℝ, ∃ z : ℝ, (R J x).eval z = 0 ∧
        ∀ a, SignType.sign ((Q a x).eval z) = SignType.sign ((Q a x).eval y) := by
    have hs := sample_all_chambers (fun a : J => Q a.val x)
      (fun a => (hx.2 a.val).mpr a.property)
    refine ⟨hs.1,fun y => ?_⟩
    obtain ⟨z,hz,hsg⟩ := hs.2 y
    refine ⟨z,hz,fun a => ?_⟩
    by_cases ha : a ∈ J
    · exact hsg ⟨a,ha⟩
    · have ha0 : Q a x = 0 := by simpa only [not_ne_iff] using mt (hx.2 a).mp ha
      simp only [ha0,eval_zero]
  let B := fun (J : Finset s) (n : Fin (N J+1)) =>
    {z : X × ℝ | z.1 ∈ U J n ∧ (R J z.1).eval z.2 = 0} ∩ A
  have hB (J : Finset s) (n : Fin (N J+1)) :
      PolynomialSignSet (fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1)) (B J n) := by
    apply PolynomialSignSet.inter _ hA
    apply polynomialSignSet_root_relation (hU J n) (R J) (2*n.val+2)
    · have hrp := (hp J).mono (show U J n ⊆ T J from inter_subset_left)
      exact hrp.mul (hrp.criticalSampler n (fun x hx => hx.2.2))
    · intro x hx
      have hb := natDegree_mul_le (p := P J x) (q := criticalSampler (P J x))
      have hc := criticalSampler_natDegree_le (P J x)
      rw [hx.2.2] at hb hc
      change (P J x * criticalSampler (P J x)).natDegree ≤ _
      omega
  refine ⟨{z | ∃ J, ∃ n, z ∈ B J n},?_,?_,?_,?_⟩
  · exact PolynomialSignSet.exists_finite _ (fun J =>
      PolynomialSignSet.exists_finite _ (hB J))
  · rintro z ⟨J,n,hz⟩
    exact hz.2
  · intro x
    have hf (J : Finset s) (n : Fin (N J+1)) : {y : ℝ | (x,y) ∈ B J n}.Finite := by
      by_cases hx : x ∈ U J n
      · apply (Polynomial.finite_setOfPred_isRoot (hrs J x hx.1).1).subset
        intro y hy
        exact hy.1.2
      · have he : {y : ℝ | (x,y) ∈ B J n} = ∅ := by
          ext y
          simp only [B,mem_inter_iff,mem_ofPred_eq,mem_empty_iff_false,iff_false,not_and]
          exact fun h _ => hx h.1
        rw [he]
        exact finite_empty
    convert Set.finite_iUnion (fun J => Set.finite_iUnion (hf J)) using 1
    ext y
    simp only [mem_iUnion,mem_ofPred_eq]
  · intro x
    constructor
    · rintro ⟨y,J,n,hy⟩
      exact ⟨y,hy.2⟩
    · rintro ⟨y,hy⟩
      let J := Finset.univ.filter (fun a : s => Q a x ≠ 0)
      have hx : x ∈ T J := ⟨mem_univ _,fun a => by simp [J]⟩
      let n : Fin (N J+1) := ⟨(P J x).natDegree,Nat.lt_succ_of_le (hpd J x hx)⟩
      obtain ⟨z,hz,hsg⟩ := (hrs J x hx).2 y
      refine ⟨z,J,n,⟨⟨⟨hx,hpn J x hx,rfl⟩,hz⟩,?_⟩⟩
      apply (hW (x,z)).mpr
      have hsg' : (fun p : s => SignType.sign (MvPolynomial.eval
          (fun o => Option.elim o z (c x)) p.val)) =
          fun p : s => SignType.sign (MvPolynomial.eval (fun o => Option.elim o y (c x)) p.val) := by
        funext p
        simpa only [Q,eval_optionEquivLeft] using hsg p
      rw [hsg']
      exact (hW (x,y)).mp hy

end Release061.SignElimination

end

end OAI
