import OAI.Algebra.DepthFive.ImmOperatorPaths
import OAI.Algebra.DepthFive.FockPaths
import OAI.Algebra.DepthFive.ImmBidegree
import OAI.Algebra.DepthFive.FiniteOperator

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

/-- The normalized coefficient contributed by one endpoint path of IMM. -/
def immPathAmplitude (n : ℕ) (hn : 0 < n)
    (isV : (Fin n × Fin n × Fin n) → Bool)
    (d : (Fin n × Fin n × Fin n) →₀ ℕ) (p : Fin (immPaths n hn).length) : ℝ :=
  (((immPaths n hn).get p).map (occupationAmplitude isV d)).prod

/-- The final occupation vector of one path operator. -/
def immPathOccupation (n : ℕ) (hn : 0 < n)
    (isV : (Fin n × Fin n × Fin n) → Bool)
    (d : (Fin n × Fin n × Fin n) →₀ ℕ) (p : Fin (immPaths n hn).length) :
    (Fin n × Fin n × Fin n) →₀ ℕ :=
  pathOccupation isV ((immPaths n hn).get p) d

theorem immPathAmplitude_nonneg (n : ℕ) (hn : 0 < n)
    (isV : (Fin n × Fin n × Fin n) → Bool)
    (d : (Fin n × Fin n × Fin n) →₀ ℕ) (p : Fin (immPaths n hn).length) :
    0 ≤ immPathAmplitude n hn isV d p := by
  apply List.prod_nonneg
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  exact occupationAmplitude_nonneg isV d i

/-- The actual IMM operator on a normalized monomial is the sum of its sparse path actions. -/
theorem mixedOperator_imm_complexFockMonomial (n : ℕ) (hn : 0 < n)
    (isV : (Fin n × Fin n × Fin n) → Bool)
    (d : (Fin n × Fin n × Fin n) →₀ ℕ) :
    mixedOperator isV (imm ℂ n) (complexFockMonomial d) =
      ∑ p : Fin (immPaths n hn).length,
        (immPathAmplitude n hn isV d p : ℂ) •
          complexFockMonomial (immPathOccupation n hn isV d p) := by
  rw [mixedOperator_imm_apply_eq_sum_paths n hn isV]
  apply Finset.sum_congr rfl
  intro p hp
  have h := mixedOperator_path_complexFockMonomial isV ((immPaths n hn).get p)
    (immPaths_nodup n hn _ (List.get_mem _ p)) d
  simpa only [map_list_prod, List.map_map, Function.comp_def, mixedOperator_X,
    immPathAmplitude, immPathOccupation] using h

/-- Normalized matrix entries of the actual IMM operator are weighted path-shift counts. -/
theorem complexFockBasis_repr_mixedOperator_imm (n : ℕ) (hn : 0 < n)
    (isV : (Fin n × Fin n × Fin n) → Bool)
    (d e : (Fin n × Fin n × Fin n) →₀ ℕ) :
    complexFockBasis.repr (mixedOperator isV (imm ℂ n) (complexFockMonomial d)) e =
      ∑ p : Fin (immPaths n hn).length,
        if immPathOccupation n hn isV d p = e then (immPathAmplitude n hn isV d p : ℂ)
        else 0 := by
  classical
  rw [mixedOperator_imm_complexFockMonomial n hn isV]
  simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← complexFockBasis_apply, Module.Basis.repr_self]
  simp [Finsupp.single_apply]

/-- A product of variables has the sum of their assigned weighted degrees. -/
theorem variable_list_product_isWeightedHomogeneous {K σ M : Type*}
    [CommSemiring K] [AddCommMonoid M] (w : σ → M) (l : List σ) :
    ((l.map (MvPolynomial.X : σ → MvPolynomial σ K)).prod).IsWeightedHomogeneous
      w (l.map w).sum := by
  induction l with
  | nil => simpa using MvPolynomial.isWeightedHomogeneous_one K w
  | cons x l ih =>
    simpa only [List.map_cons, List.prod_cons, List.sum_cons] using
      (MvPolynomial.isWeightedHomogeneous_X K w x).mul ih

/-- The path monomials all have the same layerwise bidegree as IMM. -/
theorem immPath_product_mem_bidegreeSubmodule (K : Type*) [CommSemiring K]
    (n : ℕ) (hn : 0 < n) (side : Fin n → Bool)
    (p : Fin (immPaths n hn).length) :
    ((((immPaths n hn).get p).map (MvPolynomial.X (R := K))).prod) ∈
      bidegreeSubmodule (fun x => side x.1)
        (Finset.univ.filter (fun t => side t = true)).card
        (Finset.univ.filter (fun t => side t = false)).card := by
  have h := variable_list_product_isWeightedHomogeneous (K := K)
    (fun x : Fin n × Fin n × Fin n => bidegreeWeight side x.1) ((immPaths n hn).get p)
  have hl := immPaths_labels n hn _ (List.get_mem _ p)
  have hs := congrArg (fun l : List (Fin n) => (l.map (bidegreeWeight side)).sum) hl
  simp only [List.map_map, Function.comp_def, ← List.ofFn_eq_map, List.sum_ofFn] at hs
  rw [hs] at h
  have he : (∑ t, bidegreeWeight side t) =
      ((Finset.univ.filter (fun t => side t = true)).card,
       (Finset.univ.filter (fun t => side t = false)).card) := by
    apply Prod.ext
    · simp only [Prod.fst_sum, Finset.card_filter]
      apply Finset.sum_congr rfl
      intro t ht
      cases ht' : side t <;> simp [bidegreeWeight, ht']
    · simp only [Prod.snd_sum, Finset.card_filter]
      apply Finset.sum_congr rfl
      intro t ht
      cases ht' : side t <;> simp [bidegreeWeight, ht']
  rw [he] at h
  exact h

/-- A nonzero scalar multiple of a normalized monomial determines its weighted degree. -/
theorem weight_eq_of_complexFockMonomial_smul_mem {σ M : Type*}
    [Fintype σ] [DecidableEq σ] [AddCommMonoid M]
    (w : σ → M) (d : σ →₀ ℕ) (a : M) (c : ℂ) (hc : c ≠ 0)
    (h : (c • complexFockMonomial d).IsWeightedHomogeneous w a) :
    Finsupp.weight w d = a := by
  apply h (d := d)
  rw [MvPolynomial.coeff_smul, complexFockMonomial_eq, MvPolynomial.coeff_monomial]
  simp only [smul_eq_mul]
  apply mul_ne_zero hc
  exact inv_ne_zero (by exact_mod_cast (sqrt_multiFactorial_pos d).ne')

/-- A nonzero path amplitude guarantees that its occupation lies in the genuine target bidegree. -/
theorem immPathOccupation_bidegree_of_amplitude_ne_zero (n : ℕ) (hn : 0 < n)
    (side : Fin n → Bool) (a b : ℕ)
    (d : (Fin n × Fin n × Fin n) →₀ ℕ)
    (hd : Finsupp.weight (bidegreeWeight (fun x => side x.1)) d = (a, b))
    (p : Fin (immPaths n hn).length)
    (hp : immPathAmplitude n hn (fun x => side x.1) d p ≠ 0) :
    Finsupp.weight (bidegreeWeight (fun x => side x.1))
        (immPathOccupation n hn (fun x => side x.1) d p) =
      (a - (Finset.univ.filter (fun t => side t = true)).card,
       b + (Finset.univ.filter (fun t => side t = false)).card) := by
  have hinput : complexFockMonomial d ∈
      bidegreeSubmodule (fun x => side x.1) a b := by
    rw [complexFockMonomial_eq]
    exact MvPolynomial.isWeightedHomogeneous_monomial _ _ _ hd
  have hpoly := immPath_product_mem_bidegreeSubmodule ℂ n hn side p
  have hout := mixedOperator_mem_bidegreeSubmodule_all (K := ℂ)
    (σ := Fin n × Fin n × Fin n)
    (q := (((immPaths n hn).get p).map (MvPolynomial.X (R := ℂ))).prod)
    (p := complexFockMonomial d)
    (k := (Finset.univ.filter (fun t => side t = true)).card)
    (m := (Finset.univ.filter (fun t => side t = false)).card)
    (a := a) (b := b) (fun x => side x.1) hpoly hinput
  have hact := mixedOperator_path_complexFockMonomial (fun x => side x.1)
    ((immPaths n hn).get p) (immPaths_nodup n hn _ (List.get_mem _ p)) d
  rw [hact] at hout
  exact weight_eq_of_complexFockMonomial_smul_mem _ _ _ _
    (by exact_mod_cast hp) hout

/-- Squared path amplitudes are the occupation monomials occurring in the moment calculation. -/
theorem immPathAmplitude_sq (n : ℕ) (hn : 0 < n)
    (isV : (Fin n × Fin n × Fin n) → Bool)
    (d : (Fin n × Fin n × Fin n) →₀ ℕ) (p : Fin (immPaths n hn).length) :
    (immPathAmplitude n hn isV d p) ^ 2 =
      (((immPaths n hn).get p).map
        (fun i => if isV i then (d i : ℝ) else (d i : ℝ) + 1)).prod :=
  pathAmplitude_sq isV _ d

end Problem335

end

end OAI
