import Mathlib

namespace OAI

/-!
# Exterior monomials, color counts and finite stable-graph bounds

The color-incidence set indexes slots in triples of colors. Its lexicographic
enumeration defines the color word and is used to count occurrences and
word-preserving permutations. The exterior-algebra constructions prove
nonvanishing of a factorial-scaled monomial, not a detector evaluation.

The strata class `Y`, its realizations, Pixton relation span, detector pairing
and geometric vanishing are not defined here. These combinatorial results
therefore do not assert the geometric main theorem or cohomological corollary.
-/

noncomputable section

open scoped BigOperators

namespace PixtonChow

/-! ## The numerical parameters of the proposed example -/

def genus : ℕ := 10 ^ 60

/-- Computed by the falling-factorial formula to avoid expanding Pascal's
recursion at `10^60`; `entryCount_eq_choose` proves the specified value. -/
def entryCount : ℕ := genus.descFactorial 3 / 6

theorem entryCount_eq_choose : entryCount = genus.choose 3 := by
  rw [entryCount, Nat.choose_eq_descFactorial_div_factorial]
  rfl

def markingCount : ℕ := 3 * entryCount

/-- The elementary numerical bounds needed for the parameters. -/
theorem parameter_bounds (g d : ℕ) (hg : 2 ≤ g) :
    2 < 2 * g + 3 * d ∧ 2 * d < 3 * g - 3 + 3 * d := by
  omega

/-- Stability of the specific pair in the source, in the form `2g + n > 2`. -/
theorem parameters_stable : 2 < 2 * genus + markingCount :=
  (parameter_bounds genus entryCount (by norm_num [genus])).1

/-- The proposed codimension is below the moduli dimension. This says
nothing about the existence or the degree of a strata-algebra element. -/
theorem proposed_codimension_lt_dimension :
    2 * entryCount < 3 * genus - 3 + markingCount :=
  (parameter_bounds genus entryCount (by norm_num [genus])).2

/-! ## Triples, incidences, and the color-word stabilizer -/

/-- A set of three distinct colors; sorting it gives its unique increasing triple. -/
abbrev Triple (g : ℕ) := Set.powersetCard (Fin g) 3

/-- Slots indexed by a triple together with one of its colors. -/
abbrev ColorSlot (g : ℕ) := (s : Triple g) × {c : Fin g // c ∈ s.val}

/-- The color of a slot. -/
def incidenceColor {g : ℕ} (p : ColorSlot g) : Fin g := p.2.val

theorem triple_card (g : ℕ) : Fintype.card (Triple g) = g.choose 3 := by
  rw [← Nat.card_eq_fintype_card, Set.powersetCard.card]
  simp

/-- Each block contains exactly three slots. -/
theorem block_card {g : ℕ} (s : Triple g) :
    Fintype.card {c : Fin g // c ∈ s.val} = 3 := by
  simpa only [Fintype.card_coe] using Set.powersetCard.card_eq s

theorem colorSlot_card (g : ℕ) : Fintype.card (ColorSlot g) = 3 * g.choose 3 := by
  rw [Fintype.card_sigma]
  simp_rw [block_card]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, triple_card, mul_comm]

/-- Erasing the choice of a distinguished color in a fiber of `incidenceColor`
leaves precisely a triple containing that color. -/
def colorFiberEquiv {g : ℕ} (c : Fin g) :
    {p : ColorSlot g // incidenceColor p = c} ≃ {s : Triple g // c ∈ s.val} where
  toFun p := ⟨p.val.1, by
    have h : incidenceColor p.val ∈ p.val.1.val := p.val.2.prop
    simpa only [p.prop] using h⟩
  invFun s := ⟨⟨s.val, ⟨c, s.prop⟩⟩, rfl⟩
  left_inv p := by
    rcases p with ⟨⟨s, ⟨d, hd⟩⟩, he⟩
    change d = c at he
    subst d
    rfl
  right_inv _ := rfl

/-- Repackaging as the finite set of three-element supersets of `{c}`. -/
def containingTripleEquiv {g : ℕ} (c : Fin g) :
    {s : Triple g // c ∈ s.val} ≃
      {s // s ∈ ((Finset.univ : Finset (Fin g)).powersetCard 3).filter
        ({c} ⊆ ·)} where
  toFun s := ⟨s.val.val, by simp [s.prop]⟩
  invFun s := ⟨⟨s.val, by simpa using (Finset.mem_filter.mp s.prop).1⟩,
    by simpa using (Finset.mem_filter.mp s.prop).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Every color belongs to `choose (g-1) 2` of the triples. -/
theorem containingTriple_card {g : ℕ} (c : Fin g) :
    Fintype.card {s : Triple g // c ∈ s.val} = (g - 1).choose 2 := by
  rw [Fintype.card_congr (containingTripleEquiv c), Fintype.card_coe]
  simpa using Finset.card_filter_powersetCard_subset
    ({c} : Finset (Fin g)) Finset.univ 3 (Finset.subset_univ _) (by simp)

theorem colorFiber_card {g : ℕ} (c : Fin g) :
    Fintype.card {p : ColorSlot g // incidenceColor p = c} = (g - 1).choose 2 := by
  rw [Fintype.card_congr (colorFiberEquiv c), containingTriple_card]

/-- A permutation of slots preserving their colors. -/
abbrev ColorStabilizer (g : ℕ) :=
  {p : Equiv.Perm (ColorSlot g) // incidenceColor ∘ p = incidenceColor}

/-- The factorial multiplicity appearing in `eq:detector-candidate-value`.
This counts permutations only: no equality involving the detector is asserted. -/
theorem colorStabilizer_card (g : ℕ) :
    Fintype.card (ColorStabilizer g) = ((g - 1).choose 2).factorial ^ g := by
  classical
  rw [DomMulAct.stabilizer_card]
  simp [colorFiber_card]

/-- Counts are unchanged by any enumeration of the slots, including the
lexicographic enumeration used in Definition `def:candidate`. -/
theorem reindexed_stabilizer_card (g : ℕ) {A : Type*} [Fintype A] [DecidableEq A]
    (e : A ≃ ColorSlot g) :
    Fintype.card {p : Equiv.Perm A // (incidenceColor ∘ e) ∘ p = incidenceColor ∘ e} =
      ((g - 1).choose 2).factorial ^ g := by
  classical
  rw [DomMulAct.stabilizer_card]
  have h (c : Fin g) : Fintype.card {a : A // incidenceColor (e a) = c} =
      (g - 1).choose 2 := by
    calc
      _ = Fintype.card {p : ColorSlot g // incidenceColor p = c} :=
        Fintype.card_congr (e.subtypeEquivOfSubtype)
      _ = _ := colorFiber_card c
  simp only [Function.comp_apply, h, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-! ## The lexicographic color word itself -/

/-- Lexicographic order on the sorted lists representing the triples. -/
@[instance_reducible] def tripleLexOrder (g : ℕ) : LinearOrder (Triple g) :=
  LinearOrder.lift' (fun s : Triple g => s.val.sort (· ≤ ·)) (by
    intro s t h
    apply Subtype.ext
    simpa only [Finset.sort_toFinset] using congrArg List.toFinset h)

section OrderedTriples

local instance (g : ℕ) : LinearOrder (Triple g) := tripleLexOrder g

/-- Increasing enumeration of all three-color blocks in lexicographic order. -/
def tripleEnumeration (g : ℕ) : Fin (g.choose 3) ≃ Triple g :=
  (Fintype.orderIsoFinOfCardEq (Triple g) (triple_card g)).toEquiv

/-- Each block is enumerated in increasing color order. -/
def blockSlotEquiv (g : ℕ) : Fin (g.choose 3) × Fin 3 ≃ ColorSlot g :=
  (Equiv.sigmaEquivProd (Fin (g.choose 3)) (Fin 3)).symm |>.trans
    ((Equiv.sigmaCongrRight fun j =>
      ((tripleEnumeration g j).val.orderIsoOfFin
        (Set.powersetCard.card_eq _)).toEquiv) |>.trans
      (Equiv.sigmaCongrLeft (β := fun s : Triple g => {c : Fin g // c ∈ s.val})
        (tripleEnumeration g)))

/-- The first three positions are the first lexicographic block, etc. -/
def orderedSlotEquiv (g : ℕ) : Fin (3 * g.choose 3) ≃ ColorSlot g :=
  ((Fin.castOrderIso (Nat.mul_comm 3 (g.choose 3))).toEquiv.trans
    finProdFinEquiv.symm).trans (blockSlotEquiv g)

/-- The concatenation of the increasing triples, with colors numbered `0,...,g-1`
instead of `1,...,g`. -/
def colorWord (g : ℕ) : Fin (3 * g.choose 3) → Fin g :=
  incidenceColor ∘ orderedSlotEquiv g

theorem colorWord_fiber_card {g : ℕ} (c : Fin g) :
    Fintype.card {j : Fin (3 * g.choose 3) // colorWord g j = c} =
      (g - 1).choose 2 := by
  calc
    _ = Fintype.card {p : ColorSlot g // incidenceColor p = c} :=
      Fintype.card_congr (orderedSlotEquiv g).subtypeEquivOfSubtype
    _ = _ := colorFiber_card c

theorem colorWord_stabilizer_card (g : ℕ) :
    Fintype.card {p : Equiv.Perm (Fin (3 * g.choose 3)) //
      colorWord g ∘ p = colorWord g} = ((g - 1).choose 2).factorial ^ g :=
  reindexed_stabilizer_card g (orderedSlotEquiv g)

end OrderedTriples

/-! ## The nonzero exterior monomial (without a detector evaluation) -/

/-- The exterior algebra on a freely specified set of generators. -/
abbrev ExteriorCoefficients (I : Type*) := ExteriorAlgebra ℚ (I →₀ ℚ)

/-- The generator indexed by `i`. -/
def theta {I : Type*} (i : I) : ExteriorCoefficients I :=
  ExteriorAlgebra.ι ℚ (Finsupp.single i 1)

/-- The product of all generators, in the given increasing order. -/
def topExteriorProduct (I : Type*) [Fintype I] [LinearOrder I] :
    ExteriorCoefficients I :=
  ExteriorAlgebra.ιMulti_family ℚ (Fintype.card I)
    (Finsupp.basisSingleOne : Module.Basis I ℚ (I →₀ ℚ))
    ⟨Finset.univ, by simp⟩

theorem topExteriorProduct_eq_ordered_product (I : Type*) [Fintype I] [LinearOrder I] :
    topExteriorProduct I =
      (List.ofFn (fun k : Fin (Fintype.card I) =>
        theta ((Finset.univ : Finset I).orderEmbOfFin Finset.card_univ k))).prod := by
  rfl

/-- Identifying the ordered monomial with an actual exterior-algebra basis
vector, not positing its nonvanishing. -/
theorem topExteriorProduct_eq_basis (I : Type*) [Fintype I] [LinearOrder I] :
    topExteriorProduct I =
      (Finsupp.basisSingleOne : Module.Basis I ℚ (I →₀ ℚ)).ExteriorAlgebra Finset.univ := by
  symm
  exact ExteriorAlgebra.basis_apply_ofCard _ Finset.card_univ

theorem topExteriorProduct_ne_zero (I : Type*) [Fintype I] [LinearOrder I] :
    topExteriorProduct I ≠ 0 := by
  rw [topExteriorProduct_eq_basis]
  exact Module.Basis.ne_zero _ _

/-- The proposed detector's final scalar-multiple monomial is nonzero over `ℚ`.
The crucial claim that it equals a pairing with `t_n(Y)` is not formalized. -/
theorem factorial_multiple_topExteriorProduct_ne_zero (g : ℕ) (I : Type*)
    [Fintype I] [LinearOrder I] :
    (((((g - 1).choose 2).factorial : ℕ) : ℚ) ^ g) • topExteriorProduct I ≠ 0 := by
  apply smul_ne_zero
  · exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  · exact topExteriorProduct_ne_zero I

/-- The monomial `Θ` indexed by all triples in lexicographic order,
in the exterior algebra from Section 3. -/
def candidateTheta (g : ℕ) : ExteriorCoefficients (Triple g) :=
  letI := tripleLexOrder g
  topExteriorProduct (Triple g)

theorem candidateTheta_ne_zero (g : ℕ) : candidateTheta g ≠ 0 := by
  let _ := tripleLexOrder g
  exact topExteriorProduct_ne_zero (Triple g)

/-- The unsigned right side of `eq:detector-candidate-value` is nonzero.
No equality with a value of the candidate class is claimed here. -/
theorem candidateTheta_multiple_ne_zero (g : ℕ) :
    (((((g - 1).choose 2).factorial : ℕ) : ℚ) ^ g) • candidateTheta g ≠ 0 := by
  let _ := tripleLexOrder g
  exact factorial_multiple_topExteriorProduct_ne_zero g (Triple g)

/-! ## Stable-graph incidence bounds

These are graph presentations, before passing to graph isomorphism classes.
Loops and multiple edges are allowed. The two flags of each edge are
explicitly distinguished. No strata-algebra operations are defined here.
-/

/-- The two flags at each edge, together with the labeled legs. -/
abbrev GraphFlag (E : Type*) (n : ℕ) := (E × Fin 2) ⊕ Fin n

/-- Undirected adjacency in a graph presentation. -/
def EdgeAdjacent {V E : Type*} {n : ℕ} (atVertex : GraphFlag E n → V)
    (u v : V) : Prop :=
  ∃ e : E, (atVertex (.inl (e, 0)) = u ∧ atVertex (.inl (e, 1)) = v) ∨
    (atVertex (.inl (e, 0)) = v ∧ atVertex (.inl (e, 1)) = u)

/-- A finite connected stable graph of type `(g,n)`, given by vertices, edges,
flag incidences, and nonnegative vertex genera. The integer genus equation
avoids truncated subtraction in `|E| - |V| + 1`. -/
structure StableGraph (g n : ℕ) (V E : Type*) [Fintype V] [Fintype E]
    [DecidableEq V] where
  atVertex : GraphFlag E n → V
  vertexGenus : V → ℕ
  connected : ∃ root : V, ∀ v : V, Relation.ReflTransGen (EdgeAdjacent atVertex) root v
  genus_eq : (∑ v, (vertexGenus v : ℤ)) + Fintype.card E - Fintype.card V + 1 = g
  stable : ∀ v : V, 0 < 2 * (vertexGenus v : ℤ) - 2 +
    Fintype.card {f : GraphFlag E n // atVertex f = v}

namespace StableGraph

variable {g n : ℕ} {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

/-- Number of flags, including legs, incident to a vertex. -/
def valence (Γ : StableGraph g n V E) (v : V) : ℕ :=
  Fintype.card {f : GraphFlag E n // Γ.atVertex f = v}

theorem sum_valence (Γ : StableGraph g n V E) :
    ∑ v, Γ.valence v = 2 * Fintype.card E + n := by
  unfold valence
  rw [← Fintype.card_sigma, Fintype.card_congr (Equiv.sigmaFiberEquiv Γ.atVertex)]
  simp only [GraphFlag, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, mul_comm]

/-- Summing the stability weights cancels the individual vertex genera. -/
theorem sum_stability (Γ : StableGraph g n V E) :
    ∑ v, (2 * (Γ.vertexGenus v : ℤ) - 2 + Γ.valence v) = 2 * g - 2 + n := by
  have hv : ∑ v, (Γ.valence v : ℤ) = 2 * Fintype.card E + n := by
    exact_mod_cast Γ.sum_valence
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hv]
  linarith [Γ.genus_eq]

/-- The usual bound on the number of vertices, including marked graphs. -/
theorem vertex_bound (Γ : StableGraph g n V E) :
    (Fintype.card V : ℤ) ≤ 2 * g - 2 + n := by
  calc
    _ = ∑ _v : V, (1 : ℤ) := by simp
    _ ≤ ∑ v, (2 * (Γ.vertexGenus v : ℤ) - 2 + Γ.valence v) := by
      apply Finset.sum_le_sum
      intro v _
      have h := Γ.stable v
      change 0 < 2 * (Γ.vertexGenus v : ℤ) - 2 + Γ.valence v at h
      omega
    _ = _ := Γ.sum_stability

theorem edge_bound (Γ : StableGraph g n V E) :
    (Fintype.card E : ℤ) ≤ 3 * g - 3 + n := by
  have hnonneg : 0 ≤ ∑ v, (Γ.vertexGenus v : ℤ) :=
    Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  linarith [Γ.genus_eq, Γ.vertex_bound]

/-- `R_Γ` from `lem:elementary-entry-tests`. -/
def noiseCount (_Γ : StableGraph g n V E) : ℕ :=
  2 * Fintype.card V + 2 * Fintype.card E

/-- The unmarked global noise bound `eq:global-noise-bound`. -/
theorem noiseCount_bound (Γ : StableGraph g 0 V E) :
    (Γ.noiseCount : ℤ) ≤ 10 * g := by
  simp only [noiseCount, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  have hv := Γ.vertex_bound
  have he := Γ.edge_bound
  simp only [Nat.cast_zero, add_zero] at hv he
  linarith

/-- For any distinguished vertex, the first small-deficit bound. It does not
require that this vertex have maximum genus. -/
theorem other_vertices_bound (Γ : StableGraph g 0 V E) (v : V) :
    (Fintype.card V : ℤ) - 1 ≤ 2 * ((g : ℤ) - Γ.vertexGenus v) := by
  let w : V → ℤ := fun u => 2 * (Γ.vertexGenus u : ℤ) - 2 + Γ.valence u
  have hsum : ∑ u, w u = 2 * g - 2 := by simpa [w] using Γ.sum_stability
  have hsplit : (∑ u ∈ Finset.univ.erase v, w u) + w v = ∑ u, w u :=
    Finset.sum_erase_add _ _ (Finset.mem_univ v)
  have hcard : ((Finset.univ.erase v).card : ℤ) + 1 = Fintype.card V := by
    exact_mod_cast Finset.card_erase_add_one (Finset.mem_univ v)
  have hle : ((Finset.univ.erase v).card : ℤ) ≤ ∑ u ∈ Finset.univ.erase v, w u := by
    calc
      _ = ∑ _u ∈ Finset.univ.erase v, (1 : ℤ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun u _ => by
        have h := Γ.stable u
        change 0 < w u at h
        omega)
  have hval : (0 : ℤ) ≤ Γ.valence v := Nat.cast_nonneg _
  dsimp [w] at hsplit
  linarith

/-- The edge part of `eq:small-graph-size`. -/
theorem small_deficit_edge_bound (Γ : StableGraph g 0 V E) (v : V) :
    (Fintype.card E : ℤ) ≤ 3 * ((g : ℤ) - Γ.vertexGenus v) := by
  have hgen : (Γ.vertexGenus v : ℤ) ≤ ∑ u, (Γ.vertexGenus u : ℤ) :=
    Finset.single_le_sum (fun u _ => Nat.cast_nonneg _) (Finset.mem_univ v)
  linarith [Γ.genus_eq, Γ.other_vertices_bound v]

/-- The noise budget when the genus deficit at a distinguished vertex is small. -/
theorem small_deficit_noise_bound (Γ : StableGraph g 0 V E) (v : V) :
    (Γ.noiseCount : ℤ) ≤ 10 * ((g : ℤ) - Γ.vertexGenus v) + 2 := by
  simp only [noiseCount, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  linarith [Γ.other_vertices_bound v, Γ.small_deficit_edge_bound v]

end StableGraph

/-! ## Explicit color-budget inequalities

These are only arithmetic checks. They do not assert that any Chow-theoretic
support-advancement operation exists.
-/

namespace ColorBudget

def K : ℕ := 10 ^ 5

def blockSize : ℕ := 2000 * 10 ^ 40

def blockCount : ℕ := 4 * K + 20

/-- `C_K`, computed without recursion in the upper argument of `choose`. -/
def C : ℕ := (2 * K).descFactorial 3 / 6

/-- `D_0`, computed by the same falling-factorial formula. -/
def D₀ : ℕ := blockSize.descFactorial 3 / 6

theorem C_eq_choose : C = (2 * K).choose 3 := by
  rw [C, Nat.choose_eq_descFactorial_div_factorial]
  rfl

theorem D₀_eq_choose : D₀ = blockSize.choose 3 := by
  rw [D₀, Nat.choose_eq_descFactorial_div_factorial]
  rfl

/-- `10^40` is the integer value required for `g^(2/3)` at this genus. -/
theorem block_scale : (10 ^ 40 : ℕ) ^ 3 = genus ^ 2 := by
  norm_num [genus]

/-- Fewer than one tenth of the colors are needed for the reserved blocks. -/
theorem reservation_bound : 10 * (blockCount * blockSize) < genus := by
  norm_num [blockCount, blockSize, K, genus]

/-- The remaining number of colors is strictly greater than `0.9 g`. -/
theorem remaining_bound : 9 * genus < 10 * (genus - blockCount * blockSize) := by
  have h := reservation_bound
  omega

theorem C_bound : C < 1334000000000000 := by
  norm_num [C, K, Nat.descFactorial]

theorem block_entry_bound : 10 ^ 9 * genus ^ 2 < D₀ := by
  norm_num [D₀, blockSize, genus, Nat.descFactorial]

theorem ordinary_small_cost : max (10 * K + 3) (C + 1) = C + 1 := by
  norm_num [C, K, Nat.descFactorial]

/-- The two numerical inequalities in `eq:small-loss`, with the second one
multiplied by `100` to stay in natural numbers. -/
theorem small_loss_bounds :
    3 * genus * (C + 1) + genus * (10 * K + 2) + 2 * K * C < 10 ^ 17 * genus ∧
      100 * (10 ^ 17 * genus) < D₀ := by
  norm_num [C, K, genus, D₀, blockSize, Nat.descFactorial]

/-- Bounds on the number of reserved blocks; no existence of an advancement is
assumed or derived from these numerical comparisons. -/
theorem expensive_count_bounds :
    4 * (genus - K - 2) > 3 * genus - 3 ∧ 3 * K + 5 < blockCount := by
  norm_num [genus, K, blockCount]

theorem ordinary_cost_bounds : C + 1 < 11 * genus ∧ 10 * genus + 1 < 11 * genus := by
  norm_num [C, K, genus, Nat.descFactorial]

end ColorBudget

end PixtonChow

end

end OAI
