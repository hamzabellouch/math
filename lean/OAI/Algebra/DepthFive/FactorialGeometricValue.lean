import OAI.Algebra.DepthFive.LocalFactorialExpansion

namespace OAI

/-! Finite geometric-moment evaluation of nonnegative factorial expansions. -/
namespace Problem335

open scoped BigOperators

variable {σ : Type*} [Fintype σ]

/-- Independent geometric factorial moments, with a possibly different mean per coordinate. -/
def geometricFactorialMonomial (d : σ → ℕ) (G : σ → ℝ) : ℝ :=
  ∏ i, ((d i).factorial : ℝ) * G i ^ d i

namespace FactorialExpansion

/-- The finite value to which occupation comparison bounds an expansion. -/
def geometricValue {f : (σ → ℕ) → ℕ} {S : Finset σ} {D : ℕ}
    (F : FactorialExpansion f S D) (G : σ → ℝ) : ℝ :=
  ∑ j, (F.coeff j : ℝ) * geometricFactorialMonomial (F.degree j) G

@[simp] theorem geometricValue_weaken {f : (σ → ℕ) → ℕ} {S T : Finset σ} {D E : ℕ}
    (F : FactorialExpansion f S D) (hS : S ⊆ T) (hD : D ≤ E) (G : σ → ℝ) :
    (F.weaken hS hD).geometricValue G = F.geometricValue G := rfl

@[simp] theorem geometricValue_reframe [DecidableEq σ]
    {f g : (σ → ℕ) → ℕ} {S T : Finset σ} {D E : ℕ}
    (F : FactorialExpansion f S D) (hfg : ∀ M, f M = g M)
    (hST : S ⊆ T) (hDE : D ≤ E) (G : σ → ℝ) :
    (F.reframe hfg hST hDE).geometricValue G = F.geometricValue G := rfl

variable [DecidableEq σ]

@[simp] theorem geometricFactorialMonomial_single (i : σ) (d : ℕ) (G : σ → ℝ) :
    geometricFactorialMonomial (fun j => if j = i then d else 0) G =
      (d.factorial : ℝ) * G i ^ d := by
  unfold geometricFactorialMonomial
  calc
    _ = ∏ j, if j = i then (d.factorial : ℝ) * G j ^ d else 1 := by
      apply Finset.prod_congr rfl
      intro j hj
      by_cases h : j = i <;> simp [h]
    _ = _ := by simp

omit [DecidableEq σ] in
@[simp] theorem geometricValue_add {f g : (σ → ℕ) → ℕ} {S : Finset σ} {D : ℕ}
    (F : FactorialExpansion f S D) (E : FactorialExpansion g S D) (G : σ → ℝ) :
    (F.add E).geometricValue G = F.geometricValue G + E.geometricValue G := by
  change (∑ j : F.Index ⊕ E.Index, ((Sum.elim F.coeff E.coeff j : ℕ) : ℝ) *
    geometricFactorialMonomial (Sum.elim F.degree E.degree j) G) = _
  rw [Fintype.sum_sum_type]
  rfl

/-- Independence at disjoint coordinates is an exact algebraic identity of the
finite factorial-moment values; no probability-space construction is needed. -/
@[simp] theorem geometricValue_mul {f g : (σ → ℕ) → ℕ} {S T : Finset σ} {D E : ℕ}
    (F : FactorialExpansion f S D) (H : FactorialExpansion g T E)
    (hST : Disjoint S T) (G : σ → ℝ) :
    (F.mul H hST).geometricValue G = F.geometricValue G * H.geometricValue G := by
  have hterm (a : F.Index) (b : H.Index) :
      geometricFactorialMonomial (fun i => F.degree a i + H.degree b i) G =
        geometricFactorialMonomial (F.degree a) G * geometricFactorialMonomial (H.degree b) G := by
    unfold geometricFactorialMonomial
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    by_cases hS : i ∈ S
    · have hT : i ∉ T := fun ht => (Finset.disjoint_left.mp hST) hS ht
      simp [H.supported b i hT]
    · simp [F.supported a i hS]
  change (∑ j : F.Index × H.Index, ((F.coeff j.1 * H.coeff j.2 : ℕ) : ℝ) *
      geometricFactorialMonomial (fun i => F.degree j.1 i + H.degree j.2 i) G) = _
  simp only [Fintype.sum_prod_type, Nat.cast_mul, hterm, geometricValue, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

@[simp] theorem geometricValue_coordinate (i : σ) (J : Type) [Fintype J] (c e : J → ℕ)
    {f : ℕ → ℕ} {D : ℕ} (he : ∀ j, e j ≤ D)
    (hf : ∀ z, f z = ∑ j, c j * z.descFactorial (e j)) (G : σ → ℝ) :
    (coordinate i J c e he hf).geometricValue G =
      ∑ j, (c j : ℝ) * ((e j).factorial : ℝ) * G i ^ e j := by
  change (∑ j : J, (c j : ℝ) *
    geometricFactorialMonomial (fun k => if k = i then e j else 0) G) = _
  simp only [geometricFactorialMonomial_single, mul_assoc]

@[simp] theorem geometricValue_occupation (i : σ) (G : σ → ℝ) :
    (occupation i).geometricValue G = G i := by simp [occupation]

@[simp] theorem geometricValue_successor (i : σ) (G : σ → ℝ) :
    (successor i).geometricValue G = G i + 1 := by
  simp [successor, Fin.sum_univ_two]

@[simp] theorem geometricValue_square (i : σ) (G : σ → ℝ) :
    (square i).geometricValue G = 2 * G i ^ 2 + G i := by
  simp [square, Fin.sum_univ_two]

@[simp] theorem geometricValue_successorSquare (i : σ) (G : σ → ℝ) :
    (successorSquare i).geometricValue G = 2 * G i ^ 2 + 3 * G i + 1 := by
  simp [successorSquare, Fin.sum_univ_three]

@[simp] theorem geometricValue_normalDerivative (i j : σ) (G : σ → ℝ) :
    (normalDerivative i j).geometricValue G =
      if i = j then 2 * G i ^ 2 + G i else G i * G j := by
  by_cases h : i = j
  · subst j
    simp [normalDerivative]
  · simp only [normalDerivative, dite_eq_right h, ite_eq_right h]
    change ((occupation i).mul (occupation j) (by simpa using h)).geometricValue G = _
    rw [geometricValue_mul]
    simp

@[simp] theorem geometricValue_normalMultiplication (i j : σ) (G : σ → ℝ) :
    (normalMultiplication i j).geometricValue G =
      if i = j then 2 * G i ^ 2 + 3 * G i + 1 else (G i + 1) * (G j + 1) := by
  by_cases h : i = j
  · subst j
    simp [normalMultiplication]
  · simp only [normalMultiplication, dite_eq_right h, ite_eq_right h]
    change ((successor i).mul (successor j) (by simpa using h)).geometricValue G = _
    rw [geometricValue_mul]
    simp

@[simp] theorem geometricValue_distinctDerivative (i j : σ) (h : i ≠ j) (G : σ → ℝ) :
    (distinctDerivative i j h).geometricValue G = G i * (G j + 1) := by
  change ((occupation i).mul (successor j) (by simpa using h)).geometricValue G = _
  rw [geometricValue_mul]
  simp

@[simp] theorem geometricValue_distinctMultiplication (i j : σ) (h : i ≠ j) (G : σ → ℝ) :
    (distinctMultiplication i j h).geometricValue G = (G i + 1) * G j := by
  change ((successor i).mul (occupation j) (by simpa using h)).geometricValue G = _
  rw [geometricValue_mul]
  simp

omit [DecidableEq σ] in
@[simp] theorem geometricValue_constant (c : ℕ) (G : σ → ℝ) :
    (constant c : FactorialExpansion (fun _ : σ → ℕ => c) ∅ 0).geometricValue G = c := by
  change (∑ _ : Unit, (c : ℝ) * geometricFactorialMonomial (fun _ : σ => 0) G) = _
  simp [geometricFactorialMonomial]

/-- The value depends only on the coordinates allowed by the expansion support. -/
theorem geometricValue_congr_on {f : (σ → ℕ) → ℕ} {S : Finset σ} {D : ℕ}
    (F : FactorialExpansion f S D) (G H : σ → ℝ)
    (heq : ∀ i ∈ S, G i = H i) : F.geometricValue G = F.geometricValue H := by
  unfold geometricValue
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  unfold geometricFactorialMonomial
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hS : i ∈ S
  · rw [heq i hS]
  · simp [F.supported j i hS]

/-- Choose the finite product expansion together with its exact independent
geometric factorial value. -/
theorem exists_prod_geometricValue {ι : Type*} (s : Finset ι)
    (f : ι → (σ → ℕ) → ℕ) (S : ι → Finset σ) (D : ι → ℕ)
    (F : ∀ i, FactorialExpansion (f i) (S i) (D i)) (G : σ → ℝ)
    (hdis : (s : Set ι).Pairwise fun i j => Disjoint (S i) (S j)) :
    ∃ H : FactorialExpansion (fun M => ∏ i ∈ s, f i M)
      (s.biUnion S) (∑ i ∈ s, D i),
      H.geometricValue G = ∏ i ∈ s, (F i).geometricValue G := by
  classical
  revert hdis
  induction s using Finset.induction_on with
  | empty =>
    intro hdis
    exact ⟨constant 1, by simp⟩
  | @insert a s ha ih =>
    intro hdis
    have hs : (s : Set ι).Pairwise fun i j => Disjoint (S i) (S j) := by
      intro i hi j hj hij
      exact hdis (Finset.mem_insert_of_mem hi) (Finset.mem_insert_of_mem hj) hij
    obtain ⟨H, hH⟩ := ih hs
    have hd : Disjoint (S a) (s.biUnion S) := by
      rw [Finset.disjoint_biUnion_right]
      intro j hj
      exact hdis (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hj)
        (by intro h; subst j; exact ha hj)
    let E := ((F a).mul H hd).reframe
      (g := fun M => ∏ i ∈ insert a s, f i M)
      (T := (insert a s).biUnion S) (E := ∑ i ∈ insert a s, D i)
      (by intro M; simp [ha]) (by simp) (by simp [ha])
    refine ⟨E, ?_⟩
    change (((F a).mul H hd).reframe _ _ _).geometricValue G = _
    rw [geometricValue_reframe, geometricValue_mul, hH, Finset.prod_insert ha]

end FactorialExpansion

namespace LocalMoments

variable [DecidableEq σ]

/-- Exact independent geometric expectation of the local table at a common mean. -/
def localGeometricMass (derivative : Bool) (G : ℝ) (p q r : σ) : ℝ :=
  if p = q then normalGeometricMass derivative G (decide (p = r))
  else diagonalGeometricMass G

@[simp] theorem geometricValue_localPolynomialExpansion (derivative : Bool)
    (p q r : σ) (G : ℝ) :
    (localPolynomialExpansion derivative p q r).geometricValue (fun _ => G) =
      localGeometricMass derivative G p q r := by
  by_cases hpq : p = q
  · subst q
    by_cases hpr : p = r
    · subst r
      cases derivative <;> simp [localPolynomialExpansion, localGeometricMass,
        normalGeometricMass, pow_two]
    · cases derivative <;> simp [localPolynomialExpansion, hpr, localGeometricMass,
        normalGeometricMass, pow_two]
  · cases derivative <;> simp [localPolynomialExpansion, hpq, localGeometricMass,
      diagonalGeometricMass, mul_comm]

/-- Local evaluation when only the three relevant coordinate means agree. -/
theorem geometricValue_localPolynomialExpansion_of_eq (derivative : Bool)
    (p q r : σ) (G : σ → ℝ) (g : ℝ)
    (hp : G p = g) (hq : G q = g) (hr : G r = g) :
    (localPolynomialExpansion derivative p q r).geometricValue G =
      localGeometricMass derivative g p q r := by
  rw [FactorialExpansion.geometricValue_congr_on
    (localPolynomialExpansion derivative p q r) G (fun _ => g)]
  · exact geometricValue_localPolynomialExpansion derivative p q r g
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with h | h | h
    · simpa [h] using hp
    · simpa [h] using hq
    · simpa [h] using hr

/-- The actual local-table product has an expansion whose geometric value is
exactly the product of its local expected masses. This is the finite algebraic
bridge from occupation comparison to the normalized pairing weights. -/
theorem exists_localProduct_geometricValue {ι : Type*} (layers : Finset ι)
    (derivative : ι → Bool) (p q r : ι → σ) (G : ℝ)
    (hdis : (layers : Set ι).Pairwise fun i j =>
      Disjoint ({p i, q i, r i} : Finset σ) {p j, q j, r j}) :
    ∃ F : FactorialExpansion (localProductNat layers derivative p q r)
      (layers.biUnion fun i => {p i, q i, r i}) (2 * layers.card),
      F.geometricValue (fun _ => G) =
        ∏ t ∈ layers, localGeometricMass (derivative t) G (p t) (q t) (r t) := by
  obtain ⟨F, hF⟩ := FactorialExpansion.exists_prod_geometricValue layers
    (fun i M => localPolynomialNat (derivative i) M (p i) (q i) (r i))
    (fun i => {p i, q i, r i}) (fun _ => 2)
    (fun i => localPolynomialExpansion (derivative i) (p i) (q i) (r i))
    (fun _ => G) hdis
  let H := F.reframe (g := localProductNat layers derivative p q r)
    (T := layers.biUnion fun i => {p i, q i, r i}) (E := 2 * layers.card)
    (by intro M; rfl) (by rfl) (by simp [Nat.mul_comm])
  refine ⟨H, ?_⟩
  change F.geometricValue (fun _ => G) = _
  rw [hF]
  simp

/-- Different layers may have different geometric means. In particular this
handles mean `A` on derivative layers and mean `B` on multiplication layers. -/
theorem exists_localProduct_geometricValue_of_eq {ι : Type*} (layers : Finset ι)
    (derivative : ι → Bool) (p q r : ι → σ) (G : σ → ℝ) (g : ι → ℝ)
    (hp : ∀ t ∈ layers, G (p t) = g t)
    (hq : ∀ t ∈ layers, G (q t) = g t)
    (hr : ∀ t ∈ layers, G (r t) = g t)
    (hdis : (layers : Set ι).Pairwise fun i j =>
      Disjoint ({p i, q i, r i} : Finset σ) {p j, q j, r j}) :
    ∃ F : FactorialExpansion (localProductNat layers derivative p q r)
      (layers.biUnion fun i => {p i, q i, r i}) (2 * layers.card),
      F.geometricValue G =
        ∏ t ∈ layers, localGeometricMass (derivative t) (g t) (p t) (q t) (r t) := by
  obtain ⟨F, hF⟩ := FactorialExpansion.exists_prod_geometricValue layers
    (fun i M => localPolynomialNat (derivative i) M (p i) (q i) (r i))
    (fun i => {p i, q i, r i}) (fun _ => 2)
    (fun i => localPolynomialExpansion (derivative i) (p i) (q i) (r i)) G hdis
  let H := F.reframe (g := localProductNat layers derivative p q r)
    (T := layers.biUnion fun i => {p i, q i, r i}) (E := 2 * layers.card)
    (by intro M; rfl) (by rfl) (by simp [Nat.mul_comm])
  refine ⟨H, ?_⟩
  change F.geometricValue G = _
  rw [hF]
  apply Finset.prod_congr rfl
  intro t ht
  exact geometricValue_localPolynomialExpansion_of_eq (derivative t)
    (p t) (q t) (r t) G (g t) (hp t ht) (hq t ht) (hr t ht)

/-- Layer-labelled coordinates automatically satisfy the local equal-mean and
disjoint-support requirements. -/
theorem exists_layered_localProduct_geometricValue {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (layers : Finset ι) (derivative : ι → Bool) (p q r : ι → κ) (g : ι → ℝ) :
    ∃ F : FactorialExpansion
      (localProductNat layers derivative (fun i => (i, p i))
        (fun i => (i, q i)) (fun i => (i, r i)))
      (layers.biUnion fun i => {(i, p i), (i, q i), (i, r i)}) (2 * layers.card),
      F.geometricValue (fun x => g x.1) =
        ∏ t ∈ layers, localGeometricMass (derivative t) (g t)
          (t, p t) (t, q t) (t, r t) := by
  apply exists_localProduct_geometricValue_of_eq layers derivative
    (fun i => (i, p i)) (fun i => (i, q i)) (fun i => (i, r i))
    (fun x => g x.1) g
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · exact layered_support_disjoint layers p q r

end LocalMoments
end Problem335

end OAI
