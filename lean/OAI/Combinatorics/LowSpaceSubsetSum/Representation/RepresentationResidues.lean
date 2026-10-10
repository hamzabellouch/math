import OAI.Combinatorics.LowSpaceSubsetSum.Counting.SurvivalLayout
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationFamilies
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.ResidueFilters
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.NestedPrimes

namespace OAI

/-!
# Adaptive residue hits for the surviving representatives

The top residue is exposed first. A fixed deterministic representative on
that hit determines both child shifts, after which the two independent
child residues are exposed. Collision bounds use the shared nested-prime
seed; independence of the three moduli is unnecessary.
-/

namespace LowSpaceSubsetSum

open scoped BigOperators

theorem normalizedResidue_cast {p : ℕ} (hp : 0 < p) (x : ℤ) :
    ((normalizedResidue hp x).val : ℤ) = x % (p : ℤ) := by
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hp.ne'))

theorem normalizedResidue_eq_normalizedResidue_iff {p : ℕ} (hp : 0 < p) (x y : ℤ) :
    normalizedResidue hp x = normalizedResidue hp y ↔ x % (p : ℤ) = y % (p : ℤ) := by
  rw [normalizedResidue_eq_iff, normalizedResidue_cast]

theorem normalizedResidue_eq_modEq {p : ℕ} (hp : 0 < p) (x : ℤ) (r : Fin p)
    (h : normalizedResidue hp x = r) : x ≡ (r.val : ℤ) [ZMOD (p : ℤ)] := by
  rw [← h]
  change x % (p : ℤ) = ((normalizedResidue hp x).val : ℤ) % (p : ℤ)
  rw [normalizedResidue_cast, Int.emod_emod]

noncomputable def residueTranslation {p : ℕ} (hp : 0 < p) (c : ℤ) : Fin p ≃ Fin p := by
  let f : Fin p → Fin p := fun r => normalizedResidue hp ((r.val : ℤ) + c)
  have hinj : Function.Injective f := by
    intro r s h
    have hm : (r.val : ℤ) + c ≡ (s.val : ℤ) + c [ZMOD (p : ℤ)] :=
      (normalizedResidue_eq_normalizedResidue_iff hp _ _).mp h
    have hcancel := hm.add_right_cancel' c
    change (r.val : ℤ) % (p : ℤ) = (s.val : ℤ) % (p : ℤ) at hcancel
    rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast r.isLt),
      Int.emod_eq_of_lt (by positivity) (by exact_mod_cast s.isLt)] at hcancel
    exact Fin.ext (by exact_mod_cast hcancel)
  exact Equiv.ofBijective f ⟨hinj, Finite.surjective_of_injective hinj⟩

theorem residueTranslation_apply {p : ℕ} (hp : 0 < p) (c x : ℤ) :
    residueTranslation hp c (normalizedResidue hp x) = normalizedResidue hp (x + c) := by
  change normalizedResidue hp (((normalizedResidue hp x).val : ℤ) + c) = _
  rw [normalizedResidue_cast, normalizedResidue_eq_normalizedResidue_iff]
  simp [Int.add_emod]

theorem normalizedResidue_image_card {p : ℕ} (hp : 0 < p) (X : Finset ℤ) :
    (X.image (normalizedResidue hp)).card = (X.image (fun x => x % (p : ℤ))).card := by
  have heq : X.image (fun x => x % (p : ℤ)) =
      (X.image (normalizedResidue hp)).image (fun r : Fin p => (r.val : ℤ)) := by
    rw [Finset.image_image]
    congr 1
    funext x
    exact (normalizedResidue_cast hp x).symm
  rw [heq]
  symm
  apply Finset.card_image_of_injective
  intro r s h
  change (r.val : ℤ) = (s.val : ℤ) at h
  exact Fin.ext (by exact_mod_cast h)

def shiftedResidueHit {p : ℕ} (hp : 0 < p) (X : Finset ℤ) (c : ℤ) (r : Fin p) : Prop :=
  ∃ x ∈ X, normalizedResidue hp (x + c) = r

theorem shiftedResidueHit_probability {p : ℕ} (hp : 0 < p) (X : Finset ℤ) (c : ℤ) :
    finiteUniformProbability (shiftedResidueHit hp X c) =
      ((X.image (fun x => x % (p : ℤ))).card : ℝ) / p := by
  classical
  have hevent : shiftedResidueHit hp X c =
      (fun r => r ∈ X.image (fun x => normalizedResidue hp (x + c))) := by
    funext r
    exact propext (by simp only [shiftedResidueHit, Finset.mem_image])
  rw [hevent, finiteUniformProbability_eq_cardRatio]
  simp only [Fintype.card_coe, Fintype.card_fin]
  congr 1
  have heq : X.image (fun x => normalizedResidue hp (x + c)) =
      (X.image (normalizedResidue hp)).image (residueTranslation hp c) := by
    rw [Finset.image_image]
    congr 1
    funext x
    exact (residueTranslation_apply hp c x).symm
  rw [heq, Finset.card_image_of_injective _ (residueTranslation hp c).injective,
    normalizedResidue_image_card]

theorem finiteUniformProbability_product_and {Ω Ψ : Type*} [Fintype Ω] [Fintype Ψ]
    (P : Ω → Prop) (Q : Ψ → Prop) :
    finiteUniformProbability (fun z : Ω × Ψ => P z.1 ∧ Q z.2) =
      finiteUniformProbability P * finiteUniformProbability Q := by
  classical
  let e : {z : Ω × Ψ // P z.1 ∧ Q z.2} ≃ {x : Ω // P x} × {y : Ψ // Q y} :=
    { toFun := fun z => (⟨z.val.1, z.property.1⟩, ⟨z.val.2, z.property.2⟩)
      invFun := fun z => ⟨(z.1.val, z.2.val), z.1.property, z.2.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  simp only [finiteUniformProbability, ← Nat.card_eq_fintype_card]
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_prod]
  push_cast
  rw [div_mul_div_comm]

theorem finiteUniformProbability_prod_average_left {Ω Ψ : Type*} [Fintype Ω] [Fintype Ψ]
    (P : Ω → Ψ → Prop) :
    finiteUniformProbability (fun z : Ω × Ψ => P z.1 z.2) =
      (∑ x, finiteUniformProbability (P x)) / Fintype.card Ω := by
  have he := finiteUniformProbability_equiv (Equiv.prodComm Ψ Ω)
    (fun z : Ω × Ψ => P z.1 z.2)
  exact he.symm.trans (finiteUniformProbability_prod_average (fun y x => P x y))

/-- A preceding hit may determine the later event, with a uniform lower
bound for every successful preceding outcome. -/
theorem finiteUniformProbability_adaptive_lower {Ω Ψ : Type*}
    [Fintype Ω] [Nonempty Ω] [Fintype Ψ]
    (P : Ω → Prop) (Q : Ω → Ψ → Prop) {p q : ℝ}
    (hq : 0 ≤ q) (hP : p ≤ finiteUniformProbability P)
    (hQ : ∀ x, P x → q ≤ finiteUniformProbability (Q x)) :
    p * q ≤ finiteUniformProbability (fun z : Ω × Ψ => P z.1 ∧ Q z.1 z.2) := by
  classical
  have hrow (x : Ω) : q * (if P x then (1 : ℝ) else 0) ≤
      finiteUniformProbability (fun y => P x ∧ Q x y) := by
    by_cases hx : P x
    · simpa only [hx, ↓reduceIte, true_and, mul_one] using hQ x hx
    · simp [hx, finiteUniformProbability]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun x _ => hrow x)
  have hcard : (0 : ℝ) ≤ Fintype.card Ω := Nat.cast_nonneg _
  have havg := div_le_div_of_nonneg_right hsum hcard
  rw [← finiteUniformProbability_prod_average_left] at havg
  rw [← Finset.mul_sum, mul_div_assoc, ← finiteUniformProbability_eq_indicator_mean] at havg
  exact (mul_le_mul_of_nonneg_right hP hq).trans (by simpa only [mul_comm] using havg)

/-- The top witness is fixed before either child residue is inspected. -/
noncomputable def chosenTopRepresentative {p : ℕ} (hp : 0 < p)
    (X : Finset ℤ) (c : ℤ) (r : Fin p) : ℤ := by
  classical
  exact if h : shiftedResidueHit hp X c r then Classical.choose h else 0

theorem chosenTopRepresentative_spec {p : ℕ} (hp : 0 < p)
    (X : Finset ℤ) (c : ℤ) (r : Fin p) (h : shiftedResidueHit hp X c r) :
    chosenTopRepresentative hp X c r ∈ X ∧
      normalizedResidue hp (chosenTopRepresentative hp X c r + c) = r := by
  classical
  simp only [chosenTopRepresentative, h, ↓reduceDIte]
  exact Classical.choose_spec h

def adaptiveResidueHits {p0 pL pR : ℕ} (h0 : 0 < p0) (hL : 0 < pL) (hR : 0 < pR)
    (X0 XL XR : Finset ℤ) (c0 : ℤ) (cL cR : ℤ → ℤ)
    (r : Fin p0 × (Fin pL × Fin pR)) : Prop :=
  shiftedResidueHit h0 X0 c0 r.1 ∧
    shiftedResidueHit hL XL (cL (chosenTopRepresentative h0 X0 c0 r.1)) r.2.1 ∧
    shiftedResidueHit hR XR (cR (chosenTopRepresentative h0 X0 c0 r.1)) r.2.2

theorem shiftedResidueHit_lower {p : ℕ} (hp : 0 < p) (X : Finset ℤ) (c : ℤ) (u : ℝ)
    (hX : (p : ℝ) / u ^ 16 ≤ (X.image (fun x => x % (p : ℤ))).card) :
    1 / u ^ 16 ≤ finiteUniformProbability (shiftedResidueHit hp X c) := by
  rw [shiftedResidueHit_probability]
  apply (le_div_iff₀ (by exact_mod_cast hp : (0 : ℝ) < p)).mpr
  simpa only [div_mul_eq_mul_div, one_mul] using hX

theorem independent_child_hits_probability {pL pR : ℕ}
    (hL : 0 < pL) (hR : 0 < pR) (XL XR : Finset ℤ) (cL cR : ℤ)
    (u : ℝ) (hu : 0 < u)
    (hXL : (pL : ℝ) / u ^ 16 ≤ (XL.image (fun x => x % (pL : ℤ))).card)
    (hXR : (pR : ℝ) / u ^ 16 ≤ (XR.image (fun x => x % (pR : ℤ))).card) :
    1 / u ^ 32 ≤ finiteUniformProbability
      (fun z : Fin pL × Fin pR => shiftedResidueHit hL XL cL z.1 ∧
        shiftedResidueHit hR XR cR z.2) := by
  rw [finiteUniformProbability_product_and]
  have hleft := shiftedResidueHit_lower hL XL cL u hXL
  have hright := shiftedResidueHit_lower hR XR cR u hXR
  have h := mul_le_mul hleft hright (by positivity)
    (finiteUniformProbability_nonneg (shiftedResidueHit hL XL cL))
  calc
    _ = (1 / u ^ 16) * (1 / u ^ 16) := by rw [one_div_mul_one_div, ← pow_add]
    _ ≤ _ := h

theorem adaptiveResidueHits_probability {p0 pL pR : ℕ}
    (h0 : 0 < p0) (hL : 0 < pL) (hR : 0 < pR)
    (X0 XL XR : Finset ℤ) (c0 : ℤ) (cL cR : ℤ → ℤ)
    (u : ℝ) (hu : 0 < u)
    (hX0 : (p0 : ℝ) / u ^ 16 ≤ (X0.image (fun x => x % (p0 : ℤ))).card)
    (hXL : (pL : ℝ) / u ^ 16 ≤ (XL.image (fun x => x % (pL : ℤ))).card)
    (hXR : (pR : ℝ) / u ^ 16 ≤ (XR.image (fun x => x % (pR : ℤ))).card) :
    1 / u ^ 48 ≤ finiteUniformProbability
      (adaptiveResidueHits h0 hL hR X0 XL XR c0 cL cR) := by
  let : Nonempty (Fin p0) := ⟨⟨0, h0⟩⟩
  have htop : 1 / u ^ 16 ≤ finiteUniformProbability (shiftedResidueHit h0 X0 c0) := by
    rw [shiftedResidueHit_probability]
    apply (le_div_iff₀ (by exact_mod_cast h0 : (0 : ℝ) < p0)).mpr
    simpa only [div_mul_eq_mul_div, one_mul] using hX0
  have h := finiteUniformProbability_adaptive_lower
    (Ω := Fin p0) (Ψ := Fin pL × Fin pR)
    (shiftedResidueHit h0 X0 c0)
    (fun r z => shiftedResidueHit hL XL (cL (chosenTopRepresentative h0 X0 c0 r)) z.1 ∧
      shiftedResidueHit hR XR (cR (chosenTopRepresentative h0 X0 c0 r)) z.2)
    (by positivity : 0 ≤ 1 / u ^ 32) htop
    (fun r _ => independent_child_hits_probability hL hR XL XR
      (cL (chosenTopRepresentative h0 X0 c0 r)) (cR (chosenTopRepresentative h0 X0 c0 r))
      u hu hXL hXR)
  have hnum : 1 / u ^ 48 = (1 / u ^ 16) * (1 / u ^ 32) := by
    rw [one_div_mul_one_div, ← pow_add]
  rw [hnum]
  exact h

def compatibleRepresentativeResidues {p0 pL pR : ℕ}
    (X0 XL XR : Finset ℤ) (c0 t : ℤ) (cL cR : ℤ → ℤ)
    (r : Fin p0 × (Fin pL × Fin pR)) : Prop :=
  ∃ x0 ∈ X0, ∃ xL ∈ XL, ∃ xR ∈ XR,
    x0 + c0 ≡ (r.1.val : ℤ) [ZMOD (p0 : ℤ)] ∧
    t - (x0 + c0) ≡ t - (r.1.val : ℤ) [ZMOD (p0 : ℤ)] ∧
    xL + cL x0 ≡ (r.2.1.val : ℤ) [ZMOD (pL : ℤ)] ∧
    (x0 + c0) - (xL + cL x0) ≡ (r.1.val : ℤ) - r.2.1.val [ZMOD (pL : ℤ)] ∧
    xR + cR x0 ≡ (r.2.2.val : ℤ) [ZMOD (pR : ℤ)] ∧
    (t - (x0 + c0)) - (xR + cR x0) ≡
      (t - (r.1.val : ℤ)) - r.2.2.val [ZMOD (pR : ℤ)]

theorem adaptiveResidueHits_compatible {p0 pL pR : ℕ}
    (h0 : 0 < p0) (hL : 0 < pL) (hR : 0 < pR)
    (hdivL : pL ∣ p0) (hdivR : pR ∣ p0)
    (X0 XL XR : Finset ℤ) (c0 t : ℤ) (cL cR : ℤ → ℤ)
    (r : Fin p0 × (Fin pL × Fin pR))
    (hr : adaptiveResidueHits h0 hL hR X0 XL XR c0 cL cR r) :
    compatibleRepresentativeResidues X0 XL XR c0 t cL cR r := by
  let x0 := chosenTopRepresentative h0 X0 c0 r.1
  obtain ⟨hx0, htop⟩ := chosenTopRepresentative_spec h0 X0 c0 r.1 hr.1
  obtain ⟨xL, hxL, hleft⟩ := hr.2.1
  obtain ⟨xR, hxR, hright⟩ := hr.2.2
  have hp0 : x0 + c0 ≡ (r.1.val : ℤ) [ZMOD (p0 : ℤ)] :=
    normalizedResidue_eq_modEq h0 _ _ htop
  have hpR : t - (x0 + c0) ≡ t - (r.1.val : ℤ) [ZMOD (p0 : ℤ)] := by
    simpa only [sub_eq_add_neg] using hp0.neg.add_left t
  have hcL : xL + cL x0 ≡ (r.2.1.val : ℤ) [ZMOD (pL : ℤ)] :=
    normalizedResidue_eq_modEq hL _ _ hleft
  have hcR : xR + cR x0 ≡ (r.2.2.val : ℤ) [ZMOD (pR : ℤ)] :=
    normalizedResidue_eq_modEq hR _ _ hright
  refine ⟨x0, hx0, xL, hxL, xR, hxR, hp0, hpR, hcL, ?_, hcR, ?_⟩
  · exact (hp0.of_dvd (by exact_mod_cast hdivL)).sub hcL
  · exact (hpR.of_dvd (by exact_mod_cast hdivR)).sub hcR

/-- All parent and complementary-child filters hold with the adaptive hit
probability; shared factors require divisibility, not coprimality. -/
theorem compatibleRepresentativeResidues_probability {p0 pL pR : ℕ}
    (h0 : 0 < p0) (hL : 0 < pL) (hR : 0 < pR)
    (hdivL : pL ∣ p0) (hdivR : pR ∣ p0)
    (X0 XL XR : Finset ℤ) (c0 t : ℤ) (cL cR : ℤ → ℤ)
    (u : ℝ) (hu : 0 < u)
    (hX0 : (p0 : ℝ) / u ^ 16 ≤ (X0.image (fun x => x % (p0 : ℤ))).card)
    (hXL : (pL : ℝ) / u ^ 16 ≤ (XL.image (fun x => x % (pL : ℤ))).card)
    (hXR : (pR : ℝ) / u ^ 16 ≤ (XR.image (fun x => x % (pR : ℤ))).card) :
    1 / u ^ 48 ≤ finiteUniformProbability
      (compatibleRepresentativeResidues (p0 := p0) (pL := pL) (pR := pR)
        X0 XL XR c0 t cL cR) :=
  (adaptiveResidueHits_probability h0 hL hR X0 XL XR c0 cL cR u hu hX0 hXL hXR).trans
    (finiteUniformProbability_mono
      (adaptiveResidueHits_compatible h0 hL hR hdivL hdivR X0 XL XR c0 t cL cR))

theorem uniform_probability_filter_sum {Ω : Type*} [Fintype Ω] (P : Ω → Prop) [DecidablePred P] :
    finiteUniformProbability P =
      ∑ _ω ∈ Finset.univ.filter P, (1 : ℝ) / Fintype.card Ω := by
  classical
  rw [finiteUniformProbability_eq_indicator_mean, Finset.sum_div]
  simp only [Finset.sum_filter, ite_div, one_div, zero_div]

/-- The retained-family size pays for the diagonal collisions. -/
theorem retained_family_energy_mean_bound (X : Finset ℤ) (L u : ℝ) (hu : 2 ≤ u)
    (hsize : (2 : ℝ) ^ L / u ^ 14 ≤ X.card) :
    (X.card : ℝ) + (u ^ 10 / (2 : ℝ) ^ L) * (X.card : ℝ) ^ 2 ≤
      u ^ 15 * (X.card : ℝ) ^ 2 / (2 : ℝ) ^ L := by
  have hu0 : 0 < u := by linarith
  have hu1 : 1 ≤ u := by linarith
  have hE : 0 < (2 : ℝ) ^ L := Real.rpow_pos_of_pos (by norm_num) _
  have hs := (div_le_iff₀ (pow_pos hu0 14)).mp hsize
  have hx : (X.card : ℝ) ≤ u ^ 14 * (X.card : ℝ) ^ 2 / (2 : ℝ) ^ L := by
    apply (le_div_iff₀ hE).mpr
    have h := mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg X.card)
    nlinarith
  have h10 : u ^ 10 ≤ u ^ 14 := pow_le_pow_right₀ hu1 (by decide)
  have h15 : 2 * u ^ 14 ≤ u ^ 15 := by
    rw [pow_succ]
    nlinarith [pow_nonneg hu0.le 14]
  have hcoef : u ^ 14 + u ^ 10 ≤ u ^ 15 := by linarith
  have hscaled := mul_le_mul_of_nonneg_right hcoef
    (show 0 ≤ (X.card : ℝ) ^ 2 / (2 : ℝ) ^ L by positivity)
  calc
    _ ≤ u ^ 14 * (X.card : ℝ) ^ 2 / (2 : ℝ) ^ L +
        (u ^ 10 / (2 : ℝ) ^ L) * (X.card : ℝ) ^ 2 := add_le_add hx le_rfl
    _ = (u ^ 14 + u ^ 10) * ((X.card : ℝ) ^ 2 / (2 : ℝ) ^ L) := by ring
    _ ≤ _ := hscaled
    _ = _ := by ring

/-- Uniform-law energy control needs only the pairwise marginal collision
bound, even when this modulus shares factors with other moduli. -/
theorem uniform_energy_good_probability {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (X : Finset ℤ) (hash : Ω → ℤ → ℤ) (L u : ℝ) (hu : 2 ≤ u)
    (hsize : (2 : ℝ) ^ L / u ^ 14 ≤ X.card)
    (hcollision : ∀ x ∈ X, ∀ y ∈ X, x ≠ y →
      finiteUniformProbability (fun ω => hash ω x = hash ω y) ≤ u ^ 10 / (2 : ℝ) ^ L) :
    1 - 1 / u ≤ finiteUniformProbability
      (fun ω => (collisionEnergy X (hash ω) : ℝ) ≤
        u ^ 16 * (X.card : ℝ) ^ 2 / (2 : ℝ) ^ L) := by
  classical
  have hu0 : 0 < u := by linarith
  have hE : 0 < (2 : ℝ) ^ L := Real.rpow_pos_of_pos (by norm_num) _
  have hX : (0 : ℝ) < X.card := (div_pos hE (pow_pos hu0 14)).trans_le hsize
  have hcard : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hprob : (∑ _ω : Ω, (1 : ℝ) / Fintype.card Ω) = 1 := by simp [hcard]
  have hpair : PairwiseCollisionBound Finset.univ (fun _ : Ω => 1 / Fintype.card Ω)
      X hash (u ^ 10 / (2 : ℝ) ^ L) := by
    intro x hx y hy hxy
    have h := hcollision x hx y hy hxy
    rw [uniform_probability_filter_sum] at h
    simpa only [Finset.sum_filter, mul_ite, mul_one, mul_zero] using h
  have hmean := (expected_energy_le Finset.univ (fun _ : Ω => 1 / Fintype.card Ω)
    X hash hprob (by positivity) hpair).trans
      (retained_family_energy_mean_bound X L u hu hsize)
  have hT : 0 < u ^ 16 * (X.card : ℝ) ^ 2 / (2 : ℝ) ^ L := by positivity
  have h := probability_energy_le Finset.univ (fun _ : Ω => 1 / Fintype.card Ω)
    X hash (fun _ _ => by positivity) hprob hT hmean
  rw [← uniform_probability_filter_sum] at h
  have hratio : (u ^ 15 * (X.card : ℝ) ^ 2 / (2 : ℝ) ^ L) /
      (u ^ 16 * (X.card : ℝ) ^ 2 / (2 : ℝ) ^ L) = 1 / u := by
    field_simp
  rwa [hratio] at h

theorem three_moduli_energy_probability {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (X : Fin 3 → Finset ℤ) (hash : Ω → Fin 3 → ℤ → ℤ) (L : Fin 3 → ℝ)
    (u : ℝ) (hu : 2 ≤ u)
    (hsize : ∀ i, (2 : ℝ) ^ L i / u ^ 14 ≤ (X i).card)
    (hcollision : ∀ i x, x ∈ X i → ∀ y, y ∈ X i → x ≠ y →
      finiteUniformProbability (fun ω => hash ω i x = hash ω i y) ≤ u ^ 10 / (2 : ℝ) ^ L i) :
    1 - 3 / u ≤ finiteUniformProbability
      (fun ω => ∀ i, (collisionEnergy (X i) (hash ω i) : ℝ) ≤
        u ^ 16 * ((X i).card : ℝ) ^ 2 / (2 : ℝ) ^ L i) := by
  classical
  let P (i : Fin 3) (ω : Ω) := (collisionEnergy (X i) (hash ω i) : ℝ) ≤
    u ^ 16 * ((X i).card : ℝ) ^ 2 / (2 : ℝ) ^ L i
  have hgood (i : Fin 3) : 1 - 1 / u ≤ finiteUniformProbability (P i) :=
    uniform_energy_good_probability (X i) (fun ω => hash ω i) (L i) u hu (hsize i) (hcollision i)
  have hbad (i : Fin 3) : finiteUniformProbability (fun ω => ¬P i ω) ≤ 1 / u := by
    rw [finiteUniformProbability_compl]
    linarith [hgood i]
  have h := (finiteUniformProbability_exists_le_sum (fun i ω => ¬P i ω)).trans
    (Finset.sum_le_sum (fun i _ => hbad i))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  norm_num only [Nat.cast_ofNat] at h
  have hp : (fun ω => ∀ i, P i ω) = (fun ω => ¬∃ i, ¬P i ω) := by
    funext ω
    exact propext (by simp)
  change 1 - 3 / u ≤ finiteUniformProbability (fun ω => ∀ i, P i ω)
  rw [hp, finiteUniformProbability_compl]
  have heq : (3 : ℝ) / u = 3 * (1 / u) := by ring
  rw [heq]
  linarith

end LowSpaceSubsetSum

end OAI
