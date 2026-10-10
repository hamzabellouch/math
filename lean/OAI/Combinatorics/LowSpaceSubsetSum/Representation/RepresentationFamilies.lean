import OAI.Combinatorics.LowSpaceSubsetSum.Counting.MixerBalance
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.Representatives
import OAI.Combinatorics.MatchingPSD.TableGeometry

namespace OAI

/-!
# Representative families in actual mixer subblock partitions

The three categories are the chosen representative, its complement in the
selected half, and the outside half. Their canonical disjoint-union counting
model is transported to partitions of the actual mixer indices.
-/

namespace LowSpaceSubsetSum

open scoped BigOperators

universe u v w

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- The implementation assigns the remainder in the fixed block order. -/
def balancedBlockCounts (l k : ℕ) (j : Fin l) : ℕ :=
  k / l + if j.val < k % l then 1 else 0

theorem balancedBlockCounts_sum (l k : ℕ) (hl : 0 < l) :
    ∑ j, balancedBlockCounts l k j = k := by
  classical
  let e : {j : Fin l // j.val < k % l} ≃ Fin (k % l) :=
    { toFun := fun j => ⟨j.val.val, j.property⟩
      invFun := fun j => ⟨⟨j.val, j.isLt.trans (Nat.mod_lt k hl)⟩, j.isLt⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hr : (∑ j : Fin l, if j.val < k % l then (1 : ℕ) else 0) = k % l := by
    calc
      _ = Fintype.card {j : Fin l // j.val < k % l} := by
        simp [Fintype.card_subtype]
      _ = _ := (Fintype.card_congr e).trans (Fintype.card_fin _)
  simp only [balancedBlockCounts, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, hr]
  exact Nat.div_add_mod k l

theorem balancedBlockCounts_balanced (l k : ℕ) : BalancedProfile (balancedBlockCounts l k) := by
  intro i j
  simp only [balancedBlockCounts]
  split_ifs <;> omega

theorem balancedBlockCounts_le (l t k : ℕ) (hl : l = 2 ∨ l = 4)
    (hk : k ≤ l * t) (j : Fin l) : balancedBlockCounts l k j ≤ t := by
  rcases hl with rfl | rfl <;> simp only [balancedBlockCounts] <;> split_ifs <;> omega

/-- Smaller masks, complementary masks, and outside indices fill each block. -/
def representativeBlockProfile (l t k : ℕ) : Fin 3 → Fin l → ℕ :=
  ![balancedBlockCounts l k, (fun j => t - balancedBlockCounts l k j), (fun _ => t)]

theorem representativeBlockProfile_properties (l t k : ℕ) (hl : l = 2 ∨ l = 4)
    (hk : k ≤ l * t) :
    (∀ i, ∑ j, representativeBlockProfile l t k i j = ![k, l * t - k, l * t] i) ∧
    (∀ j, ∑ i, representativeBlockProfile l t k i j = 2 * t) ∧
    (∀ i, BalancedProfile (representativeBlockProfile l t k i)) := by
  have hl0 : 0 < l := by omega
  have hc := balancedBlockCounts_le l t k hl hk
  have hsum := balancedBlockCounts_sum l k hl0
  have hbal := balancedBlockCounts_balanced l k
  refine ⟨?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hsum
    · change ∑ j : Fin l, (t - balancedBlockCounts l k j) = l * t - k
      rw [Finset.sum_tsub_distrib _ (fun j _ => hc j), hsum]
      simp
    · simp [representativeBlockProfile]
  · intro j
    rw [Fin.sum_univ_three]
    change balancedBlockCounts l k j + (t - balancedBlockCounts l k j) + t = 2 * t
    have := hc j
    omega
  · intro i
    fin_cases i
    · exact hbal
    · intro j j'
      have h1 := hc j
      have h2 := hc j'
      have h3 := hbal j' j
      change t - balancedBlockCounts l k j ≤ t - balancedBlockCounts l k j' + 1
      omega
    · intro j j'
      change t ≤ t + 1
      omega

def representativeCategories (D A M : Finset ι) : Fin 3 → Finset ι :=
  ![D, A \ D, M \ A]

omit [Fintype ι] in
theorem representativeCategories_subset {D A M : Finset ι}
    (hDA : D ⊆ A) (hAM : A ⊆ M) (i : Fin 3) :
    representativeCategories D A M i ⊆ M := by
  fin_cases i
  · exact hDA.trans hAM
  · exact Finset.sdiff_subset.trans hAM
  · exact Finset.sdiff_subset

omit [Fintype ι] in
theorem representativeCategories_disjoint {D A M : Finset ι} (hDA : D ⊆ A) :
    ∀ i j, i ≠ j → Disjoint (representativeCategories D A M i)
      (representativeCategories D A M j) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have hdx : x ∈ D → x ∈ A := fun hx => hDA hx
  fin_cases i <;> fin_cases j <;> simp_all [representativeCategories]

omit [Fintype ι] in
theorem representativeCategories_card {D A M : Finset ι}
    (hDA : D ⊆ A) (hAM : A ⊆ M) (i : Fin 3) :
    (representativeCategories D A M i).card =
      ![D.card, A.card - D.card, M.card - A.card] i := by
  fin_cases i <;> simp [representativeCategories, Finset.card_sdiff_of_subset, hDA, hAM]

/-- The canonical three-category domain is exactly the actual mixer. -/
noncomputable def representativeCategoryEquiv {D A M : Finset ι}
    (hDA : D ⊆ A) (hAM : A ⊆ M) :
    CategoryDomain (fun i => ↥(representativeCategories D A M i)) ≃ ↥M := by
  let f : CategoryDomain (fun i => ↥(representativeCategories D A M i)) → ↥M :=
    fun z => ⟨z.2.val, representativeCategories_subset hDA hAM z.1 z.2.property⟩
  apply Equiv.ofBijective f
  constructor
  · rintro ⟨i, x⟩ ⟨j, y⟩ h
    have hxy : x.val = y.val := congrArg Subtype.val h
    have hij : i = j := by
      by_contra hij
      exact (Finset.disjoint_left.mp (representativeCategories_disjoint hDA i j hij))
        x.property (hxy.symm ▸ y.property)
    subst j
    congr 1
    exact Subtype.ext hxy
  · intro x
    by_cases hD : x.val ∈ D
    · exact ⟨⟨0, ⟨x.val, hD⟩⟩, Subtype.ext rfl⟩
    by_cases hA : x.val ∈ A
    · exact ⟨⟨1, ⟨x.val, Finset.mem_sdiff.mpr ⟨hA, hD⟩⟩⟩, Subtype.ext rfl⟩
    · exact ⟨⟨2, ⟨x.val, Finset.mem_sdiff.mpr ⟨x.property, hA⟩⟩⟩, Subtype.ext rfl⟩

def coloringsPrecomposeEquiv {α β K : Type*} [Fintype α] [Fintype β]
    [Fintype K] [DecidableEq K] (e : α ≃ β) (t : K → ℕ) :
    MatchingSmoothing.Colorings β K t ≃ MatchingSmoothing.Colorings α K t where
  toFun f := ⟨f.val ∘ e, (MatchingSmoothing.histogram_comp_equiv f.val e).trans f.property⟩
  invFun f := ⟨f.val ∘ e.symm,
    (MatchingSmoothing.histogram_comp_equiv f.val e.symm).trans f.property⟩
  left_inv f := by apply Subtype.ext; funext x; simp
  right_inv f := by apply Subtype.ext; funext x; simp

omit [Fintype ι] in
/-- The actual labeled mixer partitions have the same category probability
as the canonical multinomial model. -/
theorem actual_representative_partition_probability {D A M : Finset ι}
    (hDA : D ⊆ A) (hAM : A ⊆ M) (l b : ℕ) (hl : l = 2 ∨ l = 4)
    (q : Fin 3 → Fin l → ℕ)
    (hrows : ∀ i, ∑ j, q i j = (representativeCategories D A M i).card)
    (hcols : ∀ j, ∑ i, q i j = b) (hbal : ∀ i, BalancedProfile (q i)) :
    1 / (M.card + 1 : ℝ) ^ (3 * l) ≤
      finiteUniformProbability
        (fun f : MatchingSmoothing.Colorings ↥M (Fin l) (fun _ => b) =>
          ∀ i, MatchingSmoothing.histogram
            (fun x : ↥(representativeCategories D A M i) =>
              f.val ⟨x.val, representativeCategories_subset hDA hAM i x.property⟩) = q i) := by
  let C : Fin 3 → Type u := fun i => ↥(representativeCategories D A M i)
  let e := representativeCategoryEquiv hDA hAM
  have hcount : Fintype.card (CategoryDomain C) = M.card :=
    (Fintype.card_congr e).trans (Fintype.card_coe M)
  have hcanonical := balanced_partition_probability_two_or_four l b hl C q
    (fun i => by simpa only [C, Fintype.card_coe] using hrows i) hcols hbal
  rw [hcount] at hcanonical
  have htransport := finiteUniformProbability_equiv
    (coloringsPrecomposeEquiv e (fun _ : Fin l => b))
    (fun f => ∀ i, MatchingSmoothing.histogram (fun x : C i => f.val ⟨i, x⟩) = q i)
  exact hcanonical.trans_eq htransport.symm

/-- One concrete mask for every distinct integer weight at the selected size. -/
noncomputable def representativeMask (a : ι → ℤ) (A : Finset ι) (k : ℕ)
    (x : ↥(sumsAtSize a A k)) : Finset ι :=
  Classical.choose ((mem_sumsAtSize a A k x.val).mp x.property)

theorem representativeMask_spec (a : ι → ℤ) (A : Finset ι) (k : ℕ)
    (x : ↥(sumsAtSize a A k)) :
    representativeMask a A k x ⊆ A ∧ (representativeMask a A k x).card = k ∧
      weight a (representativeMask a A k x) = x.val :=
  Classical.choose_spec ((mem_sumsAtSize a A k x.val).mp x.property)

theorem representativeMask_weights_injective (a : ι → ℤ) (A : Finset ι) (k : ℕ) :
    Function.Injective (fun x : ↥(sumsAtSize a A k) => weight a (representativeMask a A k x)) := by
  intro x y h
  apply Subtype.ext
  simpa only [(representativeMask_spec a A k x).2.2,
    (representativeMask_spec a A k y).2.2] using h

/-- The image contains distinct weights rather than repeated subset occurrences. -/
noncomputable def survivingWeights {R : Type*} [Fintype R]
    (a : ι → ℤ) (mask : R → Finset ι) (P : R → Prop) : Finset ℤ := by
  classical
  exact (Finset.univ.filter P).image (fun r => weight a (mask r))

theorem survivingWeights_probability {R : Type*} [Fintype R]
    (a : ι → ℤ) (mask : R → Finset ι)
    (hinj : Function.Injective (fun r => weight a (mask r))) (P : R → Prop) :
    finiteUniformProbability P =
      ((survivingWeights a mask P).card : ℝ) / Fintype.card R := by
  classical
  let e : {r : R // P r} ≃ ↥((Finset.univ : Finset R).filter P) :=
    { toFun := fun r => ⟨r.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, r.property⟩⟩
      invFun := fun r => ⟨r.val, (Finset.mem_filter.mp r.property).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hc : Fintype.card {r : R // P r} = (survivingWeights a mask P).card := by
    rw [Fintype.card_congr e, Fintype.card_coe, survivingWeights,
      Finset.card_image_of_injective _ hinj]
  rw [finiteUniformProbability_eq_cardRatio, hc]

theorem retained_family_denominator {u : ℝ} (hu : 2 ≤ u) (s l : ℕ)
    (hs : (s : ℝ) + 1 ≤ u) (hl : l = 2 ∨ l = 4) :
    2 * ((s : ℝ) + 1) * u ^ (3 * l) ≤ u ^ 14 := by
  have hu1 : 1 ≤ u := by linarith
  have he : 3 * l ≤ 12 := by omega
  calc
    _ ≤ u * u * u ^ 12 := by
      apply mul_le_mul
      · exact mul_le_mul hu hs (by positivity) (by linarith)
      · exact pow_le_pow_right₀ hu1 he
      · positivity
      · positivity
    _ = _ := by ring

/-- The paper's exponent fourteen absorbs the size pigeonhole factor and
half of the expected retained fraction, for both arities. -/
theorem retained_family_count {R : Type*} [Fintype R] [Nonempty R]
    (a : ι → ℤ) (mask : R → Finset ι)
    (hinj : Function.Injective (fun r => weight a (mask r)))
    (P : R → Prop) (s l : ℕ) (L u : ℝ) (hu : 2 ≤ u)
    (hs : (s : ℝ) + 1 ≤ u) (hl : l = 2 ∨ l = 4)
    (hsize : (2 : ℝ) ^ L / ((s : ℝ) + 1) ≤ Fintype.card R)
    (hretained : (1 / u ^ (3 * l)) / 2 ≤ finiteUniformProbability P) :
    (2 : ℝ) ^ L / u ^ 14 ≤ (survivingWeights a mask P).card := by
  have hupos : 0 < u := by linarith
  have hR : (0 : ℝ) < Fintype.card R := by exact_mod_cast Fintype.card_pos
  rw [survivingWeights_probability a mask hinj] at hretained
  have hr : 1 / (2 * u ^ (3 * l)) ≤
      ((survivingWeights a mask P).card : ℝ) / Fintype.card R := by
    simpa only [div_div, mul_comm] using hretained
  have hcount : (Fintype.card R : ℝ) ≤
      (survivingWeights a mask P).card * (2 * u ^ (3 * l)) := by
    simpa only [one_mul] using (div_le_div_iff₀ (by positivity) hR).mp hr
  have hsize' : (2 : ℝ) ^ L ≤ (Fintype.card R : ℝ) * ((s : ℝ) + 1) :=
    (div_le_iff₀ (by positivity)).mp hsize
  apply (div_le_iff₀ (pow_pos hupos 14)).mpr
  calc
    _ ≤ (Fintype.card R : ℝ) * ((s : ℝ) + 1) := hsize'
    _ ≤ ((survivingWeights a mask P).card : ℝ) *
        (2 * ((s : ℝ) + 1) * u ^ (3 * l)) := by nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_left (retained_family_denominator hu s l hs hl)
      (Nat.cast_nonneg _)

theorem retained_distinct_weight_probability {Ω R : Type*}
    [Fintype Ω] [Nonempty Ω] [Fintype R] [Nonempty R]
    (a : ι → ℤ) (mask : R → Finset ι)
    (hinj : Function.Injective (fun r => weight a (mask r)))
    (keeps : Ω → R → Prop) (s m l : ℕ) (L u : ℝ)
    (hu : 2 ≤ u) (hs : (s : ℝ) + 1 ≤ u) (hm : (m : ℝ) + 1 ≤ u)
    (hl : l = 2 ∨ l = 4)
    (hsize : (2 : ℝ) ^ L / ((s : ℝ) + 1) ≤ Fintype.card R)
    (hsingle : ∀ r, 1 / ((m : ℝ) + 1) ^ (3 * l) ≤
      finiteUniformProbability (fun ω => keeps ω r)) :
    1 / (2 * u ^ (3 * l)) ≤ finiteUniformProbability
      (fun ω => (2 : ℝ) ^ L / u ^ 14 ≤ (survivingWeights a mask (keeps ω)).card) := by
  have hupos : 0 < u := by linarith
  have hprob (r : R) : 1 / u ^ (3 * l) ≤ finiteUniformProbability (fun ω => keeps ω r) := by
    apply le_trans _ (hsingle r)
    exact one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_left₀ (by positivity) hm _)
  have h := surviving_representative_family keeps hprob
  have hmono := finiteUniformProbability_mono (fun ω hω =>
    retained_family_count a mask hinj (keeps ω) s l L u hu hs hl hsize hω)
  have hresult := h.trans hmono
  simpa only [div_div, mul_comm] using hresult

def representativePrescriptions {D A M : Finset ι}
    (hDA : D ⊆ A) (hAM : A ⊆ M) {l b : ℕ} (q : Fin 3 → Fin l → ℕ)
    (f : MatchingSmoothing.Colorings ↥M (Fin l) (fun _ => b)) : Prop :=
  ∀ i, MatchingSmoothing.histogram
    (fun x : ↥(representativeCategories D A M i) =>
      f.val ⟨x.val, representativeCategories_subset hDA hAM i x.property⟩) = q i

/-- The finite family consists of actual masks inside the selected half,
and the sample space consists of actual equal-size mixer partitions. -/
theorem actual_representative_family_survival {R : Type*} [Fintype R] [Nonempty R]
    (a : ι → ℤ) (A M : Finset ι) (mask : R → Finset ι)
    (hinj : Function.Injective (fun r => weight a (mask r)))
    (hDA : ∀ r, mask r ⊆ A) (hAM : A ⊆ M) (l b : ℕ)
    (hl : l = 2 ∨ l = 4) (hparts : l * b = M.card)
    (q : Fin 3 → Fin l → ℕ)
    (hrows : ∀ r i, ∑ j, q i j = (representativeCategories (mask r) A M i).card)
    (hcols : ∀ j, ∑ i, q i j = b) (hbal : ∀ i, BalancedProfile (q i))
    (s : ℕ) (L u : ℝ) (hu : 2 ≤ u) (hs : (s : ℝ) + 1 ≤ u)
    (hm : (M.card : ℝ) + 1 ≤ u)
    (hsize : (2 : ℝ) ^ L / ((s : ℝ) + 1) ≤ Fintype.card R) :
    1 / (2 * u ^ (3 * l)) ≤ finiteUniformProbability
      (fun f : MatchingSmoothing.Colorings ↥M (Fin l) (fun _ => b) =>
        (2 : ℝ) ^ L / u ^ 14 ≤
          (survivingWeights a mask (fun r => representativePrescriptions (hDA r) hAM q f)).card) := by
  obtain ⟨f, hf⟩ := exists_coloring_of_sum ↥M (fun _ : Fin l => b)
    (by simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, Fintype.card_coe] using hparts)
  let : Nonempty (MatchingSmoothing.Colorings ↥M (Fin l) (fun _ => b)) := ⟨⟨f, hf⟩⟩
  apply retained_distinct_weight_probability a mask hinj _ s M.card l L u hu hs hm hl hsize
  intro r
  exact actual_representative_partition_probability (hDA r) hAM l b hl q
    (hrows r) hcols hbal

/-- The algorithm's fixed-order remainder counts satisfy every category
condition, including the complementary masks and the outside half. -/
theorem fixed_profile_family_survival {R : Type*} [Fintype R] [Nonempty R]
    (a : ι → ℤ) (A M : Finset ι) (mask : R → Finset ι)
    (hinj : Function.Injective (fun r => weight a (mask r)))
    (hDA : ∀ r, mask r ⊆ A) (hAM : A ⊆ M) (l t k : ℕ)
    (hl : l = 2 ∨ l = 4) (hk : k ≤ l * t)
    (hD : ∀ r, (mask r).card = k) (hA : A.card = l * t)
    (hM : M.card = 2 * (l * t)) (L u : ℝ) (hu : 2 ≤ u)
    (hs : ((l * t : ℕ) : ℝ) + 1 ≤ u) (hm : (M.card : ℝ) + 1 ≤ u)
    (hsize : (2 : ℝ) ^ L / ((l * t : ℕ) + 1) ≤ Fintype.card R) :
    1 / (2 * u ^ (3 * l)) ≤ finiteUniformProbability
      (fun f : MatchingSmoothing.Colorings ↥M (Fin l) (fun _ => 2 * t) =>
        (2 : ℝ) ^ L / u ^ 14 ≤ (survivingWeights a mask
          (fun r => representativePrescriptions (hDA r) hAM
            (representativeBlockProfile l t k) f)).card) := by
  have hprofile := representativeBlockProfile_properties l t k hl hk
  apply actual_representative_family_survival a A M mask hinj hDA hAM l (2 * t) hl
    (by rw [hM]; ring) (representativeBlockProfile l t k) ?_
    hprofile.2.1 hprofile.2.2 (l * t) L u hu hs hm hsize
  intro r i
  rw [representativeCategories_card (hDA r) hAM, hD r, hA, hM]
  simpa only [two_mul, Nat.add_sub_cancel_left] using hprofile.1 i

/-- Applying the survival estimate to the concrete representative chosen for
each distinct sum gives the actual retained-weight event. -/
theorem distinct_sum_representatives_survival
    (a : ι → ℤ) (A M : Finset ι) (hAM : A ⊆ M) (l t k : ℕ)
    (hl : l = 2 ∨ l = 4) (hk : k ≤ l * t)
    (hA : A.card = l * t) (hM : M.card = 2 * (l * t))
    (L u : ℝ) (hu : 2 ≤ u) (hs : ((l * t : ℕ) : ℝ) + 1 ≤ u)
    (hm : (M.card : ℝ) + 1 ≤ u)
    (hsize : (2 : ℝ) ^ L / ((l * t : ℕ) + 1) ≤ (sumsAtSize a A k).card) :
    1 / (2 * u ^ (3 * l)) ≤ finiteUniformProbability
      (fun f : MatchingSmoothing.Colorings ↥M (Fin l) (fun _ => 2 * t) =>
        (2 : ℝ) ^ L / u ^ 14 ≤ (survivingWeights a (representativeMask a A k)
          (fun r => representativePrescriptions (representativeMask_spec a A k r).1 hAM
            (representativeBlockProfile l t k) f)).card) := by
  let R := ↥(sumsAtSize a A k)
  have hsizeR : (2 : ℝ) ^ L / ((l * t : ℕ) + 1) ≤ Fintype.card R := by
    simpa only [R, Fintype.card_coe] using hsize
  have hpos : 0 < Fintype.card R := by
    exact_mod_cast (lt_of_lt_of_le (by positivity :
      (0 : ℝ) < (2 : ℝ) ^ L / ((l * t : ℕ) + 1)) hsizeR)
  let : Nonempty R := Fintype.card_pos_iff.mp hpos
  exact fixed_profile_family_survival a A M (representativeMask a A k)
    (representativeMask_weights_injective a A k)
    (fun r => (representativeMask_spec a A k r).1) hAM l t k hl hk
    (fun r => (representativeMask_spec a A k r).2.1) hA hM L u hu hs hm hsizeR

/-- Pigeonhole-selected sizes give concrete, weight-injective representative
families on each actual selected half. -/
theorem exists_large_representative_family (a : ι → ℤ) (A : Finset ι)
    (L : ℝ) (hL : L ≤ (A.card : ℝ) - deficiency a A) :
    ∃ k ≤ A.card / 2,
      (2 : ℝ) ^ L / (A.card + 1) ≤ (sumsAtSize a A k).card ∧
      (∀ x : ↥(sumsAtSize a A k), representativeMask a A k x ⊆ A ∧
        (representativeMask a A k x).card = k ∧
        weight a (representativeMask a A k x) = x.val) ∧
      Function.Injective (fun x : ↥(sumsAtSize a A k) => weight a (representativeMask a A k x)) := by
  obtain ⟨k, hk, hmany⟩ := exists_representative_size a A
  refine ⟨k, hk, ?_, representativeMask_spec a A k, representativeMask_weights_injective a A k⟩
  apply le_trans _ hmany
  exact div_le_div_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) hL) (by positivity)

theorem finiteUniformProbability_pi {J : Type v} [Fintype J] [DecidableEq J]
    (Ω : J → Type w) [∀ i, Fintype (Ω i)] (P : ∀ i, Ω i → Prop) :
    finiteUniformProbability (fun x : ∀ i, Ω i => ∀ i, P i (x i)) =
      ∏ i, finiteUniformProbability (P i) := by
  classical
  simp only [finiteUniformProbability, ← Nat.card_eq_fintype_card]
  rw [Nat.card_congr Equiv.subtypePiEquivPi, Nat.card_pi, Nat.card_pi]
  simp only [Nat.cast_prod, Finset.prod_div_distrib]

/-- One top partition and two local partitions are independent in the
actual product sample space; their inverse-polynomial costs multiply. -/
theorem three_representative_families_probability
    (Ω : Fin 3 → Type v) [∀ i, Fintype (Ω i)] (P : ∀ i, Ω i → Prop)
    (u : ℝ) (hu : 8 ≤ u)
    (h0 : 1 / (2 * u ^ 12) ≤ finiteUniformProbability (P 0))
    (h1 : 1 / (2 * u ^ 6) ≤ finiteUniformProbability (P 1))
    (h2 : 1 / (2 * u ^ 6) ≤ finiteUniformProbability (P 2)) :
    1 / u ^ 25 ≤ finiteUniformProbability (fun x : ∀ i, Ω i => ∀ i, P i (x i)) := by
  have hu0 : 0 < u := by linarith
  rw [finiteUniformProbability_pi]
  simp only [Fin.prod_univ_three]
  have hprod := mul_le_mul (mul_le_mul h0 h1 (by positivity)
    (finiteUniformProbability_nonneg _)) h2 (by positivity)
    (mul_nonneg (finiteUniformProbability_nonneg _) (finiteUniformProbability_nonneg _))
  apply le_trans _ hprod
  have hden : 8 * u ^ 24 ≤ u ^ 25 := by
    calc
      _ ≤ u * u ^ 24 := mul_le_mul_of_nonneg_right hu (by positivity)
      _ = _ := by ring
  calc
    _ ≤ 1 / (8 * u ^ 24) := one_div_le_one_div_of_le (by positivity) hden
    _ = _ := by field_simp; ring

end LowSpaceSubsetSum

end OAI
