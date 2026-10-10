import OAI.Combinatorics.GraphThreshold.Basic
import OAI.Combinatorics.GraphThreshold.FiniteProbability
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

namespace OAI

/-!
# Distinct subset copies under a finite group action

Copies are distinct orbit elements, not group elements or labeled embeddings.
All counting and probability statements therefore retain the stabilizer
multiplicities correctly, including for the empty subset.
-/

noncomputable section

open scoped BigOperators Pointwise

namespace LeanBlast.SecondKahnKalai

universe u v

variable (G : Type u) [Group G] [Fintype G]
variable {X : Type v} [DecidableEq X] [MulAction G X]

/-- The distinct copies of a finite subset under the given action. -/
def copyOrbit (F : Finset X) : Finset (Finset X) :=
  Finset.univ.image (fun g : G => g • F)

/-- An actual distinct copy, with no labeling multiplicity. -/
abbrev OrbitCopy (F : Finset X) := {J : Finset X // J ∈ copyOrbit G F}

/-- The total number of distinct copies. -/
def orbitCount (F : Finset X) : ℕ := (copyOrbit G F).card

/-- Copies of `F` whose elements all lie in the fixed set `I`. -/
def internalCopyCount (I F : Finset X) : ℕ :=
  ((copyOrbit G F).filter (fun J => J ⊆ I)).card

/-- Copies of `I` containing the fixed observed set `U`. -/
def containingCopyCount (I U : Finset X) : ℕ :=
  ((copyOrbit G I).filter (fun J => U ⊆ J)).card

@[simp] theorem mem_copyOrbit_iff {F J : Finset X} :
    J ∈ copyOrbit G F ↔ ∃ g : G, g • F = J := by
  simp only [copyOrbit, Finset.mem_image, Finset.mem_univ, true_and]

theorem self_mem_copyOrbit (F : Finset X) : F ∈ copyOrbit G F := by
  exact (mem_copyOrbit_iff G).mpr ⟨1, one_smul _ _⟩

theorem copyOrbit_nonempty (F : Finset X) : (copyOrbit G F).Nonempty :=
  ⟨F, self_mem_copyOrbit G F⟩

theorem orbitCount_pos (F : Finset X) : 0 < orbitCount G F :=
  Finset.card_pos.mpr (copyOrbit_nonempty G F)

instance orbitCopy_nonempty (F : Finset X) : Nonempty (OrbitCopy G F) :=
  ⟨⟨F, self_mem_copyOrbit G F⟩⟩

@[simp] theorem card_OrbitCopy (F : Finset X) :
    Fintype.card (OrbitCopy G F) = orbitCount G F := Fintype.card_coe _

theorem smul_mem_copyOrbit (g : G) {F J : Finset X} (hJ : J ∈ copyOrbit G F) :
    g • J ∈ copyOrbit G F := by
  obtain ⟨h, rfl⟩ := (mem_copyOrbit_iff G).mp hJ
  exact (mem_copyOrbit_iff G).mpr ⟨g * h, mul_smul _ _ _⟩

@[simp] theorem smul_mem_copyOrbit_iff (g : G) {F J : Finset X} :
    g • J ∈ copyOrbit G F ↔ J ∈ copyOrbit G F := by
  refine ⟨fun h => ?_, smul_mem_copyOrbit G g⟩
  simpa only [inv_smul_smul] using smul_mem_copyOrbit G g⁻¹ h

@[simp] theorem copyOrbit_smul (g : G) (F : Finset X) :
    copyOrbit G (g • F) = copyOrbit G F := by
  ext J
  constructor
  · intro hJ
    obtain ⟨h, rfl⟩ := (mem_copyOrbit_iff G).mp hJ
    exact (mem_copyOrbit_iff G).mpr ⟨h * g, mul_smul _ _ _⟩
  · intro hJ
    obtain ⟨h, rfl⟩ := (mem_copyOrbit_iff G).mp hJ
    apply (mem_copyOrbit_iff G).mpr
    refine ⟨h * g⁻¹, ?_⟩
    simp only [mul_smul, inv_smul_smul]

theorem copyOrbit_eq_of_mem_copyOrbit {F J : Finset X} (hJ : J ∈ copyOrbit G F) :
    copyOrbit G J = copyOrbit G F := by
  obtain ⟨g, rfl⟩ := (mem_copyOrbit_iff G).mp hJ
  exact copyOrbit_smul G g F

theorem card_eq_of_mem_copyOrbit {F J : Finset X} (hJ : J ∈ copyOrbit G F) :
    J.card = F.card := by
  obtain ⟨g, rfl⟩ := (mem_copyOrbit_iff G).mp hJ
  exact Finset.card_smul_finset _ _

/-- The group acts bijectively on the set of actual orbit copies. -/
def orbitCopyEquiv (g : G) (F : Finset X) : OrbitCopy G F ≃ OrbitCopy G F where
  toFun J := ⟨g • J.val, smul_mem_copyOrbit G g J.property⟩
  invFun J := ⟨g⁻¹ • J.val, smul_mem_copyOrbit G g⁻¹ J.property⟩
  left_inv _ := Subtype.ext (inv_smul_smul _ _)
  right_inv _ := Subtype.ext (smul_inv_smul _ _)

@[simp] theorem orbitCopyEquiv_val (g : G) (F : Finset X) (J : OrbitCopy G F) :
    (orbitCopyEquiv G g F J).val = g • J.val := rfl

/-- There are no more internal copies than subsets of the correct size. -/
theorem internalCopyCount_le_choose (I F : Finset X) :
    internalCopyCount G I F ≤ Nat.choose I.card F.card := by
  rw [← Finset.card_powersetCard F.card I]
  apply Finset.card_le_card
  intro J hJ
  obtain ⟨hcopy, hsub⟩ := Finset.mem_filter.mp hJ
  exact Finset.mem_powersetCard.mpr ⟨hsub, card_eq_of_mem_copyOrbit G hcopy⟩

@[simp] theorem copyOrbit_empty : copyOrbit G (∅ : Finset X) = {∅} := by
  ext J
  simp only [mem_copyOrbit_iff, Finset.smul_finset_empty, Finset.mem_singleton]
  constructor
  · rintro ⟨_, h⟩
    exact h.symm
  · intro h
    exact ⟨1, h.symm⟩

@[simp] theorem orbitCount_empty : orbitCount G (∅ : Finset X) = 1 := by
  simp [orbitCount]

@[simp] theorem internalCopyCount_empty (I : Finset X) :
    internalCopyCount G I ∅ = 1 := by
  simp [internalCopyCount, Finset.filter_singleton, Finset.empty_subset]

/-- Acting permutes the distinct orbit elements with no multiplicity. -/
theorem sum_copyOrbit_smul (g : G) (F : Finset X) (f : Finset X → ℕ) :
    (∑ J ∈ copyOrbit G F, f (g • J)) = ∑ J ∈ copyOrbit G F, f J := by
  calc
    _ = ∑ J : OrbitCopy G F, f (g • J.val) :=
      (Finset.sum_coe_sort (copyOrbit G F) (fun J => f (g • J))).symm
    _ = ∑ J : OrbitCopy G F, f J.val :=
      (orbitCopyEquiv G g F).sum_comp (fun J : OrbitCopy G F => f J.val)
    _ = _ := Finset.sum_coe_sort (copyOrbit G F) f

theorem internalCopyCount_smul (g : G) (I F : Finset X) :
    internalCopyCount G (g • I) F = internalCopyCount G I F := by
  have h := sum_copyOrbit_smul G g F (fun J => if J ⊆ g • I then 1 else 0)
  simpa only [Finset.smul_finset_subset_smul_finset_iff, Finset.sum_boole,
    Nat.cast_id, internalCopyCount] using h.symm

theorem containingCopyCount_smul (g : G) (I U : Finset X) :
    containingCopyCount G I (g • U) = containingCopyCount G I U := by
  have h := sum_copyOrbit_smul G g I (fun J => if g • U ⊆ J then 1 else 0)
  simpa only [Finset.smul_finset_subset_smul_finset_iff, Finset.sum_boole,
    Nat.cast_id, containingCopyCount] using h.symm

theorem internalCopyCount_eq_of_mem_copyOrbit {I I₀ F : Finset X}
    (hI : I₀ ∈ copyOrbit G I) : internalCopyCount G I₀ F = internalCopyCount G I F := by
  obtain ⟨g, rfl⟩ := (mem_copyOrbit_iff G).mp hI
  exact internalCopyCount_smul G g I F

theorem containingCopyCount_eq_of_mem_copyOrbit {I F F₀ : Finset X}
    (hF : F₀ ∈ copyOrbit G F) :
    containingCopyCount G I F₀ = containingCopyCount G I F := by
  obtain ⟨g, rfl⟩ := (mem_copyOrbit_iff G).mp hF
  exact containingCopyCount_smul G g I F

/-- Double-count containment pairs of distinct orbit copies. -/
theorem copy_incidence_identity (I F : Finset X) :
    orbitCount G F * containingCopyCount G I F =
      orbitCount G I * internalCopyCount G I F := by
  have h : (∑ U ∈ copyOrbit G F, ∑ J ∈ copyOrbit G I, if U ⊆ J then (1 : ℕ) else 0) =
      ∑ J ∈ copyOrbit G I, ∑ U ∈ copyOrbit G F, if U ⊆ J then (1 : ℕ) else 0 :=
    Finset.sum_comm
  simp only [Finset.sum_boole] at h
  change (∑ U ∈ copyOrbit G F, containingCopyCount G I U) =
    ∑ J ∈ copyOrbit G I, internalCopyCount G J F at h
  have hleft : (∑ U ∈ copyOrbit G F, containingCopyCount G I U) =
      orbitCount G F * containingCopyCount G I F := by
    calc
      _ = ∑ _U ∈ copyOrbit G F, containingCopyCount G I F :=
        Finset.sum_congr rfl (fun _ hU => containingCopyCount_eq_of_mem_copyOrbit G hU)
      _ = _ := by simp [orbitCount]
  have hright : (∑ J ∈ copyOrbit G I, internalCopyCount G J F) =
      orbitCount G I * internalCopyCount G I F := by
    calc
      _ = ∑ _J ∈ copyOrbit G I, internalCopyCount G I F :=
        Finset.sum_congr rfl (fun _ hJ => internalCopyCount_eq_of_mem_copyOrbit G hJ)
      _ = _ := by simp [orbitCount]
  rwa [hleft, hright] at h

theorem containingCopyCount_pos_iff (I U : Finset X) :
    0 < containingCopyCount G I U ↔ ∃ g : G, U ⊆ g • I := by
  rw [containingCopyCount, Finset.card_pos]
  constructor
  · rintro ⟨J, hJ⟩
    obtain ⟨hcopy, hsub⟩ := Finset.mem_filter.mp hJ
    obtain ⟨g, rfl⟩ := (mem_copyOrbit_iff G).mp hcopy
    exact ⟨g, hsub⟩
  · rintro ⟨g, hg⟩
    refine ⟨g • I, Finset.mem_filter.mpr ⟨?_, hg⟩⟩
    exact (mem_copyOrbit_iff G).mpr ⟨g, rfl⟩

/-- Positive containment can be pulled back to an actual subset of `I`. -/
theorem exists_pullback_of_containingCopyCount_pos {I U : Finset X}
    (hpos : 0 < containingCopyCount G I U) :
    ∃ V : Finset X, V ⊆ I ∧ U ∈ copyOrbit G V ∧ V.card = U.card := by
  obtain ⟨g, hg⟩ := (containingCopyCount_pos_iff G I U).mp hpos
  refine ⟨g⁻¹ • U, (Finset.subset_smul_finset_iff.mp hg), ?_,
    Finset.card_smul_finset _ _⟩
  exact (mem_copyOrbit_iff G).mpr ⟨g, smul_inv_smul _ _⟩

/-- The uniform law on distinct copies, rather than on labeled embeddings. -/
def copyLaw (I : Finset X) : FiniteLaw (OrbitCopy G I) :=
  FiniteLaw.uniform (OrbitCopy G I)

theorem copyLaw_isPositive (I : Finset X) : (copyLaw G I).IsPositive :=
  FiniteLaw.uniform_isPositive _

/-- Probability that a uniform actual copy contains an observed finite set. -/
def containmentProb (I U : Finset X) : ℝ :=
  (copyLaw G I).prob (fun J => U ⊆ J.val)

/-- Expose the generic uniform formula with the caller's decidable predicate.
The finite sets are equal extensionally even when the generic probability
definition uses its own classical decision procedure. -/
private theorem uniform_prob_count (Ω : Type*) [Fintype Ω] [Nonempty Ω]
    (P : Ω → Prop) [DecidablePred P] :
    (FiniteLaw.uniform Ω).prob P = ((Finset.univ.filter P).card : ℝ) / Fintype.card Ω := by
  have hfilter : @Finset.filter Ω P (fun ω => Classical.propDecidable (P ω)) Finset.univ =
      Finset.univ.filter P := by
    ext ω
    simp only [Finset.mem_filter]
  rw [FiniteLaw.uniform_prob, hfilter]

theorem card_filter_OrbitCopy (I : Finset X) (P : Finset X → Prop) [DecidablePred P] :
    ((Finset.univ : Finset (OrbitCopy G I)).filter (fun J => P J.val)).card =
      ((copyOrbit G I).filter P).card := by
  have h : (∑ J : OrbitCopy G I, if P J.val then (1 : ℕ) else 0) =
      ∑ J ∈ copyOrbit G I, if P J then 1 else 0 :=
    Finset.sum_coe_sort (copyOrbit G I) (fun J => if P J then (1 : ℕ) else 0)
  simpa only [Finset.sum_boole, Nat.cast_id] using h

theorem containmentProb_eq_count (I U : Finset X) :
    containmentProb G I U = (containingCopyCount G I U : ℝ) / orbitCount G I := by
  rw [containmentProb, copyLaw, uniform_prob_count, card_OrbitCopy]
  exact congrArg (fun k : ℕ => (k : ℝ) / (orbitCount G I : ℝ))
    (card_filter_OrbitCopy G I (fun J => U ⊆ J))

theorem containmentProb_nonneg (I U : Finset X) : 0 ≤ containmentProb G I U :=
  (copyLaw G I).prob_nonneg _

theorem containmentProb_le_one (I U : Finset X) : containmentProb G I U ≤ 1 :=
  (copyLaw G I).prob_le_one _

@[simp] theorem containmentProb_empty (I : Finset X) : containmentProb G I ∅ = 1 := by
  simp [containmentProb]

theorem containmentProb_smul (g : G) (I U : Finset X) :
    containmentProb G I (g • U) = containmentProb G I U := by
  rw [containmentProb_eq_count, containmentProb_eq_count, containingCopyCount_smul]

theorem containmentProb_smul_left (g : G) (I U : Finset X) :
    containmentProb G (g • I) U = containmentProb G I U := by
  simp only [containmentProb_eq_count, containingCopyCount, orbitCount, copyOrbit_smul]

theorem containmentProb_smul_both (g : G) (I U : Finset X) :
    containmentProb G (g • I) (g • U) = containmentProb G I U := by
  rw [containmentProb_smul_left, containmentProb_smul]

theorem containmentProb_eq_of_mem_copyOrbit {I F F₀ : Finset X}
    (hF : F₀ ∈ copyOrbit G F) : containmentProb G I F₀ = containmentProb G I F := by
  obtain ⟨g, rfl⟩ := (mem_copyOrbit_iff G).mp hF
  exact containmentProb_smul G g I F

/-- The exact permutation-symmetry incidence identity, including the empty set. -/
theorem containmentProb_eq_internalCopyCount (I F : Finset X) :
    containmentProb G I F = (internalCopyCount G I F : ℝ) / orbitCount G F := by
  rw [containmentProb_eq_count]
  have hI : (orbitCount G I : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr (orbitCount_pos G I))
  have hF : (orbitCount G F : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr (orbitCount_pos G F))
  have hcount : (orbitCount G F : ℝ) * containingCopyCount G I F =
      (orbitCount G I : ℝ) * internalCopyCount G I F := by
    exact_mod_cast copy_incidence_identity G I F
  apply (div_eq_div_iff hI hF).mpr
  nlinarith [hcount]

theorem containmentProb_copy_eq_internalCopyCount {I F F₀ : Finset X}
    (hF : F₀ ∈ copyOrbit G F) :
    containmentProb G I F₀ = (internalCopyCount G I F : ℝ) / orbitCount G F := by
  rw [containmentProb_eq_of_mem_copyOrbit G hF, containmentProb_eq_internalCopyCount]

theorem containmentProb_pos_iff (I U : Finset X) :
    0 < containmentProb G I U ↔ ∃ g : G, U ⊆ g • I := by
  rw [containmentProb_eq_count,
    div_pos_iff_of_pos_right (Nat.cast_pos.mpr (orbitCount_pos G I)), Nat.cast_pos]
  exact containingCopyCount_pos_iff G I U

theorem exists_pullback_of_containmentProb_pos {I U : Finset X}
    (hpos : 0 < containmentProb G I U) :
    ∃ V : Finset X, V ⊆ I ∧ U ∈ copyOrbit G V ∧ V.card = U.card := by
  apply exists_pullback_of_containingCopyCount_pos G
  exact (containingCopyCount_pos_iff G I U).mpr ((containmentProb_pos_iff G I U).mp hpos)

/-- Every copy of a subset extends to at least one copy of its ambient set. -/
theorem containmentProb_pos_of_copy_subset {S I S₀ : Finset X}
    (hSI : S ⊆ I) (hS₀ : S₀ ∈ copyOrbit G S) : 0 < containmentProb G I S₀ := by
  obtain ⟨g, rfl⟩ := (mem_copyOrbit_iff G).mp hS₀
  exact (containmentProb_pos_iff G I (g • S)).mpr
    ⟨g, Finset.smul_finset_subset_smul_finset_iff.mpr hSI⟩

/-- Actual distinct extensions of the observed predecessor. Histories in a
tree may index this same family separately; this type never merges histories. -/
abbrev ExtensionCopy (I S : Finset X) := {J : OrbitCopy G I // S ⊆ J.val}

theorem extensionCopy_nonempty {I S : Finset X}
    (hpos : 0 < containmentProb G I S) : Nonempty (ExtensionCopy G I S) := by
  obtain ⟨g, hg⟩ := (containmentProb_pos_iff G I S).mp hpos
  exact ⟨⟨⟨g • I, (mem_copyOrbit_iff G).mpr ⟨g, rfl⟩⟩, hg⟩⟩

@[simp] theorem card_ExtensionCopy (I S : Finset X) :
    Fintype.card (ExtensionCopy G I S) = containingCopyCount G I S := by
  rw [Fintype.card_subtype, card_filter_OrbitCopy]
  rfl

/-- The uniform law on actual copies extending `S`, with positivity justified
by the actual containment event. -/
def extensionLaw (I S : Finset X) (hpos : 0 < containmentProb G I S) :
    FiniteLaw (ExtensionCopy G I S) := by
  let : Nonempty (ExtensionCopy G I S) := extensionCopy_nonempty G hpos
  exact FiniteLaw.uniform (ExtensionCopy G I S)

theorem extensionLaw_isPositive (I S : Finset X) (hpos : 0 < containmentProb G I S) :
    (extensionLaw G I S hpos).IsPositive := by
  let : Nonempty (ExtensionCopy G I S) := extensionCopy_nonempty G hpos
  exact FiniteLaw.uniform_isPositive _

def extensionIntersectionEquiv (I S J : Finset X) :
    {C : ExtensionCopy G I S // J ⊆ C.val.val} ≃ ExtensionCopy G I (S ∪ J) where
  toFun C := ⟨C.val.val, Finset.union_subset_iff.mpr ⟨C.val.property, C.property⟩⟩
  invFun C := ⟨⟨C.val, (Finset.union_subset_iff.mp C.property).1⟩,
    (Finset.union_subset_iff.mp C.property).2⟩
  left_inv C := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv C := by apply Subtype.ext; rfl

theorem card_extension_filter (I S J : Finset X) :
    ((Finset.univ : Finset (ExtensionCopy G I S)).filter
      (fun C => J ⊆ C.val.val)).card = containingCopyCount G I (S ∪ J) := by
  calc
    _ = Fintype.card {C : ExtensionCopy G I S // J ⊆ C.val.val} :=
      (Fintype.card_subtype _).symm
    _ = Fintype.card (ExtensionCopy G I (S ∪ J)) :=
      Fintype.card_congr (extensionIntersectionEquiv G I S J)
    _ = _ := card_ExtensionCopy G I (S ∪ J)

theorem extensionLaw_prob (I S J : Finset X) (hpos : 0 < containmentProb G I S) :
    (extensionLaw G I S hpos).prob (fun C => J ⊆ C.val.val) =
      containmentProb G I (S ∪ J) / containmentProb G I S := by
  let : Nonempty (ExtensionCopy G I S) := extensionCopy_nonempty G hpos
  change (FiniteLaw.uniform (ExtensionCopy G I S)).prob _ = _
  rw [uniform_prob_count]
  calc
    _ = (containingCopyCount G I (S ∪ J) : ℝ) / containingCopyCount G I S :=
      congrArg₂ (fun a b : ℕ => (a : ℝ) / (b : ℝ))
        (card_extension_filter G I S J) (card_ExtensionCopy G I S)
    _ = _ := by
      rw [containmentProb_eq_count, containmentProb_eq_count]
      have hI : (orbitCount G I : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr (orbitCount_pos G I))
      have hS : (containingCopyCount G I S : ℝ) ≠ 0 := by
        apply ne_of_gt
        apply Nat.cast_pos.mpr
        exact (containingCopyCount_pos_iff G I S).mpr ((containmentProb_pos_iff G I S).mp hpos)
      field_simp [hI, hS]

/-- For a set disjoint from the predecessor, containment in the added label
is exactly the usual conditional containment event. -/
theorem extensionLaw_added_prob (I S J : Finset X) (hpos : 0 < containmentProb G I S)
    (hdis : Disjoint J S) :
    (extensionLaw G I S hpos).prob (fun C => J ⊆ C.val.val \ S) =
      containmentProb G I (S ∪ J) / containmentProb G I S := by
  simpa only [Finset.subset_sdiff, hdis, and_true] using extensionLaw_prob G I S J hpos

/-- A set meeting the predecessor cannot lie in any added label. -/
theorem extensionLaw_added_prob_eq_zero (I S J : Finset X)
    (hpos : 0 < containmentProb G I S) (hdis : ¬ Disjoint J S) :
    (extensionLaw G I S hpos).prob (fun C => J ⊆ C.val.val \ S) = 0 := by
  simp [FiniteLaw.prob, Finset.subset_sdiff, hdis]

end LeanBlast.SecondKahnKalai

end

end OAI
