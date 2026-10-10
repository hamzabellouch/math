import OAI.Combinatorics.Progressions.Estimates.RetainedSliceAverages

namespace OAI

section

namespace Erdos3.FiniteCoefficientSlice

open scoped BigOperators Classical

def residuePattern (s : FiniteCoefficientSlice) (n : ℕ) (x : s.Domain) : ZMod n := x.val

noncomputable def residueLabels (s : FiniteCoefficientSlice) (n : ℕ) : Finset (ZMod n) :=
  Finset.univ.image (s.residuePattern n)

abbrev ResidueLabel (s : FiniteCoefficientSlice) (n : ℕ) := ↥(s.residueLabels n)

noncomputable def residueLabelMap (s : FiniteCoefficientSlice) (n : ℕ) (x : s.Domain) :
    s.ResidueLabel n := ⟨s.residuePattern n x, Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩⟩

def refineResidues (s : FiniteCoefficientSlice) (n : ℕ) (r : s.ResidueLabel n) :
    FiniteCoefficientSlice where
  length := s.length
  offset := s.offset
  stride := s.stride
  modulus := n
  residue := r.val

theorem refineResidues_old_residue (s : FiniteCoefficientSlice) (n : ℕ)
    (hdvd : s.modulus ∣ n) (r : s.ResidueLabel n) (x : (s.refineResidues n r).Domain) :
    (x.val : ZMod s.modulus) = s.residue := by
  obtain ⟨y, _, hy⟩ := Finset.mem_image.mp r.property
  have hnew : (x.val : ZMod n) = (y.val : ZMod n) :=
    (Finset.mem_filter.mp x.property).2.trans hy.symm
  have hold := congrArg (ZMod.castHom hdvd (ZMod s.modulus)) hnew
  simp only [map_intCast] at hold
  exact hold.trans (Finset.mem_filter.mp y.property).2

def refineResiduesEmbedding (s : FiniteCoefficientSlice) (n : ℕ) (hdvd : s.modulus ∣ n)
    (r : s.ResidueLabel n) : (s.refineResidues n r).Domain ↪ s.Domain where
  toFun x := ⟨x.val, Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp x.property).1,
    s.refineResidues_old_residue n hdvd r x⟩⟩
  inj' := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : s.Domain => z.val) h)

theorem refineResiduesEmbedding_value (s : FiniteCoefficientSlice) (n : ℕ)
    (hdvd : s.modulus ∣ n) (r : s.ResidueLabel n) (x : (s.refineResidues n r).Domain) :
    s.value (s.refineResiduesEmbedding n hdvd r x) = (s.refineResidues n r).value x := rfl

theorem refineResiduesEmbedding_range (s : FiniteCoefficientSlice) (n : ℕ)
    (hdvd : s.modulus ∣ n) (r : s.ResidueLabel n) :
    finiteEmbeddingRange (s.refineResiduesEmbedding n hdvd r) =
      Finset.univ.filter (fun x => s.residueLabelMap n x = r) := by
  apply Finset.ext
  intro x
  constructor
  · intro hx
    obtain ⟨y, _, hy⟩ := Finset.mem_map.mp hx
    subst x
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      Subtype.ext (Finset.mem_filter.mp y.property).2⟩
  · intro hx
    have he := congrArg Subtype.val (Finset.mem_filter.mp hx).2
    let y : (s.refineResidues n r).Domain := ⟨x.val,
      Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp x.property).1, he⟩⟩
    exact Finset.mem_map.mpr ⟨y, Finset.mem_univ y, Subtype.ext rfl⟩

theorem residueLabels_card_le (s : FiniteCoefficientSlice) (n : ℕ) [NeZero n] :
    (s.residueLabels n).card ≤ n := by
  simpa only [ZMod.card] using (Finset.card_le_univ (s.residueLabels n))

theorem residueLabelMap_value_mod (s : FiniteCoefficientSlice) (n M : ℕ) (hM : M ∣ n)
    (x : s.Domain) :
    (s.value x : ZMod M) = (s.offset : ZMod M) + (s.stride : ZMod M) *
      ZMod.castHom hM (ZMod M) (s.residueLabelMap n x).val := by
  change ((s.offset + s.stride * x.val : ℤ) : ZMod M) =
    (s.offset : ZMod M) + (s.stride : ZMod M) * ZMod.castHom hM (ZMod M) (x.val : ZMod n)
  simp only [Int.cast_add, Int.cast_mul, map_intCast]

theorem refineResidues_mass_pos (s : FiniteCoefficientSlice) [Nonempty s.Domain]
    (n : ℕ) (hdvd : s.modulus ∣ n) (r : s.ResidueLabel n) :
    0 < (FiniteProbabilityWeights.uniform s.Domain).mass
      (finiteEmbeddingRange (s.refineResiduesEmbedding n hdvd r)) := by
  rw [s.refineResiduesEmbedding_range, FiniteProbabilityWeights.uniform_mass]
  apply div_pos
  · obtain ⟨y, _, hy⟩ := Finset.mem_image.mp r.property
    have hn : (Finset.univ.filter (fun x => s.residueLabelMap n x = r)).Nonempty :=
      ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ y, Subtype.ext hy⟩⟩
    exact_mod_cast Finset.card_pos.mpr hn
  · exact_mod_cast Fintype.card_pos (α := s.Domain)

theorem retained_refineResidues_mean_ge (s : FiniteCoefficientSlice) [Nonempty s.Domain]
    (n : ℕ) (hdvd : s.modulus ∣ n) (r : s.ResidueLabel n) (w : ℤ → ℝ) (η : ℝ)
    (hr : r ∉ (FiniteProbabilityWeights.uniform s.Domain).lowWeightFibers
      (s.residueLabelMap n) (fun x => w (s.value x)) η) :
    η ≤ 𝔼 x : (s.refineResidues n r).Domain, w ((s.refineResidues n r).value x) := by
  refine FiniteProbabilityWeights.retained_embedding_mean_ge
    (s.residueLabelMap n) (fun x => w (s.value x)) η r
    (s.refineResiduesEmbedding n hdvd r) hr ?_ (s.refineResidues_mass_pos n hdvd r)
  apply (s.refineResiduesEmbedding_range n hdvd r).trans
  ext x
  simp only [Finset.mem_filter]

end Erdos3.FiniteCoefficientSlice

end

section

namespace Erdos3.FiniteCubeSlice

open scoped BigOperators Classical

def residuePattern {q : ℕ} (s : FiniteCubeSlice q) (n : Option (Fin q) → ℕ)
    (x : s.Domain) : ∀ i, ZMod (n i) := fun i => (s.coordinates x i : ZMod (n i))

noncomputable def residueLabels {q : ℕ} (s : FiniteCubeSlice q) (n : Option (Fin q) → ℕ) :
    Finset (∀ i, ZMod (n i)) := Finset.univ.image (s.residuePattern n)

abbrev ResidueLabel {q : ℕ} (s : FiniteCubeSlice q) (n : Option (Fin q) → ℕ) :=
  ↥(s.residueLabels n)

noncomputable def residueLabelMap {q : ℕ} (s : FiniteCubeSlice q) (n : Option (Fin q) → ℕ)
    (x : s.Domain) : s.ResidueLabel n :=
  ⟨s.residuePattern n x, Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩⟩

def refineResidues {q : ℕ} (s : FiniteCubeSlice q) (n : Option (Fin q) → ℕ)
    (r : s.ResidueLabel n) : FiniteCubeSlice q where
  length := s.length
  root := s.root
  modulus := n
  residue := r.val

theorem refineResidues_old_residue {q : ℕ} (s : FiniteCubeSlice q) (n : Option (Fin q) → ℕ)
    (hdvd : ∀ i, s.modulus i ∣ n i) (r : s.ResidueLabel n)
    (x : (s.refineResidues n r).Domain) (i : Option (Fin q)) :
    (supportedCubeCoordinates x.val.val i : ZMod (s.modulus i)) = s.residue i := by
  obtain ⟨y, _, hy⟩ := Finset.mem_image.mp r.property
  have hnew : (supportedCubeCoordinates x.val.val i : ZMod (n i)) =
      (s.coordinates y i : ZMod (n i)) := (x.property i).trans (congrFun hy i).symm
  have hold := congrArg (ZMod.castHom (hdvd i) (ZMod (s.modulus i))) hnew
  simp only [map_intCast] at hold
  exact hold.trans (y.property i)

def refineResiduesEmbedding {q : ℕ} (s : FiniteCubeSlice q) (n : Option (Fin q) → ℕ)
    (hdvd : ∀ i, s.modulus i ∣ n i) (r : s.ResidueLabel n) :
    (s.refineResidues n r).Domain ↪ s.Domain where
  toFun x := ⟨x.val, s.refineResidues_old_residue n hdvd r x⟩
  inj' := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : s.Domain => z.val) h)

theorem refineResiduesEmbedding_coordinates {q : ℕ} (s : FiniteCubeSlice q)
    (n : Option (Fin q) → ℕ) (hdvd : ∀ i, s.modulus i ∣ n i) (r : s.ResidueLabel n)
    (x : (s.refineResidues n r).Domain) :
    s.coordinates (s.refineResiduesEmbedding n hdvd r x) = (s.refineResidues n r).coordinates x := rfl

theorem refineResiduesEmbedding_range {q : ℕ} (s : FiniteCubeSlice q)
    (n : Option (Fin q) → ℕ) (hdvd : ∀ i, s.modulus i ∣ n i) (r : s.ResidueLabel n) :
    finiteEmbeddingRange (s.refineResiduesEmbedding n hdvd r) =
      Finset.univ.filter (fun x => s.residueLabelMap n x = r) := by
  apply Finset.ext
  intro x
  constructor
  · intro hx
    obtain ⟨y, _, hy⟩ := Finset.mem_map.mp hx
    subst x
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    apply Subtype.ext
    funext i
    exact y.property i
  · intro hx
    have he := congrArg Subtype.val (Finset.mem_filter.mp hx).2
    let y : (s.refineResidues n r).Domain := ⟨x.val, fun i => congrFun he i⟩
    exact Finset.mem_map.mpr ⟨y, Finset.mem_univ y, Subtype.ext rfl⟩

theorem residueLabels_card_le {q : ℕ} (s : FiniteCubeSlice q) (n : Option (Fin q) → ℕ)
    [∀ i, NeZero (n i)] : (s.residueLabels n).card ≤ ∏ i, n i := by
  calc
    _ ≤ Fintype.card (∀ i, ZMod (n i)) := Finset.card_le_univ _
    _ = _ := by simp only [Fintype.card_pi, ZMod.card]

theorem refineResidues_mass_pos {q : ℕ} (s : FiniteCubeSlice q) [Nonempty s.Domain]
    (n : Option (Fin q) → ℕ) (hdvd : ∀ i, s.modulus i ∣ n i) (r : s.ResidueLabel n) :
    0 < (FiniteProbabilityWeights.uniform s.Domain).mass
      (finiteEmbeddingRange (s.refineResiduesEmbedding n hdvd r)) := by
  rw [s.refineResiduesEmbedding_range, FiniteProbabilityWeights.uniform_mass]
  apply div_pos
  · obtain ⟨y, _, hy⟩ := Finset.mem_image.mp r.property
    have hn : (Finset.univ.filter (fun x => s.residueLabelMap n x = r)).Nonempty :=
      ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ y, Subtype.ext hy⟩⟩
    exact_mod_cast Finset.card_pos.mpr hn
  · exact_mod_cast Fintype.card_pos (α := s.Domain)

theorem retained_refineResidues_mean_ge {q : ℕ} (s : FiniteCubeSlice q) [Nonempty s.Domain]
    (n : Option (Fin q) → ℕ) (hdvd : ∀ i, s.modulus i ∣ n i) (r : s.ResidueLabel n)
    (w : (Option (Fin q) → ℤ) → ℝ) (η : ℝ)
    (hr : r ∉ (FiniteProbabilityWeights.uniform s.Domain).lowWeightFibers
      (s.residueLabelMap n) (fun x => w (s.coordinates x)) η) :
    η ≤ 𝔼 x : (s.refineResidues n r).Domain, w ((s.refineResidues n r).coordinates x) := by
  refine FiniteProbabilityWeights.retained_embedding_mean_ge
    (s.residueLabelMap n) (fun x => w (s.coordinates x)) η r
    (s.refineResiduesEmbedding n hdvd r) hr ?_ (s.refineResidues_mass_pos n hdvd r)
  apply (s.refineResiduesEmbedding_range n hdvd r).trans
  ext x
  simp only [Finset.mem_filter]

end Erdos3.FiniteCubeSlice

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem FiniteCubeSlice.residueLabels_card_le_uniform {q : ℕ} (s : FiniteCubeSlice q)
    (n : Option (Fin q) → ℕ) [∀ i, NeZero (n i)] (B : ℕ) (hn : ∀ i, n i ≤ B) :
    (s.residueLabels n).card ≤ B ^ (q + 1) := by
  calc
    _ ≤ ∏ i, n i := s.residueLabels_card_le n
    _ ≤ ∏ _i : Option (Fin q), B := Finset.prod_le_prod (fun i _ => hn i)
    _ = _ := by simp

theorem FiniteCubeSlice.residueLabels_product_card_le {q : ℕ} (s : FiniteCubeSlice q)
    (B M : ℕ) (hm : ∀ i, 0 < s.modulus i) (hM : 0 < M) (hmB : ∀ i, s.modulus i ≤ B) :
    (s.residueLabels (fun i => s.modulus i * M)).card ≤ (B * M) ^ (q + 1) := by
  let : ∀ i, NeZero (s.modulus i * M) := fun i => ⟨(Nat.mul_pos (hm i) hM).ne'⟩
  exact s.residueLabels_card_le_uniform _ (B * M) (fun i => Nat.mul_le_mul_right M (hmB i))

theorem FiniteCoefficientSlice.residueLabels_product_card_le (s : FiniteCoefficientSlice)
    (B M : ℕ) (hm : 0 < s.modulus) (hM : 0 < M) (hmB : s.modulus ≤ B) :
    (s.residueLabels (s.modulus * M)).card ≤ B * M := by
  let : NeZero (s.modulus * M) := ⟨(Nat.mul_pos hm hM).ne'⟩
  exact (s.residueLabels_card_le _).trans (Nat.mul_le_mul_right M hmB)

end Erdos3

end

end OAI
