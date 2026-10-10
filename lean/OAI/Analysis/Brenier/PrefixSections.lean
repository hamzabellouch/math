import OAI.Analysis.Brenier.Sections

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem358.FinitePrefix

abbrev Coordinates (n : ℕ) := Fin n → ℝ

/-- Append two finite coordinate blocks, with their usual sup norms. -/
def append (n m : ℕ) :
    (Coordinates n × Coordinates m) ≃L[ℝ] Coordinates (n + m) where
  __ := Fin.appendHomeomorph n m
  map_add' p q := by
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  map_smul' c p := by
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

@[simp] theorem append_apply (n m : ℕ) (p : Coordinates n × Coordinates m) :
    append n m p = Fin.append p.1 p.2 := rfl

/-- Reassemble a bounded prefix and its complementary coordinate block. -/
def join {n d : ℕ} (h : n ≤ d) :
    (Coordinates n × Coordinates (d - n)) ≃L[ℝ] Coordinates d :=
  (append n (d - n)).trans
    (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin d => ℝ)
      (finCongr (Nat.add_sub_of_le h)))

/-- Index of a coordinate in the prefix. -/
def leftIndex {n d : ℕ} (h : n ≤ d) (i : Fin n) : Fin d := i.castLE h

/-- Index of a coordinate in the complementary block. -/
def rightIndex {n d : ℕ} (h : n ≤ d) (i : Fin (d - n)) : Fin d :=
  Fin.cast (Nat.add_sub_of_le h) (Fin.natAdd n i)

@[simp] theorem join_left {n d : ℕ} (h : n ≤ d)
    (a : Coordinates n) (b : Coordinates (d - n)) (i : Fin n) :
    join h (a, b) (leftIndex h i) = a i := by
  change Fin.append a b (Fin.cast (Nat.add_sub_of_le h).symm (leftIndex h i)) = a i
  have hi : Fin.cast (Nat.add_sub_of_le h).symm (leftIndex h i) =
      Fin.castAdd (d - n) i := by ext; rfl
  rw [hi, Fin.append_left]

@[simp] theorem join_right {n d : ℕ} (h : n ≤ d)
    (a : Coordinates n) (b : Coordinates (d - n)) (i : Fin (d - n)) :
    join h (a, b) (rightIndex h i) = b i := by
  change Fin.append a b
    (Fin.cast (Nat.add_sub_of_le h).symm (Fin.cast (Nat.add_sub_of_le h) (Fin.natAdd n i))) = b i
  simp

/-- The actual bounded prefix. -/
def headBlock {n d : ℕ} (h : n ≤ d) (x : Coordinates d) : Coordinates n :=
  fun i => x (leftIndex h i)

/-- The remaining coordinates after a bounded prefix. -/
def tailBlock {n d : ℕ} (h : n ≤ d) (x : Coordinates d) : Coordinates (d - n) :=
  fun i => x (rightIndex h i)

@[simp] theorem prefix_join {n d : ℕ} (h : n ≤ d)
    (a : Coordinates n) (b : Coordinates (d - n)) : headBlock h (join h (a,b)) = a := by
  ext i
  exact join_left h a b i

@[simp] theorem suffix_join {n d : ℕ} (h : n ≤ d)
    (a : Coordinates n) (b : Coordinates (d - n)) : tailBlock h (join h (a,b)) = b := by
  ext i
  exact join_right h a b i

@[simp] theorem join_symm_apply {n d : ℕ} (h : n ≤ d) (x : Coordinates d) :
    (join h).symm x = (headBlock h x, tailBlock h x) := by
  obtain ⟨⟨a,b⟩, rfl⟩ := (join h).surjective x
  simp

@[simp] theorem join_prefix_suffix {n d : ℕ} (h : n ≤ d) (x : Coordinates d) :
    join h (headBlock h x, tailBlock h x) = x := by
  rw [← join_symm_apply]
  exact (join h).apply_symm_apply x

/-- Appending coordinate blocks preserves the product Lebesgue measure. -/
theorem measurePreserving_append (n m : ℕ) :
    MeasurePreserving (append n m) (volume.prod volume) volume := by
  have h₁ := volume_measurePreserving_sumPiEquivProdPi_symm
    (fun _ : Fin n ⊕ Fin m => ℝ)
  have h₂ := volume_measurePreserving_piCongrLeft (fun _ : Fin (n + m) => ℝ)
    (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m))
  have he : (append n m : (Coordinates n × Coordinates m) → Coordinates (n+m)) =
      (MeasurableEquiv.piCongrLeft (fun _ : Fin (n+m) => ℝ) finSumFinEquiv) ∘
        (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin m => ℝ)).symm := by
    funext p i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [MeasurableEquiv.piCongrLeft, MeasurableEquiv.sumPiEquivProdPi,
        Equiv.piCongrLeft_apply, Equiv.sumPiEquivProdPi]
  rw [he]
  exact h₂.comp h₁

/-- The bounded-prefix coordinate split has unit Jacobian. -/
theorem measurePreserving_join {n d : ℕ} (h : n ≤ d) :
    MeasurePreserving (join h) (volume.prod volume) volume := by
  exact (volume_measurePreserving_piCongrLeft (fun _ : Fin d => ℝ)
    (finCongr (Nat.add_sub_of_le h))).comp (measurePreserving_append n (d-n))

/-- The inverse split also preserves Lebesgue measure. -/
theorem measurePreserving_split {n d : ℕ} (h : n ≤ d) :
    MeasurePreserving (join h).symm volume (volume.prod volume) := by
  exact MeasurePreserving.symm (join h).toHomeomorph.toMeasurableEquiv
    (measurePreserving_join h)

/-- Restriction to a body commutes with coordinate reassembly. -/
theorem measurePreserving_join_restrict {n d : ℕ} (h : n ≤ d)
    {K : Set (Coordinates d)} (hK : MeasurableSet K) :
    MeasurePreserving (join h)
      ((volume.prod volume).restrict (join h ⁻¹' K)) (volume.restrict K) :=
  (measurePreserving_join h).restrict_preimage hK

theorem continuous_headBlock {n d : ℕ} (h : n ≤ d) : Continuous (headBlock h) := by
  exact continuous_pi (fun i => continuous_apply (leftIndex h i))

theorem continuous_tailBlock {n d : ℕ} (h : n ≤ d) : Continuous (tailBlock h) := by
  exact continuous_pi (fun i => continuous_apply (rightIndex h i))

@[simp] theorem init_headBlock {n d : ℕ} (h : n < d) (x : Coordinates d) :
    Fin.init (headBlock (Nat.succ_le_of_lt h) x) = headBlock h.le x := by
  ext i
  rfl

@[simp] theorem last_headBlock {n d : ℕ} (h : n < d) (x : Coordinates d) :
    headBlock (Nat.succ_le_of_lt h) x (Fin.last n) = x ⟨n,h⟩ := rfl

private def scalarBlock : ℝ ≃L[ℝ] Coordinates 1 :=
  (ContinuousLinearEquiv.piUnique ℝ (fun _ : Fin 1 => ℝ)).symm

private theorem measurePreserving_scalarBlock :
    MeasurePreserving scalarBlock volume volume := by
  exact MeasurePreserving.symm scalarBlock.symm.toHomeomorph.toMeasurableEquiv
    (volume_preserving_piUnique (fun _ : Fin 1 => ℝ))

/-- Regroup a prefix, its next scalar coordinate, and the final remainder. -/
def tripleSplit {n d : ℕ} (h : n < d) :
    (Coordinates n × (ℝ × Coordinates (d - (n + 1)))) ≃L[ℝ] Coordinates d :=
  ((ContinuousLinearEquiv.refl ℝ (Coordinates n)).prodCongr
    ((scalarBlock.prodCongr (ContinuousLinearEquiv.refl ℝ _)).trans
      (append 1 (d - (n + 1))))).trans
    ((append n (1 + (d - (n + 1)))).trans
      (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin d => ℝ)
        (finCongr (by omega : n + (1 + (d - (n + 1))) = d))))

theorem measurePreserving_tripleSplit {n d : ℕ} (h : n < d) :
    MeasurePreserving (tripleSplit h) volume volume := by
  have hs := (measurePreserving_append 1 (d - (n + 1))).comp
    (measurePreserving_scalarBlock.prod (MeasurePreserving.id volume))
  exact ((volume_measurePreserving_piCongrLeft (fun _ : Fin d => ℝ)
    (finCongr (by omega : n + (1 + (d - (n + 1))) = d))).comp
      (measurePreserving_append n (1 + (d - (n + 1))))).comp
        ((MeasurePreserving.id volume).prod hs)

@[simp] theorem tripleSplit_left {n d : ℕ} (h : n < d)
    (x : Coordinates n) (t : ℝ) (z : Coordinates (d - (n+1))) (i : Fin n) :
    tripleSplit h (x,t,z) (leftIndex h.le i) = x i := by
  change Fin.append x (Fin.append (fun _ : Fin 1 => t) z)
    (Fin.cast (by omega : d = n + (1 + (d - (n+1)))) (leftIndex h.le i)) = x i
  have hi : Fin.cast (by omega : d = n + (1 + (d - (n+1)))) (leftIndex h.le i) =
      Fin.castAdd (1 + (d - (n+1))) i := by ext; rfl
  rw [hi, Fin.append_left]

@[simp] theorem tripleSplit_next {n d : ℕ} (h : n < d)
    (x : Coordinates n) (t : ℝ) (z : Coordinates (d - (n+1))) :
    tripleSplit h (x,t,z) ⟨n,h⟩ = t := by
  change Fin.append x (Fin.append (fun _ : Fin 1 => t) z)
    (Fin.cast (by omega : d = n + (1 + (d - (n+1)))) ⟨n,h⟩) = t
  have hi : Fin.cast (by omega : d = n + (1 + (d - (n+1)))) ⟨n,h⟩ =
      Fin.natAdd n (Fin.castAdd (d - (n+1)) (0 : Fin 1)) := by ext; rfl
  rw [hi, Fin.append_right, Fin.append_left]

/-- Taking the next prefix after installing a scalar is exactly `Fin.snoc`. -/
@[simp] theorem headBlock_tripleSplit {n d : ℕ} (h : n < d)
    (x : Coordinates n) (t : ℝ) (z : Coordinates (d - (n+1))) :
    headBlock (Nat.succ_le_of_lt h) (tripleSplit h (x,t,z)) = Fin.snoc x t := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Fin.snoc_last]
    change tripleSplit h (x,t,z) ⟨n,h⟩ = t
    exact tripleSplit_next h x t z
  · change tripleSplit h (x,t,z) (leftIndex h.le j) = _
    simp

/-- Membership of the reconstructed point gives the precise next-prefix invariant. -/
theorem snoc_mem_prefix_image {n d : ℕ} (h : n < d)
    {K : Set (Coordinates d)} {x : Coordinates n} {t : ℝ}
    {z : Coordinates (d - (n+1))}
    (hy : tripleSplit h (x,t,z) ∈ interior K) :
    Fin.snoc x t ∈ headBlock (Nat.succ_le_of_lt h) '' interior K := by
  exact ⟨tripleSplit h (x,t,z), hy, headBlock_tripleSplit h x t z⟩

end Problem358.FinitePrefix

end

noncomputable section
open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal

namespace Problem358.FinitePrefix

/-- The valid coordinate prefixes are the projections of the body's interior. -/
def prefixDomain {d n : ℕ} (K : Set (Coordinates d)) (h : n ≤ d) : Set (Coordinates n) :=
  headBlock h '' interior K

/-- The remaining section after a fixed coordinate prefix. -/
def prefixSection {d n : ℕ} (K : Set (Coordinates d)) (h : n ≤ d)
    (a : Coordinates n) : Set (Coordinates (d - n)) :=
  {b | join h (a,b) ∈ K}

lemma prefixDomain_iff {d n : ℕ} {K : Set (Coordinates d)} {h : n ≤ d}
    {a : Coordinates n} : a ∈ prefixDomain K h ↔
      ∃ b : Coordinates (d - n), join h (a,b) ∈ interior K := by
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨tailBlock h x, by simpa only [join_prefix_suffix] using hx⟩
  · rintro ⟨b,hb⟩
    exact ⟨join h (a,b),hb,prefix_join h a b⟩

lemma isCompact_prefixSection {d n : ℕ} {K : Set (Coordinates d)}
    (hK : IsCompact K) (h : n ≤ d) (a : Coordinates n) :
    IsCompact (prefixSection K h a) := by
  exact AffineSlice.isCompact_fiber
    ((join h).toHomeomorph.isCompact_preimage.mpr hK) a

lemma prefixSection_interior_nonempty {d n : ℕ} {K : Set (Coordinates d)}
    {h : n ≤ d} {a : Coordinates n} (ha : a ∈ prefixDomain K h) :
    (interior (prefixSection K h a)).Nonempty := by
  obtain ⟨b,hb⟩ := prefixDomain_iff.mp ha
  refine ⟨b, preimage_interior_subset_interior_preimage ?_ hb⟩
  exact (join h).continuous.comp (continuous_const.prodMk continuous_id)

lemma prefixSection_volume_pos {d n : ℕ} {K : Set (Coordinates d)}
    {h : n ≤ d} {a : Coordinates n} (ha : a ∈ prefixDomain K h) :
    0 < volume (prefixSection K h a) :=
  measure_pos_of_nonempty_interior volume (prefixSection_interior_nonempty ha)

lemma prefixSection_volumeReal_pos {d n : ℕ} {K : Set (Coordinates d)}
    (hK : IsCompact K) {h : n ≤ d} {a : Coordinates n}
    (ha : a ∈ prefixDomain K h) :
    0 < (volume (prefixSection K h a)).toReal :=
  ENNReal.toReal_pos (prefixSection_volume_pos ha).ne'
    (isCompact_prefixSection hK h a).measure_ne_top

lemma measurable_prefixSection_volume {d n : ℕ} {K : Set (Coordinates d)}
    (hK : MeasurableSet K) (h : n ≤ d) :
    Measurable (fun a => volume (prefixSection K h a)) := by
  exact measurable_measure_prodMk_left (hK.preimage (join h).continuous.measurable)

@[simp] lemma join_zero (d : ℕ) (a : Coordinates 0) (b : Coordinates d) :
    join (Nat.zero_le d) (a,b) = b := by
  ext i
  have hi : rightIndex (Nat.zero_le d) i = i := by
    ext
    simp [rightIndex]
  simpa only [hi] using join_right (Nat.zero_le d) a b i

lemma prefixDomain_zero {d : ℕ} {K : Set (Coordinates d)}
    (hK : (interior K).Nonempty) (a : Coordinates 0) :
    a ∈ prefixDomain K (Nat.zero_le d) := by
  obtain ⟨x,hx⟩ := hK
  exact ⟨x,hx,Subsingleton.elim _ _⟩

@[simp] lemma join_full {d : ℕ} (a : Coordinates d) (b : Coordinates (d-d)) :
    join (le_refl d) (a,b) = a := by
  ext i
  exact join_left (le_refl d) a b i

@[simp] lemma prefixDomain_full {d : ℕ} (K : Set (Coordinates d)) :
    prefixDomain K (le_refl d) = interior K := by
  change id '' interior K = interior K
  exact image_id _

lemma prefixSection_full {d : ℕ} {K : Set (Coordinates d)}
    {a : Coordinates d} (ha : a ∈ K) :
    prefixSection K (le_refl d) a = univ := by
  ext b
  simp [prefixSection,ha]

end Problem358.FinitePrefix

end

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem358.FinitePrefix

/-- The density of an actual bounded coordinate prefix is the volume of its
remaining-coordinate section. No convexity or positive-volume assumption is needed. -/
theorem map_headBlock_restrict {n d : ℕ} (h : n ≤ d)
    {K : Set (Coordinates d)} (hK : MeasurableSet K) :
    Measure.map (headBlock h) (volume.restrict K) =
      volume.withDensity (fun a : Coordinates n =>
        volume {b : Coordinates (d-n) | join h (a,b) ∈ K}) := by
  rw [← (measurePreserving_join_restrict h hK).map_eq]
  rw [Measure.map_map (continuous_headBlock h).measurable (join h).continuous.measurable]
  have he : headBlock h ∘ join h = Prod.fst := by
    funext p
    exact prefix_join h p.1 p.2
  rw [he]
  exact SectionMarginal.map_fst_restrict volume volume _
    (hK.preimage (join h).continuous.measurable)

/-- Actual normalized prefix laws have the common normalization by full body
volume, not by the individual section mass. -/
theorem map_headBlock_normalized_restrict {n d : ℕ} (h : n ≤ d)
    {K : Set (Coordinates d)} (hK : MeasurableSet K) :
    Measure.map (headBlock h) ((volume K)⁻¹ • volume.restrict K) =
      (volume K)⁻¹ • volume.withDensity (fun a : Coordinates n =>
        volume {b : Coordinates (d-n) | join h (a,b) ∈ K}) := by
  rw [Measure.map_smul _ (continuous_headBlock h).measurable.aemeasurable,
    map_headBlock_restrict h hK]

end Problem358.FinitePrefix

end

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace Problem358.FinitePrefix

/-- Taking a bounded coordinate prefix is an open map, including the empty
and the full prefix. -/
theorem isOpenMap_headBlock {n d : ℕ} (h : n ≤ d) :
    IsOpenMap (headBlock h) := by
  have hh := isOpenMap_fst.comp (join h).symm.toHomeomorph.isOpenMap
  change IsOpenMap (fun x : Coordinates d => ((join h).symm x).1) at hh
  simpa only [join_symm_apply] using hh

/-- The valid prefixes of a body form an open set. -/
theorem isOpen_prefixDomain {n d : ℕ} (K : Set (Coordinates d)) (h : n ≤ d) :
    IsOpen (prefixDomain K h) :=
  isOpenMap_headBlock h _ isOpen_interior

/-- Any law carried by the body's interior has its prefix law carried by the
valid prefix domain. No choice of conditional law on bad prefixes is relevant. -/
theorem ae_mem_prefixDomain_map {n d : ℕ} {K : Set (Coordinates d)}
    (h : n ≤ d) {μ : Measure (Coordinates d)}
    (hμ : ∀ᵐ x ∂μ, x ∈ interior K) :
    ∀ᵐ a ∂Measure.map (headBlock h) μ, a ∈ prefixDomain K h := by
  apply (ae_map_iff (continuous_headBlock h).measurable.aemeasurable
    (isOpen_prefixDomain K h).measurableSet).2
  filter_upwards [hμ] with x hx
  exact ⟨x, hx, rfl⟩

/-- Convex boundaries are null, so normalization of restricted volume does
not place any mass on the boundary. Degenerate volume is allowed. -/
theorem ae_mem_interior_normalized_restrict {d : ℕ} {K : Set (Coordinates d)}
    (hK : Convex ℝ K) :
    ∀ᵐ x ∂((volume K)⁻¹ • volume.restrict K), x ∈ interior K := by
  apply Measure.ae_smul_measure
  have heq : volume.restrict K = volume.restrict (interior K) :=
    Measure.restrict_congr_set
      (interior_ae_eq_of_null_frontier (hK.addHaar_frontier volume)).symm
  rw [heq]
  exact ae_restrict_mem measurableSet_interior

/-- The actual normalized prefix marginal is almost surely a valid interior
prefix. This is the support input for geometric conditional quantiles. -/
theorem ae_mem_prefixDomain_map_normalized_restrict {n d : ℕ}
    {K : Set (Coordinates d)} (hK : Convex ℝ K) (h : n ≤ d) :
    ∀ᵐ a ∂Measure.map (headBlock h) ((volume K)⁻¹ • volume.restrict K),
      a ∈ prefixDomain K h :=
  ae_mem_prefixDomain_map h (ae_mem_interior_normalized_restrict hK)

/-- The same support statement as literal vanishing of the bad-prefix mass. -/
theorem map_normalized_restrict_compl_prefixDomain {n d : ℕ}
    {K : Set (Coordinates d)} (hK : Convex ℝ K) (h : n ≤ d) :
    (Measure.map (headBlock h) ((volume K)⁻¹ • volume.restrict K))
      (prefixDomain K h)ᶜ = 0 := by
  exact ae_iff.mp (ae_mem_prefixDomain_map_normalized_restrict hK h)

/-- A sampler with the actual prefix marginal almost surely reaches the valid
prefix domain, independently of its values on parameter-null sets. -/
theorem ae_sample_mem_prefixDomain {A : Type*} [MeasurableSpace A]
    {n d : ℕ} {K : Set (Coordinates d)} (hK : Convex ℝ K) (h : n ≤ d)
    {η : Measure A} {F : A → Coordinates n} (hF : AEMeasurable F η)
    (hlaw : Measure.map F η =
      Measure.map (headBlock h) ((volume K)⁻¹ • volume.restrict K)) :
    ∀ᵐ a ∂η, F a ∈ prefixDomain K h := by
  apply ae_of_ae_map hF
  rw [hlaw]
  exact ae_mem_prefixDomain_map_normalized_restrict hK h

end Problem358.FinitePrefix

namespace Problem358.FinitePrefix

/-- Before any coordinates are chosen, the remaining section is the full body. -/
@[simp] theorem prefixSection_zero {d : ℕ} (K : Set (Coordinates d))
    (a : Coordinates 0) :
    prefixSection K (Nat.zero_le d) a = K := by
  ext b
  simp only [prefixSection, mem_ofPred_eq, join_zero]

/-- The initial density is the volume of the full body. -/
@[simp] theorem volume_prefixSection_zero {d : ℕ} (K : Set (Coordinates d))
    (a : Coordinates 0) :
    volume (prefixSection K (Nat.zero_le d) a) = volume K := by
  rw [prefixSection_zero]

/-- A zero-dimensional terminal section has volume one on the body. -/
theorem volume_prefixSection_full {d : ℕ} {K : Set (Coordinates d)}
    {a : Coordinates d} (ha : a ∈ K) :
    volume (prefixSection K (le_refl d) a) = 1 := by
  rw [prefixSection_full ha]
  simp [volume_pi]

/-- In particular the terminal density is one at every valid full prefix. -/
theorem volume_prefixSection_full_of_mem_domain {d : ℕ} {K : Set (Coordinates d)}
    {a : Coordinates d} (ha : a ∈ prefixDomain K (le_refl d)) :
    volume (prefixSection K (le_refl d) a) = 1 := by
  apply volume_prefixSection_full
  exact interior_subset (by simpa only [prefixDomain_full] using ha)

@[simp] theorem volumeReal_prefixSection_zero {d : ℕ} (K : Set (Coordinates d))
    (a : Coordinates 0) :
    (volume (prefixSection K (Nat.zero_le d) a)).toReal = (volume K).toReal := by
  rw [volume_prefixSection_zero]

/-- The terminal real density used by the telescoping derivative product. -/
theorem volumeReal_prefixSection_full {d : ℕ} {K : Set (Coordinates d)}
    {a : Coordinates d} (ha : a ∈ prefixDomain K (le_refl d)) :
    (volume (prefixSection K (le_refl d) a)).toReal = 1 := by
  rw [volume_prefixSection_full_of_mem_domain ha, ENNReal.toReal_one]

/-- A terminal section outside the body is empty. -/
theorem prefixSection_full_of_not_mem {d : ℕ} {K : Set (Coordinates d)}
    {a : Coordinates d} (ha : a ∉ K) :
    prefixSection K (le_refl d) a = ∅ := by
  ext b
  simp [prefixSection, ha]

/-- The full-prefix density is exactly the indicator of the body. -/
theorem volume_prefixSection_full_eq_indicator {d : ℕ} (K : Set (Coordinates d))
    (a : Coordinates d) :
    volume (prefixSection K (le_refl d) a) =
      K.indicator (fun _ => (1 : ℝ≥0∞)) a := by
  classical
  by_cases ha : a ∈ K
  · rw [volume_prefixSection_full ha, indicator_of_mem ha]
  · rw [prefixSection_full_of_not_mem ha, measure_empty, indicator_of_notMem ha]

/-- The normalized zero-prefix law is the unit-volume law on the empty product. -/
theorem normalized_initial_prefix_law {d : ℕ} {K : Set (Coordinates d)}
    (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤) :
    (volume K)⁻¹ • volume.withDensity
      (fun a : Coordinates 0 => volume (prefixSection K (Nat.zero_le d) a)) =
        (volume : Measure (Coordinates 0)) := by
  simp only [volume_prefixSection_zero, withDensity_const, smul_smul]
  rw [ENNReal.inv_mul_cancel hK0 hKtop, one_smul]

/-- The terminal unnormalized prefix law is precisely restricted volume. -/
theorem terminal_prefix_law {d : ℕ} {K : Set (Coordinates d)}
    (hK : MeasurableSet K) :
    volume.withDensity
      (fun a : Coordinates d => volume (prefixSection K (le_refl d) a)) =
        volume.restrict K := by
  simp only [volume_prefixSection_full_eq_indicator]
  exact withDensity_indicator_one hK

/-- Therefore the terminal normalized prefix law is the desired uniform law. -/
theorem normalized_terminal_prefix_law {d : ℕ} {K : Set (Coordinates d)}
    (hK : MeasurableSet K) :
    (volume K)⁻¹ • volume.withDensity
      (fun a : Coordinates d => volume (prefixSection K (le_refl d) a)) =
        (volume K)⁻¹ • volume.restrict K := by
  rw [terminal_prefix_law hK]

end Problem358.FinitePrefix

end

noncomputable section
open MeasureTheory

namespace Problem358.FinitePrefix

/-- The final coordinates of the three-block split are its final input block. -/
@[simp] theorem tripleSplit_right {n d : ℕ} (h : n < d)
    (x : Coordinates n) (t : ℝ) (z : Coordinates (d - (n + 1)))
    (i : Fin (d - (n + 1))) :
    tripleSplit h (x, t, z) (rightIndex (Nat.succ_le_of_lt h) i) = z i := by
  change Fin.append x (Fin.append (fun _ : Fin 1 => t) z)
    (Fin.cast (by omega : d = n + (1 + (d - (n+1))))
      (rightIndex (Nat.succ_le_of_lt h) i)) = z i
  have hi : Fin.cast (by omega : d = n + (1 + (d - (n+1))))
      (rightIndex (Nat.succ_le_of_lt h) i) =
      Fin.natAdd n (Fin.natAdd 1 i) := by
    ext
    simp only [rightIndex, Fin.val_cast, Fin.val_natAdd]
    omega
  rw [hi, Fin.append_right, Fin.append_right]

@[simp] theorem tailBlock_tripleSplit {n d : ℕ} (h : n < d)
    (x : Coordinates n) (t : ℝ) (z : Coordinates (d - (n + 1))) :
    tailBlock (Nat.succ_le_of_lt h) (tripleSplit h (x, t, z)) = z := by
  ext i
  exact tripleSplit_right h x t z i

/-- A three-block split is the next prefix split after installing its scalar coordinate. -/
theorem tripleSplit_eq_join_snoc {n d : ℕ} (h : n < d)
    (x : Coordinates n) (t : ℝ) (z : Coordinates (d - (n + 1))) :
    tripleSplit h (x, t, z) = join (Nat.succ_le_of_lt h) (Fin.snoc x t, z) := by
  simpa only [headBlock_tripleSplit, tailBlock_tripleSplit] using
    (join_prefix_suffix (Nat.succ_le_of_lt h) (tripleSplit h (x, t, z))).symm

/-- Regroup the next scalar coordinate with the remaining tail. -/
def tailJoin {n d : ℕ} (h : n < d) :
    (ℝ × Coordinates (d - (n + 1))) ≃L[ℝ] Coordinates (d - n) :=
  (((ContinuousLinearEquiv.piUnique ℝ (fun _ : Fin 1 => ℝ)).symm.prodCongr
    (ContinuousLinearEquiv.refl ℝ _)).trans (append 1 (d - (n + 1)))).trans
      (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin (d - n) => ℝ)
        (finCongr (by omega : 1 + (d - (n + 1)) = d - n)))

/-- Regrouping a scalar and a tail has unit Jacobian. -/
theorem measurePreserving_tailJoin {n d : ℕ} (h : n < d) :
    MeasurePreserving (tailJoin h) (volume.prod volume) volume := by
  have hs : MeasurePreserving
      (ContinuousLinearEquiv.piUnique ℝ (fun _ : Fin 1 => ℝ)).symm volume volume :=
    MeasurePreserving.symm
      (ContinuousLinearEquiv.piUnique ℝ (fun _ : Fin 1 => ℝ)).toHomeomorph.toMeasurableEquiv
      (volume_preserving_piUnique (fun _ : Fin 1 => ℝ))
  exact (volume_measurePreserving_piCongrLeft (fun _ : Fin (d - n) => ℝ)
    (finCongr (by omega : 1 + (d - (n + 1)) = d - n))).comp
      ((measurePreserving_append 1 (d - (n + 1))).comp
        (hs.prod (MeasurePreserving.id volume)))

/-- The same three-block split regrouped at the old prefix. -/
theorem tripleSplit_eq_join_tailJoin {n d : ℕ} (h : n < d)
    (x : Coordinates n) (t : ℝ) (z : Coordinates (d - (n + 1))) :
    tripleSplit h (x, t, z) = join h.le (x, tailJoin h (t, z)) := by
  ext i
  obtain ⟨i, rfl⟩ := (finCongr (Nat.add_sub_of_le h.le)).surjective i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · change tripleSplit h (x,t,z) (leftIndex h.le j) =
      join h.le (x,tailJoin h (t,z)) (leftIndex h.le j)
    simp
  · change tripleSplit h (x,t,z) (rightIndex h.le j) =
      join h.le (x,tailJoin h (t,z)) (rightIndex h.le j)
    rw [join_right]
    obtain ⟨j, rfl⟩ := (finCongr (by omega : 1 + (d - (n+1)) = d-n)).surjective j
    refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · have hk : k = (0 : Fin 1) := Subsingleton.elim _ _
      subst k
      have hi : rightIndex h.le
          (finCongr (by omega : 1 + (d - (n+1)) = d-n)
            (Fin.castAdd (d-(n+1)) (0 : Fin 1))) = ⟨n,h⟩ := by
        ext
        simp [rightIndex]
      rw [hi, tripleSplit_next]
      change t = Fin.append (fun _ : Fin 1 => t) z
        (Fin.cast (by omega : d-n = 1+(d-(n+1)))
          (Fin.cast (by omega : 1+(d-(n+1)) = d-n)
            (Fin.castAdd (d-(n+1)) (0 : Fin 1))))
      simp
    · have hi : rightIndex h.le
          (finCongr (by omega : 1 + (d - (n+1)) = d-n) (Fin.natAdd 1 k)) =
          rightIndex (Nat.succ_le_of_lt h) k := by
        ext
        simp only [rightIndex, finCongr, Equiv.coe_fn_mk, Fin.val_cast, Fin.val_natAdd]
        omega
      rw [hi, tripleSplit_right]
      change z k = Fin.append (fun _ : Fin 1 => t) z
        (Fin.cast (by omega : d-n = 1+(d-(n+1)))
          (Fin.cast (by omega : 1+(d-(n+1)) = d-n) (Fin.natAdd 1 k)))
      simp

/-- Fixing the old prefix gives exactly the old tail section, in regrouped coordinates. -/
theorem tripleSplit_parentSection {n d : ℕ} (h : n < d)
    (K : Set (Coordinates d)) (a : Coordinates n) :
    AffineSlice.fiber (tripleSplit h ⁻¹' K) a =
      tailJoin h ⁻¹' prefixSection K h.le a := by
  ext p
  change tripleSplit h (a,p.1,p.2) ∈ K ↔ join h.le (a,tailJoin h p) ∈ K
  rw [tripleSplit_eq_join_tailJoin]

/-- Parent section volume is unchanged by splitting off its next scalar coordinate. -/
theorem tripleSplit_parentSection_volume {n d : ℕ} (h : n < d)
    (K : Set (Coordinates d)) (a : Coordinates n) :
    (volume.prod volume) (AffineSlice.fiber (tripleSplit h ⁻¹' K) a) =
      volume (prefixSection K h.le a) := by
  rw [tripleSplit_parentSection]
  exact (measurePreserving_tailJoin h).measure_preimage_emb
    (tailJoin h).toHomeomorph.measurableEmbedding _

/-- Real-valued parent section volume, matching the conditional density denominator. -/
theorem tripleSplit_parentSection_volumeReal {n d : ℕ} (h : n < d)
    (K : Set (Coordinates d)) (a : Coordinates n) :
    (volume.prod volume).real (AffineSlice.fiber (tripleSplit h ⁻¹' K) a) =
      volume.real (prefixSection K h.le a) := by
  simp only [Measure.real, tripleSplit_parentSection_volume]

/-- The scalar child section is precisely the section at the extended prefix. -/
theorem tripleSplit_childSection {n d : ℕ} (h : n < d)
    (K : Set (Coordinates d)) (a : Coordinates n) (t : ℝ) :
    AffineSlice.fiber (AffineSlice.fiber (tripleSplit h ⁻¹' K) a) t =
      prefixSection K (Nat.succ_le_of_lt h) (Fin.snoc a t) := by
  ext z
  change tripleSplit h (a,t,z) ∈ K ↔ join (Nat.succ_le_of_lt h) (Fin.snoc a t,z) ∈ K
  rw [tripleSplit_eq_join_snoc]

/-- Child section volume, matching the conditional density numerator. -/
theorem tripleSplit_childSection_volume {n d : ℕ} (h : n < d)
    (K : Set (Coordinates d)) (a : Coordinates n) (t : ℝ) :
    volume (AffineSlice.fiber (AffineSlice.fiber (tripleSplit h ⁻¹' K) a) t) =
      volume (prefixSection K (Nat.succ_le_of_lt h) (Fin.snoc a t)) := by
  rw [tripleSplit_childSection]

/-- The real-valued child section identity used by inverse-CDF derivatives. -/
theorem tripleSplit_childSection_volumeReal {n d : ℕ} (h : n < d)
    (K : Set (Coordinates d)) (a : Coordinates n) (t : ℝ) :
    volume.real (AffineSlice.fiber (AffineSlice.fiber (tripleSplit h ⁻¹' K) a) t) =
      volume.real (prefixSection K (Nat.succ_le_of_lt h) (Fin.snoc a t)) := by
  rw [tripleSplit_childSection]

end Problem358.FinitePrefix

end

end OAI
