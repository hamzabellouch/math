import OAI.NumberTheory.DirichletL.Moments.AddedZero

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentAddedZeroUniform
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentGaussEnergy CenteredMomentAddedZero CenteredMomentRectangle
local notation "O" => ActualEisensteinCubic.O

theorem uniform_tuple_energy (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, n ≤ N →
      ∀ (S : Finset (Fin (n + 2) → Ideal O))
      (hS : ∀ v ∈ S, Supported (tupleProduct v))
      (β : (Fin (n + 2) → Ideal O) → ℂ) (B Y T : ℝ),
      0 ≤ B → 1 ≤ Y → 0 < T →
      (∀ v ∈ S, ‖β v‖ ≤ B) →
      (∀ v ∈ S, (Ideal.absNorm (tupleProduct v) : ℝ) ≤ Y) →
      ‖normalizedIdealAddedZero (tupleColumns S) (tupleColumns_supported S hS)
          (tupleCoefficient S β) T‖ ^ 2 ≤ C * B ^ 2 * T⁻¹ * Y ^ (4 / 3 + ε : ℝ) := by
  let D (n : ℕ) := (tuple_added_zero_energy (n + 2) (by omega) ε hε).choose
  have hD (n : ℕ) : 0 < D n := (tuple_added_zero_energy (n + 2) (by omega) ε hε).choose_spec.1
  have hne : (Finset.range (N + 1)).Nonempty := ⟨0, by simp⟩
  let C := 1 + (Finset.range (N + 1)).sup' hne D
  have hzero : D 0 ≤ (Finset.range (N + 1)).sup' hne D :=
    Finset.le_sup' D (by simp : 0 ∈ Finset.range (N + 1))
  refine ⟨C, by dsimp [C]; linarith [hD 0], ?_⟩
  intro n hn S hS β B Y T hB hY hT hβ hN
  have hDn : D n ≤ C := by
    have h := Finset.le_sup' D (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))
    dsimp only [C]
    linarith
  have he := (tuple_added_zero_energy (n + 2) (by omega) ε hε).choose_spec.2
    S hS β B Y T hB hY hT hβ hN
  apply he.trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith) _)
  apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hT.le)
  exact mul_le_mul_of_nonneg_right hDn (sq_nonneg _)

abbrev Tuple (ι : Type*) := (ι ⊕ Fin 2) → Ideal O

def coordinateEquiv {ι : Type*} {n : ℕ} (e : ι ≃ Fin n) :
    ι ⊕ Fin 2 ≃ Fin (n + 2) := (e.sumCongr (Equiv.refl (Fin 2))).trans finSumFinEquiv

def tupleEquiv {ι : Type*} {n : ℕ} (e : ι ≃ Fin n) :
    Tuple ι ≃ (Fin (n + 2) → Ideal O) :=
  (coordinateEquiv e).arrowCongr (Equiv.refl (Ideal O))

def finiteTupleProduct {ι : Type*} [Fintype ι] (v : Tuple ι) : Ideal O := ∏ i, v i

lemma tupleEquiv_slot {ι : Type*} {n : ℕ} (e : ι ≃ Fin n) (v : Tuple ι) (i : ι) :
    tupleEquiv e v ((e i).castAdd 2) = v (Sum.inl i) := by
  change v ((coordinateEquiv e).symm _) = _
  have h : coordinateEquiv e (Sum.inl i) = (e i).castAdd 2 := by
    simp only [coordinateEquiv, Equiv.trans_apply, Equiv.sumCongr_apply,
      Sum.map_inl, finSumFinEquiv_apply_left]
  rw [← h, Equiv.symm_apply_apply]

lemma tupleEquiv_plain {ι : Type*} {n : ℕ} (e : ι ≃ Fin n) (v : Tuple ι) (j : Fin 2) :
    tupleEquiv e v (j.natAdd n) = v (Sum.inr j) := by
  change v ((coordinateEquiv e).symm _) = _
  have h : coordinateEquiv e (Sum.inr j) = j.natAdd n := by
    simp only [coordinateEquiv, Equiv.trans_apply, Equiv.sumCongr_apply,
      Sum.map_inr, finSumFinEquiv_apply_right, Equiv.refl_apply]
  rw [← h, Equiv.symm_apply_apply]

theorem tupleProduct_reindex {ι : Type*} [Fintype ι] {n : ℕ}
    (e : ι ≃ Fin n) (v : Tuple ι) :
    tupleProduct (tupleEquiv e v) = finiteTupleProduct v := by
  exact (coordinateEquiv e).symm.prod_comp v

def originalFiniteCoefficient {ι : Type*} [Fintype ι]
    (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O) (v : Tuple ι) : ℂ :=
  (∏ j, ν j (v (Sum.inl j)) * Wslot j ((Ideal.absNorm (v (Sum.inl j)) : ℝ) / P j)) *
    idealWeight c χ R t (finiteTupleProduct v) *
    idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (b₁ * v (Sum.inr 0)) (b₂ * v (Sum.inr 1)) *
    (if s ∣ finiteTupleProduct v then 1 else 0)

theorem originalCoefficient_reindex {ι : Type*} [Fintype ι] {n : ℕ}
    (e : ι ≃ Fin n) (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (t : ℝ) (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O) (v : Tuple ι) :
    originalCoefficient n c χ R t (fun j => ν (e.symm j)) (fun j => Wslot (e.symm j))
      (fun j => P (e.symm j)) W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s (tupleEquiv e v) =
    originalFiniteCoefficient c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s v := by
  have hslot (j : Fin n) : tupleEquiv e v (j.castAdd 2) = v (Sum.inl (e.symm j)) := by
    simpa only [Equiv.apply_symm_apply] using tupleEquiv_slot e v (e.symm j)
  have hp₀ : (⟨n, by omega⟩ : Fin (n + 2)) = (0 : Fin 2).natAdd n := by ext; simp
  have hp₁ : (⟨n + 1, by omega⟩ : Fin (n + 2)) = (1 : Fin 2).natAdd n := by ext; simp
  simp only [originalCoefficient, originalFiniteCoefficient, tupleProduct_reindex,
    hslot, hp₀, hp₁, tupleEquiv_plain]
  rw [e.symm.prod_comp (fun j => ν j (v (Sum.inl j)) * Wslot j ((Ideal.absNorm (v (Sum.inl j)) : ℝ) / P j))]

lemma reindex_supported {ι : Type*} [Fintype ι] {n : ℕ} (e : ι ≃ Fin n)
    (S : Finset (Tuple ι)) (hS : ∀ v ∈ S, Supported (finiteTupleProduct v)) :
    ∀ w ∈ S.image (tupleEquiv e), Supported (tupleProduct w) := by
  intro w hw
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
  rw [tupleProduct_reindex]
  exact hS v hv

def finiteGaussZero {ι : Type*} [Fintype ι] (S : Finset (Tuple ι))
    (hS : ∀ v ∈ S, Supported (finiteTupleProduct v)) (β : Tuple ι → ℂ) : ℂ :=
  gaussPolynomial (Finset.univ : Finset S)
    (fun v => primaryGenerator (finiteTupleProduct v.val))
    (fun v => (supported_span_primaryGenerator_iff (finiteTupleProduct v.val)).mpr (hS v.val v.property))
    (fun v => β v.val) 0

theorem finiteGaussZero_reindex {ι : Type*} [Fintype ι] {n : ℕ}
    (e : ι ≃ Fin n) (S : Finset (Tuple ι))
    (hS : ∀ v ∈ S, Supported (finiteTupleProduct v)) (β : Tuple ι → ℂ) :
    finiteGaussZero S hS β =
      idealAddedZero (tupleColumns (S.image (tupleEquiv e)))
        (tupleColumns_supported _ (reindex_supported e S hS))
        (tupleCoefficient (S.image (tupleEquiv e)) (fun w => β ((tupleEquiv e).symm w))) := by
  rw [← actual_tuple_gauss_eq_columns (S.image (tupleEquiv e)) (reindex_supported e S hS)
    (fun w => β ((tupleEquiv e).symm w))]
  unfold finiteGaussZero gaussPolynomial
  apply Finset.sum_bij (fun v _ => (⟨tupleEquiv e v.val,
    Finset.mem_image.mpr ⟨v.val, v.property, rfl⟩⟩ : S.image (tupleEquiv e)))
  · intros; exact Finset.mem_univ _
  · intro v hv w hw he
    apply Subtype.ext
    exact (tupleEquiv e).injective (congrArg Subtype.val he)
  · intro w hw
    obtain ⟨v, hv, he⟩ := Finset.mem_image.mp w.property
    exact ⟨⟨v, hv⟩, Finset.mem_univ _, Subtype.ext he⟩
  · intro v hv
    simp only [Equiv.symm_apply_apply, tupleProduct_reindex]

theorem uniform_finite_energy (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [Fintype ι], Fintype.card ι ≤ N →
      ∀ (S : Finset (Tuple ι)) (hS : ∀ v ∈ S, Supported (finiteTupleProduct v))
      (β : Tuple ι → ℂ) (B Y T : ℝ), 0 ≤ B → 1 ≤ Y → 0 < T →
      (∀ v ∈ S, ‖β v‖ ≤ B) →
      (∀ v ∈ S, (Ideal.absNorm (finiteTupleProduct v) : ℝ) ≤ Y) →
      ‖(Real.sqrt T : ℂ)⁻¹ * finiteGaussZero S hS β‖ ^ 2 ≤
        C * B ^ 2 * T⁻¹ * Y ^ (4 / 3 + ε : ℝ) := by
  obtain ⟨C, hC, he⟩ := uniform_tuple_energy N ε hε
  refine ⟨C, hC, ?_⟩
  intro ι inst hn S hS β B Y T hB hY hT hβ hN
  let e := Fintype.equivFin ι
  rw [finiteGaussZero_reindex e S hS β]
  apply he (Fintype.card ι) hn _ (reindex_supported e S hS) _ B Y T hB hY hT
  · intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    simpa only [Equiv.symm_apply_apply] using hβ v hv
  · intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    simpa only [tupleProduct_reindex] using hN v hv

theorem originalFiniteCoefficient_norm_le {ι : Type*} [Fintype ι]
    (c : O) (hc : c ≠ 0) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O)
    (Bslot : ι → ℝ) (B₁ B₂ : ℝ) (hBslot : ∀ j, 0 ≤ Bslot j)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hν : ∀ j I, ‖ν j I‖ ≤ 1) (hWslot : ∀ j x, ‖Wslot j x‖ ≤ Bslot j)
    (hW₁ : ∀ x, ‖W₁ x‖ ≤ B₁) (hW₂ : ∀ x, ‖W₂ x‖ ≤ B₂)
    (v : Tuple ι) (hv : finiteTupleProduct v ≠ 0) :
    ‖originalFiniteCoefficient c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s v‖ ≤
      (∏ j, Bslot j) * (2 * B₁ * B₂) := by
  let e := Fintype.equivFin ι
  rw [← originalCoefficient_reindex e]
  have he := originalCoefficient_norm_le (Fintype.card ι) c hc χ R t
    (fun j => ν (e.symm j)) (fun j => Wslot (e.symm j)) (fun j => P (e.symm j))
    W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s (fun j => Bslot (e.symm j)) B₁ B₂
    (fun j => hBslot _) hB₁ hB₂ (fun j I => hν _ I) (fun j x => hWslot _ x) hW₁ hW₂
    (tupleEquiv e v) (by rwa [tupleProduct_reindex])
  simpa only [e.symm.prod_comp Bslot] using he

theorem original_subset_energy {α : Type*} (A : Finset α) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (J : Finset α), J ⊆ A →
      ∀ (c : O), c ≠ 0 → ∀ (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
      (R : Ideal O) (t : ℝ) (ν : α → Ideal O → ℂ) (Wslot : α → ℝ → ℂ) (P : α → ℝ)
      (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O)
      (Bslot : α → ℝ) (B₁ B₂ : ℝ),
      (∀ j ∈ J, 0 ≤ Bslot j) → 0 ≤ B₁ → 0 ≤ B₂ →
      (∀ j ∈ J, ∀ I, ‖ν j I‖ ≤ 1) → (∀ j ∈ J, ∀ x, ‖Wslot j x‖ ≤ Bslot j) →
      (∀ x, ‖W₁ x‖ ≤ B₁) → (∀ x, ‖W₂ x‖ ≤ B₂) →
      ∀ (S : Finset (Tuple J)) (hS : ∀ v ∈ S, Supported (finiteTupleProduct v))
      (Y T : ℝ), 1 ≤ Y → 0 < T →
      (∀ v ∈ S, (Ideal.absNorm (finiteTupleProduct v) : ℝ) ≤ Y) →
      ‖(Real.sqrt T : ℂ)⁻¹ * finiteGaussZero S hS
        (originalFiniteCoefficient c χ R t (fun j : J => ν j.val)
          (fun j : J => Wslot j.val) (fun j : J => P j.val)
          W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s)‖ ^ 2 ≤
        C * ((∏ j ∈ J, Bslot j) * (2 * B₁ * B₂)) ^ 2 * T⁻¹ * Y ^ (4 / 3 + ε : ℝ) := by
  obtain ⟨C, hC, he⟩ := uniform_finite_energy A.card ε hε
  refine ⟨C, hC, ?_⟩
  intro J hJA c hc χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s Bslot B₁ B₂
    hBslot hB₁ hB₂ hν hWslot hW₁ hW₂ S hS Y T hY hT hN
  have hcard : Fintype.card J ≤ A.card := by
    simpa only [Fintype.card_coe] using Finset.card_le_card hJA
  apply he hcard S hS _ _ Y T
    (mul_nonneg (Finset.prod_nonneg hBslot) (by positivity)) hY hT _ hN
  intro v hv
  have hb := originalFiniteCoefficient_norm_le c hc χ R t
    (fun j : J => ν j.val) (fun j : J => Wslot j.val) (fun j : J => P j.val)
    W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s (fun j : J => Bslot j.val) B₁ B₂
    (fun j => hBslot j.val j.property) hB₁ hB₂
    (fun j I => hν j.val j.property I) (fun j x => hWslot j.val j.property x)
    hW₁ hW₂ v (hS v hv).1
  simpa only [Finset.prod_coe_sort J Bslot] using hb

theorem empty_finiteTupleProduct {α : Type*} (v : Tuple (∅ : Finset α)) :
    finiteTupleProduct v = v (Sum.inr 0) * v (Sum.inr 1) := by
  simp only [finiteTupleProduct, Fintype.prod_sum_type, Fin.prod_univ_two]
  have he : (∏ j : (∅ : Finset α), v (Sum.inl j)) = 1 := by
    apply Finset.prod_eq_one
    intro j hj
    exact False.elim (Finset.notMem_empty j.val j.property)
  rw [he, one_mul]

lemma reindexCoefficient_mask {ι : Type*} [Fintype ι] {n : ℕ}
    (e : ι ≃ Fin n) (S : Finset (Tuple ι)) (β : Tuple ι → ℂ) (s : Ideal O)
    (hmask : ∀ v ∈ S, ¬s ∣ finiteTupleProduct v → β v = 0)
    (I : Ideal O) (hs : ¬s ∣ I) :
    tupleCoefficient (S.image (tupleEquiv e)) (fun w => β ((tupleEquiv e).symm w)) I = 0 := by
  apply Finset.sum_eq_zero
  intro w hw
  obtain ⟨hwS, hwI⟩ := Finset.mem_filter.mp hw
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hwS
  simp only [Equiv.symm_apply_apply]
  apply hmask v hv
  rwa [← tupleProduct_reindex e v, hwI]

lemma reindexColumns_norm {ι : Type*} [Fintype ι] {n : ℕ}
    (e : ι ≃ Fin n) (S : Finset (Tuple ι)) (Y : ℝ)
    (hN : ∀ v ∈ S, (Ideal.absNorm (finiteTupleProduct v) : ℝ) ≤ Y) :
    ∀ I ∈ tupleColumns (S.image (tupleEquiv e)), (Ideal.absNorm I : ℝ) ≤ Y := by
  intro I hI
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hI
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
  simpa only [tupleProduct_reindex] using hN v hv

theorem finiteGaussZero_nonzero_mask_norm {ι : Type*} [Fintype ι]
    (S : Finset (Tuple ι)) (hS : ∀ v ∈ S, Supported (finiteTupleProduct v))
    (β : Tuple ι → ℂ) (s : Ideal O) (hs : Squarefree s)
    (hmask : ∀ v ∈ S, ¬s ∣ finiteTupleProduct v → β v = 0)
    (Y : ℝ) (hN : ∀ v ∈ S, (Ideal.absNorm (finiteTupleProduct v) : ℝ) ≤ Y)
    (hz : finiteGaussZero S hS β ≠ 0) : (Ideal.absNorm s : ℝ) ^ 6 ≤ Y := by
  let e := Fintype.equivFin ι
  rw [finiteGaussZero_reindex e S hS β] at hz
  exact idealAddedZero_nonzero_mask_norm _ _ _ s hs
    (fun I _ => reindexCoefficient_mask e S β s hmask I) Y (reindexColumns_norm e S Y hN) hz

theorem finiteGaussZero_nonzero_mask_dyad {ι : Type*} [Fintype ι]
    (S : Finset (Tuple ι)) (hS : ∀ v ∈ S, Supported (finiteTupleProduct v))
    (β : Tuple ι → ℂ) (s : Ideal O) (hs : Squarefree s)
    (hmask : ∀ v ∈ S, ¬s ∣ finiteTupleProduct v → β v = 0)
    (Z a s₀ θ : ℝ) (hZ : 1 < Z) (hNs : Z ^ s₀ ≤ (Ideal.absNorm s : ℝ))
    (hN : ∀ v ∈ S, (Ideal.absNorm (finiteTupleProduct v) : ℝ) ≤ Z ^ (a + θ))
    (hz : finiteGaussZero S hS β ≠ 0) : -θ ≤ a ∧ s₀ ≤ (a + θ) / 6 := by
  let e := Fintype.equivFin ι
  rw [finiteGaussZero_reindex e S hS β] at hz
  exact idealAddedZero_nonzero_mask_dyad _ _ _ s hs
    (fun I _ => reindexCoefficient_mask e S β s hmask I) Z a s₀ θ hZ hNs
    (reindexColumns_norm e S (Z ^ (a + θ)) hN) hz

lemma originalFiniteCoefficient_mask {ι : Type*} [Fintype ι]
    (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O)
    (v : Tuple ι) (hs : ¬s ∣ finiteTupleProduct v) :
    originalFiniteCoefficient c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s v = 0 := by
  simp only [originalFiniteCoefficient, hs, ite_false, mul_zero]

theorem uniform_finite_source_energy (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [Fintype ι], Fintype.card ι ≤ N →
      ∀ (S : Finset (Tuple ι)) (hS : ∀ v ∈ S, Supported (finiteTupleProduct v))
      (β : Tuple ι → ℂ) (s : Ideal O), Squarefree s →
      (∀ v ∈ S, ¬s ∣ finiteTupleProduct v → β v = 0) →
      ∀ (B Z a s₀ θ : ℝ), 0 ≤ B → 1 < Z → Z ^ s₀ ≤ (Ideal.absNorm s : ℝ) →
      (∀ v ∈ S, ‖β v‖ ≤ B) →
      (∀ v ∈ S, (Ideal.absNorm (finiteTupleProduct v) : ℝ) ≤ Z ^ (a + θ)) →
      ‖(Real.sqrt (Z ^ a) : ℂ)⁻¹ * finiteGaussZero S hS β‖ ^ 2 ≤
        C * B ^ 2 * Z ^ (a - s₀ + 2 * θ + ε * (a + θ)) := by
  obtain ⟨C, hC, he⟩ := uniform_finite_energy N ε hε
  refine ⟨C, hC, ?_⟩
  intro ι inst hn S hS β s hs hmask B Z a s₀ θ hB hZ hNs hβ hN
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  by_cases hz : finiteGaussZero S hS β = 0
  · rw [hz, mul_zero, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    exact mul_nonneg (mul_nonneg hC.le (sq_nonneg _)) (Real.rpow_nonneg hZ0.le _)
  · obtain ⟨ha, hss⟩ := finiteGaussZero_nonzero_mask_dyad S hS β s hs hmask Z a s₀ θ hZ hNs hN hz
    have hY : 1 ≤ Z ^ (a + θ) := Real.one_le_rpow hZ.le (by linarith)
    have hb := he hn S hS β B (Z ^ (a + θ)) (Z ^ a) hB hY
      (Real.rpow_pos_of_pos hZ0 _) hβ hN
    have hp : (Z ^ a)⁻¹ * (Z ^ (a + θ)) ^ (4 / 3 + ε : ℝ) =
        Z ^ (a / 3 + 4 * θ / 3 + ε * (a + θ)) := by
      rw [← Real.rpow_neg hZ0.le, ← Real.rpow_mul hZ0.le, ← Real.rpow_add hZ0]
      congr 1
      ring
    calc
      _ ≤ C * B ^ 2 * (Z ^ a)⁻¹ * (Z ^ (a + θ)) ^ (4 / 3 + ε : ℝ) := hb
      _ = C * B ^ 2 * Z ^ (a / 3 + 4 * θ / 3 + ε * (a + θ)) := by rw [mul_assoc, hp]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hZ.le
          (by linarith [added_zero_exponent a s₀ θ ha hss]))
        (mul_nonneg hC.le (sq_nonneg _))

theorem original_subset_source_energy {α : Type*} (A : Finset α) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (J : Finset α), J ⊆ A →
      ∀ (c : O), c ≠ 0 → ∀ (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
      (R : Ideal O) (t : ℝ) (ν : α → Ideal O → ℂ) (Wslot : α → ℝ → ℂ) (P : α → ℝ)
      (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O), Squarefree s →
      ∀ (Bslot : α → ℝ) (B₁ B₂ : ℝ),
      (∀ j ∈ J, 0 ≤ Bslot j) → 0 ≤ B₁ → 0 ≤ B₂ →
      (∀ j ∈ J, ∀ I, ‖ν j I‖ ≤ 1) → (∀ j ∈ J, ∀ x, ‖Wslot j x‖ ≤ Bslot j) →
      (∀ x, ‖W₁ x‖ ≤ B₁) → (∀ x, ‖W₂ x‖ ≤ B₂) →
      ∀ (S : Finset (Tuple J)) (hS : ∀ v ∈ S, Supported (finiteTupleProduct v))
      (Z a s₀ θ : ℝ), 1 < Z → Z ^ s₀ ≤ (Ideal.absNorm s : ℝ) →
      (∀ v ∈ S, (Ideal.absNorm (finiteTupleProduct v) : ℝ) ≤ Z ^ (a + θ)) →
      ‖(Real.sqrt (Z ^ a) : ℂ)⁻¹ * finiteGaussZero S hS
        (originalFiniteCoefficient c χ R t (fun j : J => ν j.val)
          (fun j : J => Wslot j.val) (fun j : J => P j.val)
          W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s)‖ ^ 2 ≤
        C * ((∏ j ∈ J, Bslot j) * (2 * B₁ * B₂)) ^ 2 *
          Z ^ (a - s₀ + 2 * θ + ε * (a + θ)) := by
  obtain ⟨C, hC, he⟩ := uniform_finite_source_energy A.card ε hε
  refine ⟨C, hC, ?_⟩
  intro J hJA c hc χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s hs Bslot B₁ B₂
    hBslot hB₁ hB₂ hν hWslot hW₁ hW₂ S hS Z a s₀ θ hZ hNs hN
  have hcard : Fintype.card J ≤ A.card := by
    simpa only [Fintype.card_coe] using Finset.card_le_card hJA
  apply he hcard S hS _ s hs
    (fun v _ => originalFiniteCoefficient_mask c χ R t
      (fun j : J => ν j.val) (fun j : J => Wslot j.val) (fun j : J => P j.val)
      W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s v)
    _ Z a s₀ θ (mul_nonneg (Finset.prod_nonneg hBslot) (by positivity)) hZ hNs _ hN
  intro v hv
  have hb := originalFiniteCoefficient_norm_le c hc χ R t
    (fun j : J => ν j.val) (fun j : J => Wslot j.val) (fun j : J => P j.val)
    W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s (fun j : J => Bslot j.val) B₁ B₂
    (fun j => hBslot j.val j.property) hB₁ hB₂
    (fun j I => hν j.val j.property I) (fun j x => hWslot j.val j.property x)
    hW₁ hW₂ v (hS v hv).1
  simpa only [Finset.prod_coe_sort J Bslot] using hb

end SevenEighths.CenteredMomentAddedZeroUniform

end

end OAI
