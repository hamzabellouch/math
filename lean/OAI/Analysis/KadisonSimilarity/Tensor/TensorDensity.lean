import OAI.Analysis.KadisonSimilarity.Tensor.TensorPairings

namespace OAI

/-!
# Passing finite-stage pairing identities to completed tensor words

Continuity and density extend the coefficient identity on a common matrix
stage to arbitrary letters. The final vanishing statement then uses actual
totality of elementary Hilbert tensors.
-/

noncomputable section
namespace KadisonSimilarity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem continuous_tensorWord (n : ℕ) : Continuous (tensorWord (E := E) (n := n)) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
      change Continuous (fun x : Fin (n + 1) → E => x 0 ⊗ₜ[ℂ] tensorWord (Fin.tail x))
      have htail : Continuous (fun x : Fin (n + 1) → E => Fin.tail x) :=
        continuous_pi (fun i => continuous_apply i.succ)
      have hf : Continuous (fun x : Fin (n + 1) → E => (x 0, tensorWord (Fin.tail x))) :=
        (continuous_apply 0).prodMk (ih.comp htail)
      have hg : Continuous (fun p : E × TensorWord E n => p.1 ⊗ₜ[ℂ] p.2) :=
        TensorProduct.continuous_tmul
      exact hg.comp hf

theorem continuous_completedTensorWord (n : ℕ) :
    Continuous (completedTensorWord (E := E) (n := n)) :=
  (UniformSpace.Completion.continuous_coe (α := TensorWord E n)).comp (continuous_tensorWord n)

omit [NormedAddCommGroup E] [InnerProductSpace ℂ E] in
/-- Finitely many letters in the union of nested stages lie in a common stage. -/
theorem exists_common_stage {ι : Type*} [Fintype ι]
    (S : ℕ → Set E) (hmono : Monotone S) (x : ι → E)
    (hx : ∀ i, x i ∈ ⋃ n, S n) : ∃ n, ∀ i, x i ∈ S n := by
  classical
  have hstage : ∀ i, ∃ n, x i ∈ S n := fun i => Set.mem_iUnion.mp (hx i)
  choose stage hstage using hstage
  refine ⟨Finset.univ.sup stage, fun i => ?_⟩
  exact hmono (Finset.le_sup (Finset.mem_univ i)) (hstage i)

omit [InnerProductSpace ℂ E] in
/-- Equality of continuous finite-letter functions on every common stage
extends to all letters. No coefficient identity is assumed outside the stages. -/
theorem continuous_eq_of_nested_stages {ι : Type*} [Fintype ι]
    (S : ℕ → Set E) (hmono : Monotone S) (hdense : Dense (⋃ n, S n))
    (F G : (ι → E) → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hstage : ∀ n, ∀ x : ι → E, (∀ i, x i ∈ S n) → F x = G x) : F = G := by
  let U : Set E := ⋃ n, S n
  have hd : DenseRange (Pi.map (fun _ : ι => ((↑) : U → E))) :=
    DenseRange.piMap (fun _ => hdense.denseRange_val)
  apply hd.equalizer hF hG
  funext x
  obtain ⟨n, hn⟩ := exists_common_stage S hmono (fun i => (x i : E)) (fun i => (x i).property)
  exact hstage n _ hn

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual pairing polynomial, with one bilinear factor per pair.
An injective rank function chooses a representative of each pair. -/
def pairingPolynomial (rank : ι → ℕ) (B : E →L[ℂ] E →L[ℂ] ℂ)
    (P : PerfectMatching ι) (v : ι → E) : ℂ :=
  ∏ i ∈ Finset.univ.filter (fun i => rank i < rank (P.1 i)), B (v i) (v (P.1 i))

omit [DecidableEq ι] in
theorem continuous_pairingPolynomial (rank : ι → ℕ) (B : E →L[ℂ] E →L[ℂ] ℂ)
    (P : PerfectMatching ι) : Continuous (pairingPolynomial rank B P) := by
  unfold pairingPolynomial
  fun_prop

omit [DecidableEq ι] in
/-- On a bilinearly orthonormal alphabet, the pairing polynomial is exactly
the equality-indicator kernel used by the Hilbert tensor tests. -/
theorem pairingPolynomial_labels {J : Type*} [DecidableEq J]
    (rank : ι → ℕ) (hrank : Function.Injective rank)
    (B : E →L[ℂ] E →L[ℂ] ℂ) (h : J → E)
    (hB : ∀ a b, B (h a) (h b) = if a = b then 1 else 0)
    (P : PerfectMatching ι) (labels : ι → J) :
    pairingPolynomial rank B P (fun i => h (labels i)) = pairingLabelKernel P labels := by
  classical
  unfold pairingPolynomial pairingLabelKernel
  simp only [hB]
  by_cases hall : ∀ i, labels i = labels (P.1 i)
  · have hright : (∏ i, if labels i = labels (P.1 i) then (1 : ℂ) else 0) = 1 :=
      Finset.prod_eq_one (fun i _ => ite_eq_left (hall i))
    rw [hright]
    exact Finset.prod_eq_one (fun i _ => ite_eq_left (hall i))
  · obtain ⟨i, hi⟩ := not_forall.mp hall
    have hzero : (∏ i, if labels i = labels (P.1 i) then (1 : ℂ) else 0) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)
    rw [hzero]
    have hneq : rank i ≠ rank (P.1 i) := fun he => P.2.2 i (hrank he).symm
    rcases lt_or_gt_of_ne hneq with hlt | hgt
    · exact Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hlt⟩)
        (ite_eq_right hi)
    · apply Finset.prod_eq_zero (i := P.1 i)
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa only [P.2.1 i] using hgt⟩
      · simpa only [P.2.1 i] using (ite_eq_right (Ne.symm hi) :
          (if labels (P.1 i) = labels i then (1 : ℂ) else 0) = 0)

variable {k l : ℕ}

/-- Coefficients with the test letters conjugated by the tracial involution. -/
def tracialWordCoefficient (Y : CompletedTensorWord E k →L[ℂ] CompletedTensorWord E l)
    (J : E → E) (v : Fin k ⊕ Fin l → E) : ℂ :=
  inner ℂ (completedTensorWord (fun j => J (v (Sum.inr j))))
    (Y (completedTensorWord (fun i => v (Sum.inl i))))

theorem continuous_tracialWordCoefficient
    (Y : CompletedTensorWord E k →L[ℂ] CompletedTensorWord E l)
    (J : E → E) (hJ : Continuous J) : Continuous (tracialWordCoefficient Y J) := by
  unfold tracialWordCoefficient
  apply Continuous.inner
  · apply (continuous_completedTensorWord l).comp
    exact continuous_pi (fun j => hJ.comp (continuous_apply (Sum.inr j)))
  · apply Y.continuous.comp
    apply (continuous_completedTensorWord k).comp
    exact continuous_pi (fun i => continuous_apply (Sum.inl i))

/-- The finite-stage coefficient formula extends by density, with no bounded
pairing operator presupposed. Each individual pairing polynomial is continuous
as a function of its finitely many letters. -/
theorem tracial_pairing_identity_of_stages
    (Y : CompletedTensorWord E k →L[ℂ] CompletedTensorWord E l)
    (J : E → E) (hJ : Continuous J)
    (B : E →L[ℂ] E →L[ℂ] ℂ) (rank : Fin k ⊕ Fin l → ℕ)
    (c : PerfectMatching (Fin k ⊕ Fin l) → ℂ)
    (S : ℕ → Set E) (hmono : Monotone S) (hdense : Dense (⋃ n, S n))
    (hstage : ∀ n, ∀ v : Fin k ⊕ Fin l → E, (∀ i, v i ∈ S n) →
      tracialWordCoefficient Y J v = ∑ P, c P * pairingPolynomial rank B P v) :
    ∀ v : Fin k ⊕ Fin l → E,
      tracialWordCoefficient Y J v = ∑ P, c P * pairingPolynomial rank B P v := by
  classical
  have heq := continuous_eq_of_nested_stages S hmono hdense
    (tracialWordCoefficient Y J) (fun v => ∑ P, c P * pairingPolynomial rank B P v)
    (continuous_tracialWordCoefficient Y J hJ)
    (continuous_finsetSum _ (fun P _ => continuous_const.mul
      (continuous_pairingPolynomial rank B P))) hstage
  exact congrFun heq

/-- Restricting the extended stage identity to self-adjoint orthonormal
letters gives the precise input for the completed tensor label sums. -/
theorem labelPairingExpansion_of_tracial_identity
    (Y : CompletedTensorWord E k →L[ℂ] CompletedTensorWord E l)
    (J : E → E) (B : E →L[ℂ] E →L[ℂ] ℂ)
    (rank : Fin k ⊕ Fin l → ℕ) (hrank : Function.Injective rank)
    (c : PerfectMatching (Fin k ⊕ Fin l) → ℂ) (h : ℕ → E)
    (hJ : ∀ n, J (h n) = h n)
    (hB : ∀ a b, B (h a) (h b) = if a = b then 1 else 0)
    (hfull : ∀ v, tracialWordCoefficient Y J v =
      ∑ P, c P * pairingPolynomial rank B P v) : LabelPairingExpansion Y h c := by
  intro s t
  have heq := hfull (Sum.elim (fun i => h (s i)) (fun j => h (t j)))
  simp only [tracialWordCoefficient, Sum.elim_inl, Sum.elim_inr, hJ] at heq
  rw [heq]
  apply Finset.sum_congr rfl
  intro P _
  congr 1
  rw [show Sum.elim (fun i => h (s i)) (fun j => h (t j)) =
    (fun i => h (Sum.elim s t i)) from funext (fun i => by cases i <;> rfl)]
  exact pairingPolynomial_labels rank hrank B h hB P (Sum.elim s t)

/-- In unequal degrees, the stage formula, density, and orthonormal label
tests force the actual completed tensor operator to vanish. -/
theorem tensorOperator_eq_zero_of_tracial_stages
    (Y : CompletedTensorWord E k →L[ℂ] CompletedTensorWord E l)
    (J : E → E) (hJ : Continuous J) (hJJ : Function.Involutive J)
    (B : E →L[ℂ] E →L[ℂ] ℂ)
    (rank : Fin k ⊕ Fin l → ℕ) (hrank : Function.Injective rank)
    (c : PerfectMatching (Fin k ⊕ Fin l) → ℂ)
    (h : ℕ → E) (hh : Orthonormal ℂ h) (hfix : ∀ n, J (h n) = h n)
    (hB : ∀ a b, B (h a) (h b) = if a = b then 1 else 0)
    (S : ℕ → Set E) (hmono : Monotone S) (hdense : Dense (⋃ n, S n))
    (hstage : ∀ n, ∀ v : Fin k ⊕ Fin l → E, (∀ i, v i ∈ S n) →
      tracialWordCoefficient Y J v = ∑ P, c P * pairingPolynomial rank B P v)
    (hkl : k ≠ l) : Y = 0 := by
  have hfull := tracial_pairing_identity_of_stages Y J hJ B rank c S hmono hdense hstage
  have hlab := labelPairingExpansion_of_tracial_identity Y J B rank hrank c h hfix hB hfull
  have hc := pairing_coefficients_zero_of_degrees_ne Y h hh c hlab hkl
  apply tensorOperator_eq_zero_of_word_coefficients
  intro x y
  have heq := hfull (Sum.elim x (J ∘ y))
  have hJJ' (z : E) : J (J z) = z := hJJ z
  simpa only [tracialWordCoefficient, Sum.elim_inl, Sum.elim_inr, Function.comp_apply,
    hJJ', hc, Pi.zero_apply, zero_mul, Finset.sum_const_zero] using heq

end KadisonSimilarity

end

end OAI
