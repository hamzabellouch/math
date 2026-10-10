import OAI.Probability.Ising.EdwardsSokal
import OAI.Probability.Ising.TwoSpin

namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing

/-- Extension by the actual common pins, in contrast to the deleted zero-field
comparison graph. -/
def pinExtension {n : ℕ} (F : Finset (Fin n)) (τ : Spins n)
    (σ : KeptVertex F → Bool) : Spins n :=
  fun v => if hv : v ∈ F then τ v else σ ⟨v, hv⟩

lemma pinExtension_agrees {n : ℕ} (F : Finset (Fin n)) (τ : Spins n)
    (σ : KeptVertex F → Bool) : AgreesOn F (pinExtension F τ σ) τ := by
  intro v hv
  simp only [pinExtension, dite_eq_left hv]

lemma pinExtension_apply {n : ℕ} (F : Finset (Fin n)) (τ : Spins n)
    (σ : KeptVertex F → Bool) (v : KeptVertex F) :
    pinExtension F τ σ v = σ v := by
  simp only [pinExtension, dite_eq_right v.property]

/-- Fixing sites is exactly elimination of their spin variables. This finite
bijection does not replace their interactions by deletion. -/
def pinExtensionEquiv {n : ℕ} (F : Finset (Fin n)) (τ : Spins n) :
    (KeptVertex F → Bool) ≃ {σ : Spins n // AgreesOn F σ τ} where
  toFun σ := ⟨pinExtension F τ σ, pinExtension_agrees F τ σ⟩
  invFun σ v := σ.val v
  left_inv σ := by ext v; exact pinExtension_apply F τ σ v
  right_inv σ := by
    apply Subtype.ext
    funext v
    by_cases hv : v ∈ F
    · simpa only [pinExtension, dite_eq_left hv] using (σ.property v hv).symm
    · simp only [pinExtension, dite_eq_right hv]

lemma constrainedSum_delete_variables {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (F : Finset (Fin n)) (τ : Spins n) (P : Spins n → Prop) :
    constrainedSum G h (fun σ => AgreesOn F σ τ ∧ P σ) =
      ∑ σ : KeptVertex F → Bool,
        if P (pinExtension F τ σ) then weight G h (pinExtension F τ σ) else 0 := by
  classical
  calc
    _ = ∑ σ : Spins n, if AgreesOn F σ τ then
        (if P σ then weight G h σ else 0) else 0 := by
      unfold constrainedSum
      apply Finset.sum_congr rfl
      intro σ _
      by_cases hF : AgreesOn F σ τ <;> by_cases hP : P σ <;> simp [hF, hP]
    _ = ∑ σ ∈ Finset.univ.filter (fun σ : Spins n => AgreesOn F σ τ),
        if P σ then weight G h σ else 0 := (Finset.sum_filter _ _).symm
    _ = ∑ σ : {σ : Spins n // AgreesOn F σ τ},
        if P σ.val then weight G h σ.val else 0 :=
      Finset.sum_subtype _ (by intro σ; simp only [Finset.mem_filter,
        Finset.mem_univ, true_and]) _
    _ = _ := (Equiv.sum_comp (pinExtensionEquiv F τ)
      (fun σ => if P σ.val then weight G h σ.val else 0)).symm

/-- A finite two-spin table extracted from a not necessarily normalized spin weight. -/
noncomputable def pairTable {V : Type*} [Fintype V] [DecidableEq V] (W : (V → Bool) → ℝ)
    (i j : V) (s t : Bool) : ℝ :=
  ∑ σ, if σ i = s ∧ σ j = t then W σ else 0

lemma pairTable_sum {V : Type*} [Fintype V] [DecidableEq V] (W : (V → Bool) → ℝ)
    (i j : V) (f : Bool → Bool → ℝ) :
    (∑ s, ∑ t, pairTable W i j s t * f s t) =
      ∑ σ, W σ * f (σ i) (σ j) := by
  classical
  simp only [pairTable, Finset.sum_mul]
  calc
    _ = ∑ s, ∑ σ, ∑ t, (if σ i = s ∧ σ j = t then W σ else 0) * f s t := by
      apply Finset.sum_congr rfl
      intro s _
      exact Finset.sum_comm
    _ = ∑ σ, ∑ s, ∑ t, (if σ i = s ∧ σ j = t then W σ else 0) * f s t :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro σ _
      cases σ i <;> cases σ j <;> simp

lemma pairTable_expectation {V : Type*} [Fintype V] [DecidableEq V] (W : (V → Bool) → ℝ)
    (i j : V) (f : Bool → Bool → ℝ) :
    tableExpectation (pairTable W i j) f =
      (∑ σ, W σ * f (σ i) (σ j)) / ∑ σ, W σ := by
  unfold tableExpectation
  rw [pairTable_sum]
  have H := pairTable_sum W i j (fun _ _ => 1)
  simp only [mul_one] at H
  rw [H]

/-- Global spin reversal is a permutation of configurations. -/
def spinFlipEquiv (V : Type*) : (V → Bool) ≃ (V → Bool) where
  toFun σ v := !σ v
  invFun σ v := !σ v
  left_inv σ := by ext v; simp only [Bool.not_not]
  right_inv σ := by ext v; simp only [Bool.not_not]

lemma pairTable_flip {V : Type*} [Fintype V] [DecidableEq V] (W : (V → Bool) → ℝ)
    (hW : ∀ σ, W (fun v => !σ v) = W σ) (i j : V) (s t : Bool) :
    pairTable W i j (!s) (!t) = pairTable W i j s t := by
  classical
  unfold pairTable
  rw [← Equiv.sum_comp (spinFlipEquiv V)
    (fun σ => if σ i = !s ∧ σ j = !t then W σ else 0)]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [spinFlipEquiv, Equiv.coe_fn_mk, Bool.not_inj_iff, hW]

lemma symmetricTable_balanced (w : Bool → Bool → ℝ)
    (hw : ∀ s t, w (!s) (!t) = w s t) : balancedTable w = w := by
  have h₁ := hw true true
  have h₂ := hw true false
  simp only [Bool.not_true, Bool.not_false] at h₁ h₂
  have hf : tableFieldLeft w = 0 ∧ tableFieldRight w = 0 := by
    constructor <;> dsimp only [tableFieldLeft, tableFieldRight] <;> rw [h₁, h₂] <;> ring
  funext s t
  simp only [balancedTable, hf.1, hf.2, neg_zero, zero_mul, sub_zero,
    Real.exp_zero, mul_one]

lemma symmetricTable_correlation (w : Bool → Bool → ℝ) (hw : ∀ s t, 0 < w s t)
    (hsym : ∀ s t, w (!s) (!t) = w s t) :
    tableExpectation w (fun s t => spin s * spin t) = Real.tanh (tableCoupling w) := by
  have H := balancedTable_correlation w hw
  rw [symmetricTable_balanced w hsym] at H
  exact H

lemma respects_spinFlip {V : Type*} (S : Setoid V) (σ : V → Bool) :
    Respects S (fun v => !σ v) ↔ Respects S σ := by
  unfold Respects
  simp only [Bool.not_inj_iff]

lemma deletedEnergy_spinFlip {n m : ℕ} (G : FiniteGraph n m)
    (F : Finset (Fin n)) (σ : KeptVertex F → Bool) :
    deletedEnergy G F (fun v => !σ v) = deletedEnergy G F σ := by
  unfold deletedEnergy
  apply Finset.sum_congr rfl
  intro e he
  obtain ⟨hl, hr⟩ := (Finset.mem_filter.mp he).2
  have hleft (σ : KeptVertex F → Bool) :
      extendKept F σ (G.left e) = σ ⟨G.left e, hl⟩ := by
    exact extendKept_apply F σ ⟨G.left e, hl⟩
  have hright (σ : KeptVertex F → Bool) :
      extendKept F σ (G.right e) = σ ⟨G.right e, hr⟩ := by
    exact extendKept_apply F σ ⟨G.right e, hr⟩
  rw [hleft, hright, hleft, hright, spin_not, spin_not]
  ring

lemma contractedZeroWeight_spinFlip {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (σ : KeptVertex F → Bool) :
    contractedZeroWeight G I J F (fun v => !σ v) = contractedZeroWeight G I J F σ := by
  unfold contractedZeroWeight
  rw [respects_spinFlip, deletedEnergy_spinFlip]

lemma contractedZeroWeight_nonneg {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (σ : KeptVertex F → Bool) :
    0 ≤ contractedZeroWeight G I J F σ := by
  unfold contractedZeroWeight
  split_ifs
  · exact (Real.exp_pos _).le
  · exact le_rfl

lemma contractedZero_pairTable_pos {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (hIJ : Disjoint I J)
    (i j : KeptVertex F) (hi : i.val ∈ I) (hj : j.val ∈ J) (s t : Bool) :
    0 < pairTable (contractedZeroWeight G I J F) i j s t := by
  classical
  let σ : KeptVertex F → Bool := fun v => if v.val ∈ I then s else t
  have hjI : j.val ∉ I := fun hjI => Finset.disjoint_left.mp hIJ hjI hj
  have hσi : σ i = s := by simp only [σ, ite_eq_left hi]
  have hσj : σ j = t := by simp only [σ, ite_eq_right hjI]
  have hresp : Respects (comparisonSetoid G I J F ∅) σ := by
    intro x y hxy
    have hI := comparison_empty_preserves_I G I J F hIJ x y hxy
    simp only [σ, hI]
  unfold pairTable
  apply Finset.sum_pos'
  · intro τ _
    split_ifs
    · exact contractedZeroWeight_nonneg G I J F τ
    · exact le_rfl
  · refine ⟨σ, Finset.mem_univ _, ?_⟩
    rw [ite_eq_left ⟨hσi, hσj⟩, contractedZeroWeight, ite_eq_left hresp]
    exact Real.exp_pos _

/-- The FK terminal connection probability is the hyperbolic tangent of the zero-field effective coupling. -/
lemma qZero_eq_tanh_effective {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (hIJ : Disjoint I J)
    (i j : KeptVertex F) (hi : i.val ∈ I) (hj : j.val ∈ J) :
    qZero G I J F i j =
      Real.tanh (tableCoupling (pairTable (contractedZeroWeight G I J F) i j)) := by
  rw [← symmetricTable_correlation _ (contractedZero_pairTable_pos G I J F hIJ i j hi hj)
    (pairTable_flip _ (contractedZeroWeight_spinFlip G I J F) i j)]
  rw [pairTable_expectation, qZero_eq_zero_field_correlation]
  simp only [mul_assoc]

lemma artanh_qZero_eq_effective {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (hIJ : Disjoint I J)
    (i j : KeptVertex F) (hi : i.val ∈ I) (hj : j.val ∈ J) :
    Real.artanh (qZero G I J F i j) =
      tableCoupling (pairTable (contractedZeroWeight G I J F) i j) := by
  rw [qZero_eq_tanh_effective G I J F hIJ i j hi hj, Real.artanh_tanh]

end BufferedIsing

end OAI
