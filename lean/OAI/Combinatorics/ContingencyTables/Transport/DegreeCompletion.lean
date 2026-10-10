import OAI.Combinatorics.ContingencyTables.Transport.RecursiveSignedTransport
import OAI.Combinatorics.ContingencyTables.Transport.LaminarSignature

namespace OAI

/-!
# Positive completion of a single valid degree

A fixed-degree weight is extended by the constant weight one on every
other degree. All off-degree signatures are proved, and all coefficient
sums at the original degree are unchanged. This lets the existing general
nonnegative-derivative theorem retain contracted coordinates without
assuming positivity or signatures of the original weight at other degrees.
-/

namespace ContingencyTables.DegreeCompletion

open scoped BigOperators Classical Topology
open CommonBasesFPRAS BinaryContraction RecursiveSignedTransport

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ]

noncomputable def completeDegree (f : Set Γ → ℝ) (k : ℕ) (A : Set Γ) : ℝ :=
  if A.ncard = k then f A else 1

omit [Fintype Γ] [DecidableEq Γ] in
lemma completeDegree_positive (f : Set Γ → ℝ) (k : ℕ) (hf : DegreePositive f k) :
    ∀ A, 0 < completeDegree f k A := by
  intro A
  unfold completeDegree
  split_ifs with h
  · exact hf A h
  · norm_num

lemma constant_face_signature (A : Set Γ) :
    CommonBasesFPRAS.OnePositive (faceHessian (fun _ : Set Γ => (1 : ℝ)) A).toBilin' := by
  let K := twoLevelKernel (fun i : {i // i ∉ A} => i) (fun _ => false)
    (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))
  have heq : faceHessian (fun _ : Set Γ => (1 : ℝ)) A = K := by
    ext i j
    simp [faceHessian, K, twoLevelKernel]
  rw [heq]
  apply (signature_iff _ (matrix_bilin_symm _ (by intro i j; simp [K, twoLevelKernel, eq_comm]))).mp
  exact twoLevelKernel_onePositive _ _ _ _ (by intro i; norm_num)
    (by intro i; norm_num) (by intro i; norm_num)

lemma completeDegree_face_signature (f : Set Γ → ℝ) (k : ℕ)
    (hsig : AdditionProperty f k) (A : Set Γ) :
    CommonBasesFPRAS.OnePositive (faceHessian (completeDegree f k) A).toBilin' := by
  by_cases hA : A.ncard + 2 = k
  · have heq : faceHessian (completeDegree f k) A = faceHessian f A := by
      ext i j
      by_cases hij : i = j
      · simp [faceHessian, hij]
      simp only [faceHessian, hij, ite_false, completeDegree]
      rw [ite_eq_left ((ncard_union_pair A i j hij).trans hA)]
    rw [heq]
    exact hsig A hA
  · have heq : faceHessian (completeDegree f k) A = faceHessian (fun _ => (1 : ℝ)) A := by
      ext i j
      by_cases hij : i = j
      · simp [faceHessian, hij]
      simp only [faceHessian, hij, ite_false, completeDegree]
      rw [ite_eq_right (by rw [ncard_union_pair A i j hij]; exact hA)]
    rw [heq]
    exact constant_face_signature A

/-- Positive directions are handled by the existing cubic spectral theorem.
The cardinality cutoff of a repeated derivative is established at each step. -/
lemma positive_derivatives_signature (f : Set Γ → ℝ) (hf : ∀ A, 0 < f A)
    (hsig : ∀ A, CommonBasesFPRAS.OnePositive (faceHessian f A).toBilin')
    (ds : List (Γ → ℝ)) (hds : ∀ a ∈ ds, ∀ i, 0 < a i) :
    FullPositive (coeffDerivs ds f) ds.length ∧
      ∀ A, CommonBasesFPRAS.OnePositive (faceHessian (coeffDerivs ds f) A).toBilin' := by
  induction ds with
  | nil =>
    refine ⟨⟨fun A _ => hf A, ?_⟩, hsig⟩
    intro A hA
    have hcard : A.ncard ≤ Fintype.card Γ := by simpa using Set.ncard_le_card A
    simp only [List.length_nil, Nat.add_zero] at hA
    omega
  | cons a ds ih =>
    have ha := hds a List.mem_cons_self
    obtain ⟨hp, hs⟩ := ih (fun b hb => hds b (List.mem_cons_of_mem _ hb))
    exact ⟨hp.deriv a ha, derivative_face_signature hp hs a ha⟩

/-- The zero coordinates of a direction are reached by an actual positive
perturbation and the proved closedness of the quadratic signature. -/
lemma nonnegative_derivatives_signature (f : Set Γ → ℝ) (hf : ∀ A, 0 < f A)
    (hsig : ∀ A, CommonBasesFPRAS.OnePositive (faceHessian f A).toBilin')
    (ds : List (Γ → ℝ)) (hds : ∀ a ∈ ds, ∀ i, 0 ≤ a i) (A : Set Γ) :
    CommonBasesFPRAS.OnePositive (faceHessian (coeffDerivs ds f) A).toBilin' := by
  let F : ℝ → Matrix {i // i ∉ A} {i // i ∉ A} ℝ := fun t =>
    faceHessian (coeffDerivs (ds.map (fun a i => a i + t)) f) A
  have hzero : F 0 = faceHessian (coeffDerivs ds f) A := by simp [F]
  rw [← hzero]
  let l := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  have : l.NeBot := nhdsWithin_Ioi_neBot (le_refl (0 : ℝ))
  apply onePositive_of_tendsto (l := l) F (F 0)
  · intro i j
    have hc : Continuous (fun t => F t i j) := by
      dsimp [F, faceHessian]
      by_cases hij : i = j
      · simp only [ite_eq_left hij]; exact continuous_const
      · simp only [ite_eq_right hij]
        exact continuous_coeffDerivs_perturb ds f _
    exact hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  · exact fun t => faceHessian_symm _ A
  · have hpos : ∀ᶠ t in l, 0 < t := self_mem_nhdsWithin
    filter_upwards [hpos] with t ht
    apply (positive_derivatives_signature f hf hsig _ _).2 A
    intro b hb i
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
    exact add_pos_of_nonneg_of_pos (hds a ha i) ht

/-- All retained-coordinate slot signatures of the completion are proved.
The original input is only the single valid-degree addition property. -/
theorem completeDegree_hasSlotSignature (f : Set Γ → ℝ) (k : ℕ)
    (hf : DegreePositive f k) (hsig : AdditionProperty f k) :
    HasSlotSignature (completeDegree f k) := by
  intro ps A
  apply nonnegative_derivatives_signature _ (completeDegree_positive f k hf)
    (completeDegree_face_signature f k hsig) _ _ A
  intro a ha i
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp ha
  exact slotDirection_nonneg _ i

/-- Every nonzero derivative term adds precisely one new element; no
fresh-pair or disjointness assumption is needed for this congruence. -/
lemma coeffDerivs_degree_congr (ds : List (Γ → ℝ)) (f g : Set Γ → ℝ) (k : ℕ)
    (heq : ∀ S, S.ncard = k → f S = g S) (A : Set Γ)
    (hdegree : A.ncard + ds.length = k) : coeffDerivs ds f A = coeffDerivs ds g A := by
  induction ds generalizing A with
  | nil => exact heq A (by simpa using hdegree)
  | cons a ds ih =>
    change coeffDeriv a (coeffDerivs ds f) A = coeffDeriv a (coeffDerivs ds g) A
    unfold coeffDeriv
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ A
    · simp only [ite_eq_left hi]
    · simp only [ite_eq_right hi]
      congr 1
      apply ih (insert i A)
      rw [ncard_insert_eq A i hi]
      simp only [List.length_cons] at hdegree
      omega

lemma slotTotal_completeDegree (ps : List (Γ × Γ)) (f : Set Γ → ℝ) (k : ℕ)
    (A : Set Γ) (hdegree : A.ncard + ps.length = k) :
    slotTotal ps (completeDegree f k) A = slotTotal ps f A := by
  apply coeffDerivs_degree_congr _ _ _ k
  · intro S hS
    simp [completeDegree, hS]
  · simpa only [List.length_map] using hdegree

/-- The full retained-coordinate matrix at its valid degree inherits the
signature, including coordinates of previously contracted pairs. -/
theorem slot_face_signature_degree (ps : List (Γ × Γ)) (f : Set Γ → ℝ) (k : ℕ)
    (hf : DegreePositive f k) (hsig : AdditionProperty f k) (A : Set Γ)
    (hdegree : A.ncard + ps.length + 2 = k) :
    CommonBasesFPRAS.OnePositive (faceHessian (slotTotal ps f) A).toBilin' := by
  have heq : faceHessian (slotTotal ps (completeDegree f k)) A =
      faceHessian (slotTotal ps f) A := by
    ext i j
    by_cases hij : i = j
    · simp [faceHessian, hij]
    simp only [faceHessian, hij, ite_false]
    apply slotTotal_completeDegree
    rw [ncard_union_pair A i j hij]
    omega
  rw [← heq]
  exact completeDegree_hasSlotSignature f k hf hsig ps A

lemma slotDefect_completeDegree (ps : List (Γ × Γ)) (f : Set Γ → ℝ) (k : ℕ)
    (A : Set Γ) (hdegree : A.ncard + ps.length = k) (hps : SlotsFresh ps A)
    (p r : Γ × Γ) (hp : p ∈ ps) (hr : r ∈ ps) (hpr : p ≠ r) :
    slotDefect ps (completeDegree f k) A p r = slotDefect ps f A p r := by
  have hperm := slots_perm_two hp hr hpr
  have hh := (SlotsFresh.perm hperm A).mp hps
  have hrA : r.1 ∉ A := fun h => hh.2.2.2.2.1 (Or.inr (Or.inr h))
  have hrB : r.2 ∉ A := fun h => hh.2.2.2.2.2.1 (Or.inr (Or.inr h))
  unfold slotDefect
  apply slotTotal_completeDegree
  rw [ncard_insert_eq _ r.1 (by simp only [Set.mem_insert_iff, not_or]; exact ⟨hh.2.2.2.1, hrA⟩),
    ncard_insert_eq A r.2 hrB]
  have hlen := hperm.length_eq
  simp only [List.length_cons] at hlen
  omega

/-- Actual two-pair masses satisfy the determinant bound on their valid
cardinality layer; completion disappears from the conclusion. -/
theorem slotDefect_pair_bound_degree (ps : List (Γ × Γ)) (f : Set Γ → ℝ) (k : ℕ)
    (hf : DegreePositive f k) (hsig : AdditionProperty f k)
    (A : Set Γ) (hdegree : A.ncard + ps.length = k) (hps : SlotsFresh ps A)
    (p r : Γ × Γ) (hp : p ∈ ps) (hr : r ∈ ps) (hpr : p ≠ r) :
    4 * slotDefect ps f A p r * slotDefect ps f A r p ≤ (slotTotal ps f A)^2 := by
  have h := slotDefect_pair_bound ps (completeDegree f k) (completeDegree_positive f k hf)
    (completeDegree_hasSlotSignature f k hf hsig) A hps p r hp hr hpr
  rwa [slotDefect_completeDegree ps f k A hdegree hps p r hp hr hpr,
    slotDefect_completeDegree ps f k A hdegree hps r p hr hp hpr.symm,
    slotTotal_completeDegree ps f k A hdegree] at h

/-- Actual three-pair masses satisfy the cross-entry bound, obtained from
full cubic contraction while retaining the contracted pair coordinates. -/
theorem slotDefect_triple_bound_degree (ps : List (Γ × Γ)) (f : Set Γ → ℝ) (k : ℕ)
    (hf : DegreePositive f k) (hsig : AdditionProperty f k)
    (A : Set Γ) (hdegree : A.ncard + ps.length = k) (hps : SlotsFresh ps A)
    (p r t : Γ × Γ) (hp : p ∈ ps) (hr : r ∈ ps) (ht : t ∈ ps)
    (hpr : p ≠ r) (hrt : r ≠ t) (hpt : p ≠ t) :
    slotDefect ps f A p r * slotDefect ps f A r t ≤
      slotTotal ps f A * slotDefect ps f A p t := by
  have h := slotDefect_triple_bound ps (completeDegree f k) (completeDegree_positive f k hf)
    (completeDegree_hasSlotSignature f k hf hsig) A hps p r t hp hr ht hpr hrt hpt
  rwa [slotDefect_completeDegree ps f k A hdegree hps p r hp hr hpr,
    slotDefect_completeDegree ps f k A hdegree hps r t hr ht hrt,
    slotDefect_completeDegree ps f k A hdegree hps p t hp ht hpt,
    slotTotal_completeDegree ps f k A hdegree] at h

end ContingencyTables.DegreeCompletion

end OAI
