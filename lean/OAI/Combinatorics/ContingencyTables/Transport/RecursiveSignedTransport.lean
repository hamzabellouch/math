import OAI.Combinatorics.ContingencyTables.Machines.BinaryContraction

namespace OAI

/-!
# Recursive signed transport for fixed-degree weights

The recursive transport construction of the bounded-table counting paper
uses positivity at the valid subset degree. Signatures after pair summation
follow from that degree's addition property and full cubic contraction.
-/

namespace ContingencyTables.RecursiveSignedTransport

open scoped BigOperators Classical Matrix
open CommonBasesFPRAS BinaryContraction

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ]

lemma slotTotal_degree_positive (ps : List (Γ × Γ)) (f : Set Γ → ℝ) (k : ℕ)
    (hf : DegreePositive f k) (A : Set Γ)
    (hdegree : A.ncard + ps.length = k) (hslots : SlotsFresh ps A) :
    0 < slotTotal ps f A := by
  induction ps generalizing A with
  | nil => exact hf A (by simpa using hdegree)
  | cons p ps ih =>
    obtain ⟨hp, ha, hb, ht⟩ := hslots
    rw [slotTotal_cons p ps f A hp ha hb]
    apply add_pos
    · apply ih (insert p.1 A)
      · rw [ncard_insert_eq A p.1 ha]
        simp only [List.length_cons] at hdegree
        omega
      · exact ht.mono (by intro x hx; rcases hx with rfl | hx <;> simp_all)
    · apply ih (insert p.2 A)
      · rw [ncard_insert_eq A p.2 hb]
        simp only [List.length_cons] at hdegree
        omega
      · exact ht.mono (Set.subset_insert _ _)

omit [DecidableEq Γ] in
lemma embedded_union_card {κ : Type*} (A : Set Γ) (e : κ → Γ)
    (he : Function.Injective e) (heA : ∀ i, e i ∉ A) (U : Set κ) :
    (A ∪ e '' U).ncard = A.ncard + U.ncard := by
  have hd : Disjoint A (e '' U) := by
    apply Set.disjoint_left.mpr
    rintro x hx ⟨i, _, rfl⟩
    exact heA i hx
  rw [Set.ncard_union_eq hd, Set.ncard_image_of_injective U he]

/-- The exact signature needed by the recursion, obtained after summing
fresh pairs only on the valid residual degree. -/
theorem slot_pair_signature (ps : List (Γ × Γ)) :
    ∀ {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
      (f : Set Γ → ℝ) (k : ℕ) (A : Set Γ) (e : κ → Γ),
      DegreePositive f k → AdditionProperty f k →
      A.ncard + ps.length + 2 = k → Function.Injective e →
      (∀ i, e i ∉ A) → SlotsFresh ps (A ∪ Set.range e) →
      CommonBasesFPRAS.OnePositive (pairMatrix (slotTotal ps f) A e).toBilin' := by
  induction ps with
  | nil =>
    intro κ _ _ _ f k A e hf hsig hdegree he heA _
    let e' : κ → {i // i ∉ A} := fun i => ⟨e i, heA i⟩
    have heq : pairMatrix f A e = (faceHessian f A).submatrix e' e' := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [pairMatrix, faceHessian]
      have hne : e' i ≠ e' j := fun h => hij (he (congrArg Subtype.val h))
      simp only [pairMatrix, hij, ite_false, Matrix.submatrix_apply, faceHessian, hne]
      congr 1
      ext x
      simp [e']
    change CommonBasesFPRAS.OnePositive (pairMatrix f A e).toBilin'
    rw [heq]
    exact onePositive_submatrix _ (hsig A (by simpa using hdegree)) e'
  | cons p ps ih =>
    intro κ _ _ _ f k A e hf hsig hdegree he heA hslots
    obtain ⟨hp, ha, hb, ht⟩ := hslots
    let J := κ ⊕ Bool
    let E : J → Γ := splitEmbedding e p.1 p.2
    have hE : Function.Injective E :=
      splitEmbedding_injective e p.1 p.2 he hp
        (fun h => ha (Or.inr h)) (fun h => hb (Or.inr h))
    have hEA : ∀ i, E i ∉ A := by
      intro i
      cases i with
      | inl i => exact heA i
      | inr b => cases b <;> simp only [E, splitEmbedding] <;> tauto
    have htail : SlotsFresh ps (A ∪ Set.range E) := by
      apply ht.mono
      rintro x (hx | ⟨i, rfl⟩)
      · exact Or.inr (Or.inr (Or.inl hx))
      · cases i with
        | inl i => exact Or.inr (Or.inr (Or.inr ⟨i, rfl⟩))
        | inr b => cases b <;> simp [E, splitEmbedding]
    let g : Set J → ℝ := fun U => slotTotal ps f (A ∪ E '' U)
    have hJ : 3 ≤ Fintype.card J := by
      have hκ : 0 < Fintype.card κ := Fintype.card_pos
      simp only [J, Fintype.card_sum, Fintype.card_bool]
      omega
    have hgpos : DegreePositive g 3 := by
      intro U hU
      apply slotTotal_degree_positive ps f k hf
      · rw [embedded_union_card A E hE hEA U, hU]
        simp only [List.length_cons] at hdegree
        omega
      · exact htail.mono (Set.union_subset_union_right A (Set.image_subset_range _ _))
    have hgsig : AdditionProperty g 3 := by
      intro U hU
      let C : Set Γ := A ∪ E '' U
      let v : {i : J // i ∉ U} → Γ := fun i => E i.val
      have hUcard : U.ncard = 1 := by omega
      have hCcard : C.ncard = A.ncard + 1 := by
        rw [embedded_union_card A E hE hEA U, hUcard]
      have hcardU := card_outside U
      have : Nonempty {i : J // i ∉ U} := Fintype.card_pos_iff.mp (by omega)
      have hv : Function.Injective v := fun i j h => Subtype.ext (hE h)
      have hvC : ∀ i, v i ∉ C := by
        intro i
        rintro (hiA | ⟨j, hj, hji⟩)
        · exact hEA i.val hiA
        · exact i.property ((hE hji) ▸ hj)
      have hcontexts : C ∪ Set.range v ⊆ A ∪ Set.range E := by
        rintro x ((hx | ⟨i, _, rfl⟩) | ⟨i, rfl⟩)
        · exact Or.inl hx
        · exact Or.inr ⟨i, rfl⟩
        · exact Or.inr ⟨i.val, rfl⟩
      have hsigU := ih f k C v hf hsig (by
        rw [hCcard]
        simp only [List.length_cons] at hdegree
        omega) hv hvC (htail.mono hcontexts)
      have heq : faceHessian g U = pairMatrix (slotTotal ps f) C v := by
        ext i j
        by_cases hij : i = j
        · subst j
          simp [faceHessian, pairMatrix]
        simp only [faceHessian, pairMatrix, hij, ite_false, g]
        congr 1
        ext x
        simp [C, v]
      rw [heq]
      exact hsigU
    let pa : {i : J // i ∉ (∅ : Set J)} := ⟨Sum.inr false, Set.notMem_empty _⟩
    let pb : {i : J // i ∉ (∅ : Set J)} := ⟨Sum.inr true, Set.notMem_empty _⟩
    have hfull := fixedDegree_pair_contraction g 3 hJ hgpos hgsig ∅ (by simp) pa pb
    have hsymm : ∀ i j,
        (faceCubic g ∅ pa + faceCubic g ∅ pb) i j =
          (faceCubic g ∅ pa + faceCubic g ∅ pb) j i := by
      intro i j
      simp only [Matrix.add_apply, faceCubic_symm]
    have hfull' : CommonBasesFPRAS.OnePositive
        (faceCubic g ∅ pa + faceCubic g ∅ pb).toBilin' := by
      apply (signature_iff _ (matrix_bilin_symm _ hsymm)).mp
      convert hfull using 1
      congr 2
      exact Subsingleton.elim _ _
    let old : κ → {i : J // i ∉ (∅ : Set J)} :=
      fun i => ⟨Sum.inl i, Set.notMem_empty _⟩
    have heq : (faceCubic g ∅ pa + faceCubic g ∅ pb).submatrix old old =
        pairMatrix (slotTotal (p :: ps) f) A e := by
      rw [pairMatrix_parent ps f A e p hp ha hb]
      ext i j
      by_cases hij : i = j
      · subst j
        simp [Matrix.submatrix_apply, faceCubic, pairMatrix]
      have hij' : old i ≠ old j := by
        intro h
        exact hij (Sum.inl_injective (congrArg Subtype.val h))
      simp [Matrix.submatrix_apply, Matrix.add_apply, faceCubic, pairMatrix, hij,
        hij', pa, pb, old, g, E, splitEmbedding, Set.image_insert_eq, Set.insert_comm, add_comm]
    rw [← heq]
    exact onePositive_submatrix _ hfull' old


lemma slot_split_signature_degree {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (f : Set Γ → ℝ) (k : ℕ) (hf : DegreePositive f k) (hsig : AdditionProperty f k)
    (ps : List (Γ × Γ)) (A : Set Γ) (e : κ → Γ) (p : Γ × Γ)
    (he : Function.Injective e) (heA : ∀ i, e i ∉ A)
    (hslots : SlotsFresh (p :: ps) (A ∪ Set.range e))
    (hdegree : A.ncard + ps.length + 2 = k) :
    CommonBasesFPRAS.OnePositive (splitMatrix (pairMatrix (slotTotal ps f) A e)
      (fun i => slotTotal ps f (insert (e i) (insert p.2 A)))
      (fun i => slotTotal ps f (insert (e i) (insert p.1 A)))
      (slotTotal ps f (insert p.1 (insert p.2 A)))).toBilin' := by
  obtain ⟨hp, ha, hb, ht⟩ := hslots
  rw [← pairMatrix_split]
  apply slot_pair_signature ps f k A _ hf hsig hdegree
    (splitEmbedding_injective e p.1 p.2 he hp
      (fun h => ha (Or.inr h)) (fun h => hb (Or.inr h)))
  · intro i
    cases i with
    | inl i => exact heA i
    | inr b => cases b <;> simp only [splitEmbedding] <;> tauto
  · apply ht.mono
    rintro x (hx | ⟨i, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl hx))
    · cases i with
      | inl i => exact Or.inr (Or.inr (Or.inr ⟨i, rfl⟩))
      | inr b => cases b <;> simp [splitEmbedding]

/-- The full recursive signed transport bound. Every mass and signature
is supplied by the proved exact-degree lemmas above, and all future-slot
corrections telescope through the actual binary recursion. -/
theorem transport_linear_bound_degree (ps : List (Γ × Γ)) :
    ∀ {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
      (f H : Set Γ → ℝ) (A : Set Γ) (e : κ → Γ) (h : κ → ℝ) (W : Γ → ℝ) (k : ℕ),
      DegreePositive f k → AdditionProperty f k →
      A.ncard + ps.length + 1 = k → Function.Injective e →
      (∀ i, e i ∉ A) → SlotsFresh ps (A ∪ Set.range e) →
      (∀ i, 0 < W i) → (∀ p ∈ ps, W p.1 = W p.2) →
      (∑ i, slotTotal ps f (insert (e i) A)*h i = 0) →
      2*transportDemand ps f H A e h ≤
        transportPotential ps f A e h W - transportCorrection ps f A e h W +
          transportEnergy ps f H A e W := by
  induction ps with
  | nil =>
    intro κ _ _ _ f H A e h W k hf _ hdegree _ heA _ hW _ hbal
    have hb : ∑ i, f (insert (e i) A)*h i = 0 := hbal
    have hl := clique_linear_bound (fun i => f (insert (e i) A)) (fun i => W (e i)) h
      (fun i => H (insert (e i) A)) (fun i => hf _ (by
        rw [ncard_insert_eq A (e i) (heA i)]
        simpa using hdegree)) (fun i => hW _) hb
    simpa [transportDemand, transportPotential, transportCorrection, slotPunctures,
      slotTotal, coeffDerivs, transportEnergy_nil, mul_comm, mul_left_comm, mul_assoc] using hl
  | cons p ps ih =>
    intro κ _ _ _ f H A e h W k hf hSig hdegree he heA hFresh hW hw hbal
    obtain ⟨hab,ha,hb,ht⟩ := hFresh
    have hFresh' : SlotsFresh (p::ps) (A ∪ Set.range e) := ⟨hab,ha,hb,ht⟩
    obtain ⟨hfa,hfb⟩ := slotsFresh_child e A p ps hFresh'
    let sa : κ → ℝ := fun i => slotTotal ps f (insert (e i) (insert p.2 A))
    let sb : κ → ℝ := fun i => slotTotal ps f (insert (e i) (insert p.1 A))
    let u : ℝ := slotTotal ps f (insert p.1 (insert p.2 A))
    let X : ℝ := ∑ i, h i*sa i
    let c : ℝ := -X/u
    have hpa : p.1 ∉ A := fun h => ha (Or.inl h)
    have hpb : p.2 ∉ A := fun h => hb (Or.inl h)
    have hdegA : (insert p.2 A).ncard + ps.length + 1 = k := by
      rw [ncard_insert_eq A p.2 hpb]
      simp only [List.length_cons] at hdegree
      omega
    have hdegB : (insert p.1 A).ncard + ps.length + 1 = k := by
      rw [ncard_insert_eq A p.1 hpa]
      simp only [List.length_cons] at hdegree
      omega
    have hu : 0 < u := slotTotal_degree_positive ps f k hf _ (by
      rw [ncard_insert_eq _ p.1 (by simpa using And.intro hab hpa),
        ncard_insert_eq A p.2 hpb]
      simp only [List.length_cons] at hdegree
      omega)
      (ht.mono (Set.insert_subset_insert (Set.insert_subset_insert Set.subset_union_left)))
    have hb0 : (∑ i, (sa i+sb i)*h i) = 0 := by
      simpa only [slotTotal_parent ps f A e p hab ha hb] using hbal
    have hXb : (∑ i, h i*sb i) = -X := by
      simp only [add_mul, Finset.sum_add_distrib] at hb0
      have ha' : (∑ i, sa i*h i) = X := by dsimp [X]; apply Finset.sum_congr rfl; intro i _; ring
      have hb' : (∑ i, sb i*h i) = ∑ i, h i*sb i := by apply Finset.sum_congr rfl; intro i _; ring
      rw [ha',hb'] at hb0
      linarith
    have hcB : -c = -(∑ i, h i*sb i)/u := by rw [hXb]; dsimp [c]; ring
    have hba : ∑ i, slotTotal ps f (insert (appendPoint e p.1 i) (insert p.2 A)) *
        extendVector h c i = 0 := by
      have hc := child_balance sa h u (ne_of_gt hu)
      simp only [Fintype.sum_option, extendVector] at hc
      simpa only [Fintype.sum_option, extendVector, appendPoint, sa, u, c, X] using hc
    have hbb : ∑ i, slotTotal ps f (insert (appendPoint e p.2 i) (insert p.1 A)) *
        extendVector h (-c) i = 0 := by
      rw [hcB]
      have hc := child_balance sb h u (ne_of_gt hu)
      simp only [Fintype.sum_option, extendVector] at hc
      simpa only [Fintype.sum_option, extendVector, appendPoint, u, sb, Set.insert_comm p.2 p.1] using hc
    have hwa := hw p (List.mem_cons_self ..)
    have hwt : ∀ p ∈ ps, W p.1 = W p.2 := fun q hq => hw q (List.mem_cons_of_mem _ hq)
    have hla := ih f H (insert p.2 A) (appendPoint e p.1) (extendVector h c) W k
      hf hSig hdegA (appendPoint_injective e p.1 he (fun h => ha (Or.inr h)))
      (appendPoint_fresh e A p.1 p.2 heA hab (fun h => ha (Or.inl h))
        (fun h => hb (Or.inr h))) hfa hW hwt hba
    have hlb := ih f H (insert p.1 A) (appendPoint e p.2) (extendVector h (-c)) W k
      hf hSig hdegB (appendPoint_injective e p.2 he (fun h => hb (Or.inr h)))
      (appendPoint_fresh e A p.2 p.1 heA hab.symm (fun h => hb (Or.inl h))
        (fun h => ha (Or.inr h))) hfb hW hwt hbb
    have hsplit := split_bound (pairMatrix (slotTotal ps f) A e) sa sb h u hu
      (pairMatrix_symm _ A e) (slot_split_signature_degree f k hf hSig ps A e p he heA hFresh' (by
        simp only [List.length_cons] at hdegree
        omega)) hb0
    have hcost : 2*X^2/(u*W p.1) ≤
        -(pairMatrix (slotTotal ps f) A e).toBilin' h h / W p.1 := by
      simpa only [X, div_div] using div_le_div_of_nonneg_right hsplit (hW p.1).le
    have hpot := transportPotential_split ps f A e p h X u W hab ha hb rfl
      (ne_of_gt hu) hwa (ne_of_gt (hW p.1))
    have hcN : X/u = -c := by dsimp [c]; ring
    rw [hcN] at hpot
    change transportPotential ps f (insert p.2 A) (appendPoint e p.1) (extendVector h c) W +
      transportPotential ps f (insert p.1 A) (appendPoint e p.2) (extendVector h (-c)) W = _ at hpot
    rw [← transportDemand_split ps f H A e p h c hab ha hb,
      transportEnergy_cons, transportCorrection_split ps f A e p h c W hab ha hb]
    rw [neg_div] at hcost
    linarith


theorem transport_squared_bound_degree {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (ps : List (Γ × Γ))
    (f H : Set Γ → ℝ) (A : Set Γ) (e : ι → Γ) (h : ι → ℝ) (W : Γ → ℝ) (k : ℕ)
    (hf : DegreePositive f k) (hSig : AdditionProperty f k)
    (hdegree : A.ncard + ps.length + 1 = k) (he : Function.Injective e)
    (heA : ∀ i, e i ∉ A) (hps : SlotsFresh ps (A ∪ Set.range e))
    (hW : ∀ i, 0 < W i) (hw : ∀ p ∈ ps, W p.1 = W p.2)
    (hbal : ∑ i, slotTotal ps f (insert (e i) A)*h i = 0)
    (hC : 0 < transportPotential ps f A e h W - transportCorrection ps f A e h W) :
    (transportDemand ps f H A e h)^2 ≤
      (transportPotential ps f A e h W - transportCorrection ps f A e h W) *
        transportEnergy ps f H A e W := by
  apply squared_le_of_linear_scalings _ _ _ hC
  intro t
  have hbal' : ∑ i, slotTotal ps f (insert (e i) A)*(t • h) i = 0 := by
    simp only [Pi.smul_apply, smul_eq_mul]
    simp_rw [mul_left_comm _ t, ← Finset.mul_sum, hbal, mul_zero]
  have ht := transport_linear_bound_degree ps f H A e (t • h) W k hf hSig hdegree he heA hps hW hw hbal'
  rw [transportDemand_smul,transportPotential_smul,transportCorrection_smul] at ht
  nlinarith


lemma rootCoefficient_degree_pos (ps : List (Γ × Γ)) (f : Set Γ → ℝ)
    (k : ℕ) (hf : DegreePositive f k) (A : Set Γ) (p d : Γ) (W : Γ → ℝ)
    (hpd : p ≠ d) (hpA : p ∉ A) (hdA : d ∉ A)
    (hdegree : A.ncard + ps.length + 1 = k)
    (hps : SlotsFresh ps (A ∪ Set.range (rootEmbedding p d))) (hW : ∀ i, 0 < W i) :
    0 < rootCoefficient ps f A p d W := by
  have hfp : SlotsFresh ps (insert p A) := hps.mono (by
    rintro x (rfl | hx)
    · exact Or.inr ⟨false, rfl⟩
    · exact Or.inl hx)
  have hfd : SlotsFresh ps (insert d A) := hps.mono (by
    rintro x (rfl | hx)
    · exact Or.inr ⟨true, rfl⟩
    · exact Or.inl hx)
  have hp := slotTotal_degree_positive ps f k hf (insert p A) (by
    rw [ncard_insert_eq A p hpA]
    omega) hfp
  have hd := slotTotal_degree_positive ps f k hf (insert d A) (by
    rw [ncard_insert_eq A d hdA]
    omega) hfd
  unfold rootCoefficient
  apply add_pos_of_pos_of_nonneg
  · exact add_pos (one_div_pos.mpr (mul_pos hp (hW p)))
      (one_div_pos.mpr (mul_pos hd (hW d)))
  · apply mul_nonneg (div_nonneg (by norm_num) (mul_pos hp hd).le)
    apply List.sum_nonneg
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    apply div_nonneg _ (hW _).le
    have hperm := slotPunctures_perm ps y hy
    have hlen := hperm.length_eq
    simp only [List.length_cons] at hlen
    have hfr := (SlotsFresh.perm hperm _).mp hps
    apply (slotTotal_degree_positive y.2 f k hf _ ?_ ?_).le
    · rw [ncard_insert_eq _ p (by simpa using And.intro hpd hpA),
        ncard_insert_eq A d hdA]
      omega
    · apply hfr.2.2.2.mono
      rintro x (rfl | rfl | hx)
      · exact Or.inr (Or.inr (Or.inr ⟨false, rfl⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨true, rfl⟩))
      · exact Or.inr (Or.inr (Or.inl hx))

/-- The paper's root transport coefficient and weighted mean difference,
with fixed-degree positivity and addition signatures only. For one-hole
states this is applied to the complement-set weight. -/
theorem transport_root_bound_degree (ps : List (Γ × Γ)) (f H : Set Γ → ℝ)
    (A : Set Γ) (p d : Γ) (W : Γ → ℝ) (k : ℕ)
    (hf : DegreePositive f k) (hSig : AdditionProperty f k)
    (hdegree : A.ncard + ps.length + 1 = k)
    (hpd : p ≠ d) (hpA : p ∉ A) (hdA : d ∉ A)
    (hps : SlotsFresh ps (A ∪ Set.range (rootEmbedding p d)))
    (hW : ∀ i, 0 < W i) (hw : ∀ p ∈ ps, W p.1 = W p.2) :
    (slotTotal ps (fun S => f S*H S) (insert p A) / slotTotal ps f (insert p A) -
      slotTotal ps (fun S => f S*H S) (insert d A) / slotTotal ps f (insert d A))^2 ≤
    rootCoefficient ps f A p d W * transportEnergy ps f H A (rootEmbedding p d) W := by
  have heA : ∀ i, rootEmbedding p d i ∉ A := by
    intro i
    cases i <;> assumption
  have hfresh : ∀ i, SlotsFresh ps (insert (rootEmbedding p d i) A) := by
    intro i
    apply hps.mono
    rintro x (rfl | hx)
    · exact Or.inr ⟨i, rfl⟩
    · exact Or.inl hx
  have hsp := slotTotal_degree_positive ps f k hf (insert p A) (by
    rw [ncard_insert_eq A p hpA]
    omega) (hfresh false)
  have hsd := slotTotal_degree_positive ps f k hf (insert d A) (by
    rw [ncard_insert_eq A d hdA]
    omega) (hfresh true)
  let h := rootDemand (slotTotal ps f (insert p A)) (slotTotal ps f (insert d A))
  have hbal : ∑ i, slotTotal ps f (insert (rootEmbedding p d i) A)*h i = 0 := by
    simp [h, rootDemand, rootEmbedding, ne_of_gt hsp, ne_of_gt hsd]
  have hcoef : transportPotential ps f A (rootEmbedding p d) h W -
      transportCorrection ps f A (rootEmbedding p d) h W = rootCoefficient ps f A p d W := by
    dsimp [h]
    rw [rootPotential ps f A p d W (ne_of_gt hsp) (ne_of_gt hsd), rootCorrection]
    simp only [rootCoefficient, sub_neg_eq_add]
  have ht := transport_squared_bound_degree ps f H A (rootEmbedding p d) h W k hf hSig
    hdegree (rootEmbedding_injective p d hpd) heA hps hW hw hbal (by
      rw [hcoef]
      exact rootCoefficient_degree_pos ps f k hf A p d W hpd hpA hdA hdegree hps hW)
  rw [hcoef] at ht
  simpa [transportDemand, h, rootDemand, rootEmbedding, Fintype.sum_bool, div_eq_mul_inv,
    mul_comm, sub_eq_add_neg, add_comm] using ht


lemma slotVertices_degree (ps : List (Γ × Γ)) :
    ∀ {κ : Type*} [Fintype κ] [DecidableEq κ] (A : Set Γ) (e : κ → Γ),
      Function.Injective e → (∀ i, e i ∉ A) → SlotsFresh ps (A ∪ Set.range e) →
      ∀ S ∈ slotVertices ps A e, S.ncard = A.ncard + ps.length + 1 := by
  induction ps with
  | nil =>
    intro κ _ _ A e he heA _ S hS
    rw [slotVertices] at hS
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hS
    rw [ncard_insert_eq A (e i) (heA i)]
    rfl
  | cons p ps ih =>
    intro κ _ _ A e he heA hslots S hS
    obtain ⟨hp, ha, hb, ht⟩ := hslots
    have hslots' : SlotsFresh (p :: ps) (A ∪ Set.range e) := ⟨hp, ha, hb, ht⟩
    obtain ⟨hfa, hfb⟩ := slotsFresh_child e A p ps hslots'
    rw [slotVertices] at hS
    rcases Finset.mem_union.mp hS with hS | hS
    · have h := ih (insert p.2 A) (appendPoint e p.1)
        (appendPoint_injective e p.1 he (fun h => ha (Or.inr h)))
        (appendPoint_fresh e A p.1 p.2 heA hp (fun h => ha (Or.inl h))
          (fun h => hb (Or.inr h))) hfa S hS
      rw [ncard_insert_eq A p.2 (fun h => hb (Or.inl h))] at h
      simp only [List.length_cons]
      omega
    · have h := ih (insert p.1 A) (appendPoint e p.2)
        (appendPoint_injective e p.2 he (fun h => hb (Or.inr h)))
        (appendPoint_fresh e A p.2 p.1 heA hp.symm (fun h => hb (Or.inl h))
          (fun h => ha (Or.inr h))) hfb S hS
      rw [ncard_insert_eq A p.1 (fun h => ha (Or.inl h))] at h
      simp only [List.length_cons]
      omega

lemma transportEnergy_le_graphEnergy_degree {κ : Type*} [Fintype κ] [DecidableEq κ]
    (ps : List (Γ × Γ)) (f H : Set Γ → ℝ) (A : Set Γ) (e : κ → Γ) (W : Γ → ℝ)
    (k : ℕ) (hf : DegreePositive f k) (hdegree : A.ncard + ps.length + 1 = k)
    (he : Function.Injective e) (heA : ∀ i, e i ∉ A)
    (hps : SlotsFresh ps (A ∪ Set.range e)) (hw : ∀ p ∈ ps, W p.1 = W p.2)
    (hW : ∀ i, 0 ≤ W i) :
    transportEnergy ps f H A e W ≤ slotGraphEnergy ps f H A e W := by
  rw [transportEnergy_eq_sum ps f H A e W he heA hps hw]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro ST hST
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr (transportEdges_states ps A e ST hST),
      transportEdges_adjacent ps A e he heA hps ST hST⟩
  · intro ST hST _
    obtain ⟨hs, ht⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hST).1
    have hsdeg : ST.1.ncard = k := (slotVertices_degree ps A e he heA hps ST.1 hs).trans hdegree
    have htdeg : ST.2.ncard = k := (slotVertices_degree ps A e he heA hps ST.2 ht).trans hdegree
    apply mul_nonneg _ (sq_nonneg _)
    exact le_min (mul_nonneg (missingMultiplier_nonneg ps e W hW ST.1) (hf _ hsdeg).le)
      (mul_nonneg (missingMultiplier_nonneg ps e W hW ST.2) (hf _ htdeg).le)

/-- Full one-hole transport on the actual exchange graph with the exact
minimum-endpoint conductances and unordered-edge convention. -/
theorem transport_graph_bound_degree (ps : List (Γ × Γ)) (f H : Set Γ → ℝ)
    (A : Set Γ) (p d : Γ) (W : Γ → ℝ) (k : ℕ)
    (hf : DegreePositive f k) (hSig : AdditionProperty f k)
    (hdegree : A.ncard + ps.length + 1 = k)
    (hpd : p ≠ d) (hpA : p ∉ A) (hdA : d ∉ A)
    (hps : SlotsFresh ps (A ∪ Set.range (rootEmbedding p d)))
    (hW : ∀ i, 0 < W i) (hw : ∀ p ∈ ps, W p.1 = W p.2) :
    (slotTotal ps (fun S => f S*H S) (insert p A) / slotTotal ps f (insert p A) -
      slotTotal ps (fun S => f S*H S) (insert d A) / slotTotal ps f (insert d A))^2 ≤
    rootCoefficient ps f A p d W * slotGraphEnergy ps f H A (rootEmbedding p d) W := by
  apply (transport_root_bound_degree ps f H A p d W k hf hSig hdegree hpd hpA hdA hps hW hw).trans
  apply mul_le_mul_of_nonneg_left _
    (rootCoefficient_degree_pos ps f k hf A p d W hpd hpA hdA hdegree hps hW).le
  apply transportEnergy_le_graphEnergy_degree ps f H A (rootEmbedding p d) W k hf hdegree
    (rootEmbedding_injective p d hpd) _ hps hw (fun i => (hW i).le)
  intro i
  cases i <;> assumption


/-- The one-hole statement in the paper's omission convention. An encoded
set is the complement of the original table-lift state, so the multiplier
marks its unique hole slot. -/
theorem one_hole_transport (ps : List (Γ × Γ)) (f H : Set Γ → ℝ)
    (A : Set Γ) (p d : Γ) (W : Γ → ℝ) (k : ℕ)
    (hk : k ≤ Fintype.card Γ) (hf : DegreePositive f k) (hSig : OmissionProperty f k)
    (hdegree : A.ncard + ps.length + 1 = Fintype.card Γ - k)
    (hpd : p ≠ d) (hpA : p ∉ A) (hdA : d ∉ A)
    (hps : SlotsFresh ps (A ∪ Set.range (rootEmbedding p d)))
    (hW : ∀ i, 0 < W i) (hw : ∀ p ∈ ps, W p.1 = W p.2) :
    let fc := complementWeight f
    let Hc := complementWeight H
    (slotTotal ps (fun S => fc S * Hc S) (insert p A) / slotTotal ps fc (insert p A) -
      slotTotal ps (fun S => fc S * Hc S) (insert d A) / slotTotal ps fc (insert d A)) ^ 2 ≤
      rootCoefficient ps fc A p d W * slotGraphEnergy ps fc Hc A (rootEmbedding p d) W := by
  exact transport_graph_bound_degree ps (complementWeight f) (complementWeight H) A p d W
    (Fintype.card Γ - k) (complement_degreePositive f k hk hf) hSig hdegree
    hpd hpA hdA hps hW hw

end ContingencyTables.RecursiveSignedTransport

end OAI
