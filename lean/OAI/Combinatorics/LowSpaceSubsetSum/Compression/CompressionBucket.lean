import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionDictionary
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.StreamWitness

namespace OAI

/-! # The fixed solution survives the compressed trial's bounded dictionary -/

namespace LowSpaceSubsetSum

theorem direct_complementary_residue (q z x y : ℤ) :
    x % q = (z - y) % q ↔ (x + y) % q = z % q := by
  change Int.ModEq q x (z - y) ↔ Int.ModEq q (x + y) z
  constructor
  · intro h
    simpa only [sub_add_cancel] using h.add_right y
  · intro h
    simpa only [add_sub_cancel_right] using h.sub_right y

namespace CompressionSetup

variable {n : ℕ} (R : CompressionSetup n)

theorem leftPair_mem (e : Equiv.Perm (Fin n)) {x y : ℤ}
    (hx : x ∈ R.groupList e 0) (hy : y ∈ R.groupList e 1) :
    x + y ∈ R.leftWeights e := by
  change x + y ∈ distinctSums R.weights (R.leftDomain e)
  rw [R.leftDomain_eq_groups]
  exact (distinctSums_union_mem_iff _ _ _ (R.left_groups_disjoint e) _).mpr
    ⟨x, (R.mem_groupList e 0 x).mp hx, y, (R.mem_groupList e 1 y).mp hy, rfl⟩

theorem leftSolution_pair (e : Equiv.Perm (Fin n)) :
    ∃ x ∈ R.groupList e 0, ∃ y ∈ R.groupList e 1, x + y = R.leftWeight e := by
  have h := R.leftWeight_mem e
  change R.leftWeight e ∈ distinctSums R.weights (R.leftDomain e) at h
  rw [R.leftDomain_eq_groups] at h
  obtain ⟨x, hx, y, hy, he⟩ :=
    (distinctSums_union_mem_iff _ _ _ (R.left_groups_disjoint e) _).mp h
  exact ⟨x, (R.mem_groupList e 0 x).mpr hx, y, (R.mem_groupList e 1 y).mpr hy, he⟩

theorem rightSolution_pair (e : Equiv.Perm (Fin n)) :
    ∃ x ∈ R.groupList e 2, ∃ y ∈ R.groupList e 3, x + y = R.rightWeight e := by
  have h := R.rightWeight_mem e
  change R.rightWeight e ∈ distinctSums R.weights (R.rightDomain e) at h
  rw [R.rightDomain_eq_groups] at h
  obtain ⟨x, hx, y, hy, he⟩ :=
    (distinctSums_union_mem_iff _ _ _ (R.right_groups_disjoint e) _).mp h
  exact ⟨x, (R.mem_groupList e 2 x).mpr hx, y, (R.mem_groupList e 3 y).mpr hy, he⟩

def solutionResidue (e : Equiv.Perm (Fin n)) (q : PrimeSpace n) : Fin q.val :=
  normalizedResidue (primeRange_prime q.property).pos (R.leftWeight e)

theorem solutionResidue_val (e : Equiv.Perm (Fin n)) (q : PrimeSpace n) :
    ((R.solutionResidue e q).val : ℤ) = R.leftWeight e % (q.val : ℤ) :=
  normalizedResidue_cast _ _

theorem finiteResidue_reduced (q : PrimeSpace n) (z : Fin q.val) :
    (z.val : ℤ) % q.val = z.val :=
  Int.emod_eq_of_lt (by omega) (by exact_mod_cast z.isLt)

def leftBucket (e : Equiv.Perm (Fin n)) (q : PrimeSpace n) (z : Fin q.val) : Finset ℤ :=
  (R.leftWeights e).filter (fun w => w % (q.val : ℤ) = z.val)

theorem solutionBucket_fits (e : Equiv.Perm (Fin n)) (q : PrimeSpace n)
    (hq : R.BucketFits e q) :
    (R.leftBucket e q (R.solutionResidue e q)).card ≤ compressionDictionaryCapacity n := by
  simpa only [leftBucket, solutionResidue_val, BucketFits, hashBucket, id_eq] using hq

def leftDictionary (e : Equiv.Perm (Fin n)) (q : PrimeSpace n) (z : Fin q.val) :
    BinaryTrie.BuildResult :=
  MatchFold.run (fun x => x % (q.val : ℤ)) (fun y => ((z.val : ℤ) - y) % q.val)
    (BinaryTrie.callback (compressionDictionaryCapacity n)
      (fun x y => WeightEncoding.weightKey R.input (x + y)))
    (R.groupList e 0) (R.groupList e 1) ⟨.empty, false, 0⟩

theorem leftDictionary_fits (e : Equiv.Perm (Fin n)) (q : PrimeSpace n)
    (hq : R.BucketFits e q) :
    (R.leftDictionary e q (R.solutionResidue e q)).overflow = false ∧
      BinaryTrie.contains (R.leftDictionary e q (R.solutionResidue e q)).tree
        (WeightEncoding.weightKey R.input (R.leftWeight e)) = true := by
  let z := R.solutionResidue e q
  let U := (R.leftBucket e q z).image (WeightEncoding.weightKey R.input)
  have hU : U.card ≤ compressionDictionaryCapacity n :=
    Finset.card_image_le.trans (R.solutionBucket_fits e q hq)
  have hkeys : ∀ x ∈ R.groupList e 0, ∀ y ∈ R.groupList e 1,
      x % (q.val : ℤ) = ((z.val : ℤ) - y) % q.val →
      WeightEncoding.weightKey R.input (x + y) ∈ U := by
    intro x hx y hy he
    apply Finset.mem_image.mpr
    refine ⟨x + y, Finset.mem_filter.mpr ⟨R.leftPair_mem e hx hy, ?_⟩, rfl⟩
    have hm := (direct_complementary_residue (q.val : ℤ) z.val x y).mp he
    rwa [finiteResidue_reduced q z] at hm
  have h := BinaryTrie.matchFold_fits (width := WeightEncoding.weightWidth R.input)
    (fun x => x % (q.val : ℤ)) (fun y => ((z.val : ℤ) - y) % q.val)
    (fun x y => WeightEncoding.weightKey R.input (x + y))
    (R.groupList e 0) (R.groupList e 1) U
    (fun key hk => by
      obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hk
      exact WeightEncoding.weightKey_length R.input w) hU hkeys
  change (R.leftDictionary e q z).overflow = false ∧ _
  refine ⟨h.1, ?_⟩
  rw [← BinaryTrie.mem_keySet]
  dsimp only [leftDictionary]
  rw [h.2.1, List.mem_toFinset, BinaryTrie.mem_matchingKeys]
  obtain ⟨x, hx, y, hy, he⟩ := R.leftSolution_pair e
  refine ⟨x, hx, y, hy, ?_, ?_⟩
  · apply (direct_complementary_residue (q.val : ℤ) z.val x y).mpr
    rw [he, finiteResidue_reduced q z]
    exact (R.solutionResidue_val e q).symm
  · rw [he]

def DictionarySuccess (h : TrialHistory n) : Prop :=
  R.Passing h.1 ∧
    (R.leftDictionary h.1 h.2 (R.solutionResidue h.1 h.2)).overflow = false ∧
    BinaryTrie.contains (R.leftDictionary h.1 h.2 (R.solutionResidue h.1 h.2)).tree
      (WeightEncoding.weightKey R.input (R.leftWeight h.1)) = true

theorem dictionarySuccess_probability (hn : 168000000 ≤ n)
    (hmean : (153 / 20000 : ℝ) * n ≤
      meanDeficiency R.weights Finset.univ (compressionHalfSize n))
    (hlog : Real.logb 2 (inputScale R.input) ≤ (n : ℝ) / 1000000000) :
    (1 / 4 : ℝ) ≤ (R.trialLaw hn).probability R.DictionarySuccess := by
  apply (R.successful_probability hn hmean hlog).trans
  apply FiniteLaw.probability_mono
  intro h hh
  exact ⟨hh.1, R.leftDictionary_fits h.1 h.2 hh.2⟩

/-- The generated sorted readers may permute occurrences, but their exact
group-list membership suffices for the actual join to retain the solution. -/
theorem generated_left_dictionary {σ₀ σ₁ : Type*}
    (e : Equiv.Perm (Fin n)) (q : PrimeSpace n) (hq : R.BucketFits e q)
    (read₀ : σ₀ → Option (ℤ × σ₀)) (read₁ : σ₁ → Option (ℤ × σ₁))
    (view₀ : σ₀ → List ℤ) (hread₀ : RowMerge.IsReader read₀ view₀)
    (view₁ : σ₁ → List ℤ) (hread₁ : RowMerge.IsReader read₁ view₁)
    (s₀ : σ₀) (s₁ : σ₁)
    (hview₀ : ∀ x, x ∈ view₀ s₀ ↔ x ∈ R.groupList e 0)
    (hview₁ : ∀ x, x ∈ view₁ s₁ ↔ x ∈ R.groupList e 1)
    (B fuel₀ fuel₁ controlFuel : ℕ)
    (hsort₀ : (view₀ s₀).Pairwise (fun x y => x % (q.val : ℤ) ≤ y % q.val))
    (hsort₁ : (view₁ s₁).Pairwise (fun x y =>
      (((R.solutionResidue e q).val : ℤ) - x) % q.val ≤
        (((R.solutionResidue e q).val : ℤ) - y) % q.val))
    (hcap₀ : (view₀ s₀).length ≤ fuel₀) (hcap₁ : (view₁ s₁).length ≤ fuel₁)
    (hfuel : (view₀ s₀).length + (view₁ s₁).length < controlFuel) :
    let z := R.solutionResidue e q
    let out := (StreamJoin.run read₀ (fun x => x % (q.val : ℤ))
      read₁ (fun y => ((z.val : ℤ) - y) % q.val)
      (BinaryTrie.callback (compressionDictionaryCapacity n)
        (fun x y => WeightEncoding.weightKey R.input (x + y)))
      B fuel₀ fuel₁ controlFuel s₀ s₁ ⟨.empty, false, 0⟩).user
    out.overflow = false ∧ BinaryTrie.contains out.tree
      (WeightEncoding.weightKey R.input (R.leftWeight e)) = true := by
  let z := R.solutionResidue e q
  let U := (R.leftBucket e q z).image (WeightEncoding.weightKey R.input)
  have hU : U.card ≤ compressionDictionaryCapacity n :=
    Finset.card_image_le.trans (R.solutionBucket_fits e q hq)
  have hkeys : ∀ x ∈ view₀ s₀, ∀ y ∈ view₁ s₁,
      x % (q.val : ℤ) = ((z.val : ℤ) - y) % q.val →
      WeightEncoding.weightKey R.input (x + y) ∈ U := by
    intro x hx y hy he
    apply Finset.mem_image.mpr
    refine ⟨x + y, Finset.mem_filter.mpr ⟨R.leftPair_mem e
      ((hview₀ x).mp hx) ((hview₁ y).mp hy), ?_⟩, rfl⟩
    have hm := (direct_complementary_residue (q.val : ℤ) z.val x y).mp he
    rwa [finiteResidue_reduced q z] at hm
  have h := BinaryTrie.join_fits (C := compressionDictionaryCapacity n)
    (width := WeightEncoding.weightWidth R.input)
    read₀ (fun x => x % (q.val : ℤ)) read₁ (fun y => ((z.val : ℤ) - y) % q.val)
    (fun x y => WeightEncoding.weightKey R.input (x + y))
    view₀ hread₀ view₁ hread₁ B fuel₀ fuel₁ controlFuel s₀ s₁ hsort₀ hsort₁ hcap₀ hcap₁ hfuel
    U (fun key hk => by
      obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hk
      exact WeightEncoding.weightKey_length R.input w) hU hkeys
  refine ⟨h.1, (h.2 _).mpr ?_⟩
  obtain ⟨x, hx, y, hy, he⟩ := R.leftSolution_pair e
  refine ⟨x, (hview₀ x).mpr hx, y, (hview₁ y).mpr hy, ?_, ?_⟩
  · apply (direct_complementary_residue (q.val : ℤ) z.val x y).mpr
    rw [he, finiteResidue_reduced q z]
    exact (R.solutionResidue_val e q).symm
  · rw [he]

/-- Once the left dictionary contains the fixed left weight, the actual
right readers find its complementary exact weight in the same residue pass. -/
theorem generated_right_hit {σ₂ σ₃ : Type*}
    (e : Equiv.Perm (Fin n)) (q : PrimeSpace n) (tree : BinaryTrie.Tree)
    (hleft : BinaryTrie.contains tree (WeightEncoding.weightKey R.input (R.leftWeight e)) = true)
    (read₂ : σ₂ → Option (ℤ × σ₂)) (read₃ : σ₃ → Option (ℤ × σ₃))
    (view₂ : σ₂ → List ℤ) (hread₂ : RowMerge.IsReader read₂ view₂)
    (view₃ : σ₃ → List ℤ) (hread₃ : RowMerge.IsReader read₃ view₃)
    (s₂ : σ₂) (s₃ : σ₃)
    (hview₂ : ∀ x, x ∈ view₂ s₂ ↔ x ∈ R.groupList e 2)
    (hview₃ : ∀ x, x ∈ view₃ s₃ ↔ x ∈ R.groupList e 3)
    (B fuel₂ fuel₃ controlFuel : ℕ)
    (hsort₂ : (view₂ s₂).Pairwise (fun x y => x % (q.val : ℤ) ≤ y % q.val))
    (hsort₃ : (view₃ s₃).Pairwise (fun x y =>
      ((R.input.target : ℤ) - (R.solutionResidue e q).val - x) % q.val ≤
        ((R.input.target : ℤ) - (R.solutionResidue e q).val - y) % q.val))
    (hcap₂ : (view₂ s₂).length ≤ fuel₂) (hcap₃ : (view₃ s₃).length ≤ fuel₃)
    (hfuel : (view₂ s₂).length + (view₃ s₃).length < controlFuel) :
    (StreamJoin.run read₂ (fun x => x % (q.val : ℤ)) read₃
      (fun y => ((R.input.target : ℤ) - (R.solutionResidue e q).val - y) % q.val)
      (StreamWitness.remember (fun x y => BinaryTrie.contains tree
        (WeightEncoding.weightKey R.input ((R.input.target : ℤ) - (x + y)))))
      B fuel₂ fuel₃ controlFuel s₂ s₃ false).user = true := by
  apply (StreamWitness.run_iff read₂ (fun x => x % (q.val : ℤ)) read₃
    (fun y => ((R.input.target : ℤ) - (R.solutionResidue e q).val - y) % q.val)
    (fun x y => BinaryTrie.contains tree
      (WeightEncoding.weightKey R.input ((R.input.target : ℤ) - (x + y))))
    view₂ hread₂ view₃ hread₃ B fuel₂ fuel₃ controlFuel s₂ s₃
    hsort₂ hsort₃ hcap₂ hcap₃ hfuel).mpr
  obtain ⟨x, hx, y, hy, he⟩ := R.rightSolution_pair e
  have hs := R.solution_split e
  have hw : R.rightWeight e = (R.input.target : ℤ) - R.leftWeight e := by omega
  have hmod : Int.ModEq (q.val : ℤ) (R.leftWeight e) (R.solutionResidue e q).val :=
    normalizedResidue_eq_modEq (primeRange_prime q.property).pos _ _ rfl
  have hr := (Int.ModEq.refl (R.input.target : ℤ)).sub hmod
  rw [← hw] at hr
  refine ⟨x, (hview₂ x).mpr hx, y, (hview₃ y).mpr hy, ?_, ?_⟩
  · apply (direct_complementary_residue (q.val : ℤ)
      ((R.input.target : ℤ) - (R.solutionResidue e q).val) x y).mpr
    rwa [he]
  · rw [he, show (R.input.target : ℤ) - R.rightWeight e = R.leftWeight e by omega]
    exact hleft

end CompressionSetup

end LowSpaceSubsetSum

end OAI
