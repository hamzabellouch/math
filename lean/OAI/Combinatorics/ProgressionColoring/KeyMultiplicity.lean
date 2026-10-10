import OAI.Combinatorics.ProgressionColoring.NormBands
import OAI.Combinatorics.ProgressionColoring.CyclicModel
import OAI.Combinatorics.ProgressionColoring.SmallBoxAffinity
import OAI.Combinatorics.ProgressionColoring.AdaptiveMesh

namespace OAI

noncomputable section

universe uIndex uX uBox

namespace QuantitativeVanDerWaerden

open scoped BigOperators

/-- Squared-separated points on an affine line in one half-open norm band. -/
theorem affine_norm_band_card_le_two {ι : Type uIndex} {D : ℕ} (s : Finset ι)
    (t : ι → ℝ) (A B : Vec D) (m : ℝ)
    (hsep : (s : Set ι).Pairwise fun i j =>
      1 ≤ distSq (fun d => A d + t i * B d) (fun d => A d + t j * B d))
    (hband : ∀ i ∈ s,
      m ≤ normSq (fun d => A d + t i * B d) ∧
      normSq (fun d => A d + t i * B d) < m + 1) :
    s.card ≤ 2 := by
  classical
  by_cases hB : normSq B = 0
  · have hcard : s.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro i hi j hj
      by_contra hij
      have h : 1 ≤ distSq (fun d => A d + t i * B d)
          (fun d => A d + t j * B d) := hsep hi hj hij
      rw [distSq_affine A B (t i) (t j), hB, zero_mul] at h
      norm_num at h
    exact hcard.trans (by decide)
  · apply weighted_scalar_band_card_le_two s
      (fun i => t i + (∑ d, A d * B d) / normSq B) (normSq B)
      (normSq A - (∑ d, A d * B d) ^ 2 / normSq B) m (normSq_nonneg B)
    · intro i hi j hj hij
      simpa only [distSq_affine, add_sub_add_right_eq_sub] using hsep hi hj hij
    · intro i hi
      simpa only [normSq_affine_complete_square A B (t i) hB] using hband i hi

theorem affine_norm_band_card_le_four {ι : Type uIndex} {D : ℕ} (s : Finset ι)
    (t : ι → ℝ) (A B : Vec D) (m : ℝ)
    (hsep : (s : Set ι).Pairwise fun i j =>
      1 ≤ distSq (fun d => A d + t i * B d) (fun d => A d + t j * B d))
    (hband : ∀ i ∈ s,
      m ≤ normSq (fun d => A d + t i * B d) ∧
      normSq (fun d => A d + t i * B d) < m + 1) :
    s.card ≤ 4 :=
  (affine_norm_band_card_le_two s t A B m hsep hband).trans (by decide)

/-- The literal box label and integer squared-norm band. -/
def geometricKey {X : Type uX} {Box : Type uBox} {D : ℕ}
    (box : X → Box) (point : X → Vec D) (x : X) : Box × ℤ :=
  (box x, ⌊normSq (point x)⌋)

theorem geometricKey_band {X : Type uX} {Box : Type uBox} {D : ℕ}
    (box : X → Box) (point : X → Vec D) {x : X} {key : Box × ℤ}
    (hkey : geometricKey box point x = key) :
    (key.2 : ℝ) ≤ normSq (point x) ∧ normSq (point x) < (key.2 : ℝ) + 1 := by
  have hf : ⌊normSq (point x)⌋ = key.2 := congrArg Prod.snd hkey
  constructor
  · simpa only [hf] using Int.floor_le (normSq (point x))
  · simpa only [hf] using Int.lt_floor_add_one (normSq (point x))

/-- No consecutive-index assumption is made on the selected key occurrences. -/
theorem same_geometricKey_card_le_four {ι : Type uIndex} {Box : Type uBox} {D : ℕ}
    (s : Finset ι) (t : ι → ℝ) (box : ι → Box) (point : ι → Vec D)
    (key : Box × ℤ) (hkey : ∀ i ∈ s, geometricKey box point i = key)
    (hsep : (s : Set ι).Pairwise fun i j => 1 ≤ distSq (point i) (point j))
    (A B : Vec D) (haffine : ∀ i ∈ s, point i = fun d => A d + t i * B d) :
    s.card ≤ 4 := by
  apply affine_norm_band_card_le_four s t A B (key.2 : ℝ)
  · intro i hi j hj hij
    rw [← haffine i hi, ← haffine j hj]
    exact hsep hi hj hij
  · intro i hi
    have hb := geometricKey_band box point (hkey i hi)
    rwa [haffine i hi] at hb

/-- The actual scale used by the second representative system. -/
def scaledYRep (q D dilation : ℕ) (n : CyclicGroup q D) : Vec D :=
  fun i => (q : ℝ) * yRep q D dilation n i

def yGeometricKey {Box : Type uBox} (q D dilation : ℕ)
    (box : CyclicGroup q D → Box) (n : CyclicGroup q D) : Box × ℤ :=
  geometricKey box (scaledYRep q D dilation) n

theorem yGeometricKey_fiber_card_le_four {Box : Type uBox} [DecidableEq Box]
    {q D dilation k : ℕ} {H : ℝ} (hq : 0 < q)
    (hunit : Nat.Coprime dilation (q ^ D))
    (box : CyclicGroup q D → Box)
    (hbox : ∀ n n', box n = box n' → ∀ i,
      |yRep q D dilation n i - yRep q D dilation n' i| ≤ 2 * H)
    (hH : 0 ≤ H) (hsmall : 2 * (k : ℝ) * H < 1)
    (a d : CyclicGroup q D)
    (hinj : Function.Injective (fun j : Fin k => a + (j.val : CyclicGroup q D) * d))
    (key : Box × ℤ) :
    ((Finset.range k).filter fun j : ℕ =>
      yGeometricKey q D dilation box (a + (j : CyclicGroup q D) * d) = key).card ≤ 4 := by
  classical
  let J := (Finset.range k).filter fun j : ℕ =>
    yGeometricKey q D dilation box (a + (j : CyclicGroup q D) * d) = key
  let z : ℕ → Vec D := fun j => yRep q D dilation (a + (j : CyclicGroup q D) * d)
  have hJ : ∀ j ∈ J, j < k := fun j hj =>
    Finset.mem_range.mp (Finset.mem_filter.mp hj).1
  have hkey : ∀ j ∈ J,
      yGeometricKey q D dilation box (a + (j : CyclicGroup q D) * d) = key :=
    fun j hj => (Finset.mem_filter.mp hj).2
  have hb : ∀ i ∈ J, ∀ j ∈ J, ∀ c, |z j c - z i c| ≤ 2 * H := by
    intro i hi j hj c
    have hi' : box (a + (i : CyclicGroup q D) * d) = key.1 :=
      congrArg Prod.fst (hkey i hi)
    have hj' : box (a + (j : CyclicGroup q D) * d) = key.1 :=
      congrArg Prod.fst (hkey j hj)
    exact hbox _ _ (hj'.trans hi'.symm) c
  have hint : ∀ i ∈ J, ∀ j ∈ J, ∀ l ∈ J, i < j → j < l → ∀ c,
      ∃ m : ℤ, ((l : ℝ) - j) * (z j c - z i c) -
        ((j : ℝ) - i) * (z l c - z j c) = (m : ℝ) := by
    intro i hi j hj l hl hij hjl c
    apply triple_integral_of_integer_errors
      (A := yRep q D dilation a c) (B := yRep q D dilation d c)
    intro n
    simpa only [z, nsmul_eq_mul] using yRep_ap_congr hq dilation a d n c
  obtain ⟨A, B, hAB⟩ := exists_affine_of_small_box_vector J z hJ hH hsmall hb hint
  have hsep : (J : Set ℕ).Pairwise fun i j =>
      1 ≤ distSq (scaledYRep q D dilation (a + (i : CyclicGroup q D) * d))
        (scaledYRep q D dilation (a + (j : CyclicGroup q D) * d)) := by
    intro i hi j hj hij
    have hne : a + (i : CyclicGroup q D) * d ≠ a + (j : CyclicGroup q D) * d := by
      intro heq
      have hfin : (⟨i, hJ i hi⟩ : Fin k) = ⟨j, hJ j hj⟩ := hinj heq
      exact hij (congrArg Fin.val hfin)
    exact yRep_squared_separation hq hunit hne
  change J.card ≤ 4
  apply same_geometricKey_card_le_four J (fun j => (j : ℝ))
    (fun j => box (a + (j : CyclicGroup q D) * d))
    (fun j => scaledYRep q D dilation (a + (j : CyclicGroup q D) * d)) key
    hkey hsep (fun c => (q : ℝ) * A c) (fun c => (q : ℝ) * B c)
  intro j hj
  funext c
  change (q : ℝ) * z j c = (q : ℝ) * A c + (j : ℝ) * ((q : ℝ) * B c)
  rw [hAB j hj c]
  ring

/-- The actual coordinatewise second-system box label. -/
def secondBox (mesh : AdaptiveMesh) (q D dilation : ℕ)
    (n : CyclicGroup q D) : Fin D → mesh.Label :=
  fun i => mesh.meshLabel (yRep q D dilation n i)

def perturbationKey (mesh : AdaptiveMesh) (q D dilation : ℕ)
    (n : CyclicGroup q D) : (Fin D → mesh.Label) × ℤ :=
  yGeometricKey q D dilation (secondBox mesh q D dilation) n

theorem secondBox_same_distance (mesh : AdaptiveMesh) (q D dilation : ℕ)
    {a b : CyclicGroup q D} (h : secondBox mesh q D dilation a =
      secondBox mesh q D dilation b) (i : Fin D) :
    |yRep q D dilation a i - yRep q D dilation b i| ≤ 2 * mesh.H := by
  have hi : mesh.meshLabel (yRep q D dilation a i) =
      mesh.meshLabel (yRep q D dilation b i) := congrFun h i
  have ha := yRep_mem q D dilation a i
  have hb := yRep_mem q D dilation b i
  have hd := (mesh.same_label_distance hi).trans (mesh.width_le_two_H _)
  simpa only [centered_eq_of_mem ha.1 ha.2, centered_eq_of_mem hb.1 hb.2] using hd

/-- Every literal geometric key occurs at most four times on an actual
nonconstant cyclic progression. The prime-power hypothesis supplies distinct
terms, the mesh supplies the width bound, and coprime dilation supplies
squared separation; no affinity or key-multiplicity conclusion is assumed. -/
theorem perturbationKey_fiber_card_le_four (mesh : AdaptiveMesh)
    {P e D dilation k : ℕ} (hP : P.Prime) (hk : k ≤ P)
    (hunit : Nat.Coprime dilation ((P ^ e) ^ D))
    (hsmall : 2 * (k : ℝ) * mesh.H < 1)
    (a d : CyclicGroup (P ^ e) D) (hd : d ≠ 0)
    (key : (Fin D → mesh.Label) × ℤ) :
    ((Finset.range k).filter fun j : ℕ =>
      perturbationKey mesh (P ^ e) D dilation
        (a + (j : CyclicGroup (P ^ e) D) * d) = key).card ≤ 4 := by
  apply yGeometricKey_fiber_card_le_four (pow_pos hP.pos e) hunit
    (secondBox mesh (P ^ e) D dilation) ?_ mesh.H_pos.le hsmall a d
    (prime_power_ap_injective_pow hP hk a d hd) key
  intro n n' h i
  exact secondBox_same_distance mesh (P ^ e) D dilation h i

/-- The same literal-key bound on the finite index type used by the
Bernoulli perturbation. This is only the bijection between `Fin k` and
`range k`; the geometric argument is reused unchanged. -/
theorem perturbationKey_fin_fiber_card_le_four (mesh : AdaptiveMesh)
    {P e D dilation k : ℕ} (hP : P.Prime) (hk : k ≤ P)
    (hunit : Nat.Coprime dilation ((P ^ e) ^ D))
    (hsmall : 2 * (k : ℝ) * mesh.H < 1)
    (a d : CyclicGroup (P ^ e) D) (hd : d ≠ 0)
    (key : (Fin D → mesh.Label) × ℤ) :
    (Finset.univ.filter fun j : Fin k =>
      perturbationKey mesh (P ^ e) D dilation
        (a + (j.val : CyclicGroup (P ^ e) D) * d) = key).card ≤ 4 := by
  classical
  have hcard :
      (Finset.univ.filter fun j : Fin k =>
        perturbationKey mesh (P ^ e) D dilation
          (a + (j.val : CyclicGroup (P ^ e) D) * d) = key).card =
      ((Finset.range k).filter fun j : ℕ =>
        perturbationKey mesh (P ^ e) D dilation
          (a + (j : CyclicGroup (P ^ e) D) * d) = key).card := by
    refine Finset.card_bij (fun j _ => j.val) ?_ ?_ ?_
    · intro j hj
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr j.isLt, (Finset.mem_filter.mp hj).2⟩
    · intro i hi j hj hij
      exact Fin.ext hij
    · intro j hj
      refine ⟨⟨j, Finset.mem_range.mp (Finset.mem_filter.mp hj).1⟩, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩
  rw [hcard]
  exact perturbationKey_fiber_card_le_four mesh hP hk hunit hsmall a d hd key

end QuantitativeVanDerWaerden

end

end OAI
