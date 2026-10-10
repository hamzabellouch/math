import OAI.Analysis.TreePotential.FiniteTree

namespace OAI

noncomputable section
open Set
open scoped ENNReal
namespace BoundedTreePotentials

section TestNorms
open scoped Classical
variable {I : Type*}

/-- A coefficient test family, before imposing any particular tree budget. -/
structure TestFamily (I : Type*) where
  carrier : Set (I → ℝ)
  zero_mem : (0 : I → ℝ) ∈ carrier
  neg_mem : ∀ f ∈ carrier, -f ∈ carrier
  coeff_bound : ∀ f ∈ carrier, ∀ i, |f i| ≤ 1
  singleton_mem : ∀ i, (fun j => if j = i then (1 : ℝ) else 0) ∈ carrier

instance : CoeSort (TestFamily I) (Type _) := ⟨fun K => K.carrier⟩
instance (K : TestFamily I) : Nonempty K.carrier := ⟨⟨0, K.zero_mem⟩⟩

def finitePairing (f : I → ℝ) : (I →₀ ℝ) →ₗ[ℝ] ℝ :=
  Finsupp.linearCombination ℝ f

lemma finitePairing_apply (f : I → ℝ) (x : I →₀ ℝ) :
    finitePairing f x = ∑ i ∈ x.support, x i * f i := rfl

lemma finitePairing_abs_bound (K : TestFamily I) (f : K) (x : I →₀ ℝ) :
    |finitePairing f.val x| ≤ ∑ i ∈ x.support, |x i| := by
  rw [finitePairing_apply]
  calc
    |∑ i ∈ x.support, x i * f.val i| ≤ ∑ i ∈ x.support, |x i * f.val i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ x.support, |x i| := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (K.coeff_bound _ f.property i)

def testNorm (K : TestFamily I) (x : I →₀ ℝ) : ℝ :=
  ⨆ f : K, |finitePairing f.val x|

lemma testNorm_bddAbove (K : TestFamily I) (x : I →₀ ℝ) :
    BddAbove (range fun f : K => |finitePairing f.val x|) :=
  ⟨∑ i ∈ x.support, |x i|, by rintro _ ⟨f, rfl⟩; exact finitePairing_abs_bound K f x⟩

lemma finitePairing_le_testNorm (K : TestFamily I) (f : K) (x : I →₀ ℝ) :
    |finitePairing f.val x| ≤ testNorm K x := le_ciSup (testNorm_bddAbove K x) f

lemma testNorm_nonneg (K : TestFamily I) (x : I →₀ ℝ) : 0 ≤ testNorm K x :=
  (abs_nonneg _).trans (finitePairing_le_testNorm K ⟨0, K.zero_mem⟩ x)

lemma testNorm_le_l1 (K : TestFamily I) (x : I →₀ ℝ) :
    testNorm K x ≤ ∑ i ∈ x.support, |x i| := by
  apply ciSup_le
  exact fun f => finitePairing_abs_bound K f x

@[simp] lemma testNorm_zero (K : TestFamily I) : testNorm K 0 = 0 := by
  apply le_antisymm
  · simpa using testNorm_le_l1 K 0
  · exact testNorm_nonneg K 0

lemma testNorm_add_le (K : TestFamily I) (x y : I →₀ ℝ) :
    testNorm K (x + y) ≤ testNorm K x + testNorm K y := by
  apply ciSup_le
  intro f
  rw [map_add]
  exact (abs_add_le _ _).trans (add_le_add
    (finitePairing_le_testNorm K f x) (finitePairing_le_testNorm K f y))

lemma testNorm_smul_le (K : TestFamily I) (a : ℝ) (x : I →₀ ℝ) :
    testNorm K (a • x) ≤ ‖a‖ * testNorm K x := by
  apply ciSup_le
  intro f
  rw [map_smul, smul_eq_mul, abs_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (finitePairing_le_testNorm K f x) (abs_nonneg a)

attribute [-simp] testNorm_zero in
def testSeminorm (K : TestFamily I) : Seminorm ℝ (I →₀ ℝ) := by
  have finitePairing_apply (f : I → ℝ) (x : I →₀ ℝ) :
      finitePairing f x = ∑ i ∈ x.support, x i * f i := rfl
  have finitePairing_abs_bound (K : TestFamily I) (f : K) (x : I →₀ ℝ) :
      |finitePairing f.val x| ≤ ∑ i ∈ x.support, |x i| := by
    rw [finitePairing_apply]
    calc
      |∑ i ∈ x.support, x i * f.val i| ≤ ∑ i ∈ x.support, |x i * f.val i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ x.support, |x i| := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (K.coeff_bound _ f.property i)
  have testNorm_bddAbove (K : TestFamily I) (x : I →₀ ℝ) :
      BddAbove (range fun f : K => |finitePairing f.val x|) :=
    ⟨∑ i ∈ x.support, |x i|, by rintro _ ⟨f, rfl⟩; exact finitePairing_abs_bound K f x⟩
  have finitePairing_le_testNorm (K : TestFamily I) (f : K) (x : I →₀ ℝ) :
      |finitePairing f.val x| ≤ testNorm K x := le_ciSup (testNorm_bddAbove K x) f
  have testNorm_nonneg (K : TestFamily I) (x : I →₀ ℝ) : 0 ≤ testNorm K x :=
    (abs_nonneg _).trans (finitePairing_le_testNorm K ⟨0, K.zero_mem⟩ x)
  have testNorm_le_l1 (K : TestFamily I) (x : I →₀ ℝ) :
      testNorm K x ≤ ∑ i ∈ x.support, |x i| := by
    apply ciSup_le
    exact fun f => finitePairing_abs_bound K f x
  have testNorm_zero (K : TestFamily I) : testNorm K 0 = 0 := by
    apply le_antisymm
    · simpa using testNorm_le_l1 K 0
    · exact testNorm_nonneg K 0
  have testNorm_add_le (K : TestFamily I) (x y : I →₀ ℝ) :
      testNorm K (x + y) ≤ testNorm K x + testNorm K y := by
    apply ciSup_le
    intro f
    rw [map_add]
    exact (abs_add_le _ _).trans (add_le_add
      (finitePairing_le_testNorm K f x) (finitePairing_le_testNorm K f y))
  have testNorm_smul_le (K : TestFamily I) (a : ℝ) (x : I →₀ ℝ) :
      testNorm K (a • x) ≤ ‖a‖ * testNorm K x := by
    apply ciSup_le
    intro f
    rw [map_smul, smul_eq_mul, abs_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (finitePairing_le_testNorm K f x) (abs_nonneg a)
  exact Seminorm.ofSMulLE (testNorm K) (testNorm_zero K) (testNorm_add_le K) (testNorm_smul_le K)

lemma finitePairing_single_test (x : I →₀ ℝ) (i : I) :
    finitePairing (fun j => if j = i then (1 : ℝ) else 0) x = x i := by
  classical
  rw [finitePairing_apply]
  simp only [mul_ite, mul_one, mul_zero]
  by_cases hi : i ∈ x.support
  · simp [hi]
  · simp [hi, Finsupp.notMem_support_iff.mp hi]

lemma coordinate_le_testNorm (K : TestFamily I) (x : I →₀ ℝ) (i : I) :
    |x i| ≤ testNorm K x := by
  convert finitePairing_le_testNorm K ⟨_, K.singleton_mem i⟩ x using 1
  rw [finitePairing_single_test]

lemma testNorm_eq_zero (K : TestFamily I) (x : I →₀ ℝ) : testNorm K x = 0 ↔ x = 0 := by
  constructor
  · intro h
    ext i
    exact abs_nonpos_iff.mp (h ▸ coordinate_le_testNorm K x i)
  · rintro rfl
    exact testNorm_zero K

/-- c00(I) with its actual test norm, not the ambient `Finsupp` topology. -/
def TestVector (_ : TestFamily I) := I →₀ ℝ

instance (K : TestFamily I) : AddCommGroup (TestVector K) := inferInstanceAs (AddCommGroup (I →₀ ℝ))
instance (K : TestFamily I) : Module ℝ (TestVector K) := inferInstanceAs (Module ℝ (I →₀ ℝ))
instance (K : TestFamily I) : Norm (TestVector K) := ⟨testNorm K⟩

theorem testVectorCore (K : TestFamily I) : NormedSpace.Core ℝ (TestVector K) where
  norm_nonneg := testNorm_nonneg K
  norm_smul := map_smul_eq_mul (testSeminorm K)
  norm_triangle := testNorm_add_le K
  norm_eq_zero_iff := testNorm_eq_zero K

instance (K : TestFamily I) : NormedAddCommGroup (TestVector K) := by
  have finitePairing_apply (f : I → ℝ) (x : I →₀ ℝ) :
      finitePairing f x = ∑ i ∈ x.support, x i * f i := rfl
  have finitePairing_abs_bound (K : TestFamily I) (f : K) (x : I →₀ ℝ) :
      |finitePairing f.val x| ≤ ∑ i ∈ x.support, |x i| := by
    rw [finitePairing_apply]
    calc
      |∑ i ∈ x.support, x i * f.val i| ≤ ∑ i ∈ x.support, |x i * f.val i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ x.support, |x i| := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (K.coeff_bound _ f.property i)
  have testNorm_bddAbove (K : TestFamily I) (x : I →₀ ℝ) :
      BddAbove (range fun f : K => |finitePairing f.val x|) :=
    ⟨∑ i ∈ x.support, |x i|, by rintro _ ⟨f, rfl⟩; exact finitePairing_abs_bound K f x⟩
  have finitePairing_le_testNorm (K : TestFamily I) (f : K) (x : I →₀ ℝ) :
      |finitePairing f.val x| ≤ testNorm K x := le_ciSup (testNorm_bddAbove K x) f
  have finitePairing_single_test (x : I →₀ ℝ) (i : I) :
      finitePairing (fun j => if j = i then (1 : ℝ) else 0) x = x i := by
    classical
    rw [finitePairing_apply]
    simp only [mul_ite, mul_one, mul_zero]
    by_cases hi : i ∈ x.support
    · simp [hi]
    · simp [hi, Finsupp.notMem_support_iff.mp hi]
  have coordinate_le_testNorm (K : TestFamily I) (x : I →₀ ℝ) (i : I) :
      |x i| ≤ testNorm K x := by
    convert finitePairing_le_testNorm K ⟨_, K.singleton_mem i⟩ x using 1
    rw [finitePairing_single_test]
  exact NormedAddCommGroup.ofCore (𝕜 := ℝ) {
    norm_nonneg := apply_nonneg (testSeminorm K)
    norm_smul := map_smul_eq_mul (testSeminorm K)
    norm_triangle := map_add_le_add (testSeminorm K)
    norm_eq_zero_iff := fun x => ⟨by
      intro h
      apply Finsupp.ext
      intro i
      exact abs_nonpos_iff.mp (h ▸ coordinate_le_testNorm K x i), by
      rintro rfl
      exact map_zero (testSeminorm K)⟩ }
instance (K : TestFamily I) : NormedSpace ℝ (TestVector K) where
  norm_smul_le a x := le_of_eq (map_smul_eq_mul (testSeminorm K) a x)

@[simp] lemma norm_TestVector (K : TestFamily I) (x : TestVector K) : ‖x‖ = testNorm K x := rfl

/-- Symmetry identifies the signed-evaluation supremum with the absolute-pairing norm. -/

theorem testNorm_signed_sup (K : TestFamily I) (x : I →₀ ℝ) :
    testNorm K x = ⨆ f : K, finitePairing f.val x := by
  have hb : BddAbove (range fun f : K => finitePairing f.val x) :=
    ⟨testNorm K x, by rintro _ ⟨f, rfl⟩; exact (le_abs_self _).trans (finitePairing_le_testNorm K f x)⟩
  apply le_antisymm
  · apply ciSup_le
    intro f
    rw [abs_le]
    constructor
    · have hn := le_ciSup hb (⟨-f.val, K.neg_mem _ f.property⟩ : K)
      have he : finitePairing (-f.val) x = -finitePairing f.val x := by
        simp only [finitePairing_apply, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
      rw [he] at hn
      linarith
    · exact le_ciSup hb f
  · apply ciSup_le
    intro f
    exact (le_abs_self _).trans (finitePairing_le_testNorm K f x)

end TestNorms


end BoundedTreePotentials

end

end OAI
