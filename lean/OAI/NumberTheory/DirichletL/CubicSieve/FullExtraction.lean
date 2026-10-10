import OAI.NumberTheory.DirichletL.CubicSieve.Elements

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

def firstImage (R : Finset O) : Finset (Ideal O) :=
  R.image (fun z => goodPart (firstPart (Ideal.span {z})))
def secondImage (R : Finset O) : Finset (Ideal O) :=
  R.image (fun z => goodPart (secondPart (Ideal.span {z})))
def cubeImage (R : Finset O) : Finset (Ideal O) :=
  R.image (fun z => cubePart (Ideal.span {z}))

def sourceFactor (R : Finset O)
    (d : Oˣ × CanonicalQuadraticSieve.fixedBadPrimes.powerset ×
      CanonicalQuadraticSieve.fixedBadPrimes.powerset × cubeImage R) : O :=
  d.1.val * idealGenerator d.2.2.2.val ^ 3 *
    (idealGenerator (∏ P ∈ d.2.1.val, P) * idealGenerator (∏ P ∈ d.2.2.1.val, P) ^ 2)

theorem full_element_extraction_energy {n : Type*} [Fintype n] [DecidableEq n]
    (R : Finset O) (hR : ∀ z ∈ R, z ≠ 0)
    (cols : n → Ideal O) (hc : ∀ j, primaryGenerator (cols j) ≠ 0) (coef : n → ℂ) :
    (∑ z ∈ R, ‖∑ j, coef j * elementCharacter (cols j) (hc j) z‖ ^ 2) ≤
      (96 : ℝ) * (cubeImage R).card *
        min ((secondImage R).card * squaredNorm
            (fun (i : firstImage R) j => idealKernel (cols j) i.val))
          ((firstImage R).card * squaredNorm
            (fun (k : secondImage R) j => idealKernel (cols j) k.val)) *
        ∑ j, ‖coef j‖ ^ 2 := by
  let : Finite Oˣ := PrimaryIdealUnitReindex.finite_units
  let : Fintype Oˣ := Fintype.ofFinite _
  let D := Oˣ × CanonicalQuadraticSieve.fixedBadPrimes.powerset ×
    CanonicalQuadraticSieve.fixedBadPrimes.powerset × cubeImage R
  let T := D × secondImage R × firstImage R
  let reconstruct : T → O := fun p => primaryGenerator p.2.2.val *
    primaryGenerator p.2.1.val ^ 2 * sourceFactor R p.1
  let E : O → ℝ := fun z => ‖∑ j, coef j * elementCharacter (cols j) (hc j) z‖ ^ 2
  have hcover : R ⊆ Finset.univ.image reconstruct := by
    intro z hz
    let I : Ideal O := Ideal.span {z}
    obtain ⟨u, hu⟩ := element_cubic_extraction z (hR z hz)
    obtain ⟨e, he⟩ := badPart_sector (firstPart I)
    obtain ⟨f, hf⟩ := badPart_sector (secondPart I)
    let a : firstImage R := ⟨goodPart (firstPart I), Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩
    let b : secondImage R := ⟨goodPart (secondPart I), Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩
    let c : cubeImage R := ⟨cubePart I, Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩
    refine Finset.mem_image.mpr ⟨((u, e, f, c), b, a), Finset.mem_univ _, ?_⟩
    change primaryGenerator (goodPart (firstPart I)) *
      primaryGenerator (goodPart (secondPart I)) ^ 2 *
        (u.val * idealGenerator (cubePart I) ^ 3 *
          (idealGenerator (∏ P ∈ e.val, P) * idealGenerator (∏ P ∈ f.val, P) ^ 2)) = z
    rw [hu]
    change _ = u.val * extractedGenerator I
    unfold extractedGenerator
    rw [he, hf]
    ring
  have hsum : (∑ z ∈ R, E z) ≤ ∑ p : T, E (reconstruct p) := by
    calc
      _ ≤ ∑ z ∈ Finset.univ.image reconstruct, E z :=
        Finset.sum_le_sum_of_subset_of_nonneg hcover (fun _ _ _ => sq_nonneg _)
      _ ≤ _ := Finset.sum_image_le_of_nonneg (fun _ _ => sq_nonneg _)
  have hb := element_block_energy_le
    (fun i : firstImage R => i.val) (fun k : secondImage R => k.val)
    (sourceFactor R) cols hc coef
  have hcard : Fintype.card D = 96 * (cubeImage R).card := by
    have hu : Fintype.card Oˣ = 6 := by
      simpa only [Nat.card_eq_fintype_card] using PrimaryIdealUnitReindex.card_units_eq_six
    simp only [D, Fintype.card_prod, Fintype.card_coe, hu,
      CanonicalQuadraticSieve.fixedBadPrimes_powerset_card]
    omega
  have heq : (∑ p : T, E (reconstruct p)) =
      ∑ l : D, ∑ k : secondImage R, ∑ i : firstImage R,
        ‖∑ j, coef j * elementCharacter (cols j) (hc j)
          (primaryGenerator i.val * primaryGenerator k.val ^ 2 * sourceFactor R l)‖ ^ 2 := by
    simp only [T, Fintype.sum_prod_type, E, reconstruct]
  rw [heq] at hsum
  apply hsum.trans
  dsimp only [D] at hcard
  convert hb using 1
  simp only [hcard, Nat.cast_mul, Nat.cast_ofNat, Fintype.card_coe]

end
end SevenEighths.CubicSieve

end OAI
