import OAI.Algebra.DepthFive.LocalOccupationAverage
import OAI.Algebra.DepthFive.FactorialGeometricValue

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335
namespace LocalMoments

variable {σ ι : Type*} [Fintype σ] [DecidableEq σ]

/-- The actual occupation average of the full local four-path table is bounded
by the product of its independent geometric local moments. -/
theorem partitionCompositionMean_localProduct_le
    (side : σ → Bool) [Nonempty {i // side i = true}] [Nonempty {i // ¬ side i = true}]
    (a b : ℕ) (layers : Finset ι) (derivative : ι → Bool) (p q r : ι → σ)
    (hp : ∀ t ∈ layers, side (p t) = derivative t)
    (hq : ∀ t ∈ layers, side (q t) = derivative t)
    (hr : ∀ t ∈ layers, side (r t) = derivative t)
    (hdis : (layers : Set ι).Pairwise fun i j =>
      Disjoint ({p i, q i, r i} : Finset σ) {p j, q j, r j}) :
    partitionCompositionMean side
      (fun M => ∏ t ∈ layers, localPolynomial (derivative t) M (p t) (q t) (r t)) a b ≤
      ∏ t ∈ layers, localGeometricMass (derivative t)
        (if derivative t = true then (a : ℝ) / Fintype.card {i // side i = true}
          else (b : ℝ) / Fintype.card {i // ¬ side i = true}) (p t) (q t) (r t) := by
  classical
  let G : σ → ℝ := fun i =>
    if side i = true then (a : ℝ) / Fintype.card {i // side i = true}
    else (b : ℝ) / Fintype.card {i // ¬ side i = true}
  let g : ι → ℝ := fun t =>
    if derivative t = true then (a : ℝ) / Fintype.card {i // side i = true}
    else (b : ℝ) / Fintype.card {i // ¬ side i = true}
  obtain ⟨F, hF⟩ := exists_localProduct_geometricValue_of_eq layers derivative p q r G g
    (by intro t ht; simp only [G, g, hp t ht])
    (by intro t ht; simp only [G, g, hq t ht])
    (by intro t ht; simp only [G, g, hr t ht]) hdis
  have hmean := F.partitionCompositionMean_le side a b
  change partitionCompositionMean side
    (fun M => (localProductNat layers derivative p q r M : ℝ)) a b ≤ F.geometricValue G at hmean
  rw [hF] at hmean
  simpa only [localProductNat_cast] using hmean

/-- Specialization to the matrix-layer coordinate shape: disjoint supports and
the common local mean are automatic, not additional analytic assumptions. -/
theorem partitionCompositionMean_layered_localProduct_le
    {κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (derivative : ι → Bool)
    [Nonempty {x : ι × κ // derivative x.1 = true}]
    [Nonempty {x : ι × κ // ¬ derivative x.1 = true}]
    (a b : ℕ) (layers : Finset ι) (p q r : ι → κ) :
    partitionCompositionMean (fun x : ι × κ => derivative x.1)
      (fun M => ∏ t ∈ layers, localPolynomial (derivative t) M
        (t, p t) (t, q t) (t, r t)) a b ≤
      ∏ t ∈ layers, localGeometricMass (derivative t)
        (if derivative t = true then
          (a : ℝ) / Fintype.card {x : ι × κ // derivative x.1 = true}
        else (b : ℝ) / Fintype.card {x : ι × κ // ¬ derivative x.1 = true})
        (t, p t) (t, q t) (t, r t) := by
  apply partitionCompositionMean_localProduct_le (fun x : ι × κ => derivative x.1)
    a b layers derivative (fun t => (t, p t)) (fun t => (t, q t)) (fun t => (t, r t))
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · exact layered_support_disjoint layers p q r

/-- Coordinate-form conversion to the local table used in the four-path identity. -/
@[simp] theorem localPolynomial_layered {κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (d : Bool) (M : ι × κ → ℕ) (t : ι) (p q r : κ) :
    localPolynomial d M (t, p) (t, q) (t, r) =
      localPolynomial d (fun x => M (t, x)) p q r := by
  simp [localPolynomial]

@[simp] theorem localGeometricMass_layered {κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (d : Bool) (G : ℝ) (t : ι) (p q r : κ) :
    localGeometricMass d G (t, p) (t, q) (t, r) = localGeometricMass d G p q r := by
  simp [localGeometricMass]

/-- Row-restriction presentation matching the actual four-path local table directly. -/
theorem partitionCompositionMean_layered_restrict_le
    {κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (derivative : ι → Bool)
    [Nonempty {x : ι × κ // derivative x.1 = true}]
    [Nonempty {x : ι × κ // ¬ derivative x.1 = true}]
    (a b : ℕ) (layers : Finset ι) (p q r : ι → κ) :
    partitionCompositionMean (fun x : ι × κ => derivative x.1)
      (fun M => ∏ t ∈ layers, localPolynomial (derivative t) (fun x => M (t, x))
        (p t) (q t) (r t)) a b ≤
      ∏ t ∈ layers, localGeometricMass (derivative t)
        (if derivative t = true then
          (a : ℝ) / Fintype.card {x : ι × κ // derivative x.1 = true}
        else (b : ℝ) / Fintype.card {x : ι × κ // ¬ derivative x.1 = true})
        (p t) (q t) (r t) := by
  simpa only [localPolynomial_layered, localGeometricMass_layered] using
    partitionCompositionMean_layered_localProduct_le derivative a b layers p q r

end LocalMoments
end Problem335

end

end OAI
