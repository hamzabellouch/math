import OAI.LinearAlgebra.MatrixMultiplication.Recovery.InheritedMaskAction

namespace OAI

/-! Finite orbit symmetries, masks and exact recovery operations. -/

noncomputable section

namespace MatrixMultiplication.PermutationMatching

open MatrixMultiplication.InheritedMasks
open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

def fullOrbitFilter (G : Type*) {V : Type*} [SMul G V] [Fintype V]
    (v : V) : Finset V :=
  @Finset.filter V (fun w => ∃ g : G, g • v = w)
    (fun w => Classical.propDecidable (∃ g : G, g • v = w)) Finset.univ

def rejectedFilter {V : Type*} (orbit : Finset V) (bad : V → Prop) : Finset V :=
  @Finset.filter V bad (fun v => Classical.propDecidable (bad v)) orbit

theorem orbitSet_eq_fullOrbitFilter {G V : Type*} [Group G] [Fintype G]
    [MulAction G V] [Fintype V] [DecidableEq V] (v : V) :
    OrbitCounting.orbitSet (G := G) v = fullOrbitFilter G v := by
  ext w
  simp only [OrbitCounting.orbitSet, fullOrbitFilter, Finset.mem_image,
    Finset.mem_univ, true_and, Finset.mem_filter]

theorem rejectedFilter_congr {V : Type*} (orbit : Finset V) (p q : V → Prop)
    (h : ∀ v, p v ↔ q v) : rejectedFilter orbit p = rejectedFilter orbit q := by
  ext v
  simp only [rejectedFilter, Finset.mem_filter, h]

theorem fullOrbitFilter_bad_fraction_eq_orbit {G V : Type*}
    [Group G] [Fintype G] [MulAction G V] [Fintype V] [DecidableEq V]
    (w : V) (bad : V → Prop) [DecidablePred bad] :
    ((rejectedFilter (fullOrbitFilter G w) bad).card : ℝ) /
        (fullOrbitFilter G w).card =
      (((OrbitCounting.orbitSet (G := G) w).filter bad).card : ℝ) /
        (OrbitCounting.orbitSet (G := G) w).card := by
  have horbit := orbitSet_eq_fullOrbitFilter (G := G) w
  have hbad : (OrbitCounting.orbitSet (G := G) w).filter bad =
      rejectedFilter (fullOrbitFilter G w) bad := by
    ext v
    simp only [Finset.mem_filter, rejectedFilter, horbit]
  rw [hbad, horbit]

theorem orbit_bad_fraction_eq_fullOrbitFilter_of_iff {G V : Type*}
    [Group G] [Fintype G] [MulAction G V] [Fintype V] [DecidableEq V]
    (w : V) (bad canonical : V → Prop) [DecidablePred bad]
    (h : ∀ v, bad v ↔ canonical v) :
    (((OrbitCounting.orbitSet (G := G) w).filter bad).card : ℝ) /
        (OrbitCounting.orbitSet (G := G) w).card =
      ((rejectedFilter (fullOrbitFilter G w) canonical).card : ℝ) /
        (fullOrbitFilter G w).card := by
  rw [← fullOrbitFilter_bad_fraction_eq_orbit (G := G) w bad,
    rejectedFilter_congr (fullOrbitFilter G w) bad canonical h]

theorem full_orbitSet_as_filter {G V : Type*} [Group G] [Fintype G]
    [MulAction G V] [Fintype V] [DecidableEq V] (v : V) :
    OrbitCounting.orbitSet (G := G) v =
      Finset.univ.filter (fun w => ∃ g : G, g • v = w) := by
  ext w
  simp only [OrbitCounting.orbitSet, Finset.mem_image, Finset.mem_univ,
    true_and, Finset.mem_filter]

variable {C : Type*} {P X Y : C → Type*}
variable [Fintype C] [DecidableEq C]
  [∀ c, Fintype (P c)] [∀ c, DecidableEq (P c)]
  [Fintype (CompleteWordPair P X Y)]
variable {I : Type*} [Fintype I] {SL SR : I → C → Type*}

theorem finite_selectedWordPair_full_filter_inverse_linear_of_windows
    (D : I → Finset C) (w : CompleteWordPair P X Y)
    (sl : ∀ i c, X c → SL i c) (sr : ∀ i c, Y c → SR i c)
    (s : ∀ i c, SL i c) (t : ∀ i c, SR i c)
    (hn : ∀ i c, c ∈ D i → 2 ≤ Fintype.card (P c))
    (mass : I → ℝ) (N : ℝ) (hN : 0 < N) (hmass : ∀ i, 0 < mass i)
    (hsize : ∀ i, populationSize (fun c : D i => P c) = mass i * N)
    (left right : I → C → ℝ) (η τ α ν : I → ℝ) (hη : ∀ i, 0 < η i)
    (hright0 : ∀ i c, c ∈ D i → 0 ≤ right i c)
    (hright1 : ∀ i c, c ∈ D i → right i c ≤ 1)
    (hleft : ∀ i c, c ∈ D i →
      |classDensity (wordPairLeftPositions w (sl i) (s i)) c - left i c| ≤ τ i)
    (hright : ∀ i c, c ∈ D i →
      |classDensity (wordPairRightPositions w (sr i) (t i)) c - right i c| ≤ τ i)
    (happrox : ∀ i, |classProductMixture (fun c : D i => P c)
      (fun c => left i c) (fun c => right i c) - ν i| ≤ α i)
    (hτ : ∀ i, τ i ≤ η i / 8) (hα : ∀ i, α i ≤ η i / 4) :
    ((rejectedFilter (fullOrbitFilter (HalfClassPermutations P) w)
        (fun v => ∃ i, selectedWordPairMaskBad (D i) (sl i) (sr i)
          (s i) (t i) (η i) (ν i) v)).card : ℝ) /
      (fullOrbitFilter (HalfClassPermutations P) w).card ≤
        (∑ i, 1 / (2 * mass i * (η i) ^ 2)) / N := by
  classical
  have h := finite_selectedWordPair_orbit_inverse_linear_of_windows
    D w sl sr s t hn mass N hN hmass hsize left right η τ α ν hη
    hright0 hright1 hleft hright happrox hτ hα
  exact (fullOrbitFilter_bad_fraction_eq_orbit (G := HalfClassPermutations P) w _).trans_le h

end MatrixMultiplication.PermutationMatching

end

end OAI
