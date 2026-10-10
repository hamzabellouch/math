import Mathlib
import OAI.Analysis.HardSphere.Collisions.BalancedInsertion
import OAI.Analysis.HardSphere.Orbitals.Bump

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere.CellOrbital
open MeasureTheory Set Filter PeriodicCutoff TightCutoff
open scoped ComplexConjugate

lemma dist_coord_le_torusDistance (L : Length) (x y : Torus L) (j : Fin 3) :
    dist (x j) (y j) ≤ torusDistance L x y := by
  calc
    _ = Real.sqrt (dist (x j) (y j)^2) := (Real.sqrt_sq (dist_nonneg)).symm
    _ ≤ _ := Real.sqrt_le_sqrt (Finset.single_le_sum
      (fun k _ ↦ sq_nonneg (dist (x k) (y k))) (Finset.mem_univ j))

def chi (L : Length) (δ : ℝ) (x y : Torus L) : ℝ := bump L (8*δ) x y ^ 2

def count {n : ℕ} (L : Length) (δ : ℝ) (x : Torus L) (X : Configuration n L) : ℝ :=
  ∑ i, chi L δ x (X i)

lemma chi_bounds (L : Length) (δ : ℝ) (x y : Torus L) : 0 ≤ chi L δ x y ∧ chi L δ x y ≤ 1 := by
  constructor
  · exact sq_nonneg _
  · change bump L (8*δ) x y ^ 2 ≤ 1
    nlinarith [(bump_bounds L (8*δ) x y).1,(bump_bounds L (8*δ) x y).2]

lemma chi_eq_one_of_reaches {L : Length} {δ r : ℝ} (hδ : 0<δ) (hrδ : r ≤ δ)
    (x z : Torus L) (hz : ∃ y∈tsupport (normalized L δ x).orbital, torusDistance L y z ≤ 2*r) :
    chi L δ x z=1 := by
  obtain ⟨y,hy,hyz⟩ := hz
  have hyn := TightCutoff.near_subset_box L.val hδ x (normalized_support hδ x hy)
  have hbox : z∈box L.val ((8*δ)/2) x := by
    intro j _
    change dist (z j) (x j) ≤ (8*δ)/2
    have hb : dist (y j) (x j) ≤ 2*δ := (Set.mem_univ_pi.mp hyn) j
    have hg := (dist_coord_le_torusDistance L y z j).trans hyz
    have ht := dist_triangle (z j) (y j) (x j)
    rw [dist_comm (z j) (y j)] at ht
    linarith
  rw [chi,bump_eq_one (by positivity) x hbox,one_pow]

lemma closeLabels_card_le_count {n : ℕ} {L : Length} {δ r : ℝ} (hδ : 0<δ) (hrδ : r ≤ δ)
    (x : Torus L) (X : Configuration n L) :
    ((closeLabels r (normalized L δ x) X).card : ℝ) ≤ count L δ x X := by
  classical
  calc
    _ = ∑ i∈closeLabels r (normalized L δ x) X, chi L δ x (X i) := by
      rw [Finset.sum_eq_card_nsmul (b:= (1:ℝ)) (fun i hi ↦ ?_)]
      · simp
      · exact chi_eq_one_of_reaches hδ hrδ x (X i) (Finset.mem_filter.mp hi).2
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun j _ _ ↦ (chi_bounds L δ x (X j)).1)

lemma orbitals_separated {S : Type*} {L : Length} {r : ℝ} (hr : r ≤ 1/100)
    (c : S → Torus L) (hc : ∀ z v, z≠v → 1 ≤ dist (c z) (c v)) :
    ∀ z v : S, z≠v → ∀ x : Torus L, (normalized L (1/100) (c v)).orbital x≠0 →
      ¬ ∃ y∈tsupport (normalized L (1/100) (c z)).orbital, torusDistance L y x ≤ 2*r := by
  intro z v hzv x hx ⟨y,hy,hyx⟩
  have hxb := TightCutoff.near_subset_box L.val (by norm_num : (0:ℝ)<1/100) (c v)
    (normalized_support (by norm_num) (c v) (subset_closure hx))
  have hyb := TightCutoff.near_subset_box L.val (by norm_num : (0:ℝ)<1/100) (c z)
    (normalized_support (by norm_num) (c z) hy)
  have hd : dist (c z) (c v) ≤ (6:ℝ)/100 := by
    apply (dist_pi_le_iff (by norm_num)).mpr
    intro j
    have hxj : dist (x j) (c v j) ≤ 2*(1/100) := Set.mem_univ_pi.mp hxb j
    have hyj : dist (y j) (c z j) ≤ 2*(1/100) := Set.mem_univ_pi.mp hyb j
    have hyxj := (dist_coord_le_torusDistance L y x j).trans hyx
    have ht := dist_triangle4 (c z j) (y j) (x j) (c v j)
    rw [dist_comm (c z j) (y j)] at ht
    linarith
  linarith [hc z v hzv]

theorem physical_deficiency : ∃ C B E : ℝ, 0<C ∧ 0<B ∧ 0<E ∧
    ∀ (S : Type) [Fintype S] [Nonempty S] [DecidableEq S]
      (n : ℕ) (L : Length) (r : ℝ), 0<r → r ≤ 1/100 → 0<n → 1/100 ≤ L.val →
    ∀ (g : Jet n L), IsGroundVector n L r g →
    ∀ (c : S → Torus L), (∀ z v, z≠v → 1 ≤ dist (c z) (c v)) →
    ∀ (k m : ℕ), C*B*(k+m)*r^3 ≤ 1/4 →
    ∀ u : Jet n L, u∈dirichletDomain n L r →
    (∀ᵐ X ∂volume, u.1 X≠0 → ∀ z, count L (1/100) (c z) X ≤ k) →
    m*Fintype.card S*(energy g/(n:ℝ)-C*(E+B*(k+m)*r))*‖u.1‖^2 ≤
      energy u-energy g*‖u.1‖^2 := by
  obtain ⟨C,hC,hdef⟩ := deficiency_penalty_cells
  obtain ⟨B,E,hB,hE,hw⟩ := uniform_orbitals
  refine ⟨C,B,E,hC,hB,hE,?_⟩
  intro S _ _ _ n L r hr hrδ hn hL g hg c hc k m hs u hu hk
  apply hdef S n L r hr hn g hg (fun z ↦ normalized L (1/100) (c z))
    (fun z ↦ (hw L hL (c z)).1) (fun z ↦ (hw L hL (c z)).2.1)
    (orbitals_separated hrδ c hc) k m B E
    (fun z ↦ (hw L hL (c z)).2.2.1) (fun z ↦ (hw L hL (c z)).2.2.2.1) hs u hu
  filter_upwards [hk] with X hX huX z
  exact_mod_cast (closeLabels_card_le_count (by norm_num) hrδ (c z) X).trans (hX huX z)

end HardSphere.CellOrbital

end

end OAI
