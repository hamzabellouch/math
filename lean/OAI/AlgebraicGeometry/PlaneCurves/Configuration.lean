import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import OAI.AlgebraicGeometry.PlaneCurves.AffineMultiplicity

namespace OAI

/-!
# Ordered distinct plane configurations and product Zariski geometry
-/

section

/-!
# Concrete projective configuration geometry

Source: manuscript §1, definition of `U_r` and the incidence loci.

Projective points are actual one-dimensional complex subspaces, represented by
the library's quotient of nonzero vectors. The product Zariski closed subsets
are defined by simultaneous multihomogeneous equations in all point coordinates.
This is not the topological product of the individual Zariski topologies.
-/

noncomputable section

namespace Nagata.ProjectiveGeometry

open scoped BigOperators

abbrev PlanePoint := Projectivization ℂ (Fin 3 → ℂ)

/-- The genuine set of ordered tuples of pairwise distinct plane points. -/
abbrev OrderedDistinctPoints (r : ℕ) :=
  {p : Fin r → PlanePoint // Function.Injective p}

/-- Explicit nonzero homogeneous coordinates `[1 : z : 0]`. -/
def affineLineVector (z : ℂ) : Fin 3 → ℂ :=
  fun j => if j = 0 then 1 else if j = 1 then z else 0

theorem affineLineVector_ne_zero (z : ℂ) : affineLineVector z ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [affineLineVector] at h0

def affineLinePoint (z : ℂ) : PlanePoint :=
  Projectivization.mk ℂ (affineLineVector z) (affineLineVector_ne_zero z)

theorem affineLinePoint_injective : Function.Injective affineLinePoint := by
  intro z w h
  obtain ⟨a, ha⟩ :=
    (Projectivization.mk_eq_mk_iff' ℂ (affineLineVector z) (affineLineVector w)
      (affineLineVector_ne_zero z) (affineLineVector_ne_zero w)).mp h
  have ha1 : a = 1 := by
    have h0 := congrFun ha 0
    simpa [affineLineVector] using h0
  have hwz : w = z := by
    have h1 := congrFun ha 1
    simpa [affineLineVector, ha1] using h1
  exact hwz.symm

/-- The ordered distinct tuple `[1 : i : 0]`, for `i = 0, ..., r-1`. -/
def standardConfiguration (r : ℕ) : OrderedDistinctPoints r :=
  ⟨fun i => affineLinePoint (i.val : ℂ), by
    intro i j h
    apply Fin.ext
    exact Nat.cast_injective (affineLinePoint_injective h)⟩

/-- The configuration domain is nonempty for every finite number of points. -/
theorem orderedDistinctPoints_nonempty (r : ℕ) : Nonempty (OrderedDistinctPoints r) :=
  ⟨standardConfiguration r⟩

/-- The standard two-dimensional affine chart `[1 : z₀ : z₁]`. -/
def affinePlaneVector (z : Fin 2 → ℂ) : Fin 3 → ℂ :=
  fun j => if j = 0 then 1 else if j = 1 then z 0 else z 1

theorem affinePlaneVector_ne_zero (z : Fin 2 → ℂ) : affinePlaneVector z ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [affinePlaneVector] at h0

def affinePlanePoint (z : Fin 2 → ℂ) : PlanePoint :=
  Projectivization.mk ℂ (affinePlaneVector z) (affinePlaneVector_ne_zero z)

theorem affinePlanePoint_injective : Function.Injective affinePlanePoint := by
  intro z w h
  obtain ⟨a, ha⟩ :=
    (Projectivization.mk_eq_mk_iff' ℂ (affinePlaneVector z) (affinePlaneVector w)
      (affinePlaneVector_ne_zero z) (affinePlaneVector_ne_zero w)).mp h
  have ha1 : a = 1 := by
    have h0 := congrFun ha 0
    simpa [affinePlaneVector] using h0
  have hzero : w 0 = z 0 := by
    have h1 := congrFun ha 1
    simpa [affinePlaneVector, ha1] using h1
  have hone : w 1 = z 1 := by
    have h2 := congrFun ha 2
    simpa [affinePlaneVector, ha1] using h2
  funext i
  refine Fin.cases hzero.symm ?_ i
  intro j
  have hj : j = 0 := Subsingleton.elim j 0
  subst j
  exact hone.symm

/-- An equation homogeneous separately in each block of three coordinates.
The support condition is the ordinary definition of multihomogeneity. -/
structure MultihomogeneousEquation (r : ℕ) where
  polynomial : MvPolynomial (Fin r × Fin 3) ℂ
  multidegree : Fin r → ℕ
  homogeneous : ∀ a ∈ polynomial.support, ∀ i,
    (∑ j : Fin 3, a (i, j)) = multidegree i

/-- Vanishing of a multihomogeneous equation on a tuple. Quantifying over
representatives makes independence of the chosen homogeneous coordinates
explicit in the definition. Such representatives exist for every point. -/
def equationVanishes {r : ℕ} (F : MultihomogeneousEquation r)
    (p : Fin r → PlanePoint) : Prop :=
  ∀ (v : Fin r → Fin 3 → ℂ) (hv : ∀ i, v i ≠ 0),
    (∀ i, Projectivization.mk ℂ (v i) (hv i) = p i) →
    MvPolynomial.eval (fun ij => v ij.1 ij.2) F.polynomial = 0

/-- The common zero loci of multihomogeneous equations: the algebraic
Zariski closed subsets of a product of projective planes. -/
def IsProductZariskiClosed {r : ℕ} (S : Set (Fin r → PlanePoint)) : Prop :=
  ∃ equations : Set (MultihomogeneousEquation r),
    ∀ p, p ∈ S ↔ ∀ F ∈ equations, equationVanishes F p

/-- Relative Zariski closedness on the open subset of distinct tuples. -/
def IsConfigurationZariskiClosed {r : ℕ}
    (S : Set (OrderedDistinctPoints r)) : Prop :=
  ∃ T : Set (Fin r → PlanePoint), IsProductZariskiClosed T ∧
    ∀ p, p ∈ S ↔ p.val ∈ T

theorem isProductZariskiClosed_univ (r : ℕ) :
    IsProductZariskiClosed (Set.univ : Set (Fin r → PlanePoint)) := by
  refine ⟨∅, ?_⟩
  simp

theorem isProductZariskiClosed_inter {r : ℕ}
    {S T : Set (Fin r → PlanePoint)}
    (hS : IsProductZariskiClosed S) (hT : IsProductZariskiClosed T) :
    IsProductZariskiClosed (S ∩ T) := by
  rcases hS with ⟨ES, hES⟩
  rcases hT with ⟨ET, hET⟩
  refine ⟨ES ∪ ET, ?_⟩
  intro p
  constructor
  · intro hp F hF
    rcases hF with hF | hF
    · exact (hES p).mp hp.1 F hF
    · exact (hET p).mp hp.2 F hF
  · intro hp
    exact ⟨(hES p).mpr (fun F hF => hp F (Or.inl hF)),
      (hET p).mpr (fun F hF => hp F (Or.inr hF))⟩

/-- There is an actual simultaneous nonzero representative for every tuple.
This rules out a vacuous representative quantifier in `equationVanishes`. -/
theorem representatives_exist {r : ℕ} (p : Fin r → PlanePoint) :
    ∃ (v : Fin r → Fin 3 → ℂ) (hv : ∀ i, v i ≠ 0),
      ∀ i, Projectivization.mk ℂ (v i) (hv i) = p i := by
  exact ⟨fun i => (p i).rep, fun i => (p i).rep_nonzero,
    fun i => Projectivization.mk_rep (p i)⟩

/-- Vanishing implies vanishing at the library's chosen representatives. -/
theorem equationVanishes_rep {r : ℕ} (F : MultihomogeneousEquation r)
    (p : Fin r → PlanePoint) (h : equationVanishes F p) :
    MvPolynomial.eval (fun ij => (p ij.1).rep ij.2) F.polynomial = 0 := by
  exact h (fun i => (p i).rep) (fun i => (p i).rep_nonzero)
    (fun i => Projectivization.mk_rep (p i))

/-- The constant equation `1 = 0`, of multidegree zero. -/
def oneEquation (r : ℕ) : MultihomogeneousEquation r where
  polynomial := 1
  multidegree := fun _ => 0
  homogeneous := by
    intro a ha i
    have ha0 : a = 0 := by simpa only [MvPolynomial.support_one, Finset.mem_singleton] using ha
    subst a
    simp

theorem not_equationVanishes_one (r : ℕ) (p : Fin r → PlanePoint) :
    ¬ equationVanishes (oneEquation r) p := by
  intro h
  have hrep := equationVanishes_rep (oneEquation r) p h
  simp [oneEquation] at hrep

theorem isProductZariskiClosed_empty (r : ℕ) :
    IsProductZariskiClosed (∅ : Set (Fin r → PlanePoint)) := by
  refine ⟨{oneEquation r}, ?_⟩
  intro p
  constructor
  · intro hp
    exact hp.elim
  · intro hp
    exact (not_equationVanishes_one r p (hp (oneEquation r) (Set.mem_singleton _))).elim

theorem isConfigurationZariskiClosed_empty (r : ℕ) :
    IsConfigurationZariskiClosed (∅ : Set (OrderedDistinctPoints r)) := by
  exact ⟨∅, isProductZariskiClosed_empty r, fun _ => Iff.rfl⟩

theorem configuration_empty_ne_univ (r : ℕ) :
    (∅ : Set (OrderedDistinctPoints r)) ≠ Set.univ := by
  intro h
  have hm : standardConfiguration r ∈ (∅ : Set (OrderedDistinctPoints r)) := by
    rw [h]
    trivial
  exact hm

/-- Each affine projective chart has exactly the two coordinates other than
its distinguished nonzero homogeneous coordinate. -/
abbrev ChartVariables (c : Fin 3) := {j : Fin 3 // j ≠ c}

/-- The equation of a projective form in the affine chart `X_c = 1`. -/
def dehomogenize (c : Fin 3) (F : MvPolynomial (Fin 3) ℂ) :
    MvPolynomial (ChartVariables c) ℂ :=
  MvPolynomial.eval₂ MvPolynomial.C
    (fun j => if h : j = c then 1 else MvPolynomial.X ⟨j, h⟩) F

/-- Coordinates of a projective point in chart `c`. This map is used only
when the chart coordinate is nonzero. -/
def chartCoordinates (c : Fin 3) (p : PlanePoint) : ChartVariables c → ℂ :=
  fun j => p.rep j.val / p.rep c

/-- Normalized affine coordinates do not depend on the representative chosen
by `Projectivization.rep`. -/
theorem chartCoordinates_mk (c : Fin 3) (v : Fin 3 → ℂ) (hv : v ≠ 0) :
    chartCoordinates c (Projectivization.mk ℂ v hv) =
      fun j : ChartVariables c => v j.val / v c := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hv
  funext j
  simp only [chartCoordinates, ← ha, Pi.smul_apply, Units.smul_def, smul_eq_mul]
  exact mul_div_mul_left _ _ a.ne_zero

theorem mk_rep_coordinate_ne_zero_iff (v : Fin 3 → ℂ) (hv : v ≠ 0) (c : Fin 3) :
    (Projectivization.mk ℂ v hv).rep c ≠ 0 ↔ v c ≠ 0 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hv
  rw [← ha]
  simp [Units.smul_def, smul_eq_mul, a.ne_zero]

/-- Algebraic vanishing order in every chart containing the point, using
powers of the genuine maximal ideal in the affine coordinate ring. -/
def multiplicityAtLeast (F : MvPolynomial (Fin 3) ℂ)
    (p : PlanePoint) (m : ℕ) : Prop :=
  ∀ c : Fin 3, p.rep c ≠ 0 →
    AffineMultiplicity.orderAtLeast (chartCoordinates c p) m (dehomogenize c F)

/-- Every point lies in one of the three ordinary affine charts. -/
theorem chart_exists (p : PlanePoint) : ∃ c : Fin 3, p.rep c ≠ 0 := by
  by_contra h
  apply p.rep_nonzero
  funext c
  exact Classical.not_not.mp (fun hc => h ⟨c, hc⟩)

theorem dehomogenize_mul (c : Fin 3) (F G : MvPolynomial (Fin 3) ℂ) :
    dehomogenize c (F * G) = dehomogenize c F * dehomogenize c G := by
  exact MvPolynomial.eval₂_mul _ _

theorem dehomogenize_C (c : Fin 3) (a : ℂ) :
    dehomogenize c (MvPolynomial.C a) = MvPolynomial.C a :=
  MvPolynomial.eval₂_C _ _ a

theorem dehomogenize_pow (c : Fin 3) (F : MvPolynomial (Fin 3) ℂ) (N : ℕ) :
    dehomogenize c (F ^ N) = dehomogenize c F ^ N := by
  exact MvPolynomial.eval₂_pow _ _

theorem multiplicityAtLeast_zero (F : MvPolynomial (Fin 3) ℂ)
    (p : PlanePoint) : multiplicityAtLeast F p 0 := by
  intro c hc
  exact AffineMultiplicity.orderAtLeast_zero _ _

theorem multiplicityAtLeast_mono {F : MvPolynomial (Fin 3) ℂ}
    {p : PlanePoint} {m n : ℕ} (h : multiplicityAtLeast F p n)
    (hmn : m ≤ n) : multiplicityAtLeast F p m := by
  intro c hc
  exact AffineMultiplicity.orderAtLeast_mono (h c hc) hmn

/-- Multiplication adds lower bounds in the actual affine coordinate rings. -/
theorem multiplicityAtLeast_mul {F G : MvPolynomial (Fin 3) ℂ}
    {p : PlanePoint} {m n : ℕ} (hF : multiplicityAtLeast F p m)
    (hG : multiplicityAtLeast G p n) : multiplicityAtLeast (F * G) p (m + n) := by
  intro c hc
  rw [dehomogenize_mul]
  exact AffineMultiplicity.orderAtLeast_mul (hF c hc) (hG c hc)

theorem multiplicityAtLeast_pow {F : MvPolynomial (Fin 3) ℂ}
    {p : PlanePoint} {m : ℕ} (hF : multiplicityAtLeast F p m) (N : ℕ) :
    multiplicityAtLeast (F ^ N) p (m * N) := by
  intro c hc
  rw [dehomogenize_pow]
  exact AffineMultiplicity.orderAtLeast_pow (hF c hc) N

end Nagata.ProjectiveGeometry

end
end

section

noncomputable section
namespace Nagata
open ProjectiveGeometry
open scoped BigOperators

/-- The strict, simultaneous Nagata inequality in homogeneous coordinates,
equivalent to the effective-cycle formulation `FullNagataEffectiveCurves`. -/
def FullNagata : Prop :=
  ∀ r : ℕ, 10 ≤ r →
    ∃ E : ℕ → Set (OrderedDistinctPoints r),
      (∀ n, IsConfigurationZariskiClosed (E n) ∧ E n ≠ Set.univ) ∧
      (∃ p : OrderedDistinctPoints r, ∀ n, p ∉ E n) ∧
      ∀ p : OrderedDistinctPoints r, (∀ n, p ∉ E n) →
        ∀ (d : ℕ), 1 ≤ d →
        ∀ F : MvPolynomial (Fin 3) ℂ, F ≠ 0 → F.IsHomogeneous d →
        ∀ m : Fin r → ℕ,
          (∀ i, multiplicityAtLeast F (p.val i) (m i)) →
          (∑ i, (m i : ℝ)) < (d : ℝ) * Real.sqrt (r : ℝ)

end Nagata

end
end

section

/-! # Explicit two-coordinate charts on products of projective planes -/

noncomputable section

namespace Nagata.ProjectiveGeometry

/-- Ordered enumeration of the two coordinates different from `c`. -/
def chartIndexEquiv (c : Fin 3) : Fin 2 ≃ ChartVariables c :=
  Equiv.ofBijective (fun j => ⟨c.succAbove j, Fin.succAbove_ne c j⟩) (by
    constructor
    · intro i j h
      exact Fin.succAbove_right_injective (congrArg Subtype.val h)
    · intro j
      obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq j.property
      exact ⟨i, Subtype.ext hi⟩)

@[simp] theorem chartIndexEquiv_val (c : Fin 3) (j : Fin 2) :
    (chartIndexEquiv c j).val = c.succAbove j := rfl

@[simp] theorem chartIndexEquiv_symm_succAbove (c : Fin 3) (j : Fin 2) :
    (chartIndexEquiv c).symm ⟨c.succAbove j, Fin.succAbove_ne c j⟩ = j :=
  (chartIndexEquiv c).symm_apply_apply j

def chartCoordinates₂ (c : Fin 3) (p : PlanePoint) : Fin 2 → ℂ :=
  fun j => chartCoordinates c p (chartIndexEquiv c j)

/-- The same genuine affine chart equation with its two variables enumerated
by `Fin 2`, for the finite jet matrix interface. -/
def chartDehomogenize₂ (c : Fin 3) (F : MvPolynomial (Fin 3) ℂ) :
    MvPolynomial (Fin 2) ℂ :=
  MvPolynomial.rename (chartIndexEquiv c).symm (dehomogenize c F)

/-- Identification with the direct two-variable chart substitution used by
the global homogeneous coefficient matrix. -/
theorem chartDehomogenize₂_eq_eval₂_insertNth (c : Fin 3)
    (F : MvPolynomial (Fin 3) ℂ) :
    chartDehomogenize₂ c F =
      MvPolynomial.eval₂ MvPolynomial.C (c.insertNth 1 MvPolynomial.X) F := by
  let e : MvPolynomial (Fin 3) ℂ →+* MvPolynomial (Fin 2) ℂ :=
    (MvPolynomial.rename (chartIndexEquiv c).symm).toRingHom.comp
      (MvPolynomial.eval₂Hom MvPolynomial.C
        (fun j => if h : j = c then 1 else MvPolynomial.X ⟨j, h⟩))
  have he : e = MvPolynomial.eval₂Hom MvPolynomial.C (c.insertNth 1 MvPolynomial.X) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [e]
    · intro j
      by_cases hj : j = c
      · subst j
        simp [e]
      · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
        simp [e]
  exact RingHom.congr_fun he F

theorem orderAtLeast_chartDehomogenize₂_iff (c : Fin 3) (p : PlanePoint)
    (F : MvPolynomial (Fin 3) ℂ) (m : ℕ) :
    AffineMultiplicity.orderAtLeast (chartCoordinates₂ c p) m (chartDehomogenize₂ c F) ↔
      AffineMultiplicity.orderAtLeast (chartCoordinates c p) m (dehomogenize c F) := by
  let e := (MvPolynomial.renameEquiv ℂ (chartIndexEquiv c).symm).toRingEquiv
  have he : ∀ f, MvPolynomial.eval (chartCoordinates₂ c p) (e f) =
      MvPolynomial.eval (chartCoordinates c p) f := by
    intro f
    change MvPolynomial.eval (chartCoordinates₂ c p)
      (MvPolynomial.rename (chartIndexEquiv c).symm f) = _
    rw [MvPolynomial.eval_rename]
    have hcoords : chartCoordinates₂ c p ∘ (chartIndexEquiv c).symm =
        chartCoordinates c p := by
      funext j
      simp [chartCoordinates₂]
    rw [hcoords]
  exact AffineMultiplicity.orderAtLeast_equiv_iff
    (chartCoordinates c p) (chartCoordinates₂ c p) e he m (dehomogenize c F)

def chartVector₂ (c : Fin 3) (z : Fin 2 → ℂ) : Fin 3 → ℂ := c.insertNth 1 z

theorem chartVector₂_ne_zero (c : Fin 3) (z : Fin 2 → ℂ) : chartVector₂ c z ≠ 0 := by
  intro h
  have hc := congrFun h c
  simp [chartVector₂] at hc

def chartPoint₂ (c : Fin 3) (z : Fin 2 → ℂ) : PlanePoint :=
  Projectivization.mk ℂ (chartVector₂ c z) (chartVector₂_ne_zero c z)

theorem chartPoint₂_coordinate_ne_zero (c : Fin 3) (z : Fin 2 → ℂ) :
    (chartPoint₂ c z).rep c ≠ 0 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ
    (chartVector₂ c z) (chartVector₂_ne_zero c z)
  have hcoord : (chartPoint₂ c z).rep c = (a : ℂ) := by
    change (Projectivization.mk ℂ (chartVector₂ c z) (chartVector₂_ne_zero c z)).rep c = _
    rw [← ha]
    simp [chartVector₂, Units.smul_def]
  rw [hcoord]
  exact a.ne_zero

theorem chartCoordinates₂_chartPoint₂ (c : Fin 3) (z : Fin 2 → ℂ) :
    chartCoordinates₂ c (chartPoint₂ c z) = z := by
  funext j
  change chartCoordinates c (Projectivization.mk ℂ (chartVector₂ c z)
    (chartVector₂_ne_zero c z)) (chartIndexEquiv c j) = z j
  rw [chartCoordinates_mk]
  simp [chartVector₂]

theorem chartPoint₂_injective (c : Fin 3) : Function.Injective (chartPoint₂ c) := by
  intro z w h
  have hcoords := congrArg (chartCoordinates₂ c) h
  simpa only [chartCoordinates₂_chartPoint₂] using hcoords

theorem chartPoint₂_chartCoordinates₂ (c : Fin 3) (p : PlanePoint)
    (hc : p.rep c ≠ 0) : chartPoint₂ c (chartCoordinates₂ c p) = p := by
  apply Eq.trans ?_ (Projectivization.mk_rep p)
  apply (Projectivization.mk_eq_mk_iff' ℂ
    (chartVector₂ c (chartCoordinates₂ c p)) p.rep
    (chartVector₂_ne_zero c (chartCoordinates₂ c p)) p.rep_nonzero).mpr
  refine ⟨(p.rep c)⁻¹, ?_⟩
  funext j
  by_cases hj : j = c
  · subst j
    simp [chartVector₂, hc]
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
    simp [chartVector₂, chartCoordinates₂, chartCoordinates, div_eq_mul_inv, mul_comm]

abbrev ConfigurationChart (r : ℕ) := Fin r → Fin 3

def InConfigurationChart {r : ℕ} (c : ConfigurationChart r)
    (p : Fin r → PlanePoint) : Prop := ∀ i, (p i).rep (c i) ≠ 0

/-- Explicit affine coordinates in a simultaneous product chart. -/
def configurationChartCoordinates₂ {r : ℕ} (c : ConfigurationChart r)
    (p : Fin r → PlanePoint) : Fin r × Fin 2 → ℂ :=
  fun ij => (p ij.1).rep ((c ij.1).succAbove ij.2) / (p ij.1).rep (c ij.1)

def configurationChartEmbedding {r : ℕ} (c : ConfigurationChart r)
    (z : Fin r × Fin 2 → ℂ) : Fin r → PlanePoint :=
  fun i => chartPoint₂ (c i) (fun j => z (i, j))

theorem configurationChartEmbedding_mem {r : ℕ} (c : ConfigurationChart r)
    (z : Fin r × Fin 2 → ℂ) : InConfigurationChart c (configurationChartEmbedding c z) :=
  fun i => chartPoint₂_coordinate_ne_zero (c i) (fun j => z (i, j))

theorem configurationChartCoordinates₂_embedding {r : ℕ} (c : ConfigurationChart r)
    (z : Fin r × Fin 2 → ℂ) :
    configurationChartCoordinates₂ c (configurationChartEmbedding c z) = z := by
  funext ij
  exact congrFun (chartCoordinates₂_chartPoint₂ (c ij.1) (fun j => z (ij.1, j))) ij.2

theorem configurationChartEmbedding_coordinates {r : ℕ} (c : ConfigurationChart r)
    (p : Fin r → PlanePoint) (hp : InConfigurationChart c p) :
    configurationChartEmbedding c (configurationChartCoordinates₂ c p) = p := by
  funext i
  exact chartPoint₂_chartCoordinates₂ (c i) (p i) (hp i)

theorem configurationChartEmbedding_injective {r : ℕ} (c : ConfigurationChart r) :
    Function.Injective (configurationChartEmbedding c) := by
  intro x y h
  have hcoords := congrArg (configurationChartCoordinates₂ c) h
  simpa only [configurationChartCoordinates₂_embedding] using hcoords

theorem range_configurationChartEmbedding {r : ℕ} (c : ConfigurationChart r) :
    Set.range (configurationChartEmbedding c) = {p | InConfigurationChart c p} := by
  ext p
  constructor
  · rintro ⟨z, rfl⟩
    exact configurationChartEmbedding_mem c z
  · intro hp
    exact ⟨configurationChartCoordinates₂ c p, configurationChartEmbedding_coordinates c p hp⟩

theorem configurationChartCoordinates₂_eq {r : ℕ} (c : ConfigurationChart r)
    (p : Fin r → PlanePoint) (i : Fin r) (j : Fin 2) :
    configurationChartCoordinates₂ c p (i, j) =
      chartCoordinates (c i) (p i) (chartIndexEquiv (c i) j) := rfl

/-- The simultaneous charts cover every actual projective tuple. -/
theorem configurationChart_cover {r : ℕ} (p : Fin r → PlanePoint) :
    ∃ c : ConfigurationChart r, InConfigurationChart c p := by
  let c : Fin r → Fin 3 := fun i => Classical.choose (chart_exists (p i))
  exact ⟨c, fun i => Classical.choose_spec (chart_exists (p i))⟩

end Nagata.ProjectiveGeometry

end
end

section

/-!
# Multihomogeneous equations on the actual product of projective planes

Block scaling is proved directly from polynomial coefficients and the prescribed
multidegrees. Consequently the common-zero-locus definition can be checked on
any simultaneous homogeneous representatives.
-/

noncomputable section

namespace Nagata.ProjectiveGeometry

open scoped BigOperators

theorem multihomogeneous_eval_scale {r : ℕ} (F : MultihomogeneousEquation r)
    (a : Fin r → ℂ) (v : Fin r × Fin 3 → ℂ) :
    MvPolynomial.eval (fun ij => a ij.1 * v ij) F.polynomial =
      (∏ i : Fin r, a i ^ F.multidegree i) * MvPolynomial.eval v F.polynomial := by
  classical
  simp only [MvPolynomial.eval_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  simp only [mul_pow, Finset.prod_mul_distrib]
  have hprod : (∏ ij : Fin r × Fin 3, a ij.1 ^ u ij) =
      ∏ i : Fin r, a i ^ F.multidegree i := by
    rw [Fintype.prod_prod_type]
    apply Finset.prod_congr rfl
    intro i hi
    change (∏ j : Fin 3, a i ^ u (i, j)) = a i ^ F.multidegree i
    rw [Finset.prod_pow_eq_pow_sum, F.homogeneous u hu i]
  rw [hprod]
  ac_rfl

/-- Vanishing on one chosen representative is equivalent to the intrinsic
representative-independent definition used in the configuration Zariski sets. -/
theorem equationVanishes_iff_eval_rep {r : ℕ} (F : MultihomogeneousEquation r)
    (p : Fin r → PlanePoint) :
    equationVanishes F p ↔
      MvPolynomial.eval (fun ij => (p ij.1).rep ij.2) F.polynomial = 0 := by
  constructor
  · exact equationVanishes_rep F p
  · intro hrep v hv hp
    have hex : ∀ i : Fin r, ∃ a : ℂ, a • (p i).rep = v i := by
      intro i
      apply (Projectivization.mk_eq_mk_iff' ℂ (v i) (p i).rep
        (hv i) (p i).rep_nonzero).mp
      exact (hp i).trans (Projectivization.mk_rep (p i)).symm
    let a : Fin r → ℂ := fun i => Classical.choose (hex i)
    have ha : ∀ i, a i • (p i).rep = v i := fun i => Classical.choose_spec (hex i)
    have hv_eq : (fun ij : Fin r × Fin 3 => v ij.1 ij.2) =
        fun ij => a ij.1 * (p ij.1).rep ij.2 := by
      funext ij
      simpa only [Pi.smul_apply, smul_eq_mul] using (congrFun (ha ij.1) ij.2).symm
    rw [hv_eq, multihomogeneous_eval_scale, hrep, mul_zero]

theorem equationVanishes_iff_eval_mk {r : ℕ} (F : MultihomogeneousEquation r)
    (v : Fin r → Fin 3 → ℂ) (hv : ∀ i, v i ≠ 0) :
    equationVanishes F (fun i => Projectivization.mk ℂ (v i) (hv i)) ↔
      MvPolynomial.eval (fun ij => v ij.1 ij.2) F.polynomial = 0 := by
  constructor
  · intro h
    exact h v hv (fun _ => rfl)
  · intro h
    rw [equationVanishes_iff_eval_rep]
    have hex : ∀ i, ∃ a : ℂˣ, a • v i =
        (Projectivization.mk ℂ (v i) (hv i)).rep :=
      fun i => Projectivization.exists_smul_eq_mk_rep ℂ (v i) (hv i)
    let a : Fin r → ℂˣ := fun i => Classical.choose (hex i)
    have ha := fun i => Classical.choose_spec (hex i)
    have heq : (fun ij : Fin r × Fin 3 =>
        (Projectivization.mk ℂ (v ij.1) (hv ij.1)).rep ij.2) =
        fun ij => (a ij.1 : ℂ) * v ij.1 ij.2 := by
      funext ij
      simpa only [a, Pi.smul_apply, Units.smul_def, smul_eq_mul] using
        (congrFun (ha ij.1) ij.2).symm
    rw [heq, multihomogeneous_eval_scale F (fun i => (a i : ℂ))
      (fun ij => v ij.1 ij.2), h, mul_zero]

end Nagata.ProjectiveGeometry

end
end

end OAI
