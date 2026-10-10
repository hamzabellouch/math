import OAI.Analysis.MatrixScaling.Expansion
import OAI.Geometry.ComplexBundle.BundleIncidence
import OAI.Geometry.ComplexBundle.DirectSum
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Interval.Finset.Nat

namespace OAI

noncomputable section

/-! Quantitative bundle rank margins and repeated-line replacement maps. -/

namespace Kaplansky

theorem small_incidence (m s D : ℝ) (hm : 0 < m) (hs : 0 < s)
    (hsm : s ≤ m) (hD : 64*m ≤ D) :
    0 < (16*s-2*s)*(D/4-2*s)-s*(D-s) ∧
    133*m*s ≤ (16*s-2*s)*(D/4-2*s)-s*(D-s) := by
  have h1 := mul_le_mul_of_nonneg_right hD hs.le
  have h2 := mul_le_mul_of_nonneg_right hsm hs.le
  have h3 : 0 < m*s := mul_pos hm hs
  constructor <;> nlinarith

theorem small_rank_endpoint (m s D : ℝ) (hm : 0 < m)
    (hsm : s ≤ m) (hD : 64*m ≤ D) :
    2*s < D/4 ∧ D/8 ≤ D/4-2*s := by constructor <;> linarith

theorem large_incidence (m s d η : ℝ) (hm : 0 ≤ m) (hd : 0 < d)
    (hms : m < s) (hsd : s ≤ d) (hη : η < (20/3)*m*d) :
    2*s < (15/4)*d ∧ η < (8*s-2*s)*(15*d/4-2*s)-s*(d-s) := by
  have hs : 0 < s := lt_of_le_of_lt hm hms
  have h1 := mul_le_mul_of_nonneg_right hsd hs.le
  have h2 := mul_lt_mul_of_pos_right hms hd
  have h3 := mul_nonneg hm hd.le
  constructor <;> nlinarith

theorem replacement_rank (d : ℝ) : d/4 + (15/4)*d = 4*d := by ring

theorem prefix_dimension_margin (m d₀ q : ℝ) (hm : 0 < m) (hd : 0 < d₀) :
    (5/3)*m*d₀*(4*q-1) < (20/3)*m*(d₀*q) := by
  nlinarith [mul_pos hm hd]

theorem retained_trivial_rank_bound (m d₀ e : ℝ) (hm : 0 < m) (hd : 0 < d₀)
    (he : 0 ≤ e) : (4/3)*m*d₀*(1-e) < 2*m*d₀ := by
  have h := mul_pos hm hd
  have h' := mul_nonneg h.le he
  nlinarith

end Kaplansky

namespace Kaplansky.Incidence

theorem fresh_incidence_dimension (m d r N s : ℕ) (hd : 0<d)
    (hr : 4*r=15*d) (hN : 3*N<40*m*d) (hms : m<s) (hsd : s≤d) :
    2*s≤r ∧ N+2*s*(d-s)+2*(2*s)*(r-2*s)<2*8*s*(r-2*s) := by
  have hrr : (r : ℝ)=15*(d : ℝ)/4 := by
    have hh : (4 : ℝ)*r=15*d := by exact_mod_cast hr
    linarith
  have hn : (N : ℝ)/2 < (20/3)*(m : ℝ)*d := by
    have hh : (3 : ℝ)*N<40*(m : ℝ)*d := by exact_mod_cast hN
    linarith
  obtain ⟨hep,hgap⟩ := Kaplansky.large_incidence (m : ℝ) (s : ℝ) (d : ℝ) ((N : ℝ)/2)
    (by positivity) (by exact_mod_cast hd) (by exact_mod_cast hms) (by exact_mod_cast hsd) hn
  have htr : 2*s≤r := by
    have hh : (2 : ℝ)*s<(r : ℝ) := by rw [hrr]; linarith
    exact le_of_lt (by exact_mod_cast hh)
  refine ⟨htr,?_⟩
  apply (Nat.cast_lt (α := ℝ)).mp
  push_cast [Nat.cast_sub hsd,Nat.cast_sub htr]
  rw [hrr]
  nlinarith

theorem source_incidence_dimension_iff {q d r s t h : ℕ} (hsd : s≤d) (htr : t≤r) :
    ((q : ℤ)*s-t)*(r-t)-(s : ℤ)*(d-s)>(h : ℤ) ↔
      2*h+2*s*(d-s)+2*t*(r-t)<2*q*s*(r-t) := by
  rw [← Int.ofNat_sub hsd,← Int.ofNat_sub htr]
  constructor
  · intro hh
    have hg : ((2*h+2*s*(d-s)+2*t*(r-t) : ℕ) : ℤ) <
        ((2*q*s*(r-t) : ℕ) : ℤ) := by
      push_cast
      nlinarith
    exact_mod_cast hg
  · intro hh
    have hg : ((2*h+2*s*(d-s)+2*t*(r-t) : ℕ) : ℤ) <
        ((2*q*s*(r-t) : ℕ) : ℤ) := by exact_mod_cast hh
    push_cast at hg
    nlinarith

end Kaplansky.Incidence

section
open Module
namespace Kaplansky.Incidence

theorem exists_sixteen_replacement_maps (m r : ℕ) (hm : 0<m) (hr : 16*m≤r) :
    ∃ T : MatrixTuple 16 (4*r) r, ∀ S : Submodule ℂ (Fin (4*r) → ℂ),
      finrank ℂ S≤m → 2*finrank ℂ S≤
        finrank ℂ (⨆ i, S.map (T i).toLinearMap : Submodule ℂ (Fin r → ℂ)) := by
  let pairs : Finset (ℕ × ℕ) := (Finset.Icc 1 m).image (fun s => (s,2*s))
  have hpairs : ∀ p ∈ pairs, p.1≤4*r ∧ p.2≤r ∧
      p.1*(4*r-p.1)+p.2*(r-p.2)<16*p.1*(r-p.2) := by
    intro p hp
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hp
    have hs1 : 1≤s := (Finset.mem_Icc.mp hs).1
    have hsm : s≤m := (Finset.mem_Icc.mp hs).2
    have hsd : s≤4*r := by omega
    have htr : 2*s≤r := by omega
    refine ⟨hsd,htr,?_⟩
    apply (point_dimension_inequality_iff (q := 16) hsd htr).mp
    have hi := (Kaplansky.small_incidence (m : ℝ) (s : ℝ) (4*(r : ℝ))
      (by exact_mod_cast hm) (by exact_mod_cast (show 0<s by omega)) (by exact_mod_cast hsm)
      (by exact_mod_cast (show 64*m≤4*r by omega))).1
    have hi' : 0<((16 : ℝ)*s-2*s)*(r-2*s)-(s : ℝ)*(4*r-s) := by
      convert hi using 1; ring
    exact_mod_cast hi'
  obtain ⟨T,hT⟩ := exists_point_incidence_tuple pairs hpairs
  refine ⟨T,fun S hS => ?_⟩
  by_cases hz : finrank ℂ S=0
  · simp [hz]
  · have hs1 : 1≤finrank ℂ S := by omega
    have hp : (finrank ℂ S,2*finrank ℂ S) ∈ pairs :=
      Finset.mem_image.mpr ⟨finrank ℂ S,Finset.mem_Icc.mpr ⟨hs1,hS⟩,rfl⟩
    exact (hT _ hp S rfl).le

end Kaplansky.Incidence

end

section
open Bundle Module Set
open scoped Topology Manifold ContDiff
namespace Kaplansky.Incidence
variable {X B : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [TopologicalSpace B] [ChartedSpace X B]
  [IsManifold 𝓘(ℝ,X) ∞ B] [T2Space B] [CompactSpace B]
  {d r : ℕ} (E F : B → Type*)
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (Fin d → ℂ) E)] [TopologicalSpace (TotalSpace (Fin r → ℂ) F)]
  [FiberBundle (Fin d → ℂ) E] [FiberBundle (Fin r → ℂ) F]
  [VectorBundle ℝ (Fin d → ℂ) E] [VectorBundle ℂ (Fin d → ℂ) E]
  [VectorBundle ℝ (Fin r → ℂ) F] [VectorBundle ℂ (Fin r → ℂ) F]
  [ContMDiffVectorBundle ∞ (Fin d → ℂ) E 𝓘(ℝ,X)]
  [ContMDiffVectorBundle ∞ (Fin r → ℂ) F 𝓘(ℝ,X)]

theorem exists_eight_fresh_bundle_maps (m : ℕ) (hd : 0<d)
    (hr : 4*r=15*d) (hbase : 3*finrank ℝ X<40*m*d) :
    ∃ T : Fin 8 → ∀ y, E y →L[ℂ] F y,
      (∀ i, ContMDiff 𝓘(ℝ,X) (𝓘(ℝ,X).prod 𝓘(ℝ,(Fin d → ℂ) →L[ℝ] (Fin r → ℂ))) ∞
        (fun y => TotalSpace.mk' ((Fin d → ℂ) →L[ℝ] (Fin r → ℂ)) y ((T i y).restrictScalars ℝ))) ∧
      ∀ y (S : Submodule ℂ (E y)), m<finrank ℂ S →
        2*finrank ℂ S≤finrank ℂ (⨆ i, S.map (T i y).toLinearMap : Submodule ℂ (F y)) := by
  classical
  let pairs : Finset (ℕ × ℕ) := (Finset.Icc (m+1) d).image (fun s => (s,2*s))
  have hpairs : ∀ p ∈ pairs, p.1≤d ∧ p.2≤r ∧
      finrank ℝ X+2*p.1*(d-p.1)+2*p.2*(r-p.2)<2*8*p.1*(r-p.2) := by
    intro p hp
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hms,hsd⟩ := Finset.mem_Icc.mp hs
    obtain ⟨htr,hgap⟩ := fresh_incidence_dimension m d r (finrank ℝ X) s hd hr hbase (by omega) hsd
    exact ⟨hsd,htr,hgap⟩
  obtain ⟨T,hT,hExp⟩ := exists_smooth_bundle_incidence_maps E F pairs hpairs
  refine ⟨T,hT,fun y S hS => ?_⟩
  let e := trivializationAt (Fin d → ℂ) E y
  let a := e.toPretrivialization.linearEquivAt ℂ y (mem_baseSet_trivializationAt (Fin d → ℂ) E y)
  have hsd : finrank ℂ S≤d := by
    have hh := (S.map a.toLinearMap).finrank_le
    simpa [a.finrank_map_eq,Module.finrank_pi_fintype] using hh
  have hp : (finrank ℂ S,2*finrank ℂ S) ∈ pairs :=
    Finset.mem_image.mpr ⟨finrank ℂ S,Finset.mem_Icc.mpr ⟨by omega,hsd⟩,rfl⟩
  exact (hExp y _ hp S rfl).le

end Kaplansky.Incidence

end

section
open scoped BigOperators
namespace Kaplansky
variable {d r n : ℕ} {L : Type*} [AddCommGroup L] [Module ℂ L]

/-- A scalar matrix tensored with the identity of a line fiber. This formula
uses only scalar multiplication, not a choice of a vector in that line. -/
def scalarTensor (T : (Fin d → ℂ) →ₗ[ℂ] (Fin r → ℂ)) :
    (Fin d → L) →ₗ[ℂ] (Fin r → L) where
  toFun v a := ∑ j, (T (Pi.single j 1) a) • v j
  map_add' v w := by funext a; simp [smul_add,Finset.sum_add_distrib]
  map_smul' c v := by
    funext a
    simp [Finset.smul_sum,smul_smul,mul_comm]

def lineCoordinates (e : L ≃ₗ[ℂ] ℂ) (d : ℕ) : (Fin d → L) ≃ₗ[ℂ] (Fin d → ℂ) where
  toFun v j := e (v j)
  invFun v j := e.symm (v j)
  left_inv v := by funext j; exact e.symm_apply_apply _
  right_inv v := by funext j; exact e.apply_symm_apply _
  map_add' v w := by funext j; exact map_add e _ _
  map_smul' c v := by funext j; exact map_smul e _ _

theorem scalarTensor_coordinates (T : (Fin d → ℂ) →ₗ[ℂ] (Fin r → ℂ))
    (e : L ≃ₗ[ℂ] ℂ) (v : Fin d → L) :
    lineCoordinates e r (scalarTensor T v)=T (lineCoordinates e d v) := by
  classical
  have hv : lineCoordinates e d v = ∑ j, e (v j) • Pi.single j 1 := by
    funext j
    simp [lineCoordinates,Pi.single_apply]
  rw [hv,map_sum]
  funext a
  simp [scalarTensor,lineCoordinates,map_sum,map_smul,Finset.sum_apply,mul_comm]

theorem scalarTensor_eq_conjugate (T : (Fin d → ℂ) →ₗ[ℂ] (Fin r → ℂ))
    (e : L ≃ₗ[ℂ] ℂ) :
    scalarTensor T=(lineCoordinates e r).symm.toLinearMap.comp
      (T.comp (lineCoordinates e d).toLinearMap) := by
  apply LinearMap.ext
  intro v
  apply (lineCoordinates e r).injective
  simpa using scalarTensor_coordinates T e v

/-- Tensoring an expanding scalar family with a line preserves expansion for
all subspaces, and the tensor maps themselves are independent of the frame. -/
theorem scalarTensor_expanding (m : ℕ) (T : Fin n → (Fin d → ℂ) →ₗ[ℂ] (Fin r → ℂ))
    (e : L ≃ₗ[ℂ] ℂ) (hT : ExpandingThrough m T) :
    ExpandingThrough m (fun i => scalarTensor (L := L) (T i)) := by
  have h := expandingThrough_equiv m T (lineCoordinates e d).symm (lineCoordinates e r).symm hT
  simpa only [LinearEquiv.symm_symm,← scalarTensor_eq_conjugate] using h

theorem exists_sixteen_line_replacement_maps (m r : ℕ) (hm : 0<m) (hr : 16*m≤r) :
    ∃ T : Incidence.MatrixTuple 16 (4*r) r,
      ∀ (L : Type*) [AddCommGroup L] [Module ℂ L] (_ : L ≃ₗ[ℂ] ℂ),
        ExpandingThrough m (fun i => scalarTensor (L := L) (T i).toLinearMap) := by
  obtain ⟨T,hT⟩ := Incidence.exists_sixteen_replacement_maps m r hm hr
  exact ⟨T,fun L _ _ e => scalarTensor_expanding m (fun i => (T i).toLinearMap) e hT⟩

/-- Rank one is enough; the line coordinate equivalence is constructed. -/
theorem scalarTensor_expanding_rank_one [FiniteDimensional ℂ L]
    (hL : Module.finrank ℂ L=1) (m : ℕ)
    (T : Fin n → (Fin d → ℂ) →ₗ[ℂ] (Fin r → ℂ)) (hT : ExpandingThrough m T) :
    ExpandingThrough m (fun i => scalarTensor (L := L) (T i)) := by
  obtain ⟨e⟩ := (FiniteDimensional.nonempty_linearEquiv_iff_finrank_eq
    (R := ℂ) (M := L) (M' := ℂ)).mpr (by simpa using hL)
  exact scalarTensor_expanding m T e hT

/-- Tensoring commutes with every linear change of line coordinates. -/
theorem scalarTensor_natural {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : (Fin d → ℂ) →ₗ[ℂ] (Fin r → ℂ)) (f : L →ₗ[ℂ] M) (v : Fin d → L) :
    (fun a => f (scalarTensor T v a))=scalarTensor T (fun j => f (v j)) := by
  funext a
  simp [scalarTensor,map_sum,map_smul]

/-- The actual replacement maps on a finite sum of line-multiplicity blocks
expand correlated subspaces. Each scalar family is constructed, not assumed. -/
theorem exists_line_block_replacements (k m : ℕ) (hm : 0<m) (r : Fin k → ℕ)
    (hr : ∀ j, 16*m≤r j) (L : Fin k → Type*)
    [∀ j, AddCommGroup (L j)] [∀ j, Module ℂ (L j)] [∀ j, FiniteDimensional ℂ (L j)]
    (hL : ∀ j, Module.finrank ℂ (L j)=1) :
    ∃ T : ∀ j, Incidence.MatrixTuple 16 (4*r j) (r j),
      ExpandingThrough m (blockDiagonal (fun j i => scalarTensor (L := L j) (T j i).toLinearMap)) := by
  choose T hT using fun j => Incidence.exists_sixteen_replacement_maps m (r j) hm (hr j)
  exact ⟨T,expandingThrough_blocks k m (fun j => Fin (4*r j) → L j)
    (fun j => Fin (r j) → L j) _
    (fun j => scalarTensor_expanding_rank_one (hL j) m (fun i => (T j i).toLinearMap) (hT j))⟩

end Kaplansky

end

section
open Bundle Module
open scoped Topology Manifold ContDiff
namespace Kaplansky

/-- The same scalar choices work simultaneously over every base point,
including for nontrivial line bundles; fiber coordinates are not input. -/
theorem exists_uniform_line_block_replacements {B : Type*}
    (k m : ℕ) (hm : 0<m) (r : Fin k → ℕ) (hr : ∀ j, 16*m≤r j)
    (L : Fin k → B → Type*)
    [∀ j x, AddCommGroup (L j x)] [∀ j x, Module ℂ (L j x)]
    [∀ j x, FiniteDimensional ℂ (L j x)]
    (hL : ∀ j x, finrank ℂ (L j x)=1) :
    ∃ T : ∀ j, Incidence.MatrixTuple 16 (4*r j) (r j),
      ∀ x, ExpandingThrough m
        (blockDiagonal (fun j i => scalarTensor (L := L j x) (T j i).toLinearMap)) := by
  choose T hT using fun j => Incidence.exists_sixteen_replacement_maps m (r j) hm (hr j)
  exact ⟨T,fun x => expandingThrough_blocks k m (fun j => Fin (4*r j) → L j x)
    (fun j => Fin (r j) → L j x) _
    (fun j => scalarTensor_expanding_rank_one (hL j x) m (fun i => (T j i).toLinearMap) (hT j))⟩

variable {X H B F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [TopologicalSpace H] (I : ModelWithCorners ℝ X H)
  [TopologicalSpace B] [ChartedSpace H B] [IsManifold I ∞ B]
  [T2Space B] [CompactSpace B]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  (E : B → Type*) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [∀ x, Module ℝ (E x)] [∀ x, IsScalarTower ℝ ℂ (E x)]
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle ℂ F E] [VectorBundle ℝ F E]
  [ContMDiffVectorBundle ∞ F E I]

omit [FiniteDimensional ℝ X] [IsManifold I ∞ B] [T2Space B] [CompactSpace B]
    [FiniteDimensional ℂ F] [∀ x, IsScalarTower ℝ ℂ (E x)] in
/-- The frame-independent tensor formula preserves smooth sections in every
output component. Thus the scalar tensor maps have the required local
smoothness; no smooth global frame for the line is assumed. -/
theorem scalarTensor_smooth_section_components {d r : ℕ}
    (T : (Fin d → ℂ) →ₗ[ℂ] (Fin r → ℂ)) (s : Fin d → ∀ x, E x)
    (hs : ∀ j, ContMDiff I (I.prod 𝓘(ℝ,F)) ∞
      (fun x => TotalSpace.mk' F x (s j x))) (a : Fin r) :
    ContMDiff I (I.prod 𝓘(ℝ,F)) ∞
      (fun x => TotalSpace.mk' F x (scalarTensor T (fun j => s j x) a)) :=
  sectionEvaluation_smooth I E s hs (fun j => T (Pi.single j 1) a)

end Kaplansky

end

section
open Bundle Topology
open scoped BigOperators
namespace Kaplansky
variable {B : Type*} [TopologicalSpace B] {k : ℕ}
  {J : Fin k → Type*} (C : ∀ s, VectorBundleCore ℂ B ℂ (J s))

abbrev RepeatedLineModel (D : Fin k → ℕ) := EuclideanSpace ℂ (Σ s, Fin (D s))

def repeatedLineCore (D : Fin k → ℕ) := finiteLineSumCore (fun a : Σ s, Fin (D s) => C a.1)

def repeatedLineFiberEquiv (D : Fin k → ℕ) (x : B) :
    (repeatedLineCore C D).Fiber x ≃ₗ[ℂ] (∀ s, Fin (D s) → (C s).Fiber x) where
  toFun v s a := (show RepeatedLineModel D from v) ⟨s,a⟩
  invFun v := WithLp.toLp 2 (fun a => v a.1 a.2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The actual bundle map obtained by tensoring each scalar block with its
line identity, expressed in the finite-sum core fibers. -/
def repeatedLineMap (D E : Fin k → ℕ)
    (T : ∀ s, (Fin (D s) → ℂ) →ₗ[ℂ] (Fin (E s) → ℂ)) (x : B) :
    (repeatedLineCore C D).Fiber x →ₗ[ℂ] (repeatedLineCore C E).Fiber x :=
  (repeatedLineFiberEquiv C E x).symm.toLinearMap.comp
    ((blockDiagonal (n := 1) (fun s _ => scalarTensor (L := (C s).Fiber x) (T s)) 0).comp
      (repeatedLineFiberEquiv C D x).toLinearMap)

@[simp] theorem repeatedLineMap_apply (D E : Fin k → ℕ)
    (T : ∀ s, (Fin (D s) → ℂ) →ₗ[ℂ] (Fin (E s) → ℂ)) (x : B)
    (v : (repeatedLineCore C D).Fiber x) (s : Fin k) (b : Fin (E s)) :
    (show RepeatedLineModel E from repeatedLineMap C D E T x v) ⟨s,b⟩ = ∑ a, T s (Pi.single a 1) b * (show RepeatedLineModel D from v) ⟨s,a⟩ := rfl

/-- The local chart formula is exactly the same scalar tensor expression.
In particular it contains no arbitrary choice of line frame. -/
theorem repeatedLineMap_chart (D E : Fin k → ℕ)
    (T : ∀ s, (Fin (D s) → ℂ) →ₗ[ℂ] (Fin (E s) → ℂ)) (x y : B)
    (v : (repeatedLineCore C D).Fiber y) (s : Fin k) (b : Fin (E s)) :
    ((trivializationAt (RepeatedLineModel E) (repeatedLineCore C E).Fiber x)
      ⟨y,repeatedLineMap C D E T y v⟩).2 ⟨s,b⟩ =
    ∑ a, T s (Pi.single a 1) b *
      ((trivializationAt (RepeatedLineModel D) (repeatedLineCore C D).Fiber x) ⟨y,v⟩).2 ⟨s,a⟩ := by
  change (C s).coordChange ((C s).indexAt y) ((C s).indexAt x) y
    (∑ a, T s (Pi.single a 1) b • (show RepeatedLineModel D from v) ⟨s,a⟩) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact map_smul _ _ _

/-- Componentwise smooth-section formulas alone do not establish this
claim: the map on the actual finite-sum total spaces is continuous. -/
theorem continuous_repeatedLineMap (D E : Fin k → ℕ)
    (T : ∀ s, (Fin (D s) → ℂ) →ₗ[ℂ] (Fin (E s) → ℂ)) :
    Continuous (fun z : TotalSpace (RepeatedLineModel D) (repeatedLineCore C D).Fiber =>
      TotalSpace.mk' (RepeatedLineModel E) z.proj (repeatedLineMap C D E T z.proj z.2)) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨(FiberBundle.continuous_proj _ _).continuousAt, ?_⟩
  have hc := ((trivializationAt (RepeatedLineModel D) (repeatedLineCore C D).Fiber z.proj).continuousAt
    FiberBundle.mem_trivializationAt_proj_source).snd
  have hpi := (EuclideanSpace.equiv (Σ s, Fin (D s)) ℂ).continuous.continuousAt.comp hc
  apply (EuclideanSpace.equiv (Σ s, Fin (E s)) ℂ).symm.continuous.continuousAt.comp
  apply continuousAt_pi.mpr
  rintro ⟨s,b⟩
  have h : ContinuousAt (fun w : TotalSpace (RepeatedLineModel D) (repeatedLineCore C D).Fiber =>
      ∑ a, T s (Pi.single a 1) b *
        ((trivializationAt (RepeatedLineModel D) (repeatedLineCore C D).Fiber z.proj) w).2 ⟨s,a⟩) z :=
    tendsto_finsetSum Finset.univ (fun a _ =>
    continuousAt_const.mul ((continuous_apply (⟨s,a⟩ : Σ s, Fin (D s))).continuousAt.comp hpi))
  exact h.congr (Filter.Eventually.of_forall (fun w =>
    (repeatedLineMap_chart C D E T z.proj w.proj w.2 s b).symm))

end Kaplansky

end

open Bundle Topology
namespace Kaplansky
variable {B : Type*} [TopologicalSpace B] {k : ℕ}
  {J : Fin k → Type*} (C : ∀ s, VectorBundleCore ℂ B ℂ (J s))

local instance (s : Fin k) (x : B) : FiniteDimensional ℂ ((C s).Fiber x) :=
  inferInstanceAs (FiniteDimensional ℂ ℂ)

/-- The constructed uniform scalar choices give continuous total-space
maps on the actual bundles and expand every small fiber subspace. -/
theorem exists_continuous_repeatedLine_replacements
    (m : ℕ) (hm : 0<m) (r : Fin k → ℕ) (hr : ∀ s, 16*m≤r s) :
    ∃ A : ∀ x, Fin 16 →
      (repeatedLineCore C (fun s => 4*r s)).Fiber x →ₗ[ℂ] (repeatedLineCore C r).Fiber x,
      (∀ i, Continuous (fun z : TotalSpace (RepeatedLineModel (fun s => 4*r s))
        (repeatedLineCore C (fun s => 4*r s)).Fiber =>
        TotalSpace.mk' (RepeatedLineModel r) z.proj (A z.proj i z.2))) ∧
      ∀ x, ExpandingThrough m (A x) := by
  obtain ⟨T,hT⟩ := exists_uniform_line_block_replacements k m hm r hr
    (fun s x => (C s).Fiber x) (fun _ _ => Module.finrank_self ℂ)
  let A := fun x i => repeatedLineMap C (fun s => 4*r s) r
    (fun s => (T s i).toLinearMap) x
  refine ⟨A,fun i => continuous_repeatedLineMap C _ _ _,?_⟩
  intro x
  have h := expandingThrough_equiv m _
    (repeatedLineFiberEquiv C (fun s => 4*r s) x).symm
    (repeatedLineFiberEquiv C r x).symm (hT x)
  exact h

end Kaplansky

end

end OAI
