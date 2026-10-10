import Mathlib
import OAI.Analysis.WeakInfiniteness.Hereditary
import OAI.Analysis.WeakInfiniteness.RectangularCStar

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

local instance matrixRealModule {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {n : Type*} [Fintype n] :
    Module ℝ (CStarMatrix n n A) := Module.complexToReal _

section RectangularPolar

open scoped Topology CStarAlgebra

open Filter

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]

omit [PartialOrder A] [StarOrderedRing A] [Fintype m] [Fintype n] [Fintype k] in
lemma rectangular_continuous_conjTranspose :
    Continuous (fun M : CStarMatrix m n A => M.conjTranspose) := by
  change Continuous (fun M : Matrix m n A => M.conjTranspose)
  fun_prop

omit [PartialOrder A] [StarOrderedRing A] [Fintype m] [Fintype k] in
lemma rectangular_continuous_mul :
    Continuous (fun p : CStarMatrix m n A × CStarMatrix n k A => p.1*p.2) := by
  change Continuous (fun p : Matrix m n A × Matrix n k A => p.1*p.2)
  fun_prop

omit [PartialOrder A] [StarOrderedRing A] [Fintype m] [Fintype k] in
lemma rectangular_star_mul (M : CStarMatrix m n A) (N : CStarMatrix n k A) :
    (M*N).conjTranspose = N.conjTranspose*M.conjTranspose :=
  Matrix.conjTranspose_mul _ _

omit [PartialOrder A] [StarOrderedRing A] [Fintype m] in
lemma rectangular_mul_assoc {l : Type*} (L : CStarMatrix m n A)
    (M : CStarMatrix n k A) (N : CStarMatrix k l A) :
    (L*M)*N = L*(M*N) := Matrix.mul_assoc _ _ _

omit [PartialOrder A] [StarOrderedRing A] [Fintype m] [Fintype k] in
def rectangularLeftMap (u : CStarMatrix m n A) :
    CStarMatrix n n A →ₗ[ℂ] CStarMatrix m n A where
  toFun b := u*b
  map_add' := CStarMatrix.mul_add u
  map_smul' c b := CStarMatrix.mul_smul u c b

omit [PartialOrder A] [StarOrderedRing A] [Fintype m] [Fintype k] in
def rectangularRightIdeal (u : CStarMatrix m n A) : Submodule ℂ (CStarMatrix m n A) :=
  (rectangularLeftMap u).range.topologicalClosure

omit [PartialOrder A] [StarOrderedRing A] in
lemma rectangular_initial_mul (u : CStarMatrix m n A) (b : CStarMatrix n n A) :
    (u*b).conjTranspose*(u*b) = star b*(u.conjTranspose*u)*b := by
  rw [rectangular_star_mul]
  simp only [rectangular_mul_assoc, CStarMatrix.star_eq_conjTranspose]

lemma rectangular_norm_mul_sqrt (u : CStarMatrix m n A) (b : CStarMatrix n n A) :
    ‖CFC.sqrt (u.conjTranspose*u)*b‖ = ‖u*b‖ := by
  have heq : star (CFC.sqrt (u.conjTranspose*u)*b)*(CFC.sqrt (u.conjTranspose*u)*b) =
      (u*b).conjTranspose*(u*b) := by
    rw [rectangular_initial_mul, star_mul, (CFC.sqrt_nonneg (u.conjTranspose*u)).star_eq]
    calc
      star b * CFC.sqrt (u.conjTranspose * u) * (CFC.sqrt (u.conjTranspose * u) * b) =
          star b * (CFC.sqrt (u.conjTranspose * u) * CFC.sqrt (u.conjTranspose * u)) * b := by
        noncomm_ring
      _ = star b*(u.conjTranspose*u)*b := by
        rw [CFC.sqrt_mul_sqrt_self _ (rectangular_initial_nonneg u)]
  have hn := congrArg norm heq
  rw [CStarRing.norm_star_mul_self, rectangular_norm_initial] at hn
  nlinarith [norm_nonneg (CFC.sqrt (u.conjTranspose*u)*b), norm_nonneg (u*b)]

def rectangularPolar (u : CStarMatrix m n A) :
    principalRightIdeal (CFC.sqrt (u.conjTranspose*u)) →L[ℂ] CStarMatrix m n A :=
  (rectangularLeftMap u).extendOfNorm (principalRightMap (CFC.sqrt (u.conjTranspose*u)))

lemma rectangularPolar_apply_mul (u : CStarMatrix m n A) (b : CStarMatrix n n A) :
    rectangularPolar u (principalRightMap (CFC.sqrt (u.conjTranspose*u)) b) = u*b := by
  apply LinearMap.extendOfNorm_eq (principalRightMap_dense _)
  refine ⟨1, fun c => ?_⟩
  change ‖u*c‖ ≤ 1*‖CFC.sqrt (u.conjTranspose*u)*c‖
  rw [one_mul, rectangular_norm_mul_sqrt]

lemma rectangularPolar_initial_square (u : CStarMatrix m n A)
    (a : principalRightIdeal (CFC.sqrt (u.conjTranspose*u))) :
    (rectangularPolar u a).conjTranspose*rectangularPolar u a = star (a : CStarMatrix n n A)*(a : CStarMatrix n n A) := by
  refine (principalRightMap_dense (CFC.sqrt (u.conjTranspose*u))).induction_on a ?_ ?_
  · apply isClosed_eq
    · exact rectangular_continuous_mul.comp
        ((rectangular_continuous_conjTranspose.comp (rectangularPolar u).continuous).prodMk
          (rectangularPolar u).continuous)
    · fun_prop
  · intro b
    rw [rectangularPolar_apply_mul]
    change (u*b).conjTranspose*(u*b) =
      star (CFC.sqrt (u.conjTranspose*u)*b)*(CFC.sqrt (u.conjTranspose*u)*b)
    rw [rectangular_initial_mul, star_mul, (CFC.sqrt_nonneg (u.conjTranspose*u)).star_eq]
    calc
      star b*(u.conjTranspose*u)*b =
          star b * (CFC.sqrt (u.conjTranspose*u)*CFC.sqrt (u.conjTranspose*u))*b := by
        rw [CFC.sqrt_mul_sqrt_self _ (rectangular_initial_nonneg u)]
      _ = star b*CFC.sqrt (u.conjTranspose*u)*(CFC.sqrt (u.conjTranspose*u)*b) := by
        noncomm_ring

lemma rectangularPolar_mem_rightIdeal (u : CStarMatrix m n A)
    (a : principalRightIdeal (CFC.sqrt (u.conjTranspose*u))) :
    rectangularPolar u a ∈ rectangularRightIdeal u := by
  refine (principalRightMap_dense (CFC.sqrt (u.conjTranspose*u))).induction_on a ?_ ?_
  · exact (Submodule.isClosed_topologicalClosure _).preimage (rectangularPolar u).continuous
  · intro b
    rw [rectangularPolar_apply_mul]
    exact Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ b)

lemma rectangular_exact_initial_of_domination (u : CStarMatrix m n A)
    (d : CStarMatrix n n A) (hd : 0 ≤ d) {c : ℝ} (hc : 0 ≤ c)
    (hdu : d ≤ c • (u.conjTranspose*u)) :
    ∃ r : CStarMatrix m n A, r.conjTranspose*r = d ∧ r ∈ rectangularRightIdeal u := by
  let a := CFC.sqrt d
  have ha : a*star a = d := by
    dsimp only [a]
    rw [(CFC.sqrt_nonneg d).star_eq, CFC.sqrt_mul_sqrt_self d hd]
  have hamem : a ∈ principalRightIdeal (CFC.sqrt (u.conjTranspose*u)) := by
    rw [principalRightIdeal_sqrt _ (rectangular_initial_nonneg u)]
    exact principalRightIdeal_of_square_le_smul _ a
      (rectangular_initial_nonneg u) hc (by rwa [ha])
  let a₀ : principalRightIdeal (CFC.sqrt (u.conjTranspose*u)) := ⟨a, hamem⟩
  refine ⟨rectangularPolar u a₀, ?_, rectangularPolar_mem_rightIdeal u a₀⟩
  rw [rectangularPolar_initial_square]
  change star a*a = d
  rw [show star a = a from (CFC.sqrt_nonneg d).star_eq]
  exact CFC.sqrt_mul_sqrt_self d hd

end RectangularPolar

section RectangularHereditary

open scoped Topology CStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {m n : Type*} [Fintype m] [Fintype n]

omit [PartialOrder A] [StarOrderedRing A] in
lemma rightIdeal_sandwich_mem_hereditary (h a b : A) (hh : IsSelfAdjoint h)
    (ha : a ∈ principalRightIdeal h) : a*b*star a ∈ hereditarySubalgebra h hh := by
  have hc : IsClosed {a : A | a*b*star a ∈ hereditarySubalgebra h hh} :=
    (NonUnitalStarSubalgebra.isClosed_topologicalClosure _).preimage (by fun_prop)
  apply closure_minimal _ hc ha
  rintro _ ⟨y, rfl⟩
  change (h*y)*b*star (h*y) ∈ hereditarySubalgebra h hh
  rw [star_mul, hh.star_eq]
  have he : (h*y)*b*(star y*h) = h*(y*b*star y)*h := by noncomm_ring
  rw [he]
  exact sandwich_mem h _ hh

omit [PartialOrder A] [StarOrderedRing A] in
lemma rectangular_range_mul (a : CStarMatrix m m A) (V : CStarMatrix m n A) :
    (a*V)*(a*V).conjTranspose = a*(V*V.conjTranspose)*star a := by
  rw [rectangular_star_mul]
  simp only [rectangular_mul_assoc, CStarMatrix.star_eq_conjTranspose]

lemma rectangularRightIdeal_range_mem_hereditary (h a : CStarMatrix m m A)
    (V : CStarMatrix m n A) (hh : IsSelfAdjoint h) (ha : a ∈ principalRightIdeal h)
    (r : CStarMatrix m n A) (hr : r ∈ rectangularRightIdeal (a*V)) :
    r*r.conjTranspose ∈ hereditarySubalgebra h hh := by
  have hcont : Continuous (fun r : CStarMatrix m n A => r*r.conjTranspose) :=
    rectangular_continuous_mul.comp (continuous_id.prodMk rectangular_continuous_conjTranspose)
  have hc : IsClosed {r : CStarMatrix m n A | r*r.conjTranspose ∈ hereditarySubalgebra h hh} :=
    (NonUnitalStarSubalgebra.isClosed_topologicalClosure _).preimage hcont
  apply closure_minimal _ hc hr
  rintro _ ⟨b, rfl⟩
  change ((a*V)*b)*((a*V)*b).conjTranspose ∈ hereditarySubalgebra h hh
  rw [rectangular_mul_assoc a V b, rectangular_range_mul]
  exact rightIdeal_sandwich_mem_hereditary h a _ hh ha

lemma rectangular_exact_initial_hereditary (h : CStarMatrix m m A)
    (V : CStarMatrix m n A) (d : CStarMatrix n n A) (hh : 0 ≤ h) (hd : 0 ≤ d)
    {c : ℝ} (hc : 0 ≤ c)
    (hdu : d ≤ c • ((CFC.sqrt h*V).conjTranspose*(CFC.sqrt h*V))) :
    ∃ r : CStarMatrix m n A, r.conjTranspose*r = d ∧
      r*r.conjTranspose ∈ hereditarySubalgebra h hh.isSelfAdjoint := by
  obtain ⟨r, hr, hrmem⟩ := rectangular_exact_initial_of_domination (CFC.sqrt h*V) d hd hc hdu
  refine ⟨r, hr, rectangularRightIdeal_range_mem_hereditary h (CFC.sqrt h) V
    hh.isSelfAdjoint ?_ r hrmem⟩
  exact hereditary_le_rightIdeal h hh.isSelfAdjoint
    (sqrt_mem_hereditary h h hh.isSelfAdjoint (self_mem_hereditary h hh) hh)

end RectangularHereditary

end

end WeakPureInfiniteness
end

end OAI
