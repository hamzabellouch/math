import OAI.AlgebraicTopology.IntegralHomology.Connected
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.Order.IntermediateValue

namespace OAI

noncomputable section

namespace Kaplansky

/-! Suspension homology and integral top generators of spheres. -/

section
open CategoryTheory ContinuousMap

/-- Radial normalization gives a genuine homotopy equivalence of the
punctured vector space with its unit sphere. -/
def puncturedVectorSphereHomotopyEquiv (V : Type)
    [NormedAddCommGroup V] [NormedSpace ℝ V] :
    ({0}ᶜ : Set V) ≃ₕ Metric.sphere (0 : V) 1 := by
  letI : ContractibleSpace (Set.Ioi (0 : ℝ)) :=
    (convex_Ioi (0 : ℝ)).contractibleSpace ⟨1, by norm_num⟩
  let e := Classical.choice (ContractibleSpace.hequiv_unit (Set.Ioi (0 : ℝ)))
  exact (homeomorphUnitSphereProd V).toHomotopyEquiv.trans
    (((ContinuousMap.HomotopyEquiv.refl _).prodCongr e).trans
      (Homeomorph.prodUnique _ Unit).toHomotopyEquiv)

/-- Relative homology at the origin, in degrees at least two, is identified
with the preceding integral sphere homology. No sphere group calculation is assumed. -/
def localVectorSphereHomologyIso (V : Type)
    [NormedAddCommGroup V] [NormedSpace ℝ V] (n : ℕ) (hn : n ≠ 0) :
    relativeSingularHomology (subspaceInclusion ({0}ᶜ : Set V)) (n+1) ≅
      (integralSingularHomology n).obj (TopCat.of (Metric.sphere (0 : V) 1)) :=
  puncturedVectorBoundaryIso V n hn ≪≫
    integralHomologyHomotopyIso (puncturedVectorSphereHomotopyEquiv V) n

open ComplexGrassmann
variable {ι : Type} [Fintype ι] (K : ι → ℕ)

/-- The local relative homology of the actual projective chart at its
canonical zero is now compared with ordinary sphere homology. -/
def canonicalChartSphereHomologyIso (n : ℕ) (hn : n ≠ 0) :
    relativeSingularHomology (subspaceInclusion
      ({⟨firstCoordinateProduct K, canonicalProduct_zero_in_chart K⟩}ᶜ :
        Set (canonicalProductGraphChart K).source)) (n+1) ≅
      (integralSingularHomology n).obj
        (TopCat.of (Metric.sphere (0 : ((Σ i, Fin (K i)) → ℂ)) 1)) :=
  canonicalLocalRelativeHomologyIso K (n+1) ≪≫
    localVectorSphereHomologyIso _ n hn

end

section
open Metric ContinuousMap
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The sphere with one pole removed is the actual orthogonal hyperplane. -/
def spherePoleHomeomorph (v : sphere (0 : E) 1) :
    ({v}ᶜ : Set (sphere (0 : E) 1)) ≃ₜ (ℝ ∙ (v : E))ᗮ :=
  (stereographic (norm_eq_of_mem_sphere v)).toHomeomorphSourceTarget.trans
    (Homeomorph.Set.univ _)

@[simp] theorem spherePoleHomeomorph_apply (v : sphere (0 : E) 1)
    (x : ({v}ᶜ : Set (sphere (0 : E) 1))) :
    spherePoleHomeomorph v x = stereographic (norm_eq_of_mem_sphere v) x.val := rfl

theorem sphere_pole_ne_neg (v : sphere (0 : E) 1) : v ≠ -v := by
  intro h
  have h' : (v : E) = -(v : E) := congrArg Subtype.val h
  have hz : (v : E) = 0 := by
    have : (2 : ℝ) • (v : E) = 0 := by rw [two_smul]; exact (congrArg (fun x : E => x + (v : E)) h').trans (neg_add_cancel _)
    exact (smul_eq_zero.mp this).resolve_left (by norm_num)
  have := norm_eq_of_mem_sphere v
  simp [hz] at this

theorem sphere_poles_open_cover (v : sphere (0 : E) 1) :
    IsOpen ({v}ᶜ : Set (sphere (0 : E) 1)) ∧
    IsOpen ({-v}ᶜ : Set (sphere (0 : E) 1)) ∧
    ({v}ᶜ : Set (sphere (0 : E) 1)) ∪ {-v}ᶜ = Set.univ := by
  refine ⟨isOpen_compl_singleton, isOpen_compl_singleton, ?_⟩
  ext x
  simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  by_cases h : x = v
  · exact Or.inr (h ▸ sphere_pole_ne_neg v)
  · exact Or.inl h

theorem spherePole_contractible (v : sphere (0 : E) 1) :
    ContractibleSpace ({v}ᶜ : Set (sphere (0 : E) 1)) :=
  (spherePoleHomeomorph v).contractibleSpace

/-- Stereographic projection identifies the overlap of the two pole charts
with the punctured orthogonal hyperplane. -/
def spherePoleOverlapHomeomorph (v : sphere (0 : E) 1) :
    ↥(({v}ᶜ : Set (sphere (0 : E) 1)) ∩ {-v}ᶜ) ≃ₜ
      ({0}ᶜ : Set (ℝ ∙ (v : E))ᗮ) := by
  let e := spherePoleHomeomorph v
  let s : ({v}ᶜ : Set (sphere (0 : E) 1)) :=
    ⟨-v, by simpa using (sphere_pole_ne_neg v).symm⟩
  have hs : e s = 0 := stereographic_apply_neg v
  let e' : ({s}ᶜ : Set ({v}ᶜ : Set (sphere (0 : E) 1))) ≃ₜ
      ({0}ᶜ : Set (ℝ ∙ (v : E))ᗮ) := e.subtype (fun x => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        rw [← hs, e.injective.eq_iff])
  refine Homeomorph.trans ?_ e'
  exact
    { toFun := fun x => ⟨⟨x.val, x.property.1⟩, by
        intro h
        exact x.property.2 (congrArg Subtype.val h)⟩
      invFun := fun x => ⟨x.val.val, x.val.property, by
        intro h
        exact x.property (Subtype.ext h)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }

/-- The overlap of opposite pole charts is homotopy equivalent to the equator. -/
def spherePoleOverlapHomotopyEquiv (v : sphere (0 : E) 1) :
    ↥(({v}ᶜ : Set (sphere (0 : E) 1)) ∩ {-v}ᶜ) ≃ₕ
      sphere (0 : (ℝ ∙ (v : E))ᗮ) 1 :=
  (spherePoleOverlapHomeomorph v).toHomotopyEquiv.trans
    (puncturedVectorSphereHomotopyEquiv _)

end

section
open CategoryTheory Metric

section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Actual integral homology suspension isomorphism for a unit sphere,
obtained from its pole cover and the actual equator. -/
def sphereEquatorHomologyIso (v : sphere (0 : E) 1) (n : ℕ) (hn : n ≠ 0) :
    (integralSingularHomology (n+1)).obj (TopCat.of (sphere (0 : E) 1)) ≅
      (integralSingularHomology n).obj (TopCat.of (sphere (0 : (ℝ ∙ (v : E))ᗮ) 1)) := by
  letI := spherePole_contractible v
  letI := spherePole_contractible (-v)
  obtain ⟨hU, hV, hUV⟩ := sphere_poles_open_cover v
  exact openCoverMayerVietorisBoundaryIso _ _ hU hV hUV n hn ≪≫
    integralHomologyHomotopyIso (spherePoleOverlapHomotopyEquiv v) n

/-- Restriction of a real linear isometry equivalence to actual unit spheres. -/
def linearIsometrySphereHomeomorph {F : Type} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (e : E ≃ₗᵢ[ℝ] F) :
    sphere (0 : E) 1 ≃ₜ sphere (0 : F) 1 :=
  e.toHomeomorph.subtype (fun x => by simp)

/-- The equator has the expected Euclidean dimension. -/
def sphereEquatorEuclideanHomeomorph (d : ℕ) [Fact (Module.finrank ℝ E = d+1)]
    (v : sphere (0 : E) 1) :
    sphere (0 : (ℝ ∙ (v : E))ᗮ) 1 ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin d)) 1 :=
  linearIsometrySphereHomeomorph
    (OrthonormalBasis.fromOrthogonalSpanSingleton d
      (show (v : E) ≠ 0 by
        intro h
        have := norm_eq_of_mem_sphere v
        simp [h] at this)).repr

/-- Degree recursion to a sphere in one less real dimension. The base H₁
calculation is not included in this statement. -/
def sphereEuclideanHomologyStep (d : ℕ) [Fact (Module.finrank ℝ E = d+1)]
    (v : sphere (0 : E) 1) (n : ℕ) (hn : n ≠ 0) :
    (integralSingularHomology (n+1)).obj (TopCat.of (sphere (0 : E) 1)) ≅
      (integralSingularHomology n).obj (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin d)) 1)) :=
  sphereEquatorHomologyIso v n hn ≪≫
    (integralSingularHomology n).mapIso (TopCat.isoOfHomeo (sphereEquatorEuclideanHomeomorph d v))

end

/-- Nonzero vectors transport under an actual continuous linear equivalence. -/
def continuousLinearEquivPuncturedHomeomorph {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (e : E ≃L[ℝ] F) :
    ({0}ᶜ : Set E) ≃ₜ ({0}ᶜ : Set F) :=
  e.toHomeomorph.subtype (fun x => by simp)

/-- In a real plane, the overlap of the two pole charts is the punctured real line. -/
def spherePlaneOverlapRealHomeomorph {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [Fact (Module.finrank ℝ E = 1+1)]
    (v : sphere (0 : E) 1) :
    ↥(({v}ᶜ : Set (sphere (0 : E) 1)) ∩ {-v}ᶜ) ≃ₜ ({0}ᶜ : Set ℝ) :=
  (spherePoleOverlapHomeomorph v).trans (continuousLinearEquivPuncturedHomeomorph
    ((OrthonormalBasis.fromOrthogonalSpanSingleton 1
      (show (v : E) ≠ 0 by
        intro h
        have := norm_eq_of_mem_sphere v
        simp [h] at this)).repr.toContinuousLinearEquiv.trans
      (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ))))

/-- The signs lie in different path components of the actual punctured real line. -/
theorem puncturedReal_not_joined :
    ¬ Joined (⟨-1, by simp⟩ : ({0}ᶜ : Set ℝ)) ⟨1, by simp⟩ := by
  rintro ⟨p⟩
  have hc : Continuous (fun t => (p t : ℝ)) := continuous_subtype_val.comp p.continuous
  have hz : (0 : ℝ) ∈ Set.range (fun t => (p t : ℝ)) :=
    intermediate_value_univ 0 1 hc (by simp)
  obtain ⟨t, ht⟩ := hz
  exact (p t).property ht

/-- Nonzero integral H₁ of the actual unit sphere of any real plane. -/
theorem planeSphere_homologyOne_nonzero {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [Fact (Module.finrank ℝ E = 1+1)]
    (v : sphere (0 : E) 1) :
    ∃ z : (integralSingularHomology 1).obj (TopCat.of (sphere (0 : E) 1)), z ≠ 0 := by
  let := spherePole_contractible v
  let := spherePole_contractible (-v)
  obtain ⟨hU, hV, hUV⟩ := sphere_poles_open_cover v
  let e := spherePlaneOverlapRealHomeomorph v
  let a : ({0}ᶜ : Set ℝ) := ⟨-1, by simp⟩
  let b : ({0}ᶜ : Set ℝ) := ⟨1, by simp⟩
  apply openCover_homologyOne_nonzero _ _ hU hV hUV (e.symm a) (e.symm b)
  intro h
  have hh := h.map e.continuous
  simp only [e.apply_symm_apply] at hh
  exact puncturedReal_not_joined hh

/-- The punctured real line has exactly its negative and positive path components. -/
theorem puncturedReal_two_components (x : ({0}ᶜ : Set ℝ)) :
    Joined x (⟨-1, by simp⟩ : ({0}ᶜ : Set ℝ)) ∨ Joined x ⟨1, by simp⟩ := by
  have hx : (x : ℝ) ≠ 0 := x.property
  rcases lt_or_gt_of_ne hx with hx | hx
  · left
    have h := ((convex_Iio (0 : ℝ)).isPathConnected ⟨-1, by norm_num⟩).joinedIn
      (x : ℝ) hx (-1) (by norm_num)
    exact (h.mono (by intro y hy; exact ne_of_lt hy)).joined_subtype
  · right
    have h := ((convex_Ioi (0 : ℝ)).isPathConnected ⟨1, by norm_num⟩).joinedIn
      (x : ℝ) hx 1 (by norm_num)
    exact (h.mono (by intro y hy; exact ne_of_gt hy)).joined_subtype

/-- Integral H₁ of a plane sphere, normalized by the ordered negative/positive
components of its chosen stereographic overlap. -/
def planeSphereHomologyOneIso {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [Fact (Module.finrank ℝ E = 1+1)]
    (v : sphere (0 : E) 1) :
    (integralSingularHomology 1).obj (TopCat.of (sphere (0 : E) 1)) ≅ ModuleCat.of ℤ ℤ := by
  letI := spherePole_contractible v
  letI := spherePole_contractible (-v)
  obtain ⟨hU, hV, hUV⟩ := sphere_poles_open_cover v
  let e := spherePlaneOverlapRealHomeomorph v
  let a : ({0}ᶜ : Set ℝ) := ⟨-1, by simp⟩
  let b : ({0}ᶜ : Set ℝ) := ⟨1, by simp⟩
  apply openCoverMayerVietorisOneIso _ _ hU hV hUV (e.symm a) (e.symm b)
  · intro h
    have hh := h.map e.continuous
    simp only [e.apply_symm_apply] at hh
    exact puncturedReal_not_joined hh
  · intro x
    rcases puncturedReal_two_components (e x) with hx | hx
    · left
      simpa only [e.symm_apply_apply] using hx.map e.symm.continuous
    · right
      simpa only [e.symm_apply_apply] using hx.map e.symm.continuous

/-- A fixed unit vector used to make the recursive sphere calculation a definition. -/
def euclideanSpherePole (n : ℕ) : sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 :=
  ⟨Classical.choose ((NormedSpace.sphere_nonempty (E := EuclideanSpace ℝ (Fin (n+1)))
      (x := 0) (r := 1)).mpr (by norm_num)),
    Classical.choose_spec ((NormedSpace.sphere_nonempty (E := EuclideanSpace ℝ (Fin (n+1)))
      (x := 0) (r := 1)).mpr (by norm_num))⟩

/-- The full top integral homology calculation for every positive-dimensional
Euclidean sphere. The recursive pole charts and ordered H₀ components fix a sign. -/
def euclideanSphereTopHomologyIso : (n : ℕ) →
    (integralSingularHomology (n+1)).obj
      (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin (n+2))) 1)) ≅ ModuleCat.of ℤ ℤ
  | 0 => by
      letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 1+1) := ⟨by simp⟩
      exact planeSphereHomologyOneIso (euclideanSpherePole 1)
  | n+1 => by
      letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n+1+2))) = (n+2)+1) := ⟨by simp⟩
      exact sphereEuclideanHomologyStep (n+2) (euclideanSpherePole (n+2)) (n+1)
        (Nat.succ_ne_zero n) ≪≫ euclideanSphereTopHomologyIso n

/-- The normalized integral class determined by the recursive orientation. -/
def euclideanSphereTopGenerator (n : ℕ) :
    (integralSingularHomology (n+1)).obj
      (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin (n+2))) 1)) :=
  (euclideanSphereTopHomologyIso n).inv (1 : ℤ)

theorem euclideanSphereTopGenerator_coordinate (n : ℕ) :
    (euclideanSphereTopHomologyIso n).hom (euclideanSphereTopGenerator n) = (1 : ℤ) :=
  ConcreteCategory.congr_hom (euclideanSphereTopHomologyIso n).inv_hom_id 1

theorem euclideanSphereTopGenerator_ne_zero (n : ℕ) : euclideanSphereTopGenerator n ≠ 0 := by
  intro h
  have hc := euclideanSphereTopGenerator_coordinate n
  rw [h, map_zero] at hc
  norm_num at hc

end

section
open CategoryTheory Metric ContinuousMap

theorem nonzero_class_of_iso {A B : ModuleCat.{0} ℤ} (e : A ≅ B)
    (h : ∃ b : B, b ≠ 0) : ∃ a : A, a ≠ 0 := by
  obtain ⟨b, hb⟩ := h
  refine ⟨e.inv b, ?_⟩
  intro hz
  apply hb
  exact (ModuleCat.mono_iff_injective e.inv).mp inferInstance
    (hz.trans e.inv.hom.map_zero.symm)

/-- Every positive-dimensional Euclidean sphere has a nonzero class in
its top integral singular homology, with the circle base case proved. -/
theorem euclideanSphere_topHomology_nonzero (n : ℕ) :
    ∃ z : (integralSingularHomology (n+1)).obj
      (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin (n+2))) 1)), z ≠ 0 := by
  induction n with
  | zero =>
      let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 1+1) := ⟨by simp⟩
      obtain ⟨v, hv⟩ := (NormedSpace.sphere_nonempty (E := EuclideanSpace ℝ (Fin 2))
        (x := 0) (r := 1)).mpr (by norm_num)
      exact planeSphere_homologyOne_nonzero ⟨v, hv⟩
  | succ n ih =>
      let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n+1+2))) = (n+2)+1) :=
        ⟨by simp⟩
      obtain ⟨v, hv⟩ := (NormedSpace.sphere_nonempty (E := EuclideanSpace ℝ (Fin (n+1+2)))
        (x := 0) (r := 1)).mpr (by norm_num)
      exact nonzero_class_of_iso (sphereEuclideanHomologyStep (n+2) ⟨v, hv⟩ (n+1)
        (Nat.succ_ne_zero n)) ih

def continuousLinearEquivSphereHomotopyEquiv {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (e : E ≃L[ℝ] F) :
    sphere (0 : E) 1 ≃ₕ sphere (0 : F) 1 :=
  (puncturedVectorSphereHomotopyEquiv E).symm.trans
    ((continuousLinearEquivPuncturedHomeomorph e).toHomotopyEquiv.trans
      (puncturedVectorSphereHomotopyEquiv F))

theorem finiteDimensionalSphere_topHomology_nonzero (E : Type)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (n : ℕ) (hd : Module.finrank ℝ E = n+2) :
    ∃ z : (integralSingularHomology (n+1)).obj (TopCat.of (sphere (0 : E) 1)), z ≠ 0 := by
  let e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (n+2)) :=
    ContinuousLinearEquiv.ofFinrankEq (by simpa using hd)
  exact nonzero_class_of_iso
    (integralHomologyHomotopyIso (continuousLinearEquivSphereHomotopyEquiv e) (n+1))
    (euclideanSphere_topHomology_nonzero n)

end

open CategoryTheory Limits Metric
section

/-- The actual real zero-sphere has no positive integral homology. -/
theorem realSphere_positiveHomology_isZero (n : ℕ) (hn : n ≠ 0) :
    IsZero ((integralSingularHomology n).obj (TopCat.of (sphere (0 : ℝ) 1))) := by
  have hf : (sphere (0 : ℝ) 1).Finite := by
    rw [Real.sphere_eq_pair 0 (by norm_num)]
    exact Set.toFinite _
  let := hf.fintype
  exact AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    (ModuleCat ℤ) n (ModuleCat.of ℤ ℤ) (TopCat.of (sphere (0 : ℝ) 1)) hn

/-- The pole-chart intersection is connected in real ambient dimension at least three. -/
theorem sphere_homologyOne_isZero {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (d : ℕ) (hd : 2 ≤ d)
    [Fact (Module.finrank ℝ E = d+1)] (v : sphere (0 : E) 1) :
    IsZero ((integralSingularHomology 1).obj (TopCat.of (sphere (0 : E) 1))) := by
  let := spherePole_contractible v
  let := spherePole_contractible (-v)
  obtain ⟨hU,hV,hUV⟩ := sphere_poles_open_cover v
  let e := (spherePoleOverlapHomeomorph v).trans
    (continuousLinearEquivPuncturedHomeomorph
      (OrthonormalBasis.fromOrthogonalSpanSingleton d
        (show (v : E) ≠ 0 by
          intro h
          have := norm_eq_of_mem_sphere v
          simp [h] at this)).repr.toContinuousLinearEquiv)
  have hc : PathConnectedSpace ({0}ᶜ : Set (EuclideanSpace ℝ (Fin d))) := by
    apply isPathConnected_iff_pathConnectedSpace.mp
    apply isPathConnected_compl_singleton_of_one_lt_rank
    rw [← Module.finrank_eq_rank]
    have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := by simp
    rw [hfin]
    exact_mod_cast (show 1 < d by omega)
  let := hc
  let : PathConnectedSpace ↥(({v}ᶜ : Set (sphere (0 : E) 1)) ∩ {-v}ᶜ) :=
    e.symm.surjective.pathConnectedSpace e.symm.continuous
  exact openCover_homologyOne_isZero _ _ hU hV hUV

/-- Integral sphere homology vanishes in every positive degree other than
the sphere dimension. This includes both above- and below-dimension vanishing. -/
theorem euclideanSphereHomology_isZero (d n : ℕ) (hn : n ≠ 0) (hne : n ≠ d) :
    IsZero ((integralSingularHomology n).obj
      (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin (d+1))) 1))) := by
  induction d generalizing n with
  | zero =>
      let e := integralHomologyHomotopyIso
        (continuousLinearEquivSphereHomotopyEquiv
          (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ))) n
      exact (realSphere_positiveHomology_isZero n hn).of_iso e
  | succ d ih =>
      let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (d+1+1))) = (d+1)+1) :=
        ⟨by simp⟩
      cases n with
      | zero => exact (hn rfl).elim
      | succ n =>
          by_cases hzero : n = 0
          · subst n
            exact sphere_homologyOne_isZero (d+1) (by omega) (euclideanSpherePole (d+1))
          · exact (ih n hzero (by omega)).of_iso
              (sphereEuclideanHomologyStep (d+1) (euclideanSpherePole (d+1)) n hzero)

theorem finiteDimensionalSphereHomology_isZero (E : Type)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (d n : ℕ) (hd : Module.finrank ℝ E = d+1) (hn : n ≠ 0) (hne : n ≠ d) :
    IsZero ((integralSingularHomology n).obj (TopCat.of (sphere (0 : E) 1))) :=
  (euclideanSphereHomology_isZero d n hn hne).of_iso
    (integralHomologyHomotopyIso (continuousLinearEquivSphereHomotopyEquiv
      (ContinuousLinearEquiv.ofFinrankEq (by simpa using hd) :
        E ≃L[ℝ] EuclideanSpace ℝ (Fin (d+1)))) n)

end

end Kaplansky

end

end OAI
