import OAI.Combinatorics.Coboundary.Complex
import OAI.Combinatorics.Coboundary.Expansion
import OAI.GroupTheory.Congruence.Resolution

namespace OAI

/-!
Finite labeled coset complexes, purity, growth, incidence bounds, and weighted expansion reduction.
-/

noncomputable section
open CategoryTheory
open scoped BigOperators
open CategoryTheory Finsupp
open CategoryTheory Finsupp MonoidalCategory
open scoped BigOperators Matrix
open scoped Matrix
open scoped MonoidAlgebra
open CategoryTheory CategoryTheory.Limits
open Filter

namespace CoboundaryExpanders.CosetConstruction

section

open CoboundaryExpanders.Complex

variable {G : Type*} [Group G] [Fintype G] {n : ℕ}

abbrev Vertex (H : Fin (n + 1) → Subgroup G) := (i : Fin (n + 1)) × (G ⧸ H i)

noncomputable instance vertexFintype (H : Fin (n + 1) → Subgroup G) :
    Fintype (Vertex H) := Fintype.ofFinite _

def labelEquiv (H : Fin (n + 1) → Subgroup G) :
    Vertex H ≃ Fin (Fintype.card (Vertex H)) := Fintype.equivFin _

def vertex (H : Fin (n + 1) → Subgroup G) (g : G) (i : Fin (n + 1)) :
    Fin (Fintype.card (Vertex H)) := labelEquiv H ⟨i, QuotientGroup.mk g⟩

theorem vertex_surjective (H : Fin (n + 1) → Subgroup G)
    (v : Fin (Fintype.card (Vertex H))) : ∃ i g, vertex H g i = v := by
  obtain ⟨⟨i, c⟩, rfl⟩ := (labelEquiv H).surjective v
  induction c using QuotientGroup.induction_on with
  | H g => exact ⟨i, g, rfl⟩

theorem vertex_type_eq {H : Fin (n + 1) → Subgroup G} {g h : G} {i j : Fin (n + 1)}
    (heq : vertex H g i = vertex H h j) : i = j :=
  congrArg Sigma.fst ((labelEquiv H).injective heq)

theorem vertex_injective (H : Fin (n + 1) → Subgroup G) (g : G) :
    Function.Injective (vertex H g) := fun _ _ heq => vertex_type_eq heq

theorem vertex_eq_iff (H : Fin (n + 1) → Subgroup G) (g h : G) (i : Fin (n + 1)) :
    vertex H g i = vertex H h i ↔ g⁻¹ * h ∈ H i := by
  change labelEquiv H ⟨i, (g : G ⧸ H i)⟩ = labelEquiv H ⟨i, (h : G ⧸ H i)⟩ ↔ _
  rw [Equiv.apply_eq_iff_eq]
  simpa using (QuotientGroup.eq (s := H i) (a := g) (b := h))

def chamber (H : Fin (n + 1) → Subgroup G) (g : G) :
    Finset (Fin (Fintype.card (Vertex H))) := Finset.univ.image (vertex H g)

@[simp] theorem mem_chamber {H : Fin (n + 1) → Subgroup G} {g : G} {v} :
    v ∈ chamber H g ↔ ∃ i, vertex H g i = v := by
  simp [chamber]

@[simp] theorem vertex_mem_chamber (H : Fin (n + 1) → Subgroup G) (g : G) (i) :
    vertex H g i ∈ chamber H g := mem_chamber.mpr ⟨i, rfl⟩

@[simp] theorem card_chamber (H : Fin (n + 1) → Subgroup G) (g : G) :
    (chamber H g).card = n + 1 := by
  rw [chamber, Finset.card_image_of_injective _ (vertex_injective H g)]
  simp

@[reducible] def complex (H : Fin (n + 1) → Subgroup G) : Complex where
  vertexCount := Fintype.card (Vertex H)
  faces := Finset.univ.biUnion (fun g : G => (chamber H g).powerset)
  empty_mem := Finset.mem_biUnion.mpr ⟨1, Finset.mem_univ _,
    Finset.mem_powerset.mpr (Finset.empty_subset _)⟩
  downward := by
    intro σ τ hσ hτ
    obtain ⟨g, _, hg⟩ := Finset.mem_biUnion.mp hσ
    exact Finset.mem_biUnion.mpr ⟨g, Finset.mem_univ _,
      Finset.mem_powerset.mpr (hτ.trans (Finset.mem_powerset.mp hg))⟩
  vertex_mem := by
    intro v
    obtain ⟨i, g, rfl⟩ := vertex_surjective H v
    exact Finset.mem_biUnion.mpr ⟨g, Finset.mem_univ _,
      Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr (vertex_mem_chamber H g i))⟩

@[simp] theorem mem_faces {H : Fin (n + 1) → Subgroup G} {σ} :
    σ ∈ (complex H).faces ↔ ∃ g, σ ⊆ chamber H g := by
  simp [complex]

@[simp] theorem chamber_mem_facesOf (H : Fin (n + 1) → Subgroup G) (g : G) :
    chamber H g ∈ (complex H).facesOf n := by
  exact (mem_facesOf _ _ _).mpr ⟨mem_faces.mpr ⟨g, Finset.Subset.refl _⟩,
    card_chamber H g⟩

theorem pure (H : Fin (n + 1) → Subgroup G) : (complex H).Pure n := by
  refine ⟨⟨chamber H 1, chamber_mem_facesOf H 1⟩, ?_⟩
  intro σ hσ
  obtain ⟨g, hg⟩ := mem_faces.mp hσ
  exact ⟨chamber H g, chamber_mem_facesOf H g, hg⟩

abbrev Walk (H : Fin (n + 1) → Subgroup G)
    (v w : Fin (Fintype.card (Vertex H))) : Prop :=
  Relation.ReflTransGen (fun a b => a ≠ b ∧ {a, b} ∈ (complex H).faces) v w

theorem walk_of_common_chamber {H : Fin (n + 1) → Subgroup G} {g : G}
    {v w : Fin (Fintype.card (Vertex H))} (hv : v ∈ chamber H g) (hw : w ∈ chamber H g) :
    Walk H v w := by
  by_cases heq : v = w
  · subst w
    exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single ⟨heq,
      mem_faces.mpr ⟨g, by simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro hv hw⟩⟩

theorem walk_symm {H : Fin (n + 1) → Subgroup G} {v w}
    (h : Walk H v w) : Walk H w v := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hab ih =>
    exact (Relation.ReflTransGen.single ⟨hab.1.symm,
      by simpa only [Finset.pair_comm] using hab.2⟩).trans ih

theorem walk_vertex_mul (H : Fin (n + 1) → Subgroup G)
    (hgen : Subgroup.closure (⋃ i, (H i : Set G)) = ⊤) (x : G) :
    ∀ g : G, Walk H (vertex H g 0) (vertex H (g * x) 0) := by
  have hx : x ∈ Subgroup.closure (⋃ i, (H i : Set G)) := by
    rw [hgen]
    exact Subgroup.mem_top x
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    intro g
    have hcommon : vertex H g i = vertex H (g * x) i :=
      (vertex_eq_iff H g (g * x) i).mpr (by simpa using hxi)
    have hleft := walk_of_common_chamber (vertex_mem_chamber H g 0)
      (vertex_mem_chamber H g i)
    have hright := walk_of_common_chamber (vertex_mem_chamber H (g * x) i)
      (vertex_mem_chamber H (g * x) 0)
    rw [← hcommon] at hright
    exact hleft.trans hright
  | one =>
    intro g
    simpa only [mul_one] using
      (Relation.ReflTransGen.refl : Walk H (vertex H g 0) (vertex H g 0))
  | mul x y hx hy ihx ihy =>
    intro g
    simpa only [mul_assoc] using (ihx g).trans (ihy (g * x))
  | inv x hx ih =>
    intro g
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using walk_symm (ih (g * x⁻¹))

theorem connected (H : Fin (n + 1) → Subgroup G)
    (hgen : Subgroup.closure (⋃ i, (H i : Set G)) = ⊤) :
    (complex H).Connected := by
  refine ⟨⟨vertex H 1 0⟩, ?_⟩
  intro v w
  obtain ⟨i, g, rfl⟩ := vertex_surjective H v
  obtain ⟨j, h, rfl⟩ := vertex_surjective H w
  have hleft := walk_of_common_chamber (vertex_mem_chamber H g i)
    (vertex_mem_chamber H g 0)
  have hright := walk_of_common_chamber (vertex_mem_chamber H h 0)
    (vertex_mem_chamber H h j)
  have hmid := walk_vertex_mul H hgen (g⁻¹ * h) g
  simp only [← mul_assoc, mul_inv_cancel, one_mul] at hmid
  exact hleft.trans (hmid.trans hright)

noncomputable local instance subgroupFintype (K : Subgroup G) : Fintype K :=
  Fintype.ofFinite K

def incidentInChamber (H : Fin (n + 1) → Subgroup G) (g : G)
    (v : Fin (Fintype.card (Vertex H))) (d : ℕ) :=
  ((chamber H g).powersetCard (d + 1)).filter (v ∈ ·)

@[simp] theorem mem_incidentInChamber {H : Fin (n + 1) → Subgroup G} {g v d σ} :
    σ ∈ incidentInChamber H g v d ↔ σ ⊆ chamber H g ∧ σ.card = d + 1 ∧ v ∈ σ := by
  simp [incidentInChamber, Finset.mem_powersetCard, and_assoc]

theorem card_incidentInChamber (H : Fin (n + 1) → Subgroup G) (g : G)
    (v : Fin (Fintype.card (Vertex H))) (d : ℕ) (hv : v ∈ chamber H g) :
    (incidentInChamber H g v d).card = Nat.choose n d := by
  have h := Finset.card_filter_powersetCard_subset {v} (chamber H g) (d + 1)
    (Finset.singleton_subset_iff.mpr hv) (by simp)
  simpa [incidentInChamber] using h

theorem incident_faces_subset (H : Fin (n + 1) → Subgroup G) (g : G)
    (i : Fin (n + 1)) (d : ℕ) :
    ((complex H).facesOf d).filter (vertex H g i ∈ ·) ⊆
      Finset.univ.biUnion (fun h : H i =>
        incidentInChamber H (g * h) (vertex H g i) d) := by
  intro σ hσ
  obtain ⟨hσ, hv⟩ := Finset.mem_filter.mp hσ
  obtain ⟨hface, hcard⟩ := (mem_facesOf _ _ _).mp hσ
  obtain ⟨k, hk⟩ := mem_faces.mp hface
  obtain ⟨j, hj⟩ := mem_chamber.mp (hk hv)
  have hji : j = i := vertex_type_eq hj
  subst j
  have hmem : g⁻¹ * k ∈ H i := (vertex_eq_iff H g k i).mp hj.symm
  refine Finset.mem_biUnion.mpr ⟨⟨g⁻¹ * k, hmem⟩, Finset.mem_univ _, ?_⟩
  apply mem_incidentInChamber.mpr
  simpa only [mul_inv_cancel_left] using And.intro hk (And.intro hcard hv)

theorem topDegree_le (H : Fin (n + 1) → Subgroup G) (g : G)
    (i : Fin (n + 1)) (d : ℕ) :
    (complex H).topDegree d (vertex H g i) ≤ Nat.card (H i) * Nat.choose n d := by
  calc
    _ ≤ (Finset.univ.biUnion (fun h : H i =>
        incidentInChamber H (g * h) (vertex H g i) d)).card :=
      Finset.card_le_card (incident_faces_subset H g i d)
    _ ≤ ∑ h : H i, (incidentInChamber H (g * h) (vertex H g i) d).card :=
      Finset.card_biUnion_le
    _ = Nat.card (H i) * Nat.choose n d := by
      have hc (h : H i) : vertex H g i ∈ chamber H (g * h) := by
        rw [(vertex_eq_iff H g (g * h) i).mpr (by simp)]
        exact vertex_mem_chamber _ _ _
      simp_rw [card_incidentInChamber H _ _ d (hc _)]
      simp [Nat.card_eq_fintype_card]

theorem vertexCount_eq_sum_index (H : Fin (n + 1) → Subgroup G) :
    (complex H).vertexCount = ∑ i, (H i).index := by
  change Fintype.card (Vertex H) = _
  rw [← Nat.card_eq_fintype_card, Nat.card_sigma]
  simp only [Subgroup.index_eq_card]

theorem vertexCount_mul (H : Fin (n + 1) → Subgroup G) (M : ℕ)
    (hM : ∀ i, Nat.card (H i) = M) :
    (complex H).vertexCount * M = (n + 1) * Nat.card G := by
  rw [vertexCount_eq_sum_index, Finset.sum_mul]
  have heq (i : Fin (n + 1)) : (H i).index * M = Nat.card G := by
    rw [← hM i, mul_comm]
    exact (H i).card_mul_index
  simp_rw [heq]
  simp

end

variable {G : Type} [Group G] [Fintype G] {n : ℕ}

theorem vertexCount_mul_lower (H : Fin (n + 1) → Subgroup G) (M : ℕ)
    (hM : ∀ i, Nat.card (H i) ≤ M) :
    (n + 1) * Nat.card G ≤ (complex H).vertexCount * M := by
  rw [vertexCount_eq_sum_index, Finset.sum_mul]
  calc
    _ = ∑ i : Fin (n + 1), (H i).index * Nat.card (H i) := by
      simp only [mul_comm (H _).index, Subgroup.card_mul_index]
      simp
    _ ≤ _ := Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left _ (hM i))

end CoboundaryExpanders.CosetConstruction

namespace CoboundaryExpanders.Construction

section
open Filter CosetConstruction _root_.OAI.CoboundaryExpanders.Complex
variable (p n : ℕ) [Fact p.Prime]

def localBound : ℕ := Nat.card (Matrix.GeneralLinearGroup (Fin (n + 1)) (ZMod p))

theorem localBound_pos : 0 < localBound p n := Nat.card_pos

def finiteCosetComplex (hn : 1 ≤ n) (m : ℕ) : Complex :=
  letI : Fintype (Gquot p (n + 1) m) := Fintype.ofFinite _
  CosetConstruction.complex (reducedLocalGroup p n hn m)

def finiteSkeleton (hn : 1 ≤ n) (d m : ℕ) : Complex :=
  (finiteCosetComplex p n hn (m + 2)).skeleton d

theorem finiteCosetComplex_pure (hn : 1 ≤ n) (m : ℕ) :
    (finiteCosetComplex p n hn m).Pure n := by
  let : Fintype (Gquot p (n + 1) m) := Fintype.ofFinite _
  exact CosetConstruction.pure _

theorem finiteSkeleton_pure (hn : 1 ≤ n) {d : ℕ} (hd : d ≤ n) (m : ℕ) :
    (finiteSkeleton p n hn d m).Pure d := by
  exact skeleton_pure (finiteCosetComplex_pure p n hn (m + 2)) hd

theorem finiteCosetComplex_degree (hn : 1 ≤ n) (m d : ℕ)
    (v : Fin (finiteCosetComplex p n hn m).vertexCount) :
    (finiteCosetComplex p n hn m).topDegree d v ≤ localBound p n * Nat.choose n d := by
  let : Fintype (Gquot p (n + 1) m) := Fintype.ofFinite _
  obtain ⟨i, g, rfl⟩ := vertex_surjective (reducedLocalGroup p n hn m) v
  exact (topDegree_le _ _ _ _).trans
    (Nat.mul_le_mul_right _ (reducedLocalGroup_card_le p n hn m i))

theorem finiteSkeleton_degree (hn : 1 ≤ n) (d m : ℕ)
    (v : Fin (finiteSkeleton p n hn d m).vertexCount) :
    (finiteSkeleton p n hn d m).topDegree d v ≤ localBound p n * Nat.choose n d := by
  classical
  change ((finiteCosetComplex p n hn (m + 2)).skeleton d).topDegree d v ≤ _
  unfold Complex.topDegree
  rw [skeleton_facesOf le_rfl]
  exact finiteCosetComplex_degree p n hn (m + 2) d v

theorem finiteCosetComplex_growth_bound (hn : 1 ≤ n) (m : ℕ) :
    p ^ m ≤ (finiteCosetComplex p n hn m).vertexCount * localBound p n := by
  let : Fintype (Gquot p (n + 1) m) := Fintype.ofFinite _
  exact (gquot_card_lower p n hn m).trans
    ((Nat.le_mul_of_pos_left _ (Nat.succ_pos n)).trans
      (vertexCount_mul_lower _ (localBound p n) (reducedLocalGroup_card_le p n hn m)))

theorem finiteSkeleton_growth (hn : 1 ≤ n) (d : ℕ) :
    Tendsto (fun m => (finiteSkeleton p n hn d m).vertexCount) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  apply eventually_atTop.mpr
  refine ⟨b * localBound p n, fun m hm => ?_⟩
  apply (Nat.mul_le_mul_right_iff (localBound_pos p n)).mp
  exact hm.trans ((Nat.le_add_right m 2).trans
    ((Nat.le_of_lt (Nat.lt_pow_self (Fact.out : p.Prime).one_lt)).trans
      (finiteCosetComplex_growth_bound p n hn (m + 2))))

theorem finiteSkeleton_vertex_faces_growth (hn : 1 ≤ n) (d : ℕ) :
    Tendsto (fun m => ((finiteSkeleton p n hn d m).facesOf 0).card) atTop atTop := by
  simpa only [Complex.card_facesOf_zero] using finiteSkeleton_growth p n hn d

theorem constructed_pure_bounded_growing (d : ℕ) (hd : 3 ≤ d) :
    ∃ D : ℕ, (∀ m, (finiteSkeleton p (2 * d) (by omega) d m).Pure d) ∧
      Tendsto (fun m => ((finiteSkeleton p (2 * d) (by omega) d m).facesOf 0).card)
        atTop atTop ∧
      ∀ m (v : Fin (finiteSkeleton p (2 * d) (by omega) d m).vertexCount),
        (finiteSkeleton p (2 * d) (by omega) d m).topDegree d v ≤ D := by
  refine ⟨localBound p (2 * d) * Nat.choose (2 * d) d, ?_, ?_, ?_⟩
  · exact fun m => finiteSkeleton_pure p (2 * d) (by omega) (by omega) m
  · exact finiteSkeleton_vertex_faces_growth p (2 * d) (by omega) d
  · exact fun m v => finiteSkeleton_degree p (2 * d) (by omega) d m v

end

open Filter _root_.OAI.CoboundaryExpanders.Complex
variable (p n : ℕ) [Fact p.Prime]

theorem finiteCosetComplex_connected (hn : 2 ≤ n) (m : ℕ) (hm : 1 ≤ m) :
    (finiteCosetComplex p n (by omega) m).Connected := by
  let : Fintype (Gquot p (n + 1) m) := Fintype.ofFinite _
  exact CosetConstruction.connected _ (quotient_locals_generate p n m hn hm)

theorem finiteSkeleton_connected (hn : 2 ≤ n) (d m : ℕ) (hd : 1 ≤ d) :
    (finiteSkeleton p n (by omega) d m).Connected := by
  exact skeleton_connected (finiteCosetComplex_connected p n hn (m + 2) (by omega)) hd

theorem constructed_connected_pure_bounded_growing (d : ℕ) (hd : 3 ≤ d) :
    ∃ D : ℕ,
      (∀ m, (finiteSkeleton p (2 * d) (by omega) d m).Pure d ∧
        (finiteSkeleton p (2 * d) (by omega) d m).Connected) ∧
      Tendsto (fun m => ((finiteSkeleton p (2 * d) (by omega) d m).facesOf 0).card)
        atTop atTop ∧
      ∀ m (v : Fin (finiteSkeleton p (2 * d) (by omega) d m).vertexCount),
        (finiteSkeleton p (2 * d) (by omega) d m).topDegree d v ≤ D := by
  obtain ⟨D, hpure, hgrowth, hdegree⟩ := constructed_pure_bounded_growing p d hd
  exact ⟨D, fun m => ⟨hpure m, finiteSkeleton_connected p (2 * d) (by omega) d m (by omega)⟩,
    hgrowth, hdegree⟩

theorem finiteSkeleton_zero_cohomology (hn : 2 ≤ n) (d m : ℕ) (hd : 1 ≤ d) :
    (finiteSkeleton p n (by omega) d m).cocycles 0 =
      (finiteSkeleton p n (by omega) d m).coboundaries 0 :=
  cocycles_zero_eq_coboundaries_of_connected (finiteSkeleton_connected p n hn d m hd)

end CoboundaryExpanders.Construction

namespace CoboundaryExpanders.Complex
local instance (X : Complex) (i : ℕ) : Fintype (X.Face i) := X.instFintypeFace i
local instance (X : Complex) (i : ℕ) : DecidableEq (X.Face i) := X.instDecidableEqFace i

abbrev Chain (X : Complex) (i : ℕ) := Module.Dual (ZMod 2) (X.Cochain i)

def chainBasis (X : Complex) (i : ℕ) :
    Module.Basis (X.Face i) (ZMod 2) (X.Chain i) :=
  (Pi.basisFun (ZMod 2) (X.Face i)).dualBasis

@[simp] theorem chainBasis_apply (X : Complex) (i : ℕ) (σ : X.Face i)
    (f : X.Cochain i) : X.chainBasis i σ f = f σ := by
  exact (Pi.basisFun (ZMod 2) (X.Face i)).dualBasis_apply σ f

def boundaryLinear (X : Complex) (i : ℕ) : X.Chain (i + 1) →ₗ[ZMod 2] X.Chain i :=
  (X.coboundaryLinear i).dualMap

@[simp] theorem boundary_on_face (X : Complex) (i : ℕ) (τ : X.Face (i + 1)) :
    X.boundaryLinear i (X.chainBasis (i + 1) τ) =
      ∑ σ : X.Face i, if σ.val ⊆ τ.val then X.chainBasis i σ else 0 := by
  apply LinearMap.ext
  intro f
  change X.chainBasis (i + 1) τ (X.coboundary i f) = _
  rw [chainBasis_apply]
  simp only [coboundary, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro σ _
  split_ifs <;> simp

@[simp] theorem boundary_boundary (X : Complex) (i : ℕ) :
    (X.boundaryLinear i).comp (X.boundaryLinear (i + 1)) = 0 := by
  apply LinearMap.ext
  intro c
  apply LinearMap.ext
  intro f
  change c (X.coboundary (i + 1) (X.coboundary i f)) = 0
  rw [coboundary_coboundary, map_zero]

open CategoryTheory

def chainComplex (X : Complex) : ChainComplex (ModuleCat (ZMod 2)) ℕ :=
  ChainComplex.of (fun i => ModuleCat.of (ZMod 2) (X.Chain i))
    (fun i => ModuleCat.ofHom (X.boundaryLinear i))
    (fun i => ModuleCat.hom_ext (X.boundary_boundary i))

@[simp] theorem chainComplex_d (X : Complex) (i : ℕ) :
    X.chainComplex.d (i + 1) i = ModuleCat.ofHom (X.boundaryLinear i) :=
  by simp only [chainComplex, ChainComplex.of_d]

theorem cocycles_eq_coboundaries_of_homology_isZero (X : Complex) (i : ℕ)
    (homologyZero : Limits.IsZero (X.chainComplex.homology (i + 1))) :
    X.cocycles (i + 1) = X.coboundaries (i + 1) := by
  have he := (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr homologyZero
  rw [HomologicalComplex.exactAt_iff' _ (i + 2) (i + 1) i (by simp) (by simp)] at he
  have hr := he.moduleCat_range_eq_ker
  change LinearMap.range (X.chainComplex.d (i + 2) (i + 1)).hom =
    LinearMap.ker (X.chainComplex.d (i + 1) i).hom at hr
  rw [chainComplex_d, chainComplex_d] at hr
  change LinearMap.range (X.boundaryLinear (i + 1)) = LinearMap.ker (X.boundaryLinear i) at hr
  unfold boundaryLinear at hr
  rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker,
    LinearMap.ker_dualMap_eq_dualAnnihilator_range] at hr
  have hh := Subspace.dualAnnihilator_inj.mp hr
  change LinearMap.ker (X.coboundaryLinear (i + 1)) =
    LinearMap.range (X.coboundaryLinear i) at hh
  ext f
  change (X.coboundaryLinear (i + 1) f = 0) ↔ ∃ g, X.coboundary i g = f
  exact Set.ext_iff.mp (congrArg (fun W : Submodule (ZMod 2) (X.Cochain (i + 1)) => W.carrier) hh) f

end CoboundaryExpanders.Complex

namespace CoboundaryExpanders.InfiniteChains.Complex
variable {V : Type} [DecidableEq V] [Finite V] (X : InfiniteChains.Complex V)

instance finiteFaceFintype (n : ℕ) : Fintype (X.Face n) := Fintype.ofFinite _

lemma boundary_single_subfaces (n : ℕ) (s : X.Face (n+1)) (r : k) :
    X.boundary n (Finsupp.single s r) =
      ∑ t : X.Face n, if t.val ⊆ s.val then Finsupp.single t r else 0 := by
  classical
  rw [boundary_single, ← Finset.sum_filter]
  apply Finset.sum_bij (fun (v : ↥s.val) _ => X.erase n s v)
  · intro v _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Finset.erase_subset _ _
  · intro a _ b _ he
    apply Subtype.ext
    exact (Finset.erase_inj s.val a.property).mp (congrArg Subtype.val he)
  · intro t ht
    have hsub : t.val ⊆ s.val := (Finset.mem_filter.mp ht).2
    have hcard : (s.val \ t.val).card = 1 := by
      rw [Finset.card_sdiff_of_subset hsub, s.property.2,t.property.2]
      omega
    obtain ⟨v,hv,he⟩ := (Finset.covBy_iff_card_sdiff_eq_one.mpr ⟨hsub,hcard⟩).exists_finset_erase
    exact ⟨⟨v,hv⟩,Finset.mem_univ _,Subtype.ext he⟩
  · intro _ _
    rfl
end CoboundaryExpanders.InfiniteChains.Complex

namespace CoboundaryExpanders.CosetConstruction
open CategoryTheory
local instance (X : CoboundaryExpanders.Complex) (i : ℕ) : Fintype (X.Face i) := X.instFintypeFace i
local instance (X : CoboundaryExpanders.Complex) (i : ℕ) : DecidableEq (X.Face i) := X.instDecidableEqFace i
variable {G : Type} [Group G] [Fintype G] {n : ℕ}
variable (H : Fin (n+1) → Subgroup G)

lemma labelled_face_image (g : G) (A : Finset (Fin (n+1))) :
    (TypedCosetFaces.face H g A).image (labelEquiv H) = A.image (vertex H g) := by
  simp only [TypedCosetFaces.face, Finset.image_image]
  rfl

lemma labelled_mem_faces (s : Finset (Vertex H)) :
    s.image (labelEquiv H) ∈ (complex H).faces ↔ TypedCosetFaces.IsFace H s := by
  classical
  constructor
  · intro hs
    obtain ⟨g,hg⟩ := mem_faces.mp hs
    apply (TypedCosetFaces.complex H).downward (σ := TypedCosetFaces.face H g Finset.univ)
      ⟨g,Finset.univ,rfl⟩
    intro x hx
    have hh := hg (Finset.mem_image.mpr ⟨x,hx,rfl⟩)
    obtain ⟨i,hi⟩ := mem_chamber.mp hh
    apply Finset.mem_image.mpr
    exact ⟨i,Finset.mem_univ _,(labelEquiv H).injective hi⟩
  · rintro ⟨g,A,rfl⟩
    rw [labelled_face_image]
    exact mem_faces.mpr ⟨g,Finset.image_subset_image (Finset.subset_univ A)⟩

def typedFaceEquiv (i : ℕ) :
    (TypedCosetFaces.complex H).Face (i+1) ≃ (complex H).Face i where
  toFun s := ⟨s.val.image (labelEquiv H), (Complex.mem_facesOf _ _ _).mpr
    ⟨(labelled_mem_faces H s.val).mpr s.property.1,
      (Finset.card_image_of_injective _ (labelEquiv H).injective).trans s.property.2⟩⟩
  invFun s := ⟨s.val.image (labelEquiv H).symm, by
    constructor
    · apply (labelled_mem_faces H _).mp
      simpa only [Finset.image_image, Function.comp_def, Equiv.apply_symm_apply, Finset.image_id']
        using Complex.face_mem s
    · exact (Finset.card_image_of_injective _ (labelEquiv H).symm.injective).trans (Complex.face_card s)⟩
  left_inv s := by
    apply Subtype.ext
    simp only [Finset.image_image, Function.comp_def, Equiv.symm_apply_apply, Finset.image_id']
  right_inv s := by
    apply Subtype.ext
    simp only [Finset.image_image, Function.comp_def, Equiv.apply_symm_apply, Finset.image_id']

lemma typedFaceEquiv_subset (i j : ℕ)
    (s : (TypedCosetFaces.complex H).Face (i+1))
    (t : (TypedCosetFaces.complex H).Face (j+1)) :
    (typedFaceEquiv H i s).val ⊆ (typedFaceEquiv H j t).val ↔ s.val ⊆ t.val := by
  change s.val.image (labelEquiv H) ⊆ t.val.image (labelEquiv H) ↔ _
  exact Finset.image_subset_image_iff (labelEquiv H).injective

def typedChainEquiv (i : ℕ) :
    (TypedCosetFaces.complex H).Chains (i+1) ≃ₗ[ZMod 2] (complex H).Chain i :=
  (Finsupp.domLCongr (typedFaceEquiv H i)).trans ((complex H).chainBasis i).repr.symm

@[simp] lemma typedChainEquiv_single (i : ℕ)
    (s : (TypedCosetFaces.complex H).Face (i+1)) (r : ZMod 2) :
    typedChainEquiv H i (Finsupp.single s r) = r • (complex H).chainBasis i (typedFaceEquiv H i s) := by
  simp [typedChainEquiv, Module.Basis.repr_symm_apply]

lemma typedChainEquiv_boundary (i : ℕ) :
    (typedChainEquiv H i).toLinearMap.comp ((TypedCosetFaces.complex H).boundary (i+1)) =
      ((complex H).boundaryLinear i).comp (typedChainEquiv H (i+1)).toLinearMap := by
  classical
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext
  intro r
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply,
    InfiniteChains.Complex.boundary_single_subfaces, map_sum,
    LinearEquiv.coe_coe, typedChainEquiv_single, map_smul,
    Complex.boundary_on_face, Finset.smul_sum]
  apply @Fintype.sum_equiv _ _ _ _ ((complex H).instFintypeFace_2 i) _ (typedFaceEquiv H i)
  intro t
  by_cases ht : t.val ⊆ s.val
  · have hlt := (typedFaceEquiv_subset H i (i+1) t s).mpr ht
    simp only [ite_eq_left ht,ite_eq_left hlt,typedChainEquiv_single]
  · have hlt := mt (typedFaceEquiv_subset H i (i+1) t s).mp ht
    simp only [ite_eq_right ht,ite_eq_right hlt,map_zero,smul_zero]

def typedChainIso : (TypedCosetFaces.complex H).chainComplex ≅ (complex H).chainComplex :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (typedChainEquiv H i).toModuleIso)
    (by
      intro i j hij
      have hij' : j+1 = i := by simpa using hij
      subst i
      rw [InfiniteChains.Complex.chainComplex_d, CoboundaryExpanders.Complex.chainComplex_d]
      apply ModuleCat.hom_ext
      exact (typedChainEquiv_boundary H j).symm)

theorem cocycles_eq_coboundaries_of_typed_homology (i : ℕ)
    (hz : Limits.IsZero ((TypedCosetFaces.complex H).chainComplex.homology (i+1))) :
    (complex H).cocycles (i+1) = (complex H).coboundaries (i+1) := by
  apply Complex.cocycles_eq_coboundaries_of_homology_isZero
  exact hz.of_iso ((HomologicalComplex.homologyFunctor _ _ (i+1)).mapIso (typedChainIso H)).symm

end CoboundaryExpanders.CosetConstruction

namespace CoboundaryExpanders.Construction
open CategoryTheory _root_.OAI.CoboundaryExpanders.Complex
variable (p n : ℕ) [Fact p.Prime]

theorem finiteCosetComplex_positive_cohomology (hn : 2 ≤ n) (hp : Odd p)
    (hL : OppositionAcyclic p n (by omega)) (m i : ℕ)
    (hm : 2 ≤ m) (hi : 0 < i) (hin : i < n-1)
    (hz : CongruenceCokernels.ProZero p (n-1) i)
    (hz' : CongruenceCokernels.ProZero p n i) :
    (finiteCosetComplex p n (by omega) m).cocycles i =
      (finiteCosetComplex p n (by omega) m).coboundaries i := by
  classical
  let : Fintype (Gquot p (n+1) m) := Fintype.ofFinite _
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  exact CosetConstruction.cocycles_eq_coboundaries_of_typed_homology
    (reducedLocalGroup p n (by omega) m) j
    (quotientTyped_homology_isZero p n hn hp hL m (j+1) hm hi hin hz hz')

end CoboundaryExpanders.Construction

namespace CoboundaryExpanders.Complex

theorem cofaceCount_le_topDegree {X : Complex} {i : ℕ} (σ : X.Face i)
    (n : ℕ) (v : Fin X.vertexCount) (hv : v ∈ σ.val) :
    X.cofaceCount n σ.val ≤ X.topDegree n v := by
  apply Finset.card_le_card
  intro τ hτ
  obtain ⟨hτ, hστ⟩ := Finset.mem_filter.mp hτ
  exact Finset.mem_filter.mpr ⟨hτ, hστ hv⟩

theorem cofaceCount_pos_of_pure {X : Complex} {n i : ℕ} (hX : X.Pure n)
    (σ : X.Face i) : 0 < X.cofaceCount n σ.val := by
  obtain ⟨τ,hτ,hστ⟩ := hX.2 σ.val (face_mem σ)
  exact Finset.card_pos.mpr ⟨τ,Finset.mem_filter.mpr ⟨hτ,hστ⟩⟩

theorem skeleton_cocycles {X : Complex} {s i : ℕ} (hi : i < s) :
    (X.skeletonCochainEquiv hi.le) '' X.cocycles i = (X.skeleton s).cocycles i := by
  ext f
  obtain ⟨f₀,rfl⟩ := (X.skeletonCochainEquiv hi.le).surjective f
  simp only [Set.mem_image, Set.mem_ofPred_eq, cocycles]
  constructor
  · rintro ⟨g,hg,he⟩
    have hg₀ : g = f₀ := (X.skeletonCochainEquiv hi.le).injective he
    subst g
    rw [X.skeleton_coboundary hi, hg, map_zero]
  · intro hf
    rw [X.skeleton_coboundary hi] at hf
    exact ⟨f₀, (X.skeletonCochainEquiv hi).injective (by simpa using hf), rfl⟩

theorem skeleton_cosystolic_iff {X : Complex} {s i : ℕ} (hi : i < s) (η : ℝ) :
    (∀ f : (X.skeleton s).Cochain i,
      η * (X.skeleton s).distance s i f ((X.skeleton s).cocycles i) ≤
        (X.skeleton s).norm s (i+1) ((X.skeleton s).coboundary i f)) ↔
    (∀ f : X.Cochain i,
      η * X.distance s i f (X.cocycles i) ≤ X.norm s (i+1) (X.coboundary i f)) := by
  constructor
  · intro h f
    have hh := h (X.skeletonCochainEquiv hi.le f)
    rw [← skeleton_cocycles hi, skeleton_distance_image,
      skeleton_coboundary X hi, skeleton_norm] at hh
    exact hh
  · intro h f
    obtain ⟨f₀,rfl⟩ := (X.skeletonCochainEquiv hi.le).surjective f
    rw [← skeleton_cocycles hi, skeleton_distance_image,
      skeleton_coboundary X hi, skeleton_norm]
    exact h f₀

theorem ambient_cosystolic_of_skeleton {X : Complex} {i s n : ℕ}
    (hX : X.Pure n) (hi : i < s) (hs : s ≤ n) {M η : ℝ}
    (_hM : 0 < M) (hη : 0 ≤ η)
    (hc : ∀ ρ : X.Face s, 1 ≤ (X.cofaceCount n ρ.val : ℝ) ∧
      (X.cofaceCount n ρ.val : ℝ) ≤ M)
    (hquant : ∀ f : X.Cochain i,
      η * X.distance s i f (X.cocycles i) ≤ X.norm s (i+1) (X.coboundary i f))
    (f : X.Cochain i) :
    (η/M) * X.distance n i f (X.cocycles i) ≤ X.norm n (i+1) (X.coboundary i f) := by
  have hZ : (X.cocycles i).Nonempty := ⟨0, by simp [cocycles]⟩
  have hdist := (skeleton_distance_comparison hX hi.le hs zero_lt_one hc f hZ).1
  have hnorm := (skeleton_norm_comparison hX hi hs zero_lt_one hc (X.coboundary i f)).2
  simp only [div_one] at hnorm
  apply (mul_le_mul_iff_right₀ (skeletonScale_pos hX hs)).mp
  calc
    X.skeletonScale n s * ((η / M) * X.distance n i f (X.cocycles i)) =
        η * ((X.skeletonScale n s / M) * X.distance n i f (X.cocycles i)) := by ring
    _ ≤ η * X.distance s i f (X.cocycles i) := mul_le_mul_of_nonneg_left hdist hη
    _ ≤ X.norm s (i+1) (X.coboundary i f) := hquant f
    _ ≤ X.skeletonScale n s * X.norm n (i+1) (X.coboundary i f) := hnorm

end CoboundaryExpanders.Complex

namespace CoboundaryExpanders.Construction
open _root_.OAI.CoboundaryExpanders.Complex Filter
variable (p n : ℕ) [Fact p.Prime]

def UniformCosystolic (hn : 1 ≤ n) : Prop :=
  ∃ η : ℝ, 0 < η ∧ ∀ m : ℕ, 2 ≤ m → ∀ i : ℕ, i < n-1 →
    ∀ f : ((finiteCosetComplex p n hn m).skeleton (n-1)).Cochain i,
      η * ((finiteCosetComplex p n hn m).skeleton (n-1)).distance (n-1) i f
          (((finiteCosetComplex p n hn m).skeleton (n-1)).cocycles i) ≤
        ((finiteCosetComplex p n hn m).skeleton (n-1)).norm (n-1) (i+1)
          (((finiteCosetComplex p n hn m).skeleton (n-1)).coboundary i f)

theorem finiteCosetComplex_coface_bounds (hn : 1 ≤ n) (m i : ℕ)
    (σ : (finiteCosetComplex p n hn m).Face i) :
    1 ≤ ((finiteCosetComplex p n hn m).cofaceCount n σ.val : ℝ) ∧
    ((finiteCosetComplex p n hn m).cofaceCount n σ.val : ℝ) ≤ localBound p n := by
  constructor
  · exact_mod_cast cofaceCount_pos_of_pure (finiteCosetComplex_pure p n hn m) σ
  · have hp : σ.val.Nonempty := Finset.card_pos.mp (by rw [face_card σ]; omega)
    obtain ⟨v,hv⟩ := hp
    have h := (cofaceCount_le_topDegree σ n v hv).trans
      (finiteCosetComplex_degree p n hn m n v)
    simpa only [Nat.choose_self, Nat.mul_one] using (show
      ((finiteCosetComplex p n hn m).cofaceCount n σ.val : ℝ) ≤
        (localBound p n * Nat.choose n n : ℕ) from by exact_mod_cast h)

theorem constructed_expansion_of_open_inputs (d : ℕ) (hd : 3 ≤ d) (hp : Odd p)
    (hL : OppositionAcyclic p (2*d) (by omega))
    (hz : ∀ i : ℕ, 0 < i → i < d →
      CongruenceCokernels.ProZero p (2*d-1) i ∧ CongruenceCokernels.ProZero p (2*d) i)
    (hq : UniformCosystolic p (2*d) (by omega)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ m i, i < d →
      ∀ f : (finiteSkeleton p (2*d) (by omega) d m).Cochain i,
        ε * (finiteSkeleton p (2*d) (by omega) d m).distance d i f
            ((finiteSkeleton p (2*d) (by omega) d m).coboundaries i) ≤
          (finiteSkeleton p (2*d) (by omega) d m).norm d (i+1)
            ((finiteSkeleton p (2*d) (by omega) d m).coboundary i f) := by
  obtain ⟨η,hη,hq⟩ := hq
  have hM : 0 < (localBound p (2*d) : ℝ) := by exact_mod_cast localBound_pos p (2*d)
  refine ⟨(η / localBound p (2*d)) / localBound p (2*d), div_pos (div_pos hη hM) hM, ?_⟩
  intro m i hi f
  have hvanish : (finiteCosetComplex p (2*d) (by omega) (m+2)).cocycles i =
      (finiteCosetComplex p (2*d) (by omega) (m+2)).coboundaries i := by
    by_cases hi0 : i = 0
    · subst i
      exact cocycles_zero_eq_coboundaries_of_connected
        (finiteCosetComplex_connected p (2*d) (by omega) (m+2) (by omega))
    · exact finiteCosetComplex_positive_cohomology p (2*d) (by omega) hp hL
        (m+2) i (by omega) (by omega) (by omega) (hz i (by omega) hi).1 (hz i (by omega) hi).2
  apply skeleton_expansion (finiteCosetComplex_pure p (2*d) (by omega) (m+2)) hi (by omega)
    (div_nonneg hη.le hM.le) (finiteCosetComplex_coface_bounds p (2*d) (by omega) (m+2) d)
    hvanish _ f
  intro g
  exact ambient_cosystolic_of_skeleton
    (finiteCosetComplex_pure p (2*d) (by omega) (m+2)) (by omega : i < 2*d-1)
    (by omega) hM hη.le (finiteCosetComplex_coface_bounds p (2*d) (by omega) (m+2) (2*d-1))
    ((skeleton_cosystolic_iff (by omega : i < 2*d-1) η).mp (hq (m+2) (by omega) i (by omega))) g

end CoboundaryExpanders.Construction

namespace CoboundaryExpanders
open Construction

theorem reduction_to_three_open_inputs
    (hinputs : ∀ d : ℕ, ∀ hd : 3 ≤ d, ∃ p : ℕ, ∃ hp : p.Prime, Odd p ∧
      letI : Fact p.Prime := ⟨hp⟩
      OppositionAcyclic p (2*d) (by omega) ∧
      (∀ i : ℕ, 0 < i → i < d →
        CongruenceCokernels.ProZero p (2*d-1) i ∧ CongruenceCokernels.ProZero p (2*d) i) ∧
      UniformCosystolic p (2*d) (by omega)) : MainStatement := by
  intro d hd
  obtain ⟨p,hp,ho,hL,hz,hq⟩ := hinputs d hd
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨D,hPC,hgrowth,hdegree⟩ := constructed_connected_pure_bounded_growing p d hd
  obtain ⟨ε,hε,hexp⟩ := constructed_expansion_of_open_inputs p d hd ho hL hz hq
  exact ⟨D,ε,hε,finiteSkeleton p (2*d) (by omega) d,hPC,hgrowth,hdegree,hexp⟩

end CoboundaryExpanders

end

end OAI
