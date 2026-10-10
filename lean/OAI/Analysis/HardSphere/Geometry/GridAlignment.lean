import Mathlib
import OAI.Analysis.HardSphere.Orbitals.CenteredCell
import OAI.Analysis.HardSphere.Geometry.SiteCube
import OAI.Analysis.HardSphere.PathBounds.ShiftInteracting

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
open Classical
namespace HardSphere.Groups
open CellOrbital BathSlice HardSphere.Lattice ShiftVisits

def gridCube {K : ℕ} (v : Fin 3→Fin K) : CubeCell K := (v 0,v 1,v 2)
lemma gridCube_injective {K : ℕ} : Function.Injective (gridCube (K:=K)) := by
  intro v w h
  have h0 := congrArg Prod.fst h
  have h1 := congrArg (fun p : CubeCell K ↦ p.2.1) h
  have h2 := congrArg (fun p : CubeCell K ↦ p.2.2) h
  funext j
  fin_cases j <;> assumption

def gridSite {K : ℕ} (v : Fin 3→Fin K) : DiscreteTorus K := fun j ↦ ((v j).val:ZMod K)
lemma gridSite_injective {K : ℕ} [NeZero K] : Function.Injective (gridSite (K:=K)) := by
  intro v w h
  funext j
  apply Fin.ext
  have hh := congrArg (fun f : DiscreteTorus K ↦ (f j).val) h
  simpa only [gridSite,ZMod.val_natCast_of_lt (v j).isLt,ZMod.val_natCast_of_lt (w j).isLt] using hh

lemma siteCube_gridSite {K : ℕ} [NeZero K] (v : Fin 3→Fin K) : siteCube (gridSite v)=gridCube v := by
  apply Prod.ext
  · apply Fin.ext
    exact ZMod.val_natCast_of_lt (v 0).isLt
  · apply Prod.ext <;> apply Fin.ext
    · exact ZMod.val_natCast_of_lt (v 1).isLt
    · exact ZMod.val_natCast_of_lt (v 2).isLt

def gridShift (L : Length) : Torus L := fun _ ↦ ((-1/2:ℝ):AddCircle L.val)

lemma shifted_unitCenter {K : ℕ} (L : Length) (v : Fin 3→Fin K) :
    unitCenter L (gridCube v)+gridShift L=gridCenter L v := by
  funext j
  fin_cases j <;> change ((((_:ℝ)+1/2:ℝ):AddCircle L.val)+((-1/2:ℝ):AddCircle L.val))=(_ : AddCircle L.val)
  all_goals
    rw [←AddCircle.coe_add]
    congr 1
    simp only [gridCube]
    ring_nf
    rfl

lemma shifted_siteCenter {K : ℕ} [NeZero K] (L : Length) (v : Fin 3→Fin K) :
    ShiftVisits.center L (gridShift L) (gridSite v)=gridCenter L v := by
  rw [ShiftVisits.center,←unitCenter_siteCube,siteCube_gridSite]
  exact shifted_unitCenter L v

lemma grid_visitorCount {n K : ℕ} [NeZero K] (L : Length) (E : Set (ConfigurationPath 1 L))
    (v : Fin 3→Fin K) (ω : ConfigurationPath n L) :
    ShiftVisits.visitorCount L (gridShift L) E (gridSite v) ω=
      (Finset.univ.filter (fun i : Fin n ↦ onePathAt i ω∈E ∧ pathVisitsBall L 12 (gridCenter L v) i ω)).card := by
  classical
  simp only [ShiftVisits.visitorCount,shifted_siteCenter]

end HardSphere.Groups

end
end

section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Groups
open HardSphere.Lattice HardSphere.FreeVisits HardSphere.CellOrbital
attribute [local instance] Classical.propDecidable

def rangePackingBox (c : Fin 3→ℝ) : Finset Vertex :=
  Finset.Icc (fun j ↦ ⌊c j⌋-24) (fun j ↦ ⌊c j⌋+24)
lemma card_rangePackingBox (c : Fin 3→ℝ) : (rangePackingBox c).card=49^3 := by
  unfold rangePackingBox
  rw [Pi.card_Icc]
  have h (j : Fin 3) : (Finset.Icc (⌊c j⌋-24) (⌊c j⌋+24)).card=49 := by rw [Int.card_Icc]; omega
  simp only [h,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

lemma grid_packing_witness {K : ℕ} [NeZero K] (L : Length) (hL : L.val=(K:ℝ))
    (c : Fin 3→ℝ) (v : Fin 3→Fin K)
    (hv : ∀j,dist (gridCenter L v j) ((c j:ℝ):AddCircle L.val)≤23) :
    ∃z∈rangePackingBox c,torusProjection K z=gridSite v := by
  let k : Vertex := fun j ↦ round (L.val⁻¹*((v j).val-c j))
  let z : Vertex := fun j ↦ ((v j).val:ℤ)-k j*(K:ℤ)
  refine ⟨z,?_,?_⟩
  · apply Finset.mem_Icc.mpr
    have hz (j : Fin 3) : ⌊c j⌋-24≤z j ∧ z j≤⌊c j⌋+24 := by
      have hd := hv j
      change dist (((v j).val:ℝ):AddCircle L.val) ((c j:ℝ):AddCircle L.val)≤23 at hd
      rw [dist_eq_norm,←AddCircle.coe_sub,AddCircle.norm_eq] at hd
      have hd' : |(z j:ℝ)-c j|≤23 := by
        convert hd using 1
        dsimp [z,k]
        push_cast
        rw [hL]
        ring_nf
      have hl := Int.floor_le (c j)
      have hu := Int.lt_floor_add_one (c j)
      obtain ⟨h₁,h₂⟩ := abs_le.mp hd'
      constructor <;> (apply (Int.cast_le (R:=ℝ)).mp; push_cast; linarith)
    exact ⟨fun j ↦ (hz j).1,fun j ↦ (hz j).2⟩
  · ext j
    simp [torusProjection,z,gridSite]

lemma card_near_grid_le {K : ℕ} [NeZero K] (L : Length) (hL : L.val=(K:ℝ))
    (x : Torus L) (A : Finset (Fin 3→Fin K))
    (hA : ∀v∈A,torusDistance L (gridCenter L v) x≤23) : A.card≤49^3 := by
  let c : Fin 3→ℝ := fun j ↦ (AddCircle.equivIco L.val 0 (x j)).val
  have hc (j : Fin 3) : ((c j:ℝ):AddCircle L.val)=x j := AddCircle.coe_equivIco
  have hsub : A.image gridSite⊆(rangePackingBox c).image (torusProjection K) := by
    intro v hv
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨z,hz,he⟩ := grid_packing_witness L hL c w (fun j ↦ by
      rw [hc]
      exact (dist_coord_le_torusDistance L (gridCenter L w) x j).trans (hA w hw))
    exact Finset.mem_image.mpr ⟨z,hz,he⟩
  have hh : (A.image gridSite).card≤49^3 :=
    (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (card_rangePackingBox c).le)
  rwa [Finset.card_image_of_injective A gridSite_injective] at hh

lemma card_near_labels {I : Type*} [Fintype I] {K : ℕ} [NeZero K]
    (L : Length) (hL : L.val=(K:ℝ)) (anchor : I→Fin 3→Fin K) (M : ℕ)
    (hm : ∀v,(Finset.univ.filter (fun i : I ↦ anchor i=v)).card≤M) (x : Torus L) :
    (Finset.univ.filter (fun i : I ↦ torusDistance L (gridCenter L (anchor i)) x≤23)).card≤49^3*M := by
  let A : Finset (Fin 3→Fin K) := Finset.univ.filter (fun v ↦ torusDistance L (gridCenter L v) x≤23)
  let S : Finset I := Finset.univ.filter (fun i ↦ torusDistance L (gridCenter L (anchor i)) x≤23)
  have hs : ∀i∈S,anchor i∈A := by intro i hi; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2⟩
  have hcard := Finset.card_eq_sum_card_fiberwise hs
  change S.card≤_
  rw [hcard]
  calc
    _ ≤ ∑_v∈A,M := Finset.sum_le_sum (fun v _ ↦ (Finset.card_le_card (by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2⟩)).trans (hm v))
    _ = A.card*M := by simp
    _ ≤ 49^3*M := Nat.mul_le_mul_right _ (card_near_grid_le L hL x A (fun v hv ↦ (Finset.mem_filter.mp hv).2))

end HardSphere.Groups

end
end

end

end OAI
