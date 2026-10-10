import Mathlib

namespace OAI

section


/-! Integral boundary elimination for a collared fan triangulation of a
polygon. Independent lifted polygons may index `C`; there is no finite-cover
or coefficient-identification assumption. This is chain algebra, not a claim
of topological Hurewicz or cellular approximation. -/
noncomputable section
namespace HyperbolicObstruction.CyclicTriangleBoundary
attribute [local instance] Classical.propDecidable
variable {C A : Type*} (size : C → ℕ) (pos : ∀ c, 0 < size c)
abbrev Corner := (c : C) × Fin (size c)
abbrev Triangle := Corner size × Fin 3

def next (q : Corner size) : Corner size := ⟨q.1,finRotate _ q.2⟩
def first (c : C) : Triangle size := (⟨c,⟨0,pos c⟩⟩,0)
lemma first_injective : Function.Injective (first size pos) := by
  intro c d h
  exact congrArg (fun t : Triangle size => t.1.1) h

def collapse (z : Triangle size →₀ ℤ) : C →₀ ℤ :=
  Finsupp.comapDomain (first size pos) z (first_injective size pos).injOn

def expansionColumn (c : C) : Triangle size →₀ ℤ :=
  ∑ i : Fin (size c), ∑ j : Fin 3, Finsupp.single (⟨c,i⟩,j) 1

def expand : (C →₀ ℤ) →ₗ[ℤ] (Triangle size →₀ ℤ) :=
  Finsupp.linearCombination ℤ (expansionColumn size)

lemma expansionColumn_apply (c : C) (q : Corner size) (j : Fin 3) :
    expansionColumn size c (q,j) = if c = q.1 then 1 else 0 := by
  classical
  rcases q with ⟨d,i⟩
  by_cases h : c = d
  · subst d
    simp only [expansionColumn, Finsupp.finsetSum_apply, ite_true]
    change (∑ x : Fin (size c), ∑ k : Fin 3,
      (Finsupp.single ((⟨c,x⟩ : Corner size),k) (1 : ℤ)) (⟨c,i⟩,j)) = 1
    rw [Finset.sum_eq_single i]
    · simp [Finsupp.single_apply]
    · intro k hk hki
      simp [hki]
    · simp
  · simp only [expansionColumn,Finsupp.finsetSum_apply]
    have he (k : Fin (size c)) (l : Fin 3) : ((⟨c,k⟩ : Corner size),l) ≠ (⟨d,i⟩,j) :=
      fun hh => h (congrArg (fun t : Triangle size => t.1.1) hh)
    simp [he,h]

lemma expand_apply (x : C →₀ ℤ) (q : Corner size) (j : Fin 3) :
    expand size x (q,j) = x q.1 := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx,hy]
  | single c a =>
    simp only [expand,Finsupp.linearCombination_single,Finsupp.smul_apply,
      expansionColumn_apply,smul_eq_mul,Finsupp.single_apply]
    split_ifs <;> simp_all

lemma rotate_invariant_constant {m : ℕ} (hm : 0 < m) {B : Type*}
    (f : Fin m → B) (hf : ∀ i, f (finRotate m i) = f i) (i : Fin m) :
    f i = f ⟨0,hm⟩ := by
  cases m with
  | zero => omega
  | succ m =>
    induction i using Fin.induction with
    | zero => rfl
    | succ i hi =>
      have he : finRotate (m+1) i.castSucc = i.succ := by
        exact finRotate_of_lt i.isLt
      rw [←he,hf,hi]

/-- The three internal edge coordinates force every triangle in a lifted
polygon to have one common coefficient. -/
lemma expand_collapse (z : Triangle size →₀ ℤ)
    (diag : ∀ q, z (q,1) = z (q,0))
    (outer : ∀ q, z (q,2) = z (q,1))
    (radial : ∀ q, z (next size q,2) = z (q,2)) :
    expand size (collapse size pos z) = z := by
  apply Finsupp.ext
  rintro ⟨⟨c,i⟩,j⟩
  rw [expand_apply]
  change z (first size pos c) = z ((⟨c,i⟩ : Corner size),j)
  have hconstant := rotate_invariant_constant (pos c)
    (fun i => z ((⟨c,i⟩ : Corner size),2)) (fun i => radial ⟨c,i⟩) i
  have hj (q : Corner size) (k : Fin 3) : z (q,k) = z (q,2) := by
    fin_cases k
    · exact ((outer q).trans (diag q)).symm
    · exact (outer q).symm
    · rfl
  exact (hj _ 0).trans (hconstant.symm.trans (hj _ j).symm)

variable (edge : Corner size → A →₀ ℤ)

def polygonBoundary (c : C) : A →₀ ℤ := ∑ i, edge ⟨c,i⟩
def polygonD₂ : (C →₀ ℤ) →ₗ[ℤ] (A →₀ ℤ) :=
  Finsupp.linearCombination ℤ (polygonBoundary size edge)
def graphPart : (Triangle size →₀ ℤ) →ₗ[ℤ] (A →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun t => if t.2 = 0 then edge t.1 else 0)

lemma graphPart_expand (x : C →₀ ℤ) :
    graphPart size edge (expand size x) = polygonD₂ size edge x := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx,hy]
  | single c a =>
    simp [expand,Finsupp.linearCombination_single,expansionColumn,
      graphPart,map_sum,polygonD₂,polygonBoundary]

include pos in
/-- Full independent cycle elimination, not a scalar augmentation test. -/
lemma cycle_zero (hinj : Function.Injective (polygonD₂ size edge))
    (z : Triangle size →₀ ℤ)
    (graph : graphPart size edge z = 0)
    (diag : ∀ q, z (q,1) = z (q,0))
    (outer : ∀ q, z (q,2) = z (q,1))
    (radial : ∀ q, z (next size q,2) = z (q,2)) : z = 0 := by
  have hz := expand_collapse size pos z diag outer radial
  have hx : collapse size pos z = 0 := by
    apply hinj
    rw [map_zero,←graphPart_expand, hz,graph]
  rw [hx,map_zero] at hz
  exact hz.symm

/-- The previous boundary occurrence, within the same independent polygon. -/
def prev (q : Corner size) : Corner size := ⟨q.1,(finRotate _).symm q.2⟩

@[simp] lemma prev_next (q : Corner size) : prev size (next size q) = q := by
  rcases q with ⟨c,i⟩
  exact congrArg (fun j : Fin (size c) => (⟨c,j⟩ : Corner size))
    ((finRotate (size c)).symm_apply_apply i)
@[simp] lemma next_prev (q : Corner size) : next size (prev size q) = q := by
  rcases q with ⟨c,i⟩
  exact congrArg (fun j : Fin (size c) => (⟨c,j⟩ : Corner size))
    ((finRotate (size c)).apply_symm_apply i)

/-- Full oriented boundary in edge coordinates. The internal factors are,
respectively, radial, collar diagonal, outer and apex edges. Their indices
include the entire independent polygon index; no deck augmentation occurs.
The graph factor can itself be an arbitrary lifted-edge module. -/
def fullD₂ : (Triangle size →₀ ℤ) →ₗ[ℤ]
    ((A →₀ ℤ) × (Corner size → ℤ) × (Corner size → ℤ) ×
      (Corner size → ℤ) × (Corner size → ℤ)) where
  toFun z := (graphPart size edge z,
    (fun q => z (q,0) - z (prev size q,1)),
    (fun q => z (q,1) - z (q,0)),
    (fun q => z (q,2) - z (q,1)),
    (fun q => z (q,2) - z (prev size q,2)))
  map_add' z w := by
    ext <;> simp only [map_add,Finsupp.add_apply,Prod.fst_add,Prod.snd_add,Pi.add_apply] <;> ring
  map_smul' a z := by
    simp only [RingHom.id_apply]
    ext <;> simp [mul_sub]

include pos in
/-- Elimination of the actual collared-fan boundary equations. -/
lemma fullD₂_injective (hinj : Function.Injective (polygonD₂ size edge)) :
    Function.Injective (fullD₂ size edge) := by
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro z hz
  have graph : graphPart size edge z = 0 := congrArg Prod.fst hz
  have diag (q) : z (q,1) = z (q,0) := by
    have h := congrArg (fun x => x.2.2.1 q) hz
    exact sub_eq_zero.mp h
  have outer (q) : z (q,2) = z (q,1) := by
    have h := congrArg (fun x => x.2.2.2.1 q) hz
    exact sub_eq_zero.mp h
  have radial (q) : z (next size q,2) = z (q,2) := by
    have h := congrArg (fun x => x.2.2.2.2 (next size q)) hz
    simpa only [fullD₂,LinearMap.coe_mk,AddHom.coe_mk,Prod.snd_zero,Pi.zero_apply,
      prev_next,sub_eq_zero] using h
  exact cycle_zero size pos edge hinj z graph diag outer radial

end HyperbolicObstruction.CyclicTriangleBoundary
end
end

section

end

end OAI
