import Mathlib
import OAI.Analysis.Conductivity.Flux.FiniteEndPhysicalTensor
import OAI.Analysis.Conductivity.Sources.FacePasting
import OAI.Analysis.Conductivity.Variational.SymmetricQuadraticBound

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise
local instance variableCollarTensorMeasurableSpace : MeasurableSpace Mat3 :=
  inferInstanceAs (MeasurableSpace (Fin 3 → Fin 3 → ℝ))
local instance variableCollarTensorBorelSpace : BorelSpace Mat3 :=
  inferInstanceAs (BorelSpace (Fin 3 → Fin 3 → ℝ))

def variableFaceTensor (K : Coord3 → Mat3) (a b : ℝ) (i j : Fin 4) : Coord3 → Mat3 :=
  fun y => attachedVariableTensor
    (fun x => K (flatEndCoordinates a b (sourceFaceAngles i j x))) a i j
      (sourceCollarInverse i j y)

def variableCollarTensor (K : Coord3 → Mat3) (a b : ℝ) : Coord3 → Mat3 :=
  sourceFacePaste (variableFaceTensor K a b) 1

lemma variableFaceTensor_measurable {K : Coord3 → Mat3} (hK : Measurable K)
    (a b : ℝ) (i j : Fin 4) : Measurable (variableFaceTensor K a b i j) := by
  apply (attachedVariableTensor_measurable
    (hK.comp ((contDiff_flatEndCoordinates a b).continuous.measurable.comp
      (show Differentiable ℝ (sourceFaceAngles i j) from
        fun x => (sourceFaceAngles_hasFDeriv i j x).differentiableAt).continuous.measurable)) a i j).comp
    (measurable_sourceCollarInverse i j)

lemma variableCollarTensor_measurable {K : Coord3 → Mat3} (hK : Measurable K)
    (a b : ℝ) : Measurable (variableCollarTensor K a b) :=
  sourceFacePaste_measurable (variableFaceTensor_measurable hK a b) 1

lemma variableFaceTensor_symm {K : Coord3 → Mat3} (hK : ∀ x,(K x).IsSymm)
    (a b : ℝ) (i j : Fin 4) (y : Coord3) :
    (variableFaceTensor K a b i j y).IsSymm :=
  attachedVariableTensor_symmetric (fun _ => hK _) a i j _

lemma sourceFacePasteList_symm {B : Fin 4 → Fin 4 → Coord3 → Mat3}
    (hB : ∀ i j y,(B i j y).IsSymm) (ks : List (Fin 4 × Fin 4)) (y : Coord3) :
    (sourceFacePasteList B 1 ks y).IsSymm := by
  induction ks with
  | nil => exact Matrix.transpose_one
  | cons k ks ih =>
    rw [sourceFacePasteList_cons]
    split_ifs
    · exact hB _ _ _
    · exact ih

lemma variableCollarTensor_symm {K : Coord3 → Mat3} (hK : ∀ x,(K x).IsSymm)
    (a b : ℝ) (y : Coord3) : (variableCollarTensor K a b y).IsSymm :=
  sourceFacePasteList_symm (variableFaceTensor_symm hK a b) _ y

lemma sourceFacePasteList_elliptic {B : Fin 4 → Fin 4 → Coord3 → Mat3}
    (hB : ∀ i j,∃ c C : ℝ,0<c ∧ c<C ∧ ∀ y∈sourceFlatPatch i j,∀ v : Coord3,
      c*‖v‖^2≤v ⬝ᵥ(B i j y*ᵥv) ∧ v ⬝ᵥ(B i j y*ᵥv)≤C*‖v‖^2)
    (ks : List (Fin 4 × Fin 4)) :
    ∃ c C : ℝ,0<c ∧ c<C ∧ ∀ y (v : Coord3),
      c*‖v‖^2≤v ⬝ᵥ(sourceFacePasteList B 1 ks y*ᵥv) ∧
        v ⬝ᵥ(sourceFacePasteList B 1 ks y*ᵥv)≤C*‖v‖^2 := by
  induction ks with
  | nil =>
    obtain ⟨c,C,hc,hcC,h⟩ := identity_matrix_energy_bounds
    exact ⟨c,C,hc,hcC,fun _ => h⟩
  | cons k ks ih =>
    obtain ⟨c,C,hc,hcC,h⟩ := ih
    obtain ⟨d,D,hd,hdD,hk⟩ := hB k.1 k.2
    refine ⟨min c d,max C D,lt_min hc hd,
      lt_of_le_of_lt (min_le_left _ _) (hcC.trans_le (le_max_left _ _)),?_⟩
    intro y v
    rw [sourceFacePasteList_cons]
    split_ifs with hy
    · exact ⟨(mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)).trans (hk y hy v).1,
        (hk y hy v).2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _))⟩
    · exact ⟨(mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)).trans (h y v).1,
        (h y v).2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))⟩

lemma variableCollarTensor_elliptic {K : Coord3 → Mat3} {c C : ℝ}
    (hc : 0<c) (hcC : c≤C)
    (hK : ∀ x v,c*(v ⬝ᵥ v)≤v ⬝ᵥ(K x*ᵥv) ∧ v ⬝ᵥ(K x*ᵥv)≤C*(v ⬝ᵥ v))
    {a : ℝ} (ha : a≠0) (b : ℝ) :
    ∃ l L : ℝ,0<l ∧ l<L ∧ ∀ y (v : Coord3),
      l*‖v‖^2≤v ⬝ᵥ(variableCollarTensor K a b y*ᵥv) ∧
        v ⬝ᵥ(variableCollarTensor K a b y*ᵥv)≤L*‖v‖^2 := by
  apply sourceFacePasteList_elliptic
  intro i j
  obtain ⟨l,L,hl,hlL,h⟩ := attachedVariableTensor_elliptic hc hcC
    (fun x v => hK (flatEndCoordinates a b (sourceFaceAngles i j x)) v) ha i j
  refine ⟨l,L,hl,hlL,?_⟩
  rintro _ ⟨x,hx,rfl⟩ v
  simpa only [variableFaceTensor,sourceCollarInverse_extended i j (le_refl _) (le_refl _) hx]
    using h x hx v

lemma variableCollarTensor_bounded {K : Coord3 → Mat3} (hS : ∀ x,(K x).IsSymm)
    {c C : ℝ} (hc : 0<c) (hcC : c≤C)
    (hK : ∀ x v,c*(v ⬝ᵥ v)≤v ⬝ᵥ(K x*ᵥv) ∧ v ⬝ᵥ(K x*ᵥv)≤C*(v ⬝ᵥ v))
    {a : ℝ} (ha : a≠0) (b : ℝ) :
    ∃ B : ℝ,0<B ∧ ∀ y,‖variableCollarTensor K a b y‖≤B := by
  obtain ⟨l,L,hl,hlL,h⟩ := variableCollarTensor_elliptic hc hcC hK ha b
  refine ⟨3*L,mul_pos (by norm_num) (hl.trans hlL),fun y => ?_⟩
  exact symmetric_matrix_bounded_of_quadratic _ (variableCollarTensor_symm hS a b y)
    (hl.trans hlL).le (fun v => ⟨(mul_nonneg hl.le (sq_nonneg _)).trans (h y v).1,(h y v).2⟩)

lemma variableCollarTensor_open (K : Coord3 → Mat3) (a b : ℝ)
    (i j : Fin 4) {x : Coord3} (hx : x∈sourceCollarOpenBox) :
    variableCollarTensor K a b (sourceCollarPiece i j x)=
      attachedVariableTensor (fun y => K (flatEndCoordinates a b (sourceFaceAngles i j y))) a i j x := by
  rw [variableCollarTensor,sourceFacePaste_open _ _ i j hx]
  simp only [variableFaceTensor,sourceCollarInverse_point i j hx]

end ScalarConductivity

end
end

end OAI
