import Mathlib
import OAI.Analysis.Conductivity.Walls.CriticalWallResidual
import OAI.Analysis.Conductivity.Walls.ParametricWallOperators
import OAI.Analysis.Conductivity.Sources.ParametricSymmetricSources

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [ProperSpace P]

lemma wallParticularTensor_parametric_smoothOn {χ : Box3 → ℝ}
    {v r₁ r₂ : P×Box3 → ℝ} (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ)
    (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v) (h₁ : ContDiff ℝ (↑(⊤:ℕ∞)) r₁)
    (h₂ : ContDiff ℝ (↑(⊤:ℕ∞)) r₂) {V : Set P} (hV : IsOpen V)
    (hne : ∀ p∈V,∀ x∈tsupport χ,
      wallQuotient (wallDerivative (fun y => v (p,y))) x≠0) :
    ContDiffOn ℝ (↑(⊤:ℕ∞)) (fun q : P×Coord3 =>
      wallParticularTensor χ (fun y => v (q.1,y)) (fun y => r₁ (q.1,y)) (fun y => r₂ (q.1,y)) q.2)
      (V×ˢuniv) := by
  unfold wallParticularTensor
  apply wallMatrix_parametric_smoothOn
    (A:=fun q : P×Box3 => χ q.2*wallPrimitive (fun y => r₁ (q.1,y)) q.2)
    (B:=fun q : P×Box3 => χ q.2*(wallQuotient
      (wallParticularNumerator (1,0) (fun y => v (q.1,y)) (fun y => r₁ (q.1,y))
        (fun y => r₂ (q.1,y))) q.2 / wallQuotient (wallDerivative (fun y => v (q.1,y))) q.2))
  · exact ((hχ.comp contDiff_snd).mul (wallPrimitive_parametric_smooth h₁)).contDiffOn
  · exact parametric_smooth_wall_cutoff_ratio hχ
      (wallParticularNumerator_parametric_smooth (1,0) hv h₁ h₂)
      (wallDerivative_parametric_smooth hv) hV hne

lemma wallHomogeneousTensor_parametric_smoothOn {χ : Box3 → ℝ}
    {v : P×Box3 → ℝ} {a : P×(ℝ×ℝ) → ℝ} (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ)
    (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v) (ha : ContDiff ℝ (↑(⊤:ℕ∞)) a)
    {V : Set P} (hV : IsOpen V)
    (hne : ∀ p∈V,∀ x∈tsupport χ,
      wallQuotient (wallDerivative (fun y => v (p,y))) x≠0) :
    ContDiffOn ℝ (↑(⊤:ℕ∞)) (fun q : P×Coord3 =>
      wallHomogeneousTensor χ (fun y => v (q.1,y)) (fun y => a (q.1,y)) q.2) (V×ˢuniv) := by
  unfold wallHomogeneousTensor
  apply wallMatrix_parametric_smoothOn
    (A:=fun q : P×Box3 => χ q.2*a (q.1,q.2.1))
    (B:=fun q : P×Box3 => χ q.2*(wallQuotient
      (wallHomogeneousNumerator (1,0) (fun y => v (q.1,y)) (fun y => a (q.1,y))) q.2 /
        wallQuotient (wallDerivative (fun y => v (q.1,y))) q.2))
  · exact ((hχ.comp contDiff_snd).mul
      (ha.comp (contDiff_fst.prodMk contDiff_snd.fst))).contDiffOn
  · exact parametric_smooth_wall_cutoff_ratio hχ (wallHomogeneousNumerator_parametric_smooth (1,0) hv ha)
      (wallDerivative_parametric_smooth hv) hV hne

lemma wallParticularTensor_zero (χ v : Box3 → ℝ) :
    wallParticularTensor χ v (fun _ => 0) (fun _ => 0)=0 := by
  have hP : wallPrimitive (fun _ : Box3 => (0:ℝ))=fun _ => 0 := by
    funext x; simp [wallPrimitive]
  have hG : wallParticularNumerator (1,0) v (fun _ => 0) (fun _ => 0)=fun _ => 0 := by
    funext x
    simp [wallParticularNumerator,hP,wallAlong]
  funext x
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [wallParticularTensor,wallMatrix,hP,hG,wallQuotient,wallDerivative]

lemma wallHomogeneousTensor_zero (χ v : Box3 → ℝ) :
    wallHomogeneousTensor χ v (fun _ => 0)=0 := by
  have hG : wallHomogeneousNumerator (1,0) v (fun _ => 0)=fun _ => 0 := by
    funext x; simp [wallHomogeneousNumerator,wallAlong]
  funext x
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [wallHomogeneousTensor,wallMatrix,hG,wallQuotient,wallDerivative]

lemma symmetricSource_zero (u : Coord3 → Fin 2 → ℝ) (j : Fin 2) :
    symmetricSource 0 u j=0 := by
  funext x
  simp [symmetricSource,coordinateDivergence]

lemma wallParticularResidual_parametric_smoothOn {χ : Box3 → ℝ}
    {v r₁ r₂ : P×Box3 → ℝ} (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ)
    (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v) (h₁ : ContDiff ℝ (↑(⊤:ℕ∞)) r₁)
    (h₂ : ContDiff ℝ (↑(⊤:ℕ∞)) r₂) {V : Set P} (hV : IsOpen V)
    (hne : ∀ p∈V,∀ x∈tsupport χ,
      wallQuotient (wallDerivative (fun y => v (p,y))) x≠0) (j : Fin 2) :
    ContDiffOn ℝ (↑(⊤:ℕ∞)) (fun q : P×Coord3 =>
      wallParticularResidual χ (fun y => v (q.1,y)) (fun y => r₁ (q.1,y)) (fun y => r₂ (q.1,y)) j q.2)
      (V×ˢuniv) := by
  have hs := symmetricSource_parametric_smoothOn (hV.prod isOpen_univ)
    (wallParticularTensor_parametric_smoothOn hχ hv h₁ h₂ hV hne)
    (wallCoordinatePair_parametric_smooth hv).contDiffOn j
  have hm : ContDiff ℝ (↑(⊤:ℕ∞)) (fun q : P×Coord3 => (q.1,boxCoordinates q.2)) :=
    contDiff_fst.prodMk (boxCoordinates.contDiff.comp contDiff_snd)
  fin_cases j
  · exact (h₁.comp hm).contDiffOn.sub hs
  · exact (h₂.comp hm).contDiffOn.sub hs

end ScalarConductivity

end


noncomputable section
namespace ScalarConductivity
open Set Matrix MeasureTheory Filter Topology

lemma wallCoordinatePair_surjective {v : Box3 → ℝ} (hv : Differentiable ℝ v)
    {x : Coord3} (hne : wallDerivative v (boxCoordinates x)≠0) :
    Function.Surjective (fderiv ℝ (wallCoordinatePair v) x) := by
  intro b
  let c := (b 1-wallAlong (1,0) v (boxCoordinates x)*b 0)/wallDerivative v (boxCoordinates x)
  refine ⟨![b 0,0,c],?_⟩
  rw [wallCoordinatePair_derivative hv]
  have he : boxCoordinates ![b 0,0,c]=
      b 0 • (((1:ℝ),0),0)+c • (((0:ℝ),0),1) := by
    ext <;> simp [boxCoordinates_apply]
  rw [he,map_add,map_smul,map_smul]
  ext j
  fin_cases j
  · rfl
  · change b 0*wallAlong (1,0) v (boxCoordinates x)+c*wallDerivative v (boxCoordinates x)=b 1
    dsimp [c]
    field_simp
    ring

lemma wallCoordinatePair_surjective_off_wall {v : Box3 → ℝ}
    (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v) (hz : ∀ q,wallDerivative v (q,0)=0)
    {x : Coord3} (hx : (boxCoordinates x).2≠0)
    (hne : wallQuotient (wallDerivative v) (boxCoordinates x)≠0) :
    Function.Surjective (fderiv ℝ (wallCoordinatePair v) x) := by
  apply wallCoordinatePair_surjective (hv.differentiable (by simp))
  rw [(smooth_wall_division (wallDerivative_smooth hv) hz).2 (boxCoordinates x)]
  exact mul_ne_zero hx hne

def wallPositiveCut (δ : ℝ) (f : Coord3 → ℝ) (x : Coord3) : ℝ :=
  Real.smoothTransition (x 2/δ)*f x

lemma wallPositiveCut_smooth {δ : ℝ} {f : Coord3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (wallPositiveCut δ f) :=
  (Real.smoothTransition.contDiff.comp ((contDiff_apply ℝ ℝ (2:Fin 3)).div_const δ)).mul hf

lemma wallPositiveCut_indicator {δ : ℝ} (hδ : 0<δ) {f : Coord3 → ℝ}
    (hs : ∀ x∈tsupport f,δ≤|x 2|) :
    wallPositiveCut δ f={x : Coord3 | 0<x 2}.indicator f := by
  funext x
  by_cases hx : 0<x 2
  · rw [indicator_of_mem (show x∈{x : Coord3 | 0<x 2} from hx)]
    by_cases hf : f x=0
    · simp [wallPositiveCut,hf]
    · have hbound := hs x (subset_tsupport f hf)
      rw [abs_of_pos hx] at hbound
      simp only [wallPositiveCut,Real.smoothTransition.one_of_one_le ((le_div_iff₀ hδ).mpr (by simpa using hbound)),one_mul]
  · rw [indicator_of_notMem (show x∉{x : Coord3 | 0<x 2} from hx)]
    exact mul_eq_zero_of_left (Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hx) hδ.le)) _

lemma wallPositiveCut_tsupport {δ : ℝ} (hδ : 0<δ) {f : Coord3 → ℝ}
    (hs : ∀ x∈tsupport f,δ≤|x 2|) :
    tsupport (wallPositiveCut δ f)⊆tsupport f∩{x : Coord3 | δ≤x 2} := by
  apply subset_inter tsupport_mul_subset_right
  apply closure_minimal _ (isClosed_le continuous_const (continuous_apply 2))
  intro x hx
  have hf : f x≠0 := fun hh => hx (by simp [hh])
  have hp : 0<x 2 := by
    by_contra hn
    apply hx
    exact mul_eq_zero_of_left (Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hδ.le)) _
  change δ≤x 2
  simpa only [abs_of_pos hp] using hs x (subset_tsupport f hf)

lemma wallNegativeCut_tsupport {δ : ℝ} (hδ : 0<δ) {f : Coord3 → ℝ}
    (hs : ∀ x∈tsupport f,δ≤|x 2|) :
    tsupport (fun x => f x-wallPositiveCut δ f x)⊆tsupport f∩{x : Coord3 | x 2≤ -δ} := by
  apply subset_inter
  · exact (tsupport_sub _ _).trans (union_subset Subset.rfl tsupport_mul_subset_right)
  · apply closure_minimal _ (isClosed_le (continuous_apply 2) continuous_const)
    intro x hx
    have hf : f x≠0 := fun hh => hx (by simp [wallPositiveCut,hh])
    have hn : x 2≤0 := by
      by_contra hn
      have hp : 0<x 2 := lt_of_not_ge hn
      have he := congrFun (wallPositiveCut_indicator hδ hs) x
      rw [indicator_of_mem (show x∈{x : Coord3 | 0<x 2} from hp)] at he
      exact hx (by change f x-wallPositiveCut δ f x=0; rw [he,sub_self])
    have hh := hs x (subset_tsupport f hf)
    rw [abs_of_nonpos hn] at hh
    change x 2≤ -δ
    linarith

end ScalarConductivity

end

end OAI
