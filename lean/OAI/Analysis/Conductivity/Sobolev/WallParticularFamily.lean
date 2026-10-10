import Mathlib
import OAI.Analysis.Conductivity.Walls.WallSideMoments

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Matrix Filter Topology
open scoped Matrix.Norms.Elementwise
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

def wallInputPair (r : Fin 2 → P×Box3 → ℝ) (p : P) : PhysicalSourcePair :=
  fun j x => r j (p,boxCoordinates x)

def wallParticularFamily (χ : Box3 → ℝ) (v : P×Box3 → ℝ)
    (r : Fin 2 → P×Box3 → ℝ) (q : P×Coord3) : Mat3 :=
  wallParticularTensor χ (fun y => v (q.1,y))
    (fun y => r 0 (q.1,y)) (fun y => r 1 (q.1,y)) q.2

def wallResidualFamily (χ : Box3 → ℝ) (v : P×Box3 → ℝ)
    (r : Fin 2 → P×Box3 → ℝ) (j : Fin 2) (q : P×Coord3) : ℝ :=
  wallParticularResidual χ (fun y => v (q.1,y))
    (fun y => r 0 (q.1,y)) (fun y => r 1 (q.1,y)) j q.2

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
lemma wallResidualFamily_eq (χ : Box3 → ℝ) (v : P×Box3 → ℝ)
    (r : Fin 2 → P×Box3 → ℝ) (p : P) :
    (fun j x => wallResidualFamily χ v r j (p,x))=
      wallInputPair r p-symmetricSource (fun x => wallParticularFamily χ v r (p,x))
        (wallCoordinatePair (fun y => v (p,y))) := by
  ext j x
  fin_cases j <;> rfl

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
lemma wallResidualFamily_zero {χ : Box3 → ℝ} {v : P×Box3 → ℝ}
    {r : Fin 2 → P×Box3 → ℝ} {p : P} (hz : ∀ j y,r j (p,y)=0) (j x) :
    wallResidualFamily χ v r j (p,x)=0 := by
  have he (j) : (fun y => r j (p,y))=fun _ => 0 := funext (hz j)
  dsimp [wallResidualFamily,wallParticularResidual]
  rw [he 0,he 1,wallParticularTensor_zero,symmetricSource_zero]
  fin_cases j <;> simp [hz]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
lemma wallParticularFamily_zero {χ : Box3 → ℝ} {v : P×Box3 → ℝ}
    {r : Fin 2 → P×Box3 → ℝ} {p : P} (hz : ∀ j y,r j (p,y)=0) (x) :
    wallParticularFamily χ v r (p,x)=0 := by
  have he (j) : (fun y => r j (p,y))=fun _ => 0 := funext (hz j)
  dsimp [wallParticularFamily]
  rw [he 0,he 1,wallParticularTensor_zero]
  rfl

omit [FiniteDimensional ℝ P] in
lemma wallInputPair_compactSmooth {r : Fin 2 → P×Box3 → ℝ}
    (hr : ∀ j,ContDiff ℝ (↑(⊤:ℕ∞)) (r j)) {S : Set Box3} (hS : IsCompact S)
    {p : P} (hs : ∀ j,tsupport (fun y => r j (p,y))⊆S) :
    CompactSmoothPair (wallInputPair r p) := by
  intro j
  refine ⟨(hr j).comp (contDiff_const.prodMk boxCoordinates.contDiff),?_⟩
  have hc : HasCompactSupport (fun y => r j (p,y)) := hS.of_isClosed_subset (isClosed_tsupport _) (hs j)
  exact hc.comp_homeomorph boxCoordinates.toHomeomorph

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
lemma wallResidualFamily_tsupport {χ : Box3 → ℝ} {v : P×Box3 → ℝ}
    {r : Fin 2 → P×Box3 → ℝ} {S : Set Box3} {p : P}
    (hχc : HasCompactSupport χ) (hs : ∀ j,tsupport (fun y => r j (p,y))⊆S) (j : Fin 2) :
    tsupport (fun x => wallResidualFamily χ v r j (p,x))⊆boxCoordinates ⁻¹' (S∪tsupport χ) := by
  have he := congrFun (wallResidualFamily_eq χ v r p) j
  rw [he]
  apply (tsupport_sub _ _).trans
  apply union_subset
  · exact (tsupport_comp_subset_preimage (fun y => r j (p,y)) boxCoordinates.continuous).trans
      ((preimage_mono (hs j)).trans (preimage_mono subset_union_left))
  · exact (symmetricSource_tsupport _ _ j).trans
      ((wallParticularTensor_compact (χ:=χ) (v:=fun y => v (p,y))
        (r₁:=fun y => r 0 (p,y)) (r₂:=fun y => r 1 (p,y))
        hχc).2.trans (preimage_mono subset_union_right))

lemma wallParticularFamily_smoothOn {χ : Box3 → ℝ} {v : P×Box3 → ℝ}
    {r : Fin 2 → P×Box3 → ℝ} (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ)
    (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v) (hr : ∀ j,ContDiff ℝ (↑(⊤:ℕ∞)) (r j))
    {V : Set P} (hV : IsOpen V)
    (hne : ∀ p∈V,∀ x∈tsupport χ,wallQuotient (wallDerivative (fun y => v (p,y))) x≠0) :
    ContDiffOn ℝ (↑(⊤:ℕ∞)) (wallParticularFamily χ v r) (V×ˢuniv) :=
  wallParticularTensor_parametric_smoothOn hχ hv (hr 0) (hr 1) hV hne

lemma wallResidualFamily_smoothOn {χ : Box3 → ℝ} {v : P×Box3 → ℝ}
    {r : Fin 2 → P×Box3 → ℝ} (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ)
    (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v) (hr : ∀ j,ContDiff ℝ (↑(⊤:ℕ∞)) (r j))
    {V : Set P} (hV : IsOpen V)
    (hne : ∀ p∈V,∀ x∈tsupport χ,wallQuotient (wallDerivative (fun y => v (p,y))) x≠0) (j) :
    ContDiffOn ℝ (↑(⊤:ℕ∞)) (wallResidualFamily χ v r j) (V×ˢuniv) :=
  wallParticularResidual_parametric_smoothOn hχ hv (hr 0) (hr 1) hV hne j

lemma wallParticularFamily_small {χ : Box3 → ℝ} {v : P×Box3 → ℝ}
    {r : Fin 2 → P×Box3 → ℝ} (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ)
    (hχc : HasCompactSupport χ) (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v)
    (hr : ∀ j,ContDiff ℝ (↑(⊤:ℕ∞)) (r j)) {p : P} {V : Set P}
    (hV : IsOpen V) (hp : p∈V)
    (hne : ∀ p∈V,∀ x∈tsupport χ,wallQuotient (wallDerivative (fun y => v (p,y))) x≠0)
    (hz : ∀ j y,r j (p,y)=0) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ q in 𝓝 p,∀ x,‖wallParticularFamily χ v r (q,x)‖≤ε := by
  apply compact_parametric_norm_small_global (f:=wallParticularFamily χ v r) (p:=p)
    (boxCoordinates.toHomeomorph.isCompact_preimage.mpr hχc)
  · intro x _
    exact ((wallParticularFamily_smoothOn hχ hv hr hV hne).contDiffAt
      ((hV.prod isOpen_univ).mem_nhds ⟨hp,mem_univ x⟩)).continuousAt
  · exact wallParticularFamily_zero hz
  · apply Eventually.of_forall
    intro q
    exact (wallParticularTensor_compact (χ:=χ) (v:=fun y => v (q,y))
      (r₁:=fun y => r 0 (q,y)) (r₂:=fun y => r 1 (q,y)) hχc).2
  · exact hε

omit [FiniteDimensional ℝ P] in
lemma wallResidualFamily_moment {χ : Box3 → ℝ} {v : P×Box3 → ℝ}
    {r : Fin 2 → P×Box3 → ℝ} (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ)
    (hχc : HasCompactSupport χ) (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v)
    (hr : ∀ j,ContDiff ℝ (↑(⊤:ℕ∞)) (r j)) {p : P}
    (hrs : ∀ j,HasCompactSupport (fun y => r j (p,y)))
    (hne : ∀ x∈tsupport χ,wallQuotient (wallDerivative (fun y => v (p,y))) x≠0) :
    physicalSourceMoment (wallCoordinatePair (fun y => v (p,y)))
      (fun j x => wallResidualFamily χ v r j (p,x))=
    physicalSourceMoment (wallCoordinatePair (fun y => v (p,y))) (wallInputPair r p) := by
  have hvp : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y => v (p,y)) := hv.comp (contDiff_const.prodMk contDiff_id)
  have hrp (j) : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y => r j (p,y)) := (hr j).comp (contDiff_const.prodMk contDiff_id)
  have hh := wallParticularResidual_moments hχ hχc hvp (hrp 0) (hrp 1) (hrs 0) (hrs 1) hne
  ext i
  fin_cases i
  · exact hh.2.2.1
  · exact hh.2.2.2.1
  · exact hh.2.2.2.2

end ScalarConductivity

end
end

end OAI
