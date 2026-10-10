import Mathlib
import OAI.Analysis.Conductivity.Walls.WallSideMoments
import OAI.Analysis.Conductivity.Variational.ParametricMomentSmall
import OAI.Analysis.Conductivity.Walls.ParametricWallAmplitude

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Matrix Filter Topology
open scoped Matrix.Norms.Elementwise
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

def wallTransferSource (χ : Box3 → ℝ) (v : P×Box3 → ℝ)
    (θ η : ℝ → ℝ) (σ lam : ℝ) (j : Fin 2) (q : (P×Coord3)×Coord3) : ℝ :=
  symmetricSource (fun x => wallTransferFamily χ v θ η σ lam (q.1,x))
    (wallCoordinatePair (fun y => v (q.1.1,y))) j q.2

lemma wallTransferSource_smoothOn {χ : Box3 → ℝ} {v : P×Box3 → ℝ}
    {θ η : ℝ → ℝ} (σ lam : ℝ)
    (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v)
    (hθ : ContDiff ℝ (↑(⊤:ℕ∞)) θ) (hη : ContDiff ℝ (↑(⊤:ℕ∞)) η)
    {V : Set P} (hV : IsOpen V)
    (hne : ∀ p∈V,∀ x∈tsupport χ,wallQuotient (wallDerivative (fun y => v (p,y))) x≠0) (j) :
    ContDiffOn ℝ (↑(⊤:ℕ∞)) (wallTransferSource χ v θ η σ lam j) ((V×ˢuniv)×ˢuniv) :=
  symmetricSource_parametric_smoothOn
    (H:=wallTransferFamily χ v θ η σ lam)
    (u:=fun q : (P×Coord3)×Coord3 => wallCoordinatePair (fun y => v (q.1.1,y)) q.2)
    ((hV.prod isOpen_univ).prod isOpen_univ)
    (wallTransferFamily_smoothOn σ lam hχ hv hθ hη hV hne)
    ((wallCoordinatePair_parametric_smooth hv).comp
      (contDiff_fst.fst.prodMk contDiff_snd)).contDiffOn j

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
lemma wallTransferSource_zero (χ : Box3 → ℝ) (v : P×Box3 → ℝ)
    (θ η : ℝ → ℝ) (σ lam : ℝ) (p : P) (j : Fin 2) (x : Coord3) :
    wallTransferSource χ v θ η σ lam j ((p,0),x)=0 := by
  have he : (fun x => wallTransferFamily χ v θ η σ lam ((p,0),x))=0 :=
    funext (wallTransferFamily_zero χ v θ η σ lam p)
  dsimp only [wallTransferSource]
  rw [he,symmetricSource_zero]
  rfl

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
lemma wallTransferSource_tsupport {χ : Box3 → ℝ} (hχc : HasCompactSupport χ)
    (v : P×Box3 → ℝ) (θ η : ℝ → ℝ) (σ lam : ℝ) (q : P×Coord3) (j) :
    tsupport (fun x => wallTransferSource χ v θ η σ lam j (q,x))⊆boxCoordinates ⁻¹' tsupport χ :=
  (symmetricSource_tsupport (fun x => wallTransferFamily χ v θ η σ lam (q,x))
    (wallCoordinatePair (fun y => v (q.1,y))) j).trans
      (wallHomogeneousTensor_compact (χ:=χ) (v:=fun y => v (q.1,y))
        (a:=wallMomentAmplitude θ η σ lam q.2) hχc).2

lemma wallTransferFamily_small {χ : Box3 → ℝ} {v : P×Box3 → ℝ}
    {θ η : ℝ → ℝ} (σ lam : ℝ)
    (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hχc : HasCompactSupport χ)
    (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v)
    (hθ : ContDiff ℝ (↑(⊤:ℕ∞)) θ) (hη : ContDiff ℝ (↑(⊤:ℕ∞)) η)
    {p : P} {V : Set P} (hV : IsOpen V) (hp : p∈V)
    (hne : ∀ p∈V,∀ x∈tsupport χ,wallQuotient (wallDerivative (fun y => v (p,y))) x≠0)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ q in 𝓝 (p,(0:Coord3)),∀ x,‖wallTransferFamily χ v θ η σ lam (q,x)‖≤ε := by
  apply compact_parametric_norm_small_global (f:=wallTransferFamily χ v θ η σ lam) (p:=(p,(0:Coord3)))
    (boxCoordinates.toHomeomorph.isCompact_preimage.mpr hχc)
  · intro x _
    exact ((wallTransferFamily_smoothOn σ lam hχ hv hθ hη hV hne).contDiffAt
      (((hV.prod isOpen_univ).prod isOpen_univ).mem_nhds ⟨⟨hp,mem_univ 0⟩,mem_univ x⟩)).continuousAt
  · exact wallTransferFamily_zero χ v θ η σ lam p
  · apply Eventually.of_forall
    intro q
    exact (wallHomogeneousTensor_compact (χ:=χ) (v:=fun y => v (q.1,y))
      (a:=wallMomentAmplitude θ η σ lam q.2) hχc).2
  · exact hε

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

lemma wall_transfer_balanced_residual
    {χ v : Box3 → ℝ} {a : ℝ×ℝ → ℝ}
    (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hχc : HasCompactSupport χ)
    (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v) (ha : ContDiff ℝ (↑(⊤:ℕ∞)) a)
    (hz : ∀ z,wallDerivative v (z,0)=0)
    (hne : ∀ z∈tsupport χ,wallQuotient (wallDerivative v) z≠0)
    (hcut : ∀ z,χ (z,0)*a z=a z)
    {δ : ℝ} (hδ : 0<δ)
    (hgap : ∀ j x,x∈tsupport (symmetricSource (wallHomogeneousTensor χ v a) (wallCoordinatePair v) j) → δ≤|x 2|)
    {r : PhysicalSourcePair} (hr : CompactSmoothPair r)
    (hm : physicalSourceMoment (wallCoordinatePair v) r=0)
    (hp : ∀ i,(∫ z,a z*wallActualMoment v z i)=
      -physicalSourceMoment (wallCoordinatePair v) (fun j => wallPositiveCut δ (r j)) i) :
    physicalSourceMoment (wallCoordinatePair v)
      (r-symmetricSource (wallHomogeneousTensor χ v a) (wallCoordinatePair v))=0 ∧
    physicalSourceMoment (wallCoordinatePair v)
      (fun j => wallPositiveCut δ ((r-symmetricSource (wallHomogeneousTensor χ v a) (wallCoordinatePair v)) j))=0 := by
  let H := wallHomogeneousTensor χ v a
  let u := wallCoordinatePair v
  have hH : ContDiff ℝ (↑(⊤:ℕ∞)) H := wallHomogeneousTensor_smooth hχ hv ha hne
  have hHc : HasCompactSupport H := (wallHomogeneousTensor_compact (v:=v) (a:=a) hχc).1
  have hu : ContDiff ℝ (↑(⊤:ℕ∞)) u := wallCoordinatePair_smooth hv
  have hs := symmetricSource_compactSmoothPair hH hHc hu
  have hpos : physicalSourceMoment u (fun j => wallPositiveCut δ (symmetricSource H u j))=
      physicalSourceMoment u (fun j => wallPositiveCut δ (r j)) := by
    rw [wallPositiveSource_moment hχ hχc hv ha hz hne hcut hδ hgap]
    ext i
    rw [hp i,neg_neg]
  constructor
  · rw [physicalSourceMoment_sub hu.continuous hr hs,hm,
      physicalSourceMoment_symmetricSource hH hHc (wallMatrix_symmetric _ _) hu,sub_self]
  · have he : (fun j => wallPositiveCut δ ((r-symmetricSource H u) j))=
        (fun j => wallPositiveCut δ (r j))-(fun j => wallPositiveCut δ (symmetricSource H u j)) := by
      ext j x
      exact congrFun (wallPositiveCut_sub δ (r j) (symmetricSource H u j)) x
    change physicalSourceMoment u (fun j => wallPositiveCut δ ((r-symmetricSource H u) j))=0
    rw [he,physicalSourceMoment_sub hu.continuous (hr.wallPositiveCut δ) (hs.wallPositiveCut δ),hpos,sub_self]

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

lemma wall_transfer_residual_solver
    {v : P×Box3 → ℝ} (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v) (p : P)
    {U : Set Coord3} (hU : IsOpen U)
    (hcp : IsPreconnected (U∩{x : Coord3 | 0<x 2}))
    (hcn : IsPreconnected (U∩{x : Coord3 | x 2<0}))
    (hD : ∀ x∈U,x 2≠0 → Function.Surjective
      (fderiv ℝ (wallCoordinatePair (fun y => v (p,y))) x))
    {χ : Box3 → ℝ} (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hχc : HasCompactSupport χ)
    (hχU : boxCoordinates ⁻¹' tsupport χ⊆U)
    {θ η : ℝ → ℝ} (hθ : ContDiff ℝ (↑(⊤:ℕ∞)) θ) (hη : ContDiff ℝ (↑(⊤:ℕ∞)) η)
    (σ lam : ℝ) {V : Set P} (hV : IsOpen V) (hp : p∈V)
    (hne : ∀ q∈V,∀ z∈tsupport χ,wallQuotient (wallDerivative (fun y => v (q,y))) z≠0)
    {r : Fin 2 → P×Coord3 → ℝ}
    (hr : ∀ j,ContDiffOn ℝ (↑(⊤:ℕ∞)) (r j) (V×ˢuniv))
    {K : Set Coord3} (hK : IsCompact K) (hKU : K⊆U)
    (hs : ∀ᶠ q in 𝓝 p,PairSupported (fun j x => r j (q,x)) K)
    {δ : ℝ} (hδ : 0<δ)
    (hgap : ∀ᶠ q in 𝓝 p,∀ j x,x∈tsupport (fun y => r j (q,y)) → δ≤|x 2|)
    (hG : ∀ q∈V,∀ c j x,x∈tsupport (fun y => wallTransferSource χ v θ η σ lam j ((q,c),y)) → δ≤|x 2|)
    (hrz : ∀ j x,r j (p,x)=0) {ε : ℝ} (hε : 0<ε) :
    let R : Fin 2 → (P×Coord3)×Coord3 → ℝ := fun j q =>
      r j (q.1.1,q.2)-wallTransferSource χ v θ η σ lam j q
    ∀ᶠ q in 𝓝 (p,(0:Coord3)),
      physicalSourceMoment (wallCoordinatePair (fun y => v (q.1,y))) (fun j x => R j (q,x))=0 →
      physicalSourceMoment (wallCoordinatePair (fun y => v (q.1,y)))
        (fun j => wallPositiveCut δ (fun x => R j (q,x)))=0 →
      BoundedPhysicallyCorrectable (wallCoordinatePair (fun y => v (q.1,y))) U (fun j x => R j (q,x)) ε := by
  let u : P×Coord3 → Fin 2 → ℝ := fun q => wallCoordinatePair (fun y => v (q.1,y)) q.2
  have hu : ContDiff ℝ (↑(⊤:ℕ∞)) u := wallCoordinatePair_parametric_smooth hv
  let R : Fin 2 → (P×Coord3)×Coord3 → ℝ := fun j q =>
    r j (q.1.1,q.2)-wallTransferSource χ v θ η σ lam j q
  have hR (j) : ContDiffOn ℝ (↑(⊤:ℕ∞)) (R j) ((V×ˢuniv)×ˢuniv) := by
    exact ((hr j).comp (contDiff_fst.fst.prodMk contDiff_snd).contDiffOn
      (fun q hq => ⟨hq.1.1,mem_univ q.2⟩)).sub
        (wallTransferSource_smoothOn σ lam hχ hv hθ hη hV hne j)
  have hRz (j x) : R j ((p,0),x)=0 := by
    simp only [R,hrz,wallTransferSource_zero,sub_self]
  have hlift : Tendsto (Prod.fst : P×Coord3 → P) (𝓝 (p,0)) (𝓝 p) := continuous_fst.tendsto _
  have hRs : ∀ᶠ q in 𝓝 (p,(0:Coord3)),PairSupported (fun j x => R j (q,x))
      (K∪boxCoordinates ⁻¹' tsupport χ) := by
    filter_upwards [hlift.eventually hs] with q hq
    intro j
    exact (tsupport_sub _ _).trans (union_subset ((hq j).trans subset_union_left)
      ((wallTransferSource_tsupport hχc v θ η σ lam q j).trans subset_union_right))
  have hRg : ∀ᶠ q in 𝓝 (p,(0:Coord3)),∀ j x,x∈tsupport (fun y => R j (q,y)) → δ≤|x 2| := by
    filter_upwards [hlift.eventually hgap,hlift.eventually (hV.mem_nhds hp)] with q hq hqV
    intro j x hx
    rcases tsupport_sub _ _ hx with hx | hx
    · exact hq j x hx
    · exact hG q.1 hqV q.2 j x hx
  exact two_sided_vanishing_family_correction
    (u:=fun q : (P×Coord3)×Coord3 => u (q.1.1,q.2))
    (r:=R) (hu.comp (contDiff_fst.fst.prodMk contDiff_snd)) (p,(0:Coord3)) hU hcp hcn hD
    (hK.union (boxCoordinates.toHomeomorph.isCompact_preimage.mpr hχc))
    (union_subset hKU hχU) hδ (hV.prod isOpen_univ) ⟨hp,mem_univ 0⟩ hR hRs hRg hRz hε

end ScalarConductivity

end
end

end OAI
