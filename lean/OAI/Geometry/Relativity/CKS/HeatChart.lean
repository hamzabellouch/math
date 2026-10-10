import OAI.Geometry.Relativity.CKS.FullSphereHeat
import OAI.Geometry.Relativity.CKS.AngularFreeze
import OAI.Geometry.Relativity.CKS.SphericalTensorChart

namespace OAI

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter Finset CKSCalculus CKSRealizedRound CKSSphericalHarmonics
open CKSInducedSphere (E Ix Mat U)
open scoped Topology ContDiff

def positiveChart : Set Point := {x | 0 < x 0}
lemma positiveChart_open : IsOpen positiveChart := isOpen_lt continuous_const (coord 0).continuous

lemma joint_slice {F : ℝ → E → ℝ}
    (hF : ContDiffOn ℝ ∞ (fun z : ℝ × E => F z.1 z.2) heatDomain) (t : ℝ) :
    ContDiffOn ℝ ∞ (F t) U := by
  exact hF.comp (contDiffOn_const.prodMk contDiffOn_id) (fun x hx => hx)
lemma joint_time {F : ℝ → E → ℝ}
    (hF : ContDiffOn ℝ ∞ (fun z : ℝ × E => F z.1 z.2) heatDomain)
    {n : E} (hn : n ∈ U) : ContDiff ℝ ∞ (fun t => F t n) :=
  hF.comp_contDiff (contDiff_id.prodMk contDiff_const) (fun _ => hn)

def chartMass (f : ℝ → E → ℝ) (t c : ℝ → ℝ) (x : Point) : ℝ :=
  c (x 0) + f (t (x 0)) (sphereParam x)
def chartTensorA (T : ℝ → E → Mat) (t : ℝ → ℝ) (x : Point) : ℝ :=
  tensorA (T (t (x 0))) x
def chartTensorPhi (T : ℝ → E → Mat) (t : ℝ → ℝ) (x : Point) : ℝ :=
  tensorPhi (T (t (x 0))) x

lemma radius_comp_smooth {q : ℝ → ℝ} (hq : ContDiffOn ℝ ∞ q (Ioi 0)) :
    ContDiffOn ℝ ∞ (fun x : Point => q (x 0)) positiveChart :=
  hq.comp (coord 0).contDiff.contDiffOn (fun _ hx => hx)

lemma joint_chart_smooth {F : ℝ → E → ℝ} {t : ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ (fun z : ℝ × E => F z.1 z.2) heatDomain)
    (ht : ContDiffOn ℝ ∞ t (Ioi 0)) :
    ContDiffOn ℝ ∞ (fun x : Point => F (t (x 0)) (sphereParam x)) positiveChart :=
  hF.comp ((radius_comp_smooth ht).prodMk sphereParam_smooth.contDiffOn)
    (fun x _ => sphereParam_mem x)

lemma chartMass_smooth {F : ℝ → E → ℝ} {t c : ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ (fun z : ℝ × E => F z.1 z.2) heatDomain)
    (ht : ContDiffOn ℝ ∞ t (Ioi 0)) (hc : ContDiffOn ℝ ∞ c (Ioi 0)) :
    ContDiffOn ℝ ∞ (chartMass F t c) positiveChart :=
  (radius_comp_smooth hc).add (joint_chart_smooth hF ht)

lemma chartTensorA_smooth {T : ℝ → E → Mat} {t : ℝ → ℝ}
    (hT : ∀ i j, ContDiffOn ℝ ∞ (fun z : ℝ × E => T z.1 z.2 i j) heatDomain)
    (ht : ContDiffOn ℝ ∞ t (Ioi 0)) :
    ContDiffOn ℝ ∞ (chartTensorA T t) positiveChart := by
  unfold chartTensorA tensorA pair
  apply ContDiffOn.sum
  intro i hi
  apply ContDiffOn.sum
  intro j hj
  exact (((contDiff_euclidean.mp thetaFrame_smooth i).mul
    (contDiff_euclidean.mp thetaFrame_smooth j)).contDiffOn).mul
      (joint_chart_smooth (F := fun s y => T s y i j) (hT i j) ht)

lemma chartTensorPhi_smooth {T : ℝ → E → Mat} {t : ℝ → ℝ}
    (hT : ∀ i j, ContDiffOn ℝ ∞ (fun z : ℝ × E => T z.1 z.2 i j) heatDomain)
    (ht : ContDiffOn ℝ ∞ t (Ioi 0)) :
    ContDiffOn ℝ ∞ (chartTensorPhi T t) positiveChart := by
  unfold chartTensorPhi tensorPhi tensorB pair
  apply ((coord 1).contDiff.sin.contDiffOn).mul
  apply ContDiffOn.sum
  intro i hi
  apply ContDiffOn.sum
  intro j hj
  exact (((contDiff_euclidean.mp thetaFrame_smooth i).mul
    (contDiff_euclidean.mp phiUnit_smooth j)).contDiffOn).mul
      (joint_chart_smooth (F := fun s y => T s y i j) (hT i j) ht)

lemma chartMass_laplace {F : ℝ → E → ℝ} {t c : ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ (fun z : ℝ × E => F z.1 z.2) heatDomain)
    (ht : ContDiffOn ℝ ∞ t (Ioi 0)) (hc : ContDiffOn ℝ ∞ c (Ioi 0))
    {x : Point} (hx : x ∈ positiveChart) (hs : Real.sin (x 1) ≠ 0) :
    (massJet (chartMass F t c) x).laplace (Real.sin (x 1)) (Real.cos (x 1)) =
      CKSInducedSphere.roundLaplacian (F (t (x 0))) (sphereParam x) := by
  let G : E → ℝ := fun y => c (x 0) + F (t (x 0)) y
  have hG : ContDiffOn ℝ ∞ G U := contDiffOn_const.add (joint_slice hF _)
  have hGchart := hG.comp_contDiff sphereParam_smooth sphereParam_mem
  have hfull := chartMass_smooth hF ht hc
  have he : ∀ y : Point, y 0 = x 0 → chartMass F t c y = G (sphereParam y) := by
    intro y hy
    simp only [chartMass,G,hy]
  have hf2 (y : Point) (hy : y 0 = x 0) : ContDiffAt ℝ 2 (chartMass F t c) y :=
    (hfull.contDiffAt (positiveChart_open.mem_nhds (by change 0 < y 0; rw [hy]; exact hx))).of_le ((ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  have hg2 (y : Point) (_hy : y 0 = x 0) : ContDiffAt ℝ 2 (fun z => G (sphereParam z)) y :=
    hGchart.contDiffAt.of_le ((ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  have h11 := angular_second_congr_leaf hf2 hg2 he (1:Ix) 1 (by decide) (by decide)
  have h22 := angular_second_congr_leaf hf2 hg2 he (2:Ix) 2 (by decide) (by decide)
  have h1 := angular_first_congr_leaf ((hf2 x rfl).differentiableAt (by norm_num))
    (hGchart.differentiable (by simp) x) he (1:Ix) (by decide)
  change D (basis 1) (D (basis 1) (chartMass F t c)) x +
    Real.cos (x 1)/Real.sin (x 1)*D (basis 1) (chartMass F t c) x +
    D (basis 2) (D (basis 2) (chartMass F t c)) x / Real.sin (x 1)^2 = _
  rw [h11,h22,h1]
  simp only [Function.comp_def]
  rw [angular_laplacian hG x hs]
  exact CKSInducedSphere.roundLaplacian_const_add _ _ _

lemma chartMass_first {F : ℝ → E → ℝ} {t c : ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ (fun z : ℝ × E => F z.1 z.2) heatDomain)
    (ht : ContDiffOn ℝ ∞ t (Ioi 0)) (hc : ContDiffOn ℝ ∞ c (Ioi 0))
    {x : Point} (hx : x ∈ positiveChart) (i : Ix) (hi : i ≠ 0) :
    D (basis i) (chartMass F t c) x =
      D (basis i) (fun y => F (t (x 0)) (sphereParam y)) x := by
  have hfull := (chartMass_smooth hF ht hc).contDiffAt (positiveChart_open.mem_nhds hx)
  have hfixed := (joint_slice hF (t (x 0))).comp_contDiff sphereParam_smooth sphereParam_mem
  have he := angular_first_congr_leaf (hfull.differentiableAt (by simp))
    ((contDiff_const.add hfixed).differentiable (by simp) x)
    (G := fun y => c (x 0) + F (t (x 0)) (sphereParam y))
    (by intro y hy; simp only [chartMass,hy]) i hi
  simpa only [D, fderiv_const_add] using he

end
end CKSSphericalChart

end

end OAI
