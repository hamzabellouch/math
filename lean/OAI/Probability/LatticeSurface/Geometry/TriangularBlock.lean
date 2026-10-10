import Mathlib
import OAI.Probability.LatticeSurface.Convexity.BrunnMinkowski
import OAI.Probability.LatticeSurface.Convexity.CubePrekopa
import OAI.Probability.LatticeSurface.Convexity.FacetDeficitAnalytic
import OAI.Probability.LatticeSurface.Convexity.FacetQuantile
import OAI.Probability.LatticeSurface.Convexity.InteriorQuantile
import OAI.Probability.LatticeSurface.Convexity.QuantileCentroid
import OAI.Probability.LatticeSurface.Convexity.QuantileTransport
import OAI.Probability.LatticeSurface.Convexity.QuantitativeTransport
import OAI.Probability.LatticeSurface.Convexity.RadialExposure
import OAI.Probability.LatticeSurface.Convexity.SliceDensity
import OAI.Probability.LatticeSurface.Convexity.SliceGeometry
import OAI.Probability.LatticeSurface.Convexity.SliceMoments
import OAI.Probability.LatticeSurface.Convexity.WeightedPrekopa
import OAI.Probability.LatticeSurface.Dynamics.DisplacementInequality
import OAI.Probability.LatticeSurface.Geometry.BlockAnalytic
import OAI.Probability.LatticeSurface.Geometry.BlockEdgeGeometry
import OAI.Probability.LatticeSurface.Geometry.BlockFacetGeometry
import OAI.Probability.LatticeSurface.Geometry.BlockRadial
import OAI.Probability.LatticeSurface.Geometry.BlockTelescope
import OAI.Probability.LatticeSurface.Geometry.BlockVolume
import OAI.Probability.LatticeSurface.Geometry.EdgeCoordinates
import OAI.Probability.LatticeSurface.Geometry.FacetBody
import OAI.Probability.LatticeSurface.Geometry.FacetExposure
import OAI.Probability.LatticeSurface.Geometry.TriangularCover
import OAI.Probability.LatticeSurface.Geometry.TriangularGeometry
import OAI.Probability.LatticeSurface.Geometry.UniformFacet

namespace OAI

open MeasureTheory

open scoped ENNReal

noncomputable section

namespace TriangularLipschitz

end TriangularLipschitz

namespace FacetExposure

end FacetExposure

namespace TriangularLipschitz

end TriangularLipschitz

namespace TriangularLipschitz

end TriangularLipschitz

namespace TriangularLipschitz

end TriangularLipschitz

open MeasureTheory Set

open scoped ENNReal

noncomputable section

namespace EdgeCoordinates

end EdgeCoordinates

namespace EdgeCoordinates

end EdgeCoordinates

namespace EdgeCoordinates

end EdgeCoordinates

namespace TriangularLipschitz

end TriangularLipschitz

namespace TriangularLipschitz

end TriangularLipschitz

namespace TriangularLipschitz

end TriangularLipschitz

open Set MeasureTheory Filter

open scoped Topology

noncomputable section

namespace FacetVolume

end FacetVolume

open Set MeasureTheory Filter

open scoped Topology

noncomputable section

namespace SliceTransport

end SliceTransport

namespace FacetVolume

end FacetVolume

namespace FacetVolume

end FacetVolume

namespace TriangularLipschitz

end TriangularLipschitz

open scoped BigOperators

namespace TriangularLipschitz

end TriangularLipschitz

namespace TriangularLipschitz

lemma fillingVolume_shrunk_pos {L : ℕ} {h χ : Vertex → ℝ} {δ α : ℝ}
    (hδ : 0 < δ) (hα : 0 ≤ α) (hα1 : α < 1)
    (hne : ∀ x ∈ box L, ∀ y ∈ box L, Adj x y → |h x-h y| ≤ 1-δ)
    (hplus : 0 < fillingVolume L (fun x => h x+χ x)) :
    0 < fillingVolume L (fun x => h x+α*χ x) := by
  have heq : (fun x => (1-α)*h x+α*(h x+χ x))=(fun x => h x+α*χ x) := by funext x; ring
  rw [← heq]
  exact fillingVolume_interpolated_pos hδ hα hα1 hne (nonempty_of_measure_ne_zero hplus.ne')

lemma shrunk_deficit_le {L n : ℕ} (E : Filling L ≃ₗ[ℝ] (Fin n → ℝ)) (hE : MeasurePreserving E)
    {h χ : Vertex → ℝ} {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hh : 0 < fillingVolume L h)
    (hplus : 0 < fillingVolume L (fun x => h x+χ x))
    (hminus : 0 < fillingVolume L (fun x => h x-χ x)) :
    positiveLogVolume L h-(positiveLogVolume L (fun x => h x+α*χ x)+
      positiveLogVolume L (fun x => h x-α*χ x))/2 ≤
    positiveLogVolume L h-(positiveLogVolume L (fun x => h x+χ x)+
      positiveLogVolume L (fun x => h x-χ x))/2 := by
  have hp := positiveLogVolume_concave E hE h (fun x => h x+χ x) hh hplus
    (by linarith : 0 ≤ 1-α) hα (by ring : (1-α)+α=1)
  have hm := positiveLogVolume_concave E hE h (fun x => h x-χ x) hh hminus
    (by linarith : 0 ≤ 1-α) hα (by ring : (1-α)+α=1)
  have hmid := positiveLogVolume_concave E hE (fun x => h x+χ x) (fun x => h x-χ x)
    hplus hminus (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1/2:ℝ)+1/2=1)
  have hfp : (fun x => (1-α)*h x+α*(h x+χ x))=(fun x => h x+α*χ x) := by funext x; ring
  have hfm : (fun x => (1-α)*h x+α*(h x-χ x))=(fun x => h x-α*χ x) := by funext x; ring
  have hfmid : (fun x => (1/2:ℝ)*(h x+χ x)+(1/2:ℝ)*(h x-χ x))=h := by funext x; ring
  rw [hfp] at hp
  rw [hfm] at hm
  rw [hfmid] at hmid
  have hg : 0 ≤ positiveLogVolume L h-(positiveLogVolume L (fun x => h x+χ x)+
      positiveLogVolume L (fun x => h x-χ x))/2 := by linarith
  have hmul := mul_le_mul_of_nonneg_right hα1 hg
  nlinarith

theorem triangular_block_deficit
    (δ δ₀ s₀ : ℝ) (k₀ L : ℕ)
    (hδ : 0 < δ) (hδδ₀ : δ ≤ δ₀) (hδ₀ : δ₀ ≤ 1 / 16)
    (hk₀ : 4 / δ₀ ≤ (k₀ : ℝ)) (hs₀ : 0 < s₀)
    (hLeven : Even L) (hL : 8 * ((k₀ : ℝ) + 2) / δ₀ ≤ (L : ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ h χ : Vertex → ℝ,
      ConvexGood L k₀ δ δ₀ s₀ h →
      0 < fillingVolume L (fun x => h x + χ x) →
      0 < fillingVolume L (fun x => h x - χ x) →
      ∀ v w : Fin 4,
        c * |χ (faceCenter L v) - χ (faceCenter L w)| ^ 2 ≤
          positiveLogVolume L h -
            (positiveLogVolume L (fun x => h x + χ x) +
              positiveLogVolume L (fun x => h x - χ x)) / 2 := by
  classical
  obtain ⟨β,hβ,hβ1,hβδ,hβs,hexpose⟩ :=
    triangular_radial_exposure δ δ₀ s₀ k₀ L hδ hδδ₀ hδ₀ hk₀ hs₀ hLeven hL
  have hδ₀pos := hδ.trans_le hδδ₀
  have hLposR : (0:ℝ) < L := lt_of_lt_of_le (div_pos (by positivity) hδ₀pos) hL
  have hLpos : 0 < L := by exact_mod_cast hLposR
  obtain ⟨m,hm⟩ := hLeven
  have hLeq : L=2*m := by omega
  clear hm
  subst L
  have hm : 0 < m := by omega
  let α : ℝ := β/(16*((2*m:ℕ)+1))
  have hα : 0 < α := div_pos hβ (by positivity)
  have hα1 : α < 1 := by
    apply (div_lt_iff₀ (by positivity : (0:ℝ) < 16*((2*m:ℕ)+1))).mpr
    have hnonneg : (0:ℝ) ≤ (2*m:ℕ) := Nat.cast_nonneg _
    linarith
  have hαβ : |α| * (2*((2*m:ℕ):ℝ)) ≤ β/4 := by
    rw [abs_of_pos hα]
    dsimp [α]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : (0:ℝ) < 16*((2*m:ℕ)+1))).mpr
    nlinarith [hβ]
  have hαβneg : |(-α)| * (2*((2*m:ℕ):ℝ)) ≤ β/4 := by simpa only [abs_neg] using hαβ
  obtain ⟨n,e,he⟩ := EdgeCoordinates.exists_indexEquiv
    (⟨radialPoint (2*m) 0 1,radialPoint_mem_interior (by omega) (by omega : 1 ≤ m) 0⟩ :
      {x : Vertex // x ∈ interior (2*m)})
  let E₀ := EdgeCoordinates.reindex e
  have hE₀ : MeasurePreserving E₀ := EdgeCoordinates.reindex_measurePreserving e
  obtain ⟨κ,hκ,hfacet⟩ := exists_filling_facet_constant (2*m) n β hβ
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hmsq : (0:ℝ) < (m:ℝ)^2 := sq_pos_of_pos hmR
  refine ⟨κ*α^2/(m:ℝ)^2,by positivity,?_⟩
  intro h χ hgood hplus hminus v w
  have hh : 0 < fillingVolume (2*m) h := fillingVolume_pos_of_strict hδ hgood.1
  let s : Vertex → ℝ := fun x => h x+α*χ x
  let t : Vertex → ℝ := fun x => h x-α*χ x
  have hs : 0 < fillingVolume (2*m) s := fillingVolume_shrunk_pos hδ hα.le hα1 hgood.1 hplus
  have ht : 0 < fillingVolume (2*m) t := by
    have hm' : 0 < fillingVolume (2*m) (fun x => h x+(-χ x)) := by simpa only [sub_eq_add_neg] using hminus
    simpa only [t,mul_neg,sub_eq_add_neg] using fillingVolume_shrunk_pos hδ hα.le hα1 hgood.1 hm'
  let U : Vertex → ℝ := fun x => meanHeight (2*m) s x-meanHeight (2*m) t x
  let gα := positiveLogVolume (2*m) h-(positiveLogVolume (2*m) s+positiveLogVolume (2*m) t)/2
  have hedge : ∀ side : Fin 4, ∀ k < m,
      κ*(U (radialPoint (2*m) side (k+1))-U (radialPoint (2*m) side k))^2 ≤ gα := by
    intro side k hk
    obtain ⟨g,hg,hgrad,hother⟩ := hexpose h hgood side k (by simpa using hk)
    let x := radialPoint (2*m) side k
    let y := radialPoint (2*m) side (k+1)
    let τ := g y-g x
    have hτ : |τ|=1 := by simpa only [τ,x,y,abs_sub_comm] using hgrad
    have hxy : Adj x y := radialPoint_adj (2*m) k side
    obtain ⟨E,hE,hEn,hE0⟩ := exists_filling_edge_coordinates e
      (radialPoint_mem_interior (by omega : 0 < k+1) (by omega : k+1 ≤ m) side) (adj_ne hxy) hτ
    have hball (σ : ℝ) (hσ : |σ| * (2*((2*m:ℕ):ℝ)) ≤ β/4) :
        ∃ q₀ : Fin n → ℝ, ∀ q ∈ Metric.ball q₀ (β/16),
          Fin.cons (1+edgeOffset (2*m) τ (fun b => h b+σ*χ b) x) q ∈
            E '' fillingPolytope (2*m) (fun b => h b+σ*χ b) := by
      apply filling_facet_ball hτ hβ E hEn hE0 (fun z => g z+σ*χ (faceCenter (2*m) side))
      · exact shifted_radial_facet hm hk side hg hgrad
      · exact shifted_exposure hβ
          (shifted_shell_error hβ (faceCenter_mem_shell hm side) hg hplus hminus hσ) hother
    have hbp := hball α hαβ
    have hbm := hball (-α) hαβneg
    have hbm' : ∃ q₀ : Fin n → ℝ, ∀ q ∈ Metric.ball q₀ (β/16),
        Fin.cons (1+edgeOffset (2*m) τ t x) q ∈ E '' fillingPolytope (2*m) t := by
      simpa only [neg_mul,← sub_eq_add_neg] using hbm
    have hresult := hfacet s t h x y τ E hE hτ
      (radialPoint_mem_box (Nat.le_of_lt hk) side) (radialPoint_mem_box (by omega : k+1 ≤ m) side)
      hxy hE0 hs ht hh hbp hbm' (by intro b; dsimp [s,t]; ring)
    convert hresult using 1; dsimp [U,gα,x,y]; ring
  have hends (side : Fin 4) : U (radialPoint (2*m) side 0)=2*α*χ (faceCenter (2*m) side) := by
    rw [radialPoint_zero]
    have hfix := (shell_eq_box_not_interior.mp (faceCenter_mem_shell hm side)).2
    dsimp [U]
    rw [meanHeight_fixed hs hfix,meanHeight_fixed ht hfix]
    dsimp [s,t]
    ring
  have hbound := two_radial_square_bound (fun k => U (radialPoint (2*m) v k))
    (fun k => U (radialPoint (2*m) w k)) m hκ.le (by rw [radialPoint_center,radialPoint_center])
    (hedge v) (hedge w)
  rw [hends v,hends w] at hbound
  have hga := shrunk_deficit_le E₀ hE₀ hα.le hα1.le hh hplus hminus
  calc
    κ*α^2/(m:ℝ)^2 * |χ (faceCenter (2*m) v)-χ (faceCenter (2*m) w)|^2 =
      (κ*α^2*|χ (faceCenter (2*m) v)-χ (faceCenter (2*m) w)|^2)/(m:ℝ)^2 := by ring
    _ ≤ gα := (div_le_iff₀ hmsq).mpr (by
      rw [sq_abs]
      nlinarith only [hbound])
    _ ≤ _ := hga

end TriangularLipschitz

end
end
end
end

end OAI
