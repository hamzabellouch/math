import Mathlib
import OAI.Analysis.HardSphere.Geometry.LocalCloseLabelsMeasurable
import OAI.Analysis.HardSphere.Allocation.FinsetSeparatedNet
import OAI.Analysis.HardSphere.PathBounds.InteractingVisits

namespace OAI

section

section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere
theorem spatial_translated_grid_close_probability : ∃ Q : ℕ, 0<Q ∧ ∃ C c G : ℝ, 0<C ∧ 0<c ∧ 0<G ∧
    ∀ (n K : ℕ) [Nontrivial (Fin n)] (L : Length) (_hL : L.val=(K:ℝ)) (r b D h : ℝ),
      D=(n:ℝ)/L.val^3 → 1≤D → 1≤D*r → 0<r → 0<b → 0<h →
      2*spatialCloseScale D b≤1 → 10*spatialCloseScale D b≤L.val →
      (n:ℝ)*(2*Real.pi*r)^3≤L.val^3/2 → (C+1)*D≤c/b^3*(h/4) →
      G/(h*(spatialCloseScale D b)^2)/((D*r)*D)≤1 →
    ∀ (g : Jet n L), IsGroundVector n L r g → ∀ (z : Torus L) (A : Finset (CubeCell K)),
      groundPositionLaw n L g {X | ∀ v∈A, 8*h≤((localCloseLabels L (spatialCloseScale D b) (unitCenter L v+z) X).card:ℝ)}≤
        ENNReal.ofReal ((Real.rpow (G/(h*(spatialCloseScale D b)^2)/((D*r)*D)) (1/(Q:ℝ)))^A.card) := by
  obtain ⟨C,c,G,hC,hc,hG,hsep⟩ := spatial_separated_close_probability
  obtain ⟨Q,hQ,hsubset⟩ := unitGrid_separated_subset
  refine ⟨Q,hQ,C,c,G,hC,hc,hG,?_⟩
  intro n K _ L hL r b D h hDeq hD hα hr hb hh hs1 hsL hsmall hcoef hbase g hg z A
  classical
  obtain ⟨B,hBA,hB,hcard⟩ := hsubset K L hL A
  have hBshift : ∀ v∈B, ∀ w∈B,v≠w → 20≤torusDistance L (unitCenter L v+z) (unitCenter L w+z) := by
    intro v hv w hw hne
    rw [torusDistance_add]
    exact hB v hv w hw hne
  let q : ℝ := G/(h*(spatialCloseScale D b)^2)/((D*r)*D)
  have hDpos : 0<D := zero_lt_one.trans_le hD
  have hs : 0<spatialCloseScale D b := spatialCloseScale_pos hDpos hb
  have hq : 0<q := by dsimp [q]; positivity
  have hQpos : 0<(Q:ℝ) := by exact_mod_cast hQ
  have hinj : Set.InjOn (fun v ↦ unitCenter L v+z) (B : Set (CubeCell K)) := by
    intro v hv w hw heq
    by_contra hvw
    have hd := hBshift v hv w hw hvw
    change unitCenter L v+z=unitCenter L w+z at heq
    rw [heq] at hd
    simp only [torusDistance,dist_self,zero_pow (by omega : (2:ℕ)≠0),Finset.sum_const_zero,Real.sqrt_zero] at hd
    norm_num at hd
  have hbcard : (B.image (fun v ↦ unitCenter L v+z)).card=B.card := Finset.card_image_of_injOn hinj
  have hbsep : ∀ v∈B.image (fun v ↦ unitCenter L v+z), ∀ w∈B.image (fun v ↦ unitCenter L v+z), v≠w → 20≤torusDistance L v w := by
    intro v hv w hw hvw
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hw
    exact hBshift i hi j hj (fun he ↦ hvw (congrArg (fun v ↦ unitCenter L v+z) he))
  have hp := hsep n K L hL r b D h hDeq hD hα hr hb hh hs1 hsL hsmall hcoef g hg (B.image (fun v ↦ unitCenter L v+z)) hbsep
  have hpow : q^B.card≤(Real.rpow q (1/(Q:ℝ)))^A.card := by
    change q^B.card≤(q^(1/(Q:ℝ)))^A.card
    rw [←Real.rpow_natCast q B.card,←Real.rpow_mul_natCast hq.le (1/(Q:ℝ)) A.card]
    apply Real.rpow_le_rpow_of_exponent_ge hq hbase
    have hh : (A.card:ℝ)/(Q:ℝ)≤(B.card:ℝ) := (div_le_iff₀ hQpos).mpr (by simpa only [mul_comm] using hcard)
    simpa [div_eq_mul_inv,mul_comm] using hh
  apply (measure_mono (show
      {X : Configuration n L | ∀ v∈A, 8*h≤((localCloseLabels L (spatialCloseScale D b) (unitCenter L v+z) X).card:ℝ)} ⊆
      {X : Configuration n L | ∀ v∈B.image (fun v ↦ unitCenter L v+z), 8*h≤((localCloseLabels L (spatialCloseScale D b) v X).card:ℝ)} by
    intro X hX v hv
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
    exact hX i (hBA hi))).trans
  exact hp.trans (ENNReal.ofReal_le_ofReal (by simpa only [hbcard] using hpow))

end HardSphere

end
end

end

end OAI
