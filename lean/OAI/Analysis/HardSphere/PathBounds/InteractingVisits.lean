import Mathlib
import OAI.Analysis.HardSphere.Geometry.SmoothSpatialCountMgf
import OAI.Analysis.HardSphere.PathBounds.SingleVisitDefect
import OAI.Analysis.HardSphere.Orbitals.SelectedDeletion

namespace OAI

section

section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere
open Wiener
lemma spatial_count_mgf_enn : ∃ C αstar : ℝ, 0 < C ∧ 0 < αstar ∧
    ∀ (n K : ℕ) (L : Length), L.val=(K:ℝ) → ∀ (r D : ℝ),
      D=(n:ℝ)/L.val^3 → 1≤D → αstar≤D*r → 0<r → 1≤L.val →
      (n:ℝ)*(2*Real.pi*r)^3≤L.val^3/2 →
    ∀ (g : Jet n L), IsGroundVector n L r g →
    ∀ (A : Finset (Torus L)) (z : ℝ), 0≤z → z≤1 →
      (∫⁻ X, ENNReal.ofReal (Real.exp (z*weightedSiteCount L A X)) ∂groundPositionLaw n L g)≤
        ENNReal.ofReal (Real.exp (C*z*D*(A.card:ℝ))) := by
  obtain ⟨C,αstar,hC,hα,h⟩ := spatial_count_mgf
  refine ⟨C,αstar,hC,hα,?_⟩
  intro n K L hL r D hDeq hD hαr hr hsize hs g hg A z hz hz1
  let := groundPositionLaw_probability g hg.2.2.1
  have hi := bounded_mgf_integrable (groundPositionLaw n L g)
    (weightedSiteCount_continuous L A).measurable
    (fun X ↦ (abs_of_nonneg (weightedSiteCount_nonneg L A X)).trans_le (weightedSiteCount_le L A X)) z
  rw [←ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun X ↦ (Real.exp_pos _).le))]
  apply ENNReal.ofReal_le_ofReal
  have hp : 0<∫ X,Real.exp (z*weightedSiteCount L A X) ∂groundPositionLaw n L g := ProbabilityTheory.mgf_pos hi
  calc
    _ = Real.exp (Real.log (∫ X,Real.exp (z*weightedSiteCount L A X) ∂groundPositionLaw n L g)) := (Real.exp_log hp).symm
    _ ≤ _ := Real.exp_le_exp.mpr (h n K L hL r D hDeq hD hαr hr hsize hs g hg A z hz hz1)

namespace FreeVisits
open HardSphere.BathSlice HardSphere.Lattice HardSphere.CellOrbital
attribute [local irreducible] freeTrajectory pathVisitedSites torusDistance

def defectiveTotalVisits {n K : ℕ} (L : Length) (A : Finset (DiscreteTorus K))
    (D : Set (ConfigurationPath 1 L)) (ω : ConfigurationPath n L) : ℕ := by
  classical
  exact ∑ i, if onePathAt i ω∈D then (pathVisitedSites L (siteCenter L) A i ω).card else 0

lemma pathVisitedSites_onePathAt {n K : ℕ} (L : Length) (A : Finset (DiscreteTorus K))
    (i : Fin n) (ω : ConfigurationPath n L) :
    pathVisitedSites L (siteCenter L) A 0 (onePathAt i ω)=pathVisitedSites L (siteCenter L) A i ω := by
  simp only [pathVisitedSites,pathVisitsBall,onePathAt,oneConfiguration,ContinuousMap.coe_mk]
  rfl

lemma exp_defectiveTotalVisits {n K : ℕ} (L : Length) (A : Finset (DiscreteTorus K))
    (D : Set (ConfigurationPath 1 L)) {η : ℝ} (hη : 0≤η) (ω : ConfigurationPath n L) :
    ENNReal.ofReal (Real.exp (η*(defectiveTotalVisits L A D ω : ℝ)))=
      ∏ i, (1+singleVisitDefect L A η D (onePathAt i ω)) := by
  classical
  simp only [defectiveTotalVisits,Nat.cast_sum,Finset.mul_sum,Real.exp_sum,
    ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ (Real.exp_pos _).le)]
  apply Finset.prod_congr rfl
  intro i _
  rw [singleVisitDefect,pathVisitedSites_onePathAt]
  have hx : 0≤η*(if onePathAt i ω∈D then ((pathVisitedSites L (siteCenter L) A i ω).card:ℝ) else 0) := by positivity
  have he : 0≤Real.exp (η*(if onePathAt i ω∈D then ((pathVisitedSites L (siteCenter L) A i ω).card:ℝ) else 0))-1 := sub_nonneg.mpr (Real.one_le_exp_iff.mpr hx)
  simp only [Nat.cast_ite,Nat.cast_zero]
  rw [←ENNReal.ofReal_one,←ENNReal.ofReal_add zero_le_one he]
  congr 1
  ring

lemma product_one_add_exp_le {n : ℕ} (L : Length) (A : Finset (Torus L))
    (hA : A.Nonempty) {z : ℝ} (hz : 0≤z) (X : Configuration n L) :
    (∏ i, (1+ENNReal.ofReal (z*Real.exp (-spatialSiteDistance L A (X i)))))≤
      ENNReal.ofReal (Real.exp (z*weightedSiteCount L A X)) := by
  classical
  simp only [weightedSiteCount,ite_eq_left hA,Finset.mul_sum,Real.exp_sum,
    ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ (Real.exp_pos _).le)]
  apply Finset.prod_le_prod
  intro i _
  rw [←ENNReal.ofReal_one,←ENNReal.ofReal_add zero_le_one (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  linarith [Real.add_one_le_exp (z*Real.exp (-spatialSiteDistance L A (X i)))]

theorem interacting_visit_mgf {η₀ : ℝ} (hη₀ : 0≤η₀) :
    ∃ Cdel Cfree Csp αstar : ℝ,
      0<Cdel ∧ 0<Cfree ∧ 0<Csp ∧ 0<αstar ∧
    ∀ (n K : ℕ) [NeZero K] (L : Length), L.val=(K:ℝ) → ∀ r D : ℝ,
      D=(n:ℝ)/L.val^3 → 1≤D → αstar≤D*r → 0<r →
      (n:ℝ)*(2*Real.pi*r)^3≤L.val^3/2 →
    ∀ (g : Jet n L), IsGroundVector n L r g →
    ∀ (A : Finset (DiscreteTorus K)) {t η ε : ℝ},
      0<t → t≤2 → 0≤η → η≤η₀ → 0≤ε →
    ∀ E : Set (ConfigurationPath 1 L), MeasurableSet E →
      (∀ω,reverseConfigurationPath 1 L ω∈E ↔ ω∈E) →
      (∀ y : Torus L, coordinateWiener 1 {w | freeTrajectory 1 L t w (oneConfiguration y)∈E}≤ENNReal.ofReal ε) →
      Real.exp (t*Cdel*D*r)*(Cfree*η*ε^(1/3:ℝ))≤1 →
      (∫⁻ ω, ENNReal.ofReal (Real.exp (η*(defectiveTotalVisits L A E ω:ℝ)))
        ∂groundPathLaw n L r t g) ≤
        ENNReal.ofReal (Real.exp (Csp*(Real.exp (t*Cdel*D*r)*(Cfree*η*ε^(1/3:ℝ)))*D*(A.card:ℝ))) := by
  classical
  obtain ⟨Cdel,hCdel,hdel⟩ := ground_product_one_add
  obtain ⟨Cfree,hCfree,hfree⟩ := free_single_defect_bound hη₀
  obtain ⟨Csp,αstar,hCsp,hα,hsp⟩ := spatial_count_mgf_enn
  refine ⟨Cdel,Cfree,Csp,αstar,hCdel,hCfree,hCsp,hα,?_⟩
  intro n K inst L hL r D hDeq hD hαr hr hs g hg A t η ε ht ht2 hη hη0 hε E hE hrev hprob hz1
  let z := Real.exp (t*Cdel*D*r)*(Cfree*η*ε^(1/3:ℝ))
  have hz : 0≤z := by positivity
  have hsize : 1≤L.val := by rw [hL]; exact_mod_cast (NeZero.pos K)
  let := hg.groundPathLaw_probability ht.le
  by_cases hA : A.Nonempty
  · let B := A.image (siteCenter L)
    have hB : B.Nonempty := hA.image _
    have hDexp : t*Cdel*(n:ℝ)*r/L.val^3=t*Cdel*D*r := by rw [hDeq]; ring
    calc
      _ = ∫⁻ ω,∏i,(1+singleVisitDefect L A η E (onePathAt i ω)) ∂groundPathLaw n L r t g :=
        lintegral_congr (exp_defectiveTotalVisits L A E hη)
      _ ≤ ∫⁻ X,∏i,(1+ENNReal.ofReal (Real.exp (t*Cdel*(n:ℝ)*r/L.val^3))*
          oneFreeExpectation t (singleVisitDefect L A η E) (X i)) ∂groundPositionLaw n L g :=
        hdel n L r t hr ht hs g hg _ (singleVisitDefect_measurable L A η hE) (singleVisitDefect_reverse L A η hrev)
      _ ≤ ∫⁻ X,ENNReal.ofReal (Real.exp (z*weightedSiteCount L B X)) ∂groundPositionLaw n L g := by
        apply lintegral_mono
        intro X
        apply le_trans _ (product_one_add_exp_le L B hB hz X)
        apply Finset.prod_le_prod
        intro i _
        gcongr
        have H := hfree L hL A ht ht2 hη hη0 hε E hE hprob (X i)
        calc
          _ ≤ ENNReal.ofReal (Real.exp (t*Cdel*(n:ℝ)*r/L.val^3))*
              ENNReal.ofReal (Cfree*η*ε^(1/3:ℝ)*Real.exp (-spatialSiteDistance L B (X i))) := by gcongr
          _ = _ := by rw [←ENNReal.ofReal_mul (Real.exp_nonneg _),hDexp]; congr 1; dsimp [z]; ring
      _ ≤ ENNReal.ofReal (Real.exp (Csp*z*D*(B.card:ℝ))) :=
        hsp n K L hL r D hDeq hD hαr hr hsize hs g hg B z hz hz1
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        have hc : (B.card:ℝ)≤(A.card:ℝ) := by exact_mod_cast Finset.card_image_le
        exact mul_le_mul_of_nonneg_left hc (by positivity)
  · have he : A=∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    subst A
    simp [defectiveTotalVisits,pathVisitedSites]

end FreeVisits
end HardSphere

end
end

section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere
open Wiener BathSlice _root_.OAI.HardSphere.Lattice CellOrbital

lemma torusDistance_add (L : Length) (x y c : Torus L) :
    torusDistance L (x+c) (y+c)=torusDistance L x y := by
  unfold torusDistance
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp only [Pi.add_apply,dist_add_right]

def shiftPath {n : ℕ} {L : Length} (c : Torus L) (ω : ConfigurationPath n L) : ConfigurationPath n L :=
  ⟨fun s i ↦ ω s i+c,by fun_prop⟩

lemma shiftPath_continuous {n : ℕ} {L : Length} (c : Torus L) : Continuous (shiftPath (n:=n) c) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : ConfigurationPath n L×Time ↦ fun i ↦ p.1 p.2 i+c)
  fun_prop

@[simp] lemma shiftPath_neg {n : ℕ} {L : Length} (c : Torus L) (ω : ConfigurationPath n L) :
    shiftPath c (shiftPath (-c) ω)=ω := by
  ext s i j
  simp [shiftPath]

@[simp] lemma shiftPath_reverse {n : ℕ} {L : Length} (c : Torus L) (ω : ConfigurationPath n L) :
    shiftPath c (reverseConfigurationPath n L ω)=reverseConfigurationPath n L (shiftPath c ω) := rfl

lemma shiftPath_free {n : ℕ} {L : Length} (c : Torus L) (t : ℝ) (w : CoordinatePaths n) (X : Configuration n L) :
    shiftPath c (freeTrajectory n L t w X)=freeTrajectory n L t w (fun i ↦ X i+c) := by
  ext s i j
  simp only [shiftPath,ContinuousMap.coe_mk,freeTrajectory,Pi.add_apply]
  abel

lemma spatialSiteDistance_add (L : Length) (A : Finset (Torus L)) (x c : Torus L) :
    spatialSiteDistance L (A.image (fun v ↦ v+c)) (x+c)=spatialSiteDistance L A x := by
  classical
  by_cases hA : A.Nonempty
  · obtain ⟨y,hy,he⟩ := spatialSiteDistance_attained L A hA x
    obtain ⟨z,hz,hf⟩ := spatialSiteDistance_attained L (A.image (fun v ↦ v+c)) (hA.image _) (x+c)
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
    apply le_antisymm
    · rw [he]
      have h := spatialSiteDistance_le L (A.image (fun v ↦ v+c)) (x+c) (y+c) (Finset.mem_image.mpr ⟨y,hy,rfl⟩)
      simpa only [torusDistance_add] using h
    · rw [hf,torusDistance_add]
      exact spatialSiteDistance_le L A x w hw
  · have := Finset.not_nonempty_iff_eq_empty.mp hA
    subst A
    simp [spatialSiteDistance]

namespace ShiftVisits
open FreeVisits
attribute [local instance] Classical.propDecidable

def center {K : ℕ} (L : Length) (c : Torus L) (v : DiscreteTorus K) : Torus L := siteCenter L v+c

def singleDefect {K : ℕ} (L : Length) (c : Torus L) (A : Finset (DiscreteTorus K))
    (η : ℝ) (D : Set (ConfigurationPath 1 L)) (ω : ConfigurationPath 1 L) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (η*(if ω∈D then ((pathVisitedSites L (center L c) A 0 ω).card:ℝ) else 0))-1)

lemma shifted_visits {n K : ℕ} (L : Length) (c : Torus L) (A : Finset (DiscreteTorus K))
    (i : Fin n) (ω : ConfigurationPath n L) :
    pathVisitedSites L (siteCenter L) A i (shiftPath (-c) ω)=pathVisitedSites L (center L c) A i ω := by
  apply Finset.filter_congr
  intro v _
  unfold pathVisitsBall
  apply exists_congr
  intro s
  change (torusDistance L (ω s i+-c) (siteCenter L v)≤12) ↔ _
  have hd := torusDistance_add L (ω s i+-c) (siteCenter L v) c
  simp only [neg_add_cancel_right] at hd
  rw [←hd]
  rfl

lemma singleDefect_eq (L : Length) {K : ℕ} (c : Torus L) (A : Finset (DiscreteTorus K))
    (η : ℝ) (D : Set (ConfigurationPath 1 L)) (ω : ConfigurationPath 1 L) :
    singleDefect L c A η D ω=singleVisitDefect L A η ((shiftPath c)⁻¹' D) (shiftPath (-c) ω) := by
  simp only [singleDefect,singleVisitDefect,Set.mem_preimage,shiftPath_neg,shifted_visits]

lemma singleDefect_measurable (L : Length) {K : ℕ} (c : Torus L) (A : Finset (DiscreteTorus K))
    (η : ℝ) {D : Set (ConfigurationPath 1 L)} (hD : MeasurableSet D) :
    Measurable (singleDefect L c A η D) := by
  have he : singleDefect L c A η D=(singleVisitDefect L A η ((shiftPath c)⁻¹' D)) ∘ shiftPath (-c) :=
    funext (singleDefect_eq L c A η D)
  rw [he]
  exact (singleVisitDefect_measurable L A η (hD.preimage (shiftPath_continuous c).measurable)).comp
    (shiftPath_continuous (-c)).measurable

lemma singleDefect_reverse (L : Length) {K : ℕ} (c : Torus L) (A : Finset (DiscreteTorus K))
    (η : ℝ) {D : Set (ConfigurationPath 1 L)}
    (hD : ∀ω,reverseConfigurationPath 1 L ω∈D ↔ ω∈D) (ω : ConfigurationPath 1 L) :
    singleDefect L c A η D (reverseConfigurationPath 1 L ω)=singleDefect L c A η D ω := by
  simp only [singleDefect,hD,pathVisitedSites_reverse]

lemma free_single_defect_bound {η₀ : ℝ} (hη₀ : 0≤η₀) : ∃ C : ℝ,0<C ∧
    ∀ {K : ℕ} [NeZero K] (L : Length),L.val=(K:ℝ) → ∀ (c : Torus L) (A : Finset (DiscreteTorus K)),
    ∀ {t η ε : ℝ},0<t → t≤2 → 0≤η → η≤η₀ → 0≤ε →
    ∀ D : Set (ConfigurationPath 1 L),MeasurableSet D →
      (∀ y : Torus L,coordinateWiener 1 {w | freeTrajectory 1 L t w (oneConfiguration y)∈D}≤ENNReal.ofReal ε) →
    ∀ y : Torus L,oneFreeExpectation t (singleDefect L c A η D) y ≤
      ENNReal.ofReal (C*η*ε^(1/3:ℝ)*Real.exp (-spatialSiteDistance L (A.image (center L c)) y)) := by
  obtain ⟨C,hC,h⟩ := FreeVisits.free_single_defect_bound hη₀
  refine ⟨C,hC,?_⟩
  intro K _ L hL c A t η ε ht ht2 hη hη0 hε D hD hprob y
  let E := (shiftPath c)⁻¹' D
  have hE : MeasurableSet E := hD.preimage (shiftPath_continuous c).measurable
  have hp (z : Torus L) : coordinateWiener 1 {w | freeTrajectory 1 L t w (oneConfiguration z)∈E}≤ENNReal.ofReal ε := by
    have hh := hprob (z+c)
    change coordinateWiener 1 {w | freeTrajectory 1 L t w (fun _ ↦ z+c)∈D}≤ENNReal.ofReal ε at hh
    simpa only [E,mem_preimage,shiftPath_free,oneConfiguration] using hh
  have hh := h L hL A ht ht2 hη hη0 hε E hE hp (y+-c)
  have hf : oneFreeExpectation t (singleDefect L c A η D) y=
      oneFreeExpectation t (singleVisitDefect L A η E) (y+-c) := by
    apply lintegral_congr
    intro w
    rw [singleDefect_eq,shiftPath_free]
    rfl
  rw [hf]
  have hd : spatialSiteDistance L (A.image (center L c)) y=spatialSiteDistance L (A.image (siteCenter L)) (y+-c) := by
    have hh := spatialSiteDistance_add L (A.image (siteCenter L)) (y+-c) c
    change spatialSiteDistance L (A.image (fun v ↦ siteCenter L v+c)) y = _
    simpa only [Finset.image_image,Function.comp_def,neg_add_cancel_right] using hh
  rw [hd]
  exact hh

end ShiftVisits
end HardSphere

end
end

end

end OAI
