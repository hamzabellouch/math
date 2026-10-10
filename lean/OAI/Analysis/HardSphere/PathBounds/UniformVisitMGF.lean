import Mathlib
import OAI.Analysis.HardSphere.PathBounds.VisitCounts
import OAI.Analysis.HardSphere.Cutoffs.StandardRegular

namespace OAI

section

section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.FreeVisits
open Wiener HardSphere.BathSlice HardSphere.Lattice HardSphere.CellOrbital
attribute [local irreducible] freeTrajectory pathVisitedSites torusDistance

theorem interacting_visit_mgf_uniform :
    ∃ Cdel Csp αstar : ℝ, 0<Cdel ∧ 0<Csp ∧ 0<αstar ∧
    ∀ η₀ : ℝ, 0≤η₀ → ∃ Cfree : ℝ, 0<Cfree ∧
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
  obtain ⟨Csp,αstar,hCsp,hα,hsp⟩ := spatial_count_mgf_enn
  refine ⟨Cdel,Csp,αstar,hCdel,hCsp,hα,?_⟩
  intro η₀ hη₀
  obtain ⟨Cfree,hCfree,hfree⟩ := free_single_defect_bound hη₀
  refine ⟨Cfree,hCfree,?_⟩
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

end HardSphere.FreeVisits

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.FreeVisits
open Wiener PathCutoff HardSphere.Lattice

theorem ground_regularVisitors_uniform :
    ∃ αstar : ℝ, 0 < αstar ∧ ∀ (η : ℝ), 0 < η → ∀ αmax C a b : ℝ,
      0 < αmax → 0 < C → 0 < a → 0 < b →
    ∃ D₀ : ℝ, 1 ≤ D₀ ∧ ∀ (n K : ℕ) [NeZero K] (L : Length), L.val=(K:ℝ) →
    ∀ r D : ℝ, D=(n:ℝ)/L.val^3 → D₀ ≤ D → αstar ≤ D*r → D*r ≤ αmax → 0 < r →
      (n:ℝ)*(2*Real.pi*r)^3 ≤ L.val^3/2 →
    ∀ (g : Jet n L), IsGroundVector n L r g → ∀ (A : Finset (DiscreteTorus K))
    (m : ℕ) (τ : ℝ), 0 < m → 0 < τ → τ ≤ r^2 →
      a*D^2 ≤ (m:ℝ) → (m:ℝ) ≤ C*D^2 → (m:ℝ)*τ ≤ 2 →
    ∀ (hD : 0 < D) (hhT : D⁻¹ < (m:ℝ)*τ),
      groundPathLaw n L r ((m:ℝ)*τ) g {ω | ∀v∈A,1 ≤
        (visitorCount L {p | ¬Regular m r (D^(1/12:ℝ)) (meanCost+1)
          (splitTime D⁻¹ ((m:ℝ)*τ-D⁻¹) (inv_pos.mpr hD) (sub_pos.mpr hhT))
          (b*D^(-(1/3:ℝ))/8) p} v ω:ℝ)} ≤
        ENNReal.ofReal (Real.exp (-(η/2)*(A.card:ℝ))) := by
  obtain ⟨c,M,hc,hM,htail⟩ := wiener_norm_gaussian_tail
  obtain ⟨Cd,Cs,α,hCd,hCs,hα,hmgf⟩ := interacting_visit_mgf_uniform
  refine ⟨α,hα,?_⟩
  intro η hη αmax C a b hαmax hC ha hb
  obtain ⟨Cf,hCf,hm⟩ := hmgf η hη.le
  let ε := fun D : ℝ ↦ scalarRegularBound C (3*M.toReal) c a b D
  let B := Real.exp (2*Cd*αmax)*Cf*η
  have hB : 0 < B := by dsimp [B]; positivity
  let δ := min 1 (η/(2*Cs))
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hlim : Tendsto (fun D : ℝ ↦ B*(D*(ε D)^(1/3:ℝ))) atTop (𝓝 0) := by
    simpa using (regular_root_decay hC.le (by positivity : 0 ≤ 3*M.toReal) hc ha hb).const_mul B
  obtain ⟨D₀,hsmall⟩ := (eventually_atTop.1
    ((eventually_ge_atTop (1:ℝ)).and (hlim.eventually (gt_mem_nhds hδ))))
  refine ⟨max 1 D₀,le_max_left _ _,?_⟩
  intro n K inst L hL r D hDeq hDD hαr hαup hr hs g hg A m τ hmpos hτ hτr hmlo hmhi ht2 hD hhT
  have hD1 : 1 ≤ D := (le_max_left _ _).trans hDD
  have hsmallD : B*(D*(ε D)^(1/3:ℝ)) ≤ δ := ((hsmall D ((le_max_right _ _).trans hDD)).2).le
  have hε : 0 ≤ ε D := scalarRegularBound_nonneg hC.le (by positivity) c a b D
  have ht : 0 < (m:ℝ)*τ := mul_pos (Nat.cast_pos.mpr hmpos) hτ
  have hxp : ((m:ℝ)*τ)*Cd*D*r ≤ 2*Cd*αmax := by
    calc
      _ = (((m:ℝ)*τ)*Cd)*(D*r) := by ring
      _ ≤ (((m:ℝ)*τ)*Cd)*αmax := mul_le_mul_of_nonneg_left hαup (by positivity)
      _ ≤ (2*Cd)*αmax := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ht2 hCd.le) hαmax.le
  let z := Real.exp (((m:ℝ)*τ)*Cd*D*r)*(Cf*η*(ε D)^(1/3:ℝ))
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hzD : z*D ≤ δ := by
    apply le_trans _ hsmallD
    calc
      _ ≤ Real.exp (2*Cd*αmax)*(Cf*η*(ε D)^(1/3:ℝ))*D := by
        dsimp [z]
        gcongr
      _ = B*(D*(ε D)^(1/3:ℝ)) := by dsimp [B]; ring
  have hz1 : z ≤ 1 := (by nlinarith : z ≤ z*D).trans (hzD.trans (min_le_left _ _))
  let E : Set (ConfigurationPath 1 L) := {p | ¬Regular m r (D^(1/12:ℝ)) (meanCost+1)
    (splitTime D⁻¹ ((m:ℝ)*τ-D⁻¹) (inv_pos.mpr hD) (sub_pos.mpr hhT)) (b*D^(-(1/3:ℝ))/8) p}
  have hE : MeasurableSet E := (regular_measurable _ _ _ _ _ _).compl
  have hrev (p : ConfigurationPath 1 L) : reverseConfigurationPath 1 L p∈E ↔ p∈E :=
    (regular_reverse _ _ _ _ _ _ p).not
  have hp (y : Torus L) : coordinateWiener 1 {w | freeTrajectory 1 L ((m:ℝ)*τ) w (oneConfiguration y)∈E} ≤ ENNReal.ofReal (ε D) :=
    free_regular_standard_tail hM.ne htail hr hτ hτr hc.le hD1 hC.le ha.le hb.le m hmpos hmlo hmhi hhT (oneConfiguration y)
  have hh := hm n K L hL r D hDeq hD1 hαr hr hs g hg A ht ht2 hη.le (le_refl η) hε E hE hrev hp hz1
  have hj := joint_visitors_markov L A hE (groundPathLaw n L r ((m:ℝ)*τ) g) hη.le hh (H:=1)
  apply hj.trans
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg A.card)
  have hδη : Cs*δ ≤ η/2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < (2:ℝ)*Cs)).mp (min_le_right 1 (η/(2*Cs)))
    dsimp [δ]
    linarith
  have hcost := (mul_le_mul_of_nonneg_left hzD hCs.le).trans hδη
  change Cs*z*D-η*1 ≤ -(η/2)
  nlinarith

end HardSphere.FreeVisits

end
end

end

end OAI
