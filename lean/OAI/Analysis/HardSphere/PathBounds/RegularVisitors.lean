import Mathlib
import OAI.Analysis.HardSphere.PathBounds.VisitCounts
import OAI.Analysis.HardSphere.Cutoffs.StandardRegular

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.FreeVisits
open Wiener PathCutoff HardSphere.Lattice

theorem ground_regularVisitors_tail (η : ℝ) (hη : 0 < η) :
    ∃ αstar : ℝ, 0 < αstar ∧ ∀ αmax C a b : ℝ,
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
  obtain ⟨Cd,Cf,Cs,α,hCd,hCf,hCs,hα,hm⟩ := interacting_visit_mgf (η₀:=η) hη.le
  refine ⟨α,hα,?_⟩
  intro αmax C a b hαmax hC ha hb
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
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hxp) (by positivity)) hD.le
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
