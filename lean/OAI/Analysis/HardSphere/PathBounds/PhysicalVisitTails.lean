import Mathlib
import OAI.Analysis.HardSphere.Bridges.EndpointTail
import OAI.Analysis.HardSphere.PathBounds.VisitCounts

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.FreeVisits
open Wiener PathCutoff BathSlice HardSphere.Lattice CellOrbital

theorem ground_excessVisitors_tail :
    ∃ αstar : ℝ, 0<αstar ∧ ∀ αmax : ℝ, 0<αmax →
    ∃ H : ℝ, 0<H ∧ ∀ (n K : ℕ) [NeZero K] (L : Length), L.val=(K:ℝ) →
    ∀ r D : ℝ, D=(n:ℝ)/L.val^3 → 1≤D → αstar≤D*r → D*r≤αmax → 0<r →
      (n:ℝ)*(2*Real.pi*r)^3≤L.val^3/2 →
    ∀ (g : Jet n L), IsGroundVector n L r g → ∀ (A : Finset (DiscreteTorus K)) {t : ℝ},
      0<t → t≤2 →
      groundPathLaw n L r t g {ω | ∀v∈A,H*D≤(visitorCount L Set.univ v ω:ℝ)}≤
        ENNReal.ofReal (Real.exp (-(D*(A.card:ℝ)))) := by
  obtain ⟨Cd,Cf,Cs,α,hCd,hCf,hCs,hα,hm⟩ := interacting_visit_mgf (η₀:=1) (by norm_num)
  refine ⟨α,hα,?_⟩
  intro αmax hαmax
  let B := Real.exp (2*Cd*αmax)*Cf
  have hB : 0<B := by dsimp [B]; positivity
  let η := min 1 B⁻¹
  have hη : 0<η := lt_min (by norm_num) (inv_pos.mpr hB)
  have hη1 : η≤1 := min_le_left _ _
  have hb : B*η≤1 := by
    calc
      B*η≤B*B⁻¹ := mul_le_mul_of_nonneg_left (min_le_right _ _) hB.le
      _ = 1 := mul_inv_cancel₀ hB.ne'
  let H := (Cs+1)/η
  have hH : 0<H := div_pos (by linarith) hη
  refine ⟨H,hH,?_⟩
  intro n K inst L hL r D hDeq hD hαr hαup hr hs g hg A t ht ht2
  have hD0 : 0≤D := by linarith
  have hxp : t*Cd*D*r≤2*Cd*αmax := by
    calc
      t*Cd*D*r = (t*Cd)*(D*r) := by ring
      _ ≤ (t*Cd)*αmax := mul_le_mul_of_nonneg_left hαup (by positivity)
      _ ≤ (2*Cd)*αmax := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ht2 hCd.le) hαmax.le
  have hz : Real.exp (t*Cd*D*r)*(Cf*η*(1:ℝ)^(1/3:ℝ))≤1 := by
    simp only [Real.one_rpow,mul_one]
    calc
      _ ≤ Real.exp (2*Cd*αmax)*(Cf*η) := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hxp) (by positivity)
      _ = B*η := by dsimp [B]; ring
      _ ≤ 1 := hb
  have hp (y : Torus L) : coordinateWiener 1 {w | freeTrajectory 1 L t w (oneConfiguration y)∈(Set.univ : Set (ConfigurationPath 1 L))}≤ENNReal.ofReal 1 := by simp
  have hh := hm n K L hL r D hDeq hD hαr hr hs g hg A ht ht2 hη.le hη1
    (by norm_num : (0:ℝ)≤1) Set.univ MeasurableSet.univ (fun _ ↦ Iff.rfl) hp hz
  have hj := joint_visitors_markov L A MeasurableSet.univ (groundPathLaw n L r t g) hη.le hh (H:=H*D)
  apply hj.trans
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  rw [←neg_mul]
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg A.card)
  have hhH : η*H=Cs+1 := by dsimp [H]; field_simp
  have he : Cs*(Real.exp (t*Cd*D*r)*(Cf*η*(1:ℝ)^(1/3:ℝ)))*D≤Cs*D := by
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hz hCs.le) hD0).trans_eq (by ring)
  change _≤ -D
  nlinarith

end HardSphere.FreeVisits

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.FreeVisits
open Wiener PathCutoff HardSphere.Lattice

theorem free_long_probability_small {ε : ℝ} (hε : 0<ε) :
    ∃ t₀ : ℝ, 0<t₀ ∧ ∀ (L : Length) {t : ℝ},0<t→t≤t₀→∀y : Torus L,
      coordinateWiener 1 {w | 1 < intervalDiameter 0 1 (freeTrajectory 1 L t w (oneConfiguration y))}≤
        ENNReal.ofReal ε := by
  obtain ⟨c,M,hc,hM,htail⟩ := wiener_norm_gaussian_tail
  have hlim : Tendsto (fun q:ℝ ↦ (3*M.toReal)*Real.exp (-q)) atTop (𝓝 0) := by
    simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul (3*M.toReal)
  obtain ⟨T,hT,hsmall⟩ := ((eventually_gt_atTop (0:ℝ)).and
    (hlim.eventually (gt_mem_nhds hε))).exists
  refine ⟨c/(1296*T),by positivity,?_⟩
  intro L t ht htt y
  apply (free_diameter_tail htail ht (by norm_num : (0:ℝ)≤1) (oneConfiguration y)).trans
  have hsq : c*(1/(36*Real.sqrt t))^2=c/(1296*t) := by
    rw [div_pow,mul_pow,Real.sq_sqrt ht.le]
    norm_num
    ring
  have hcT : T≤c/(1296*t) := by
    apply (le_div_iff₀ (by positivity : 0<(1296:ℝ)*t)).mpr
    have hh := (le_div_iff₀ (by positivity : 0<(1296:ℝ)*T)).mp htt
    nlinarith
  have hm : (3:ℝ≥0∞)*M=ENNReal.ofReal (3*M.toReal) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤3),ENNReal.ofReal_toReal hM.ne]
    norm_num
  rw [hm,←ENNReal.ofReal_mul (by positivity : (0:ℝ)≤3*M.toReal)]
  apply ENNReal.ofReal_le_ofReal
  apply le_trans _ hsmall.le
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  nlinarith [hsq]

theorem ground_longVisitors_tail :
    ∃ αstar : ℝ, 0<αstar ∧ ∀ αmax θ : ℝ, 0<αmax → 0<θ →
    ∃ t₀ : ℝ, 0<t₀ ∧ ∀ (n K : ℕ) [NeZero K] (L : Length), L.val=(K:ℝ) →
    ∀ r D : ℝ, D=(n:ℝ)/L.val^3 → 1≤D → αstar≤D*r → D*r≤αmax → 0<r →
      (n:ℝ)*(2*Real.pi*r)^3≤L.val^3/2 →
    ∀ (g : Jet n L), IsGroundVector n L r g → ∀ (A : Finset (DiscreteTorus K)) {t : ℝ},
      0<t → t ≤ min 2 t₀ →
      groundPathLaw n L r t g {ω | ∀v∈A,θ*D≤
        (visitorCount L {p | 1 < intervalDiameter 0 1 p} v ω:ℝ)}≤
        ENNReal.ofReal (Real.exp (-(θ*D/2)*(A.card:ℝ))) := by
  obtain ⟨Cd,Cf,Cs,α,hCd,hCf,hCs,hα,hm⟩ := interacting_visit_mgf (η₀:=1) (by norm_num)
  refine ⟨α,hα,?_⟩
  intro αmax θ hαmax hθ
  let B := Real.exp (2*Cd*αmax)*Cf
  have hB : 0<B := by dsimp [B]; positivity
  let δ := min 1 (θ/(2*Cs))
  have hδ : 0<δ := lt_min (by norm_num) (by positivity)
  let ε := (δ/B)^3
  have hε : 0<ε := by dsimp [ε]; positivity
  have hrp : ε^(1/3:ℝ)=δ/B := by
    simpa [ε] using Real.pow_rpow_inv_natCast (n:=3) (div_pos hδ hB).le (by norm_num : (3:ℕ)≠0)
  obtain ⟨t₀,ht₀,hsmall⟩ := free_long_probability_small hε
  refine ⟨t₀,ht₀,?_⟩
  intro n K inst L hL r D hDeq hD hαr hαup hr hs g hg A t ht htt
  have ht2 := (le_min_iff.mp htt).1
  have hD0 : 0≤D := by linarith
  have hxp : t*Cd*D*r≤2*Cd*αmax := by
    calc
      t*Cd*D*r = (t*Cd)*(D*r) := by ring
      _ ≤ (t*Cd)*αmax := mul_le_mul_of_nonneg_left hαup (by positivity)
      _ ≤ (2*Cd)*αmax := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ht2 hCd.le) hαmax.le
  have hzδ : Real.exp (t*Cd*D*r)*(Cf*1*ε^(1/3:ℝ))≤δ := by
    rw [hrp,mul_one]
    calc
      _ ≤ Real.exp (2*Cd*αmax)*(Cf*(δ/B)) := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hxp) (by positivity)
      _ = δ := by dsimp [B]; field_simp
  have hz1 := hzδ.trans (min_le_left 1 (θ/(2*Cs)))
  let E : Set (ConfigurationPath 1 L) := {p | 1 < intervalDiameter 0 1 p}
  have hE : MeasurableSet E := measurableSet_lt measurable_const (intervalDiameter_continuous L 0 1).measurable
  have hrev (p : ConfigurationPath 1 L) : reverseConfigurationPath 1 L p∈E↔p∈E := by
    simp only [E,Set.mem_ofPred_eq,intervalDiameter_reverse,reverseTime_zero,reverseTime_one]
  have hp (y : Torus L) : coordinateWiener 1 {w | freeTrajectory 1 L t w (oneConfiguration y)∈E}≤ENNReal.ofReal ε :=
    hsmall L ht (le_min_iff.mp htt).2 y
  have hh := hm n K L hL r D hDeq hD hαr hr hs g hg A ht ht2 (by norm_num : (0:ℝ)≤1)
    (le_refl 1) hε.le E hE hrev hp hz1
  have hj := joint_visitors_markov L A hE (groundPathLaw n L r t g) (by norm_num : (0:ℝ)≤1) hh (H:=θ*D)
  apply hj.trans
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg A.card)
  have hδθ : Cs*δ≤θ/2 := by
    have hh := (le_div_iff₀ (by positivity : 0<(2:ℝ)*Cs)).mp (min_le_right 1 (θ/(2*Cs)))
    dsimp [δ]
    linarith
  have hc := mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left hzδ hCs.le).trans hδθ) hD0
  nlinarith

end HardSphere.FreeVisits

end
end

end

end OAI
