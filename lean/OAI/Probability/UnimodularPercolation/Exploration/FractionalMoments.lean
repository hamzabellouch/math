import Mathlib
import OAI.Probability.UnimodularPercolation.Criticality.Susceptibility

namespace OAI

/-! Fractional Moments for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section GhostPowerTransfer
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem sqrt_log_power_bound (h : unitInterval) (hh : 0 < (h:ℝ))
    (a : ℝ) (ha : 1/2 < a) :
    Real.sqrt (Real.log (1/(h:ℝ))/(h:ℝ))*(h:ℝ)^a ≤ Real.sqrt (1/(2*a-1)) := by
  let ε := 2*a-1
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hpow := Real.rpow_pos_of_pos hh ε
  have hl := Real.log_le_rpow_div (show 0 ≤ 1/(h:ℝ) by positivity) hε
  rw [Real.div_rpow (by norm_num) hh.le,Real.one_rpow] at hl
  have hpowid : ((h:ℝ)^a)^2 = (h:ℝ)^ε*(h:ℝ) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hh.le]
    have he : a*(2:ℝ) = ε+1 := by dsimp [ε]; ring
    norm_num only [Nat.cast_ofNat]
    rw [he,Real.rpow_add hh,Real.rpow_one]
  have hbase : (Real.log (1/(h:ℝ))/(h:ℝ))*((h:ℝ)^a)^2 ≤ 1/ε := by
    rw [hpowid]
    calc
      _ = Real.log (1/(h:ℝ))*(h:ℝ)^ε := by field_simp
      _ ≤ ((1/(h:ℝ)^ε)/ε)*(h:ℝ)^ε := mul_le_mul_of_nonneg_right hl hpow.le
      _ = 1/ε := by field_simp
  have hlog : 0 ≤ Real.log (1/(h:ℝ))/(h:ℝ) := div_nonneg
    (Real.log_nonneg ((one_le_div hh).mpr h.2.2)) hh.le
  have hsq := Real.sq_sqrt hlog
  have htarget := Real.sq_sqrt (one_div_pos.mpr hε).le
  have hn := Real.sqrt_nonneg (1/ε)
  change _ ≤ Real.sqrt (1/ε)
  nlinarith [sq_nonneg (Real.sqrt (1/ε)-Real.sqrt (Real.log (1/(h:ℝ))/(h:ℝ))*(h:ℝ)^a)]

 

theorem markedConnection_power_transfer (G : BondGraph V E) (Q : Finset E) (x : V)
    (d : ℕ) (hd : 0 < d) (hdeg : ∀ v, (Q.filter (fun e => v ∈ G e)).card ≤ d)
    (p q h : unitInterval) (hq0 : 0 < (q:ℝ)) (hq1 : (q:ℝ) < 1)
    (hp : (q:ℝ)/2 ≤ (p:ℝ)) (hh : 0 < (h:ℝ))
    (a : ℝ) (ha : 1/2 < a) (he : (q:ℝ)-(p:ℝ) = (h:ℝ)^a) :
    markedConnectionPolynomial G Q x h q ≤
      Real.exp ((Real.sqrt ((d:ℝ)/2)/(((q:ℝ)/2)*(1-(q:ℝ)))) *
        Real.sqrt (1/(2*a-1))) * markedConnectionPolynomial G Q x h p := by
  have hp0 : 0 < (p:ℝ) := lt_of_lt_of_le (half_pos hq0) hp
  have hpq : p ≤ q := by change (p:ℝ) ≤ (q:ℝ); linarith [Real.rpow_pos_of_pos hh a]
  have H := markedConnection_transfer G Q x d hd hdeg p q h hp0 hpq hq1 hh
  apply H.trans
  apply mul_le_mul_of_nonneg_right
  · apply Real.exp_le_exp.mpr
    rw [he]
    have hr : Real.sqrt ((d:ℝ)/2)/((p:ℝ)*(1-(q:ℝ))) ≤
        Real.sqrt ((d:ℝ)/2)/(((q:ℝ)/2)*(1-(q:ℝ))) :=
      div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (mul_pos (half_pos hq0) (sub_pos.mpr hq1))
        (mul_le_mul_of_nonneg_right hp (sub_pos.mpr hq1).le)
    calc
      _ = (Real.sqrt ((d:ℝ)/2)/((p:ℝ)*(1-(q:ℝ)))) *
        (Real.sqrt (Real.log (1/(h:ℝ))/(h:ℝ))*(h:ℝ)^a) := by ring
      _ ≤ _ := mul_le_mul hr (sqrt_log_power_bound h hh a ha)
        (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg h.2.1 _)) (by positivity)
  · rw [markedConnectionPolynomial_eq_tree]
    exact ProbeTree.successMass_nonneg p h _

end GhostPowerTransfer
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section DyadicGhostParameters
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def dyadicGhost (j : ℕ) : unitInterval :=
  ⟨(1/2:ℝ)^j,⟨pow_nonneg (by norm_num) _,pow_le_one₀ (by norm_num) (by norm_num)⟩⟩

theorem dyadicGhost_pos (j : ℕ) : 0 < (dyadicGhost j:ℝ) := pow_pos (by norm_num) _

theorem dyadicGhost_volume (j : ℕ) : (dyadicGhost j:ℝ)*(2^j:ℕ) = 1 := by
  simp only [dyadicGhost,Nat.cast_pow,Nat.cast_ofNat,←mul_pow]
  norm_num

theorem tendsto_dyadicGhost : Tendsto (fun j => (dyadicGhost j:ℝ)) atTop (nhds 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

theorem dyadicGhost_rpow (j : ℕ) (t : ℝ) :
    (dyadicGhost j:ℝ)^t = (2:ℝ)^(-t*(j:ℝ)) := by
  change ((1/2:ℝ)^j)^t = _
  rw [←Real.rpow_natCast,←Real.rpow_mul (by norm_num : (0:ℝ) ≤ 1/2)]
  rw [show (1/2:ℝ) = (2:ℝ)^(-1:ℝ) by norm_num,
    ←Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  ring

 

theorem eventually_dyadic_backstep (q : unitInterval) (hq : 0 < (q:ℝ))
    (a : ℝ) (ha : 0 < a) (P : unitInterval → Prop) (hP : ∀ᶠ p in nhds q, P p) :
    ∀ᶠ j : ℕ in atTop, ∃ p : unitInterval,
      (q:ℝ)/2 ≤ (p:ℝ) ∧ p < q ∧ (q:ℝ)-(p:ℝ) = (dyadicGhost j:ℝ)^a ∧ P p := by
  obtain ⟨ε,hε,hball⟩ := Metric.eventually_nhds_iff.mp hP
  have ht : Tendsto (fun j => (dyadicGhost j:ℝ)^a) atTop (nhds 0) := by
    simpa only [Real.zero_rpow ha.ne', Function.comp_apply] using!
      (Real.continuousAt_rpow_const 0 a (Or.inr ha.le)).tendsto.comp tendsto_dyadicGhost
  filter_upwards [ht.eventually (eventually_lt_nhds (half_pos hq)),ht.eventually (eventually_lt_nhds hε)] with j hj hεj
  have hz := Real.rpow_pos_of_pos (dyadicGhost_pos j) a
  let p : unitInterval := ⟨(q:ℝ)-(dyadicGhost j:ℝ)^a,⟨by linarith,by linarith [q.2.2]⟩⟩
  refine ⟨p,by dsimp [p]; linarith,by change (q:ℝ)-(dyadicGhost j:ℝ)^a < (q:ℝ); linarith,
    by dsimp [p]; ring,?_⟩
  apply hball
  change |((q:ℝ)-(dyadicGhost j:ℝ)^a)-(q:ℝ)| < ε
  rw [show (q:ℝ)-(dyadicGhost j:ℝ)^a-(q:ℝ) = -(dyadicGhost j:ℝ)^a by ring,abs_neg,abs_of_pos hz]
  exact hεj

end DyadicGhostParameters
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section CriticalDyadicTail
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem critical_dyadic_bound_of_susceptibility [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (hq0 : 0 < (pc G:ℝ)) (hq1 : (pc G:ℝ) < 1)
    (C b a : ℝ) (hC : 0 < C) (ha : 1/2 < a)
    (hχ : ∀ᶠ p in nhds (pc G), p < pc G → ∀ x,
      susceptibility G p x ≤ C*((pc G:ℝ)-(p:ℝ))^(-b)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ j : ℕ in atTop, ∀ x,
      clusterWindowProbability G (pc G) x (2^j) (2^(j+1)) ≤
        K*(dyadicGhost j:ℝ)^(1-a*b) := by
  obtain ⟨d,hd,hdeg⟩ := exists_degree_bound G hqt
  let B := Real.exp ((Real.sqrt ((d:ℝ)/2)/(((pc G:ℝ)/2)*(1-(pc G:ℝ)))) * Real.sqrt (1/(2*a-1)))
  have hB : 0 < B := Real.exp_pos _
  refine ⟨2*B*C,by positivity,?_⟩
  filter_upwards [eventually_dyadic_backstep (pc G) hq0 a (by linarith) _ hχ] with j hj
  obtain ⟨p,hp,hpc,he,hχp⟩ := hj
  intro x
  let Q := incidentSupport G hloc (finite_reachBall hloc x (2^(j+1))).toFinset
  have hwin := clusterWindow_le_markedConnection G hloc x (2^j) (2^(j+1)) (pc G) (dyadicGhost j)
    (by rw [dyadicGhost_volume])
  have htra := markedConnection_power_transfer G Q x d hd
    (fun v => (incident_filter_card_le_degree G hloc Q v).trans (hdeg v)) p (pc G) (dyadicGhost j)
    hq0 hq1 hp (dyadicGhost_pos j) a ha he
  have hsub := markedConnection_le_susceptibility G hloc hqt Q x (dyadicGhost j) p hpc
  have hid : (dyadicGhost j:ℝ)*((dyadicGhost j:ℝ)^a)^(-b) = (dyadicGhost j:ℝ)^(1-a*b) := by
    rw [←Real.rpow_mul (dyadicGhost j).2.1]
    calc
      _ = (dyadicGhost j:ℝ)^1*(dyadicGhost j:ℝ)^(a*(-b)) := by rw [Real.rpow_one]
      _ = (dyadicGhost j:ℝ)^(1+a*(-b)) := (Real.rpow_add (dyadicGhost_pos j) _ _).symm
      _ = _ := by congr 1; ring
  calc
    _ ≤ 2*markedConnectionPolynomial G Q x (dyadicGhost j) (pc G) := hwin
    _ ≤ 2*(B*markedConnectionPolynomial G Q x (dyadicGhost j) p) :=
      mul_le_mul_of_nonneg_left htra (by norm_num)
    _ ≤ 2*(B*((dyadicGhost j:ℝ)*susceptibility G p x)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsub hB.le) (by norm_num)
    _ ≤ 2*(B*((dyadicGhost j:ℝ)*(C*((pc G:ℝ)-(p:ℝ))^(-b)))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hχp hpc x) (dyadicGhost j).2.1) hB.le) (by norm_num)
    _ = 2*B*C*((dyadicGhost j:ℝ)*((dyadicGhost j:ℝ)^a)^(-b)) := by rw [he]; ring
    _ = _ := by rw [hid]

 

theorem critical_power_integrable_of_dyadic_bound (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (α θ K : ℝ) (hα : 0 < α) (hθ : α < θ)
    (hbound : ∀ᶠ j : ℕ in atTop, ∀ x,
      clusterWindowProbability G p x (2^j) (2^(j+1)) ≤ K*(dyadicGhost j:ℝ)^θ) :
    ∀ x, Integrable (fun ω => ((cluster G ω x).ncard:ℝ)^α) (law p) := by
  intro x
  apply integrable_cluster_power_of_dyadic G hloc p x α hα
  have hs : Summable (fun j : ℕ => K*((2:ℝ)^(α-θ))^j) := by
    apply Summable.mul_left
    apply summable_geometric_of_norm_lt_one
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (by norm_num) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (sub_neg.mpr hθ)
  apply hs.of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hbound] with j hj
  rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    (clusterWindowProbability_nonneg G p x _ _))]
  calc
    _ ≤ (2:ℝ)^(α*(j:ℝ))*(K*(dyadicGhost j:ℝ)^θ) :=
      mul_le_mul_of_nonneg_left (hj x) (Real.rpow_nonneg (by norm_num) _)
    _ = K*((2:ℝ)^(α-θ))^j := by
      rw [dyadicGhost_rpow,←Real.rpow_natCast,←Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      rw [show (α-θ)*(j:ℝ) = α*(j:ℝ)+(-θ*(j:ℝ)) by ring,Real.rpow_add (by norm_num : (0:ℝ)<2)]
      ring

end CriticalDyadicTail
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section MomentFromGrowth
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem critical_moment_of_susceptibility_growth [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (hq0 : 0 < (pc G:ℝ)) (hq1 : (pc G:ℝ) < 1)
    (hgrowth : ∀ γ : ℝ, 0 < γ → γ < 1 → ∃ C : ℝ, 0 < C ∧
      ∀ᶠ p in nhds (pc G), p < pc G → ∀ x,
        susceptibility G p x ≤ C*((pc G:ℝ)-(p:ℝ))^(-1/(1-γ)))
    (α : ℝ) (hα : 0 < α) (hα1 : α < 1/2) :
    ∀ x, Integrable (fun ω => ((cluster G ω x).ncard:ℝ)^α) (law (pc G)) := by
  let γ := (1/2-α)/2
  have hγ : 0 < γ := by dsimp [γ]; linarith
  have hγ1 : γ < 1 := by dsimp [γ]; linarith
  have hprod : (1/2:ℝ) < (1-γ)*(1-α) := by
    have : 0 < γ*α := mul_pos hγ hα
    dsimp [γ] at *
    nlinarith
  obtain ⟨a,ha,hap⟩ := exists_between hprod
  have hden : 0 < 1-γ := sub_pos.mpr hγ1
  obtain ⟨C,hC,hnear⟩ := hgrowth γ hγ hγ1
  have he : -(1/(1-γ)) = -1/(1-γ) := by ring
  obtain ⟨K,hK,hbound⟩ := critical_dyadic_bound_of_susceptibility G hloc hqt hq0 hq1
    C (1/(1-γ)) a hC ha (by simpa only [he] using hnear)
  apply critical_power_integrable_of_dyadic_bound G hloc (pc G) α (1-a*(1/(1-γ))) K hα _ hbound
  have : a*(1/(1-γ)) < 1-α := by
    rw [mul_one_div]
    apply (div_lt_iff₀ hden).mpr
    nlinarith [hap]
  linarith

end MomentFromGrowth
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section CriticalRootMoments
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem critical_root_power_integrable
    [Countable V] [Countable E] [Nonempty V] [Nonempty E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hconn : Connected G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G)
    {ι : Type*} [Fintype ι] [Nonempty ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ e ∈ Γ, e (root i) = x)
    (hw : ∀ i, 0 < weight i) (hw1 : ∑ i, weight i = 1)
    (hp₀ : 0 < (pc G:ℝ)) (hp₁ : (pc G:ℝ) < 1)
    (hfin : ∀ i, ∀ᵐ ω ∂law (pc G), (cluster G ω (root i)).Finite)
    (α : ℝ) (hα : 0 < α) (hα1 : α < 1/2) :
    ∀ i, Integrable (fun ω => ((cluster G ω (root i)).ncard:ℝ)^α) (law (pc G)) := by
  by_contra hbad
  have hdiv : ∃ i, ¬ Integrable (fun ω => ((cluster G ω (root i)).ncard:ℝ)^α) (law (pc G)) :=
    not_forall.mp hbad
  obtain ⟨β,hαβ,hβ⟩ := exists_between hα1
  let ε := (1/2-β)/2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hε1 : ε < 1/2 := by dsimp [ε]; linarith
  have hsmall : β+(1/2+ε) < 1 := by dsimp [ε]; linarith
  have hg := susceptibility_growth_of_divergent_moment G hloc hconn hqt hh root weight Γ hΓ htr
    hcov hw hw1 hp₀ hp₁ hfin α β ε hα hαβ hε hε1 hsmall hdiv
  have hcover : ∀ x, ∃ i, x ∈ vertexOrbit G (root i) := by
    intro x
    obtain ⟨i,a,ha,hax⟩ := hcov x
    obtain ⟨b,hab⟩ := hΓ ha
    exact ⟨i,a,b,hab,hax⟩
  let c : ℝ := ∑ i, 1/weight i
  have hc : 0 < c := Finset.sum_pos (fun i _ => one_div_pos.mpr (hw i)) Finset.univ_nonempty
  have hmin (i : ι) : 1 ≤ c*weight i := by
    apply (div_le_iff₀ (hw i)).mp
    exact Finset.single_le_sum (fun j _ => (one_div_pos.mpr (hw j)).le) (Finset.mem_univ i)
  have hall := critical_moment_of_susceptibility_growth G hloc hqt hp₀ hp₁ (by
    intro γ hγ hγ1
    obtain ⟨C,hC,hnear⟩ := hg γ hγ hγ1
    refine ⟨c*C,mul_pos hc hC,?_⟩
    filter_upwards [hnear] with p hp
    intro hpc x
    calc
      _ ≤ c*rootSusceptibility G root weight p :=
        susceptibility_le_rootSusceptibility G root weight (fun i => (hw i).le) hcover c hc.le hmin p x
      _ ≤ c*(C*((pc G:ℝ)-(p:ℝ))^(-1/(1-γ))) := mul_le_mul_of_nonneg_left (hp hpc) hc.le
      _ = _ := by ring) α hα hα1
  obtain ⟨i,hi⟩ := hdiv
  exact hi (hall (root i))

end CriticalRootMoments
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section UniformFractionalMoments
attribute [local instance] Classical.propDecidable Classical.decEq

theorem measurable_cluster_power (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) (α : ℝ) :
    Measurable (fun ω : Set E => ((cluster G ω x).ncard:ℝ)^α) :=
  (measurable_of_countable (fun n : ℕ => (n:ℝ)^α)).comp (measurable_cluster_ncard G hloc x)

theorem integrable_cluster_power_covariant [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (x : V) (α : ℝ) :
    Integrable (fun ω => ((cluster G ω (a x)).ncard:ℝ)^α) (law p) ↔
      Integrable (fun ω => ((cluster G ω x).ncard:ℝ)^α) (law p) := by
  have h := integrable_map_measure (μ := law p)
    (measurable_cluster_power G hloc x α).aestronglyMeasurable
    (measurable_set_preimage b).aemeasurable
  rw [law_map_preimage_equiv] at h
  have he : ((fun ω : Set E => ((cluster G ω x).ncard:ℝ)^α) ∘ (fun ω => b ⁻¹' ω)) =
      (fun ω : Set E => ((cluster G ω (a x)).ncard:ℝ)^α) := by
    funext ω
    dsimp only [Function.comp_apply]
    rw [cluster_ncard_covariant G hab]
  rw [he] at h
  exact h.symm

theorem integral_cluster_power_covariant [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (x : V) (α : ℝ) :
    (∫ ω, ((cluster G ω (a x)).ncard:ℝ)^α ∂law p) =
      ∫ ω, ((cluster G ω x).ncard:ℝ)^α ∂law p := by
  have h := integral_map (μ := law p) (measurable_set_preimage b).aemeasurable
    (measurable_cluster_power G hloc x α).aestronglyMeasurable
  rw [law_map_preimage_equiv] at h
  simpa only [cluster_ncard_covariant G hab] using! h.symm

 
theorem uniform_cluster_power_of_root [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval)
    {ι : Type*} [Fintype ι] (root : ι → V)
    (hcover : ∀ x, ∃ i, x ∈ vertexOrbit G (root i)) (α : ℝ)
    (hi : ∀ i, Integrable (fun ω => ((cluster G ω (root i)).ncard:ℝ)^α) (law p)) :
    ∃ C : ℝ, 0 < C ∧ ∀ x,
      Integrable (fun ω => ((cluster G ω x).ncard:ℝ)^α) (law p) ∧
      (∫ ω, ((cluster G ω x).ncard:ℝ)^α ∂law p) ≤ C := by
  let C := 1+∑ i, ∫ ω, ((cluster G ω (root i)).ncard:ℝ)^α ∂law p
  have hn (x : V) : 0 ≤ ∫ ω, ((cluster G ω x).ncard:ℝ)^α ∂law p :=
    integral_nonneg (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hC : 0 < C := by dsimp [C]; linarith [Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hn (root i))]
  refine ⟨C,hC,?_⟩
  intro x
  obtain ⟨i,a,b,hab,rfl⟩ := hcover x
  refine ⟨(integrable_cluster_power_covariant G hloc p hab (root i) α).mpr (hi i),?_⟩
  rw [integral_cluster_power_covariant G hloc p hab]
  have hh := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => hn (root j)) (Finset.mem_univ i)
  dsimp [C]
  linarith

end UniformFractionalMoments
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section FractionalMomentCoupling
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem cluster_power_mono_integral [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) (p q : unitInterval) (hpq : p ≤ q)
    (α : ℝ) (hα : 0 ≤ α)
    (hfin : ∀ᵐ ω ∂law q, (cluster G ω x).Finite)
    (hi : Integrable (fun ω => ((cluster G ω x).ncard:ℝ)^α) (law q)) :
    Integrable (fun ω => ((cluster G ω x).ncard:ℝ)^α) (law p) ∧
      (∫ ω, ((cluster G ω x).ncard:ℝ)^α ∂law p) ≤
      ∫ ω, ((cluster G ω x).ncard:ℝ)^α ∂law q := by
  let f (r : unitInterval) (labels : E → unitInterval) := ((cluster G (openEdges labels r) x).ncard:ℝ)^α
  have hm (r : unitInterval) : Measurable (f r) :=
    (measurable_cluster_power G hloc x α).comp (measurable_openEdges r)
  have hmap (r : unitInterval) :
      Integrable (fun ω => ((cluster G ω x).ncard:ℝ)^α) (law r) ↔ Integrable (f r) labelLaw := by
    rw [←map_openEdges r]
    exact integrable_map_measure (measurable_cluster_power G hloc x α).aestronglyMeasurable
      (measurable_openEdges r).aemeasurable
  have hf : ∀ᵐ labels ∂(labelLaw : Measure (E → unitInterval)), (cluster G (openEdges labels q) x).Finite := by
    apply ae_of_ae_map (μ := (labelLaw : Measure (E → unitInterval)))
      (p := fun ω : Set E => (cluster G ω x).Finite) (measurable_openEdges q).aemeasurable
    rwa [map_openEdges]
  have hle : f p ≤ᵐ[labelLaw] f q := by
    filter_upwards [hf] with labels hlabels
    apply Real.rpow_le_rpow (Nat.cast_nonneg _) _ hα
    exact_mod_cast Set.ncard_le_ncard (show cluster G (openEdges labels p) x ⊆ cluster G (openEdges labels q) x from
      fun y hy => conn_mono G (openEdges_mono labels hpq) hy) hlabels
  have hiq := (hmap q).mp hi
  have hip : Integrable (f p) labelLaw := hiq.mono' (hm p).aestronglyMeasurable (by
    filter_upwards [hle] with labels hl
    rwa [Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)] )
  refine ⟨(hmap p).mpr hip,?_⟩
  have he (r : unitInterval) : (∫ labels, f r labels ∂labelLaw) =
      ∫ ω, ((cluster G ω x).ncard:ℝ)^α ∂law r := by
    rw [←map_openEdges r]
    exact (integral_map (measurable_openEdges r).aemeasurable
      (measurable_cluster_power G hloc x α).aestronglyMeasurable).symm
  rw [←he p,←he q]
  exact integral_mono_ae hip hiq hle

end FractionalMomentCoupling
end Percolation

 
namespace Percolation
universe u v
variable {E : Type v}
section DecisionCovarianceAlgebra
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def finiteCovariance (Q : Finset E) (p : ℝ) (f g : Finset E → ℝ) : ℝ :=
  bernoulliPolynomial Q (fun ω => f ω*g ω) p - bernoulliPolynomial Q f p*bernoulliPolynomial Q g p

noncomputable def coordinateAverage (e : E) (p : ℝ) (f : Finset E → ℝ) (ω : Finset E) : ℝ :=
  (1-p)*f ω+p*f (insert e ω)

noncomputable def coordinateVariation (Q : Finset E) (p : ℝ) (f : Finset E → ℝ) (e : E) : ℝ :=
  bernoulliPolynomial (Q.erase e) (fun ω => |f (insert e ω)-f ω|) p

theorem bernoulliPolynomial_abs (Q : Finset E) (p : unitInterval) (f : Finset E → ℝ) :
    |bernoulliPolynomial Q f p| ≤ bernoulliPolynomial Q (fun ω => |f ω|) p := by
  rw [abs_le]
  constructor
  · have h := bernoulliPolynomial_mono Q (fun ω => -|f ω|) f p p.2
      (fun _ _ => neg_abs_le _)
    have he : bernoulliPolynomial Q (fun ω => -|f ω|) p =
        -bernoulliPolynomial Q (fun ω => |f ω|) p := by
      simp only [bernoulliPolynomial,neg_mul,Finset.sum_neg_distrib]
    rwa [he] at h
  · exact bernoulliPolynomial_mono Q f (fun ω => |f ω|) p p.2 (fun _ _ => le_abs_self _)

theorem coordinateVariation_nonneg (Q : Finset E) (p : unitInterval) (f : Finset E → ℝ) (e : E) :
    0 ≤ coordinateVariation Q p f e :=
  bernoulliPolynomial_nonneg _ _ p p.2 (fun _ _ => abs_nonneg _)

 
theorem finiteCovariance_first_coordinate (S : Finset E) (e : E) (he : e ∉ S)
    (p : ℝ) (f g : Finset E → ℝ) :
    finiteCovariance (insert e S) p f g =
      (1-p)*finiteCovariance S p (coordinateAverage e p f) g +
      p*finiteCovariance S p (coordinateAverage e p f) (fun ω => g (insert e ω)) +
      p*(1-p)*bernoulliPolynomial S
        (fun ω => (f (insert e ω)-f ω)*(g (insert e ω)-g ω)) p := by
  unfold finiteCovariance
  rw [bernoulliPolynomial_insert S e he,bernoulliPolynomial_insert S e he,
    bernoulliPolynomial_insert S e he]
  have hav := bernoulliPolynomial_affine S f (fun ω => f (insert e ω)) (1-p) p p
  change bernoulliPolynomial S (coordinateAverage e p f) p = _ at hav
  rw [hav]
  have h0 : bernoulliPolynomial S (fun ω => coordinateAverage e p f ω*g ω) p =
      (1-p)*bernoulliPolynomial S (fun ω => f ω*g ω) p+
      p*bernoulliPolynomial S (fun ω => f (insert e ω)*g ω) p := by
    simpa only [coordinateAverage,add_mul,mul_assoc] using
      bernoulliPolynomial_affine S (fun ω => f ω*g ω) (fun ω => f (insert e ω)*g ω) (1-p) p p
  have h1 : bernoulliPolynomial S (fun ω => coordinateAverage e p f ω*g (insert e ω)) p =
      (1-p)*bernoulliPolynomial S (fun ω => f ω*g (insert e ω)) p+
      p*bernoulliPolynomial S (fun ω => f (insert e ω)*g (insert e ω)) p := by
    simpa only [coordinateAverage,add_mul,mul_assoc] using
      bernoulliPolynomial_affine S (fun ω => f ω*g (insert e ω)) (fun ω => f (insert e ω)*g (insert e ω)) (1-p) p p
  rw [h0,h1]
  have herr : bernoulliPolynomial S (fun ω => (f (insert e ω)-f ω)*(g (insert e ω)-g ω)) p =
      bernoulliPolynomial S (fun ω => f (insert e ω)*g (insert e ω)) p-
      bernoulliPolynomial S (fun ω => f (insert e ω)*g ω) p-
      bernoulliPolynomial S (fun ω => f ω*g (insert e ω)) p+
      bernoulliPolynomial S (fun ω => f ω*g ω) p := by
    simp only [bernoulliPolynomial]
    simp only [←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ω _
    ring
  rw [herr]
  ring

end DecisionCovarianceAlgebra
end Percolation

 
namespace Percolation
universe v
variable {E : Type v}
section CoordinateAveragingBounds
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem coordinateVariation_average_le (S : Finset E) (e j : E) (he : e ∉ S) (hje : j ≠ e)
    (p : unitInterval) (f : Finset E → ℝ) :
    coordinateVariation S p (coordinateAverage e p f) j ≤ coordinateVariation (insert e S) p f j := by
  unfold coordinateVariation
  rw [Finset.erase_insert_of_ne hje.symm,bernoulliPolynomial_insert _ e (by simp [he])]
  let f₀ := fun ω : Finset E => |f (insert j ω)-f ω|
  let f₁ := fun ω : Finset E => |f (insert j (insert e ω))-f (insert e ω)|
  change _ ≤ (1-(p:ℝ))*bernoulliPolynomial (S.erase j) f₀ p+
    (p:ℝ)*bernoulliPolynomial (S.erase j) f₁ p
  rw [←bernoulliPolynomial_affine]
  apply bernoulliPolynomial_mono _ _ _ p p.2
  intro ω _
  have hid : coordinateAverage e p f (insert j ω)-coordinateAverage e p f ω =
      (1-(p:ℝ))*(f (insert j ω)-f ω)+(p:ℝ)*(f (insert j (insert e ω))-f (insert e ω)) := by
    simp only [coordinateAverage,Finset.insert_comm e j]
    ring
  rw [hid]
  calc
    _ ≤ |(1-(p:ℝ))*(f (insert j ω)-f ω)|+|(p:ℝ)*(f (insert j (insert e ω))-f (insert e ω))| := abs_add_le _ _
    _ = _ := by rw [abs_mul,abs_mul,abs_of_nonneg (sub_nonneg.mpr p.2.2),abs_of_nonneg p.2.1]

 

theorem finiteCovariance_first_bound (S : Finset E) (e : E) (he : e ∉ S)
    (p : unitInterval) (f g : Finset E → ℝ)
    (hg : ∀ ω ⊆ insert e S, g ω ∈ Set.Icc (0:ℝ) 1) :
    |finiteCovariance (insert e S) p f g| ≤
      (1-(p:ℝ))*|finiteCovariance S p (coordinateAverage e p f) g|+
      (p:ℝ)*|finiteCovariance S p (coordinateAverage e p f) (fun ω => g (insert e ω))|+
      (p:ℝ)*(1-(p:ℝ))*coordinateVariation (insert e S) p f e := by
  have hgood : |bernoulliPolynomial S (fun ω => (f (insert e ω)-f ω)*(g (insert e ω)-g ω)) p| ≤
      coordinateVariation (insert e S) p f e := by
    apply (bernoulliPolynomial_abs S p _).trans
    unfold coordinateVariation
    rw [Finset.erase_insert he]
    apply bernoulliPolynomial_mono _ _ _ p p.2
    intro ω hω
    rw [abs_mul]
    have h₀ := hg ω (hω.trans (Finset.subset_insert _ _))
    have h₁ := hg (insert e ω) (Finset.insert_subset_insert e hω)
    have hd : |g (insert e ω)-g ω| ≤ 1 := by rw [abs_le]; constructor <;> linarith [h₀.1,h₀.2,h₁.1,h₁.2]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hd (abs_nonneg (f (insert e ω)-f ω))
  rw [finiteCovariance_first_coordinate S e he]
  calc
    _ ≤ |(1-(p:ℝ))*finiteCovariance S p (coordinateAverage e p f) g+
          (p:ℝ)*finiteCovariance S p (coordinateAverage e p f) (fun ω => g (insert e ω))|+
        |(p:ℝ)*(1-(p:ℝ))*bernoulliPolynomial S (fun ω => (f (insert e ω)-f ω)*(g (insert e ω)-g ω)) p| := abs_add_le _ _
    _ ≤ |(1-(p:ℝ))*finiteCovariance S p (coordinateAverage e p f) g|+
          |(p:ℝ)*finiteCovariance S p (coordinateAverage e p f) (fun ω => g (insert e ω))|+
        |(p:ℝ)*(1-(p:ℝ))*bernoulliPolynomial S (fun ω => (f (insert e ω)-f ω)*(g (insert e ω)-g ω)) p| :=
      add_le_add (abs_add_le _ _) le_rfl
    _ ≤ _ := by
      rw [abs_mul,abs_mul,abs_mul,abs_of_nonneg (sub_nonneg.mpr p.2.2),abs_of_nonneg p.2.1,
        abs_of_nonneg (mul_nonneg p.2.1 (sub_nonneg.mpr p.2.2))]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hgood (mul_nonneg p.2.1 (sub_nonneg.mpr p.2.2)))

end CoordinateAveragingBounds
end Percolation

 
namespace Percolation
universe v
variable {E : Type v}
section EdgeDecisionTrees
attribute [local instance] Classical.propDecidable Classical.decEq

 
inductive EdgeQueryTree (E : Type v) where
  | done (b : Bool)
  | query (e : E) (closed opened : EdgeQueryTree E)

namespace EdgeQueryTree

def Valid (Q : Finset E) : EdgeQueryTree E → Prop
  | .done _ => True
  | .query e t₀ t₁ => e ∈ Q ∧ Valid (Q.erase e) t₀ ∧ Valid (Q.erase e) t₁

noncomputable def eval (ω : Finset E) : EdgeQueryTree E → Bool
  | .done b => b
  | .query e t₀ t₁ => if e ∈ ω then eval ω t₁ else eval ω t₀

noncomputable def value (t : EdgeQueryTree E) (ω : Finset E) : ℝ := if t.eval ω then 1 else 0

noncomputable def reads (ω : Finset E) (i : E) : EdgeQueryTree E → Prop
  | .done _ => False
  | .query e t₀ t₁ => i = e ∨ if e ∈ ω then reads ω i t₁ else reads ω i t₀

noncomputable def revealment (p : ℝ) (i : E) : EdgeQueryTree E → ℝ
  | .done _ => 0
  | .query e t₀ t₁ => if i = e then 1 else (1-p)*revealment p i t₀+p*revealment p i t₁

theorem value_mem (t : EdgeQueryTree E) (ω : Finset E) : t.value ω ∈ Set.Icc (0:ℝ) 1 := by
  unfold value
  split <;> simp

theorem revealment_nonneg (p : unitInterval) (i : E) (t : EdgeQueryTree E) : 0 ≤ t.revealment p i := by
  induction t with
  | done => rfl
  | query e t₀ t₁ ih₀ ih₁ =>
    simp only [revealment]
    split_ifs
    · norm_num
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr p.2.2) ih₀) (mul_nonneg p.2.1 ih₁)

theorem eval_congr (t : EdgeQueryTree E) {Q : Finset E} (ht : t.Valid Q)
    {ω η : Finset E} (h : ∀ e ∈ Q, e ∈ ω ↔ e ∈ η) : t.eval ω = t.eval η := by
  induction t generalizing Q with
  | done => rfl
  | query e t₀ t₁ ih₀ ih₁ =>
    simp only [eval,h e ht.1]
    split
    · exact ih₁ ht.2.2 (fun a ha => h a (Finset.mem_of_mem_erase ha))
    · exact ih₀ ht.2.1 (fun a ha => h a (Finset.mem_of_mem_erase ha))

theorem eval_insert (t : EdgeQueryTree E) {Q : Finset E} (ht : t.Valid Q)
    {e : E} (he : e ∉ Q) (ω : Finset E) : t.eval (insert e ω) = t.eval ω := by
  apply eval_congr t ht
  intro a ha
  simp [show a ≠ e from fun h => he (h ▸ ha)]

theorem value_insert (t : EdgeQueryTree E) {Q : Finset E} (ht : t.Valid Q)
    {e : E} (he : e ∉ Q) (ω : Finset E) : t.value (insert e ω) = t.value ω := by
  simp only [value,eval_insert t ht he]

theorem reads_congr (t : EdgeQueryTree E) {Q : Finset E} (ht : t.Valid Q)
    {ω η : Finset E} (h : ∀ e ∈ Q, e ∈ ω ↔ e ∈ η) (i : E) : t.reads ω i ↔ t.reads η i := by
  induction t generalizing Q with
  | done => rfl
  | query e t₀ t₁ ih₀ ih₁ =>
    simp only [reads,h e ht.1]
    split
    · rw [ih₁ ht.2.2 (fun a ha => h a (Finset.mem_of_mem_erase ha))]
    · rw [ih₀ ht.2.1 (fun a ha => h a (Finset.mem_of_mem_erase ha))]

theorem reads_mem (t : EdgeQueryTree E) {Q : Finset E} (ht : t.Valid Q)
    (ω : Finset E) (i : E) (hi : t.reads ω i) : i ∈ Q := by
  induction t generalizing Q with
  | done => exact hi.elim
  | query e t₀ t₁ ih₀ ih₁ =>
    rcases hi with rfl | hi
    · exact ht.1
    · split_ifs at hi
      · exact Finset.mem_of_mem_erase (ih₁ ht.2.2 hi)
      · exact Finset.mem_of_mem_erase (ih₀ ht.2.1 hi)

end EdgeQueryTree
end EdgeDecisionTrees
end Percolation

 
namespace Percolation
universe v
variable {E : Type v}
section EdgeTreeCovariance
attribute [local instance] Classical.propDecidable Classical.decEq

theorem finiteCovariance_congr_right (Q : Finset E) (p : ℝ) (f : Finset E → ℝ)
    {g h : Finset E → ℝ} (he : ∀ ω ⊆ Q, g ω = h ω) :
    finiteCovariance Q p f g = finiteCovariance Q p f h := by
  unfold finiteCovariance
  rw [bernoulliPolynomial_congr Q (fun ω hω => congrArg (f ω * ·) (he ω hω)),
    bernoulliPolynomial_congr Q he]

namespace EdgeQueryTree

 

theorem covariance_bound (t : EdgeQueryTree E) {Q : Finset E} (ht : t.Valid Q)
    (p : unitInterval) (f : Finset E → ℝ) :
    |finiteCovariance Q p f t.value| ≤
      ∑ i ∈ Q, t.revealment p i * ((p:ℝ)*(1-(p:ℝ))*coordinateVariation Q p f i) := by
  induction t generalizing Q f with
  | done b =>
    have hv : (done b : EdgeQueryTree E).value = (fun _ => if b then (1:ℝ) else 0) := rfl
    rw [hv]
    cases b
    · simp [finiteCovariance,revealment]
    · simp [finiteCovariance,revealment,bernoulliPolynomial_const]
  | query e t₀ t₁ ih₀ ih₁ =>
    have he := ht.1
    have heS : e ∉ Q.erase e := Finset.notMem_erase _ _
    have hQ : insert e (Q.erase e) = Q := Finset.insert_erase he
    let fav := coordinateAverage e (p:ℝ) f
    have hcov₀ : finiteCovariance (Q.erase e) p fav (query e t₀ t₁).value =
        finiteCovariance (Q.erase e) p fav t₀.value := by
      apply finiteCovariance_congr_right
      intro ω hω
      have heω : e ∉ ω := fun h => heS (hω h)
      simp only [value,eval,ite_eq_right heω]
    have hcov₁ : finiteCovariance (Q.erase e) p fav (fun ω => (query e t₀ t₁).value (insert e ω)) =
        finiteCovariance (Q.erase e) p fav t₁.value := by
      apply finiteCovariance_congr_right
      intro ω _
      simp only [value,eval,Finset.mem_insert_self,ite_true,eval_insert t₁ ht.2.2 heS]
    have hav (i : E) (hi : i ∈ Q.erase e) :
        coordinateVariation (Q.erase e) p fav i ≤ coordinateVariation Q p f i := by
      simpa only [hQ] using coordinateVariation_average_le (Q.erase e) e i heS
        (Finset.ne_of_mem_erase hi) p f
    have hb₀ : |finiteCovariance (Q.erase e) p fav t₀.value| ≤
        ∑ i ∈ Q.erase e, t₀.revealment p i * ((p:ℝ)*(1-(p:ℝ))*coordinateVariation Q p f i) := by
      apply (ih₀ ht.2.1 fav).trans
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hav i hi) (mul_nonneg p.2.1 (sub_nonneg.mpr p.2.2)))
        (revealment_nonneg p i t₀)
    have hb₁ : |finiteCovariance (Q.erase e) p fav t₁.value| ≤
        ∑ i ∈ Q.erase e, t₁.revealment p i * ((p:ℝ)*(1-(p:ℝ))*coordinateVariation Q p f i) := by
      apply (ih₁ ht.2.2 fav).trans
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hav i hi) (mul_nonneg p.2.1 (sub_nonneg.mpr p.2.2)))
        (revealment_nonneg p i t₁)
    have hfirst := finiteCovariance_first_bound (Q.erase e) e heS p f (query e t₀ t₁).value
      (fun ω _ => value_mem _ ω)
    change _ ≤ (1-(p:ℝ))*|finiteCovariance (Q.erase e) p fav (query e t₀ t₁).value|+
      (p:ℝ)*|finiteCovariance (Q.erase e) p fav (fun ω => (query e t₀ t₁).value (insert e ω))|+_ at hfirst
    rw [hQ,hcov₀,hcov₁] at hfirst
    apply hfirst.trans
    calc
      _ ≤ (1-(p:ℝ))*(∑ i ∈ Q.erase e, t₀.revealment p i * ((p:ℝ)*(1-(p:ℝ))*coordinateVariation Q p f i))+
          (p:ℝ)*(∑ i ∈ Q.erase e, t₁.revealment p i * ((p:ℝ)*(1-(p:ℝ))*coordinateVariation Q p f i))+
          (p:ℝ)*(1-(p:ℝ))*coordinateVariation Q p f e :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_left hb₀ (sub_nonneg.mpr p.2.2))
          (mul_le_mul_of_nonneg_left hb₁ p.2.1)) le_rfl
      _ = _ := by
        rw [←Finset.sum_erase_add _ _ he]
        congr 1
        · rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          rw [revealment,ite_eq_right (Finset.ne_of_mem_erase hi)]
          ring
        · simp [revealment]

end EdgeQueryTree
end EdgeTreeCovariance
end Percolation

 
namespace Percolation
universe v
variable {E : Type v}
section RevealmentProbability
attribute [local instance] Classical.propDecidable Classical.decEq
namespace EdgeQueryTree

theorem reads_insert (t : EdgeQueryTree E) {Q : Finset E} (ht : t.Valid Q)
    {e : E} (he : e ∉ Q) (ω : Finset E) (i : E) : t.reads (insert e ω) i ↔ t.reads ω i := by
  apply reads_congr t ht
  intro a ha
  simp [show a ≠ e from fun h => he (h ▸ ha)]

 
theorem revealment_eq_probability (t : EdgeQueryTree E) {Q : Finset E} (ht : t.Valid Q)
    (p : ℝ) (i : E) :
    t.revealment p i = bernoulliPolynomial Q (fun ω => if t.reads ω i then 1 else 0) p := by
  induction t generalizing Q with
  | done => simp [revealment,reads]
  | query e t₀ t₁ ih₀ ih₁ =>
    by_cases hie : i = e
    · subst i
      simp [revealment,reads,bernoulliPolynomial_const]
    · have heS : e ∉ Q.erase e := Finset.notMem_erase _ _
      conv_rhs => rw [←Finset.insert_erase ht.1]
      rw [bernoulliPolynomial_insert _ e heS]
      simp only [revealment,ite_eq_right hie]
      rw [ih₀ ht.2.1,ih₁ ht.2.2]
      congr 1
      · congr 1
        apply bernoulliPolynomial_congr
        intro ω hω
        have heω : e ∉ ω := fun h => heS (hω h)
        simp only [reads,hie,false_or,ite_eq_right heω]
      · congr 1
        apply bernoulliPolynomial_congr
        intro ω _
        simp only [reads,hie,false_or,Finset.mem_insert_self,ite_true,reads_insert t₁ ht.2.2 heS]

end EdgeQueryTree
end RevealmentProbability
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section SeededEdgeSearch
attribute [local instance] Classical.propDecidable Classical.decEq

 

noncomputable def seededEdgeSearch (G : BondGraph V E) (x : V) :
    ℕ → Finset E → Finset V → EdgeQueryTree E
  | 0, _, R => .done (decide (x ∈ R))
  | n+1, Q, R =>
    if hc : SearchCrossing G Q R then
      let t := searchCrossing G Q R hc
      .query t.1 (seededEdgeSearch G x n (Q.erase t.1) R)
        (seededEdgeSearch G x n (Q.erase t.1) (insert t.2.2 R))
    else .done (decide (x ∈ R))

theorem seededEdgeSearch_valid (G : BondGraph V E) (x : V) (n : ℕ) (Q : Finset E) (R : Finset V) :
    (seededEdgeSearch G x n Q R).Valid Q := by
  induction n generalizing Q R with
  | zero => trivial
  | succ n ih =>
    simp only [seededEdgeSearch]
    split_ifs with hc
    · exact ⟨(searchCrossing_spec G Q R hc).1,ih _ _,ih _ _⟩
    · trivial

theorem seedMarked_singleton_of_no_crossing (G : BondGraph V E) (Q : Finset E) (R : Finset V)
    (x : V) (h : ¬ SearchCrossing G Q R) (ω : Finset E) (hω : ω ⊆ Q) :
    SeedMarked G (ω : Set E) R {x} ↔ x ∈ R := by
  constructor
  · intro hx
    by_contra hn
    exact seedMarked_false_of_no_crossing G Q R {x} h (by simpa using hn) ω hω hx
  · intro hx
    exact ⟨x,hx,x,Finset.mem_singleton_self x,conn_refl G _ x⟩

 
theorem seededEdgeSearch_correct (G : BondGraph V E) (x : V) (n : ℕ) (Q : Finset E) (R : Finset V)
    (hn : Q.card ≤ n) (ω : Finset E) (hω : ω ⊆ Q) :
    (seededEdgeSearch G x n Q R).eval ω = true ↔ SeedMarked G (ω : Set E) R {x} := by
  induction n generalizing Q R ω with
  | zero =>
    have hQ : Q = ∅ := Finset.card_eq_zero.mp (by omega)
    simp only [seededEdgeSearch,EdgeQueryTree.eval,decide_eq_true_eq]
    exact (seedMarked_singleton_of_no_crossing G Q R x (by simp [SearchCrossing,hQ]) ω hω).symm
  | succ n ih =>
    simp only [seededEdgeSearch]
    split_ifs with hc
    · obtain ⟨he,ha,hb,hends⟩ := searchCrossing_spec G Q R hc
      have hcard : (Q.erase (searchCrossing G Q R hc).1).card ≤ n := by
        rw [Finset.card_erase_of_mem he]; omega
      simp only [EdgeQueryTree.eval]
      by_cases heω : (searchCrossing G Q R hc).1 ∈ ω
      · simp only [ite_eq_left heω]
        rw [←Finset.insert_erase heω,Finset.coe_insert,seedMarked_insert_edge G _ R {x} _ _ _ ha hends,
          EdgeQueryTree.eval_insert _ (seededEdgeSearch_valid G x n _ _) (Finset.notMem_erase _ _)]
        exact ih _ _ hcard _ (Finset.erase_subset_erase _ hω)
      · simp only [ite_eq_right heω]
        exact ih _ _ hcard ω (Finset.subset_erase.mpr ⟨hω,heω⟩)
    · simp only [EdgeQueryTree.eval,decide_eq_true_eq]
      exact (seedMarked_singleton_of_no_crossing G Q R x hc ω hω).symm

 

theorem seededEdgeSearch_reads (G : BondGraph V E) (x : V) (n : ℕ) (Q : Finset E) (R : Finset V)
    (ω : Finset E) (i : E) (hi : (seededEdgeSearch G x n Q R).reads ω i) :
    ∃ a ∈ G i, ∃ r ∈ R, Conn G (ω : Set E) r a := by
  induction n generalizing Q R with
  | zero => exact hi.elim
  | succ n ih =>
    simp only [seededEdgeSearch] at hi
    split_ifs at hi with hc
    · obtain ⟨he,ha,hb,hends⟩ := searchCrossing_spec G Q R hc
      rcases hi with rfl | hi
      · refine ⟨(searchCrossing G Q R hc).2.1,?_,_,ha,conn_refl G _ _⟩
        rw [hends]; simp
      · split_ifs at hi with heω
        · obtain ⟨a,hai,r,hr,hra⟩ := ih _ _ hi
          rcases Finset.mem_insert.mp hr with rfl | hr
          · refine ⟨a,hai,(searchCrossing G Q R hc).2.1,ha,?_⟩
            exact (Relation.ReflTransGen.single ⟨(searchCrossing G Q R hc).1,heω,hends⟩).trans hra
          · exact ⟨a,hai,r,hr,hra⟩
        · exact ih _ _ hi
    · exact hi.elim

end SeededEdgeSearch
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section RandomizedDecisionCovariance
attribute [local instance] Classical.propDecidable Classical.decEq

theorem finiteCovariance_average_right (Q : Finset E) (F : Finset V) (p h : ℝ)
    (f : Finset E → ℝ) (g : Finset V → Finset E → ℝ) :
    finiteCovariance Q p f (fun ω => bernoulliPolynomial F (fun m => g m ω) h) =
      bernoulliPolynomial F (fun m => finiteCovariance Q p f (g m)) h := by
  unfold finiteCovariance
  rw [bernoulliPolynomial_sub,bernoulliPolynomial_const_mul,
    ←bernoulliPolynomial_commute Q F (fun ω m => g m ω) p h]
  congr 1
  calc
    _ = bernoulliPolynomial Q (fun ω => bernoulliPolynomial F (fun m => f ω*g m ω) h) p := by
      apply bernoulliPolynomial_congr
      intro ω _
      exact (bernoulliPolynomial_const_mul F (fun m => g m ω) (f ω) h).symm
    _ = _ := bernoulliPolynomial_commute Q F _ p h

 

theorem EdgeQueryTree.randomized_covariance_bound (Q : Finset E) (F : Finset V)
    (p h : unitInterval) (f : Finset E → ℝ) (trees : Finset V → EdgeQueryTree E)
    (ht : ∀ m ⊆ F, (trees m).Valid Q) :
    |finiteCovariance Q p f (fun ω => bernoulliPolynomial F (fun m => (trees m).value ω) h)| ≤
      ∑ i ∈ Q, bernoulliPolynomial F (fun m => (trees m).revealment p i) h *
        ((p:ℝ)*(1-(p:ℝ))*coordinateVariation Q p f i) := by
  rw [finiteCovariance_average_right]
  apply (bernoulliPolynomial_abs F h _).trans
  calc
    _ ≤ bernoulliPolynomial F (fun m => ∑ i ∈ Q, (trees m).revealment p i *
        ((p:ℝ)*(1-(p:ℝ))*coordinateVariation Q p f i)) h := by
      apply bernoulliPolynomial_mono _ _ _ h h.2
      intro m hm
      exact (trees m).covariance_bound (ht m hm) p f
    _ = _ := by simp only [bernoulliPolynomial_sum,bernoulliPolynomial_mul_const]

noncomputable def finiteSeedProbability (G : BondGraph V E) (F : Finset V)
    (ω : Finset E) (x : V) (h : ℝ) : ℝ :=
  bernoulliPolynomial F (fun m => if ∃ y ∈ m, Conn G (ω:Set E) x y then 1 else 0) h

theorem seededEdgeSearch_value (G : BondGraph V E) (x : V) (Q : Finset E)
    (m : Finset V) (ω : Finset E) (hω : ω ⊆ Q) :
    (seededEdgeSearch G x Q.card Q m).value ω =
      if ∃ y ∈ m, Conn G (ω:Set E) x y then 1 else 0 := by
  have hc := seededEdgeSearch_correct G x Q.card Q m le_rfl ω hω
  have he : SeedMarked G (ω:Set E) m {x} ↔ ∃ y ∈ m, Conn G (ω:Set E) x y := by
    simp only [SeedMarked,Finset.mem_singleton,exists_eq_left]
    exact exists_congr (fun y => and_congr_right (fun _ => ⟨conn_symm G _,conn_symm G _⟩))
  unfold EdgeQueryTree.value
  simp only [hc,he]

theorem finiteSeedProbability_tree (G : BondGraph V E) (Q : Finset E) (F : Finset V)
    (x : V) (h : ℝ) (ω : Finset E) (hω : ω ⊆ Q) :
    finiteSeedProbability G F ω x h =
      bernoulliPolynomial F (fun m => (seededEdgeSearch G x Q.card Q m).value ω) h := by
  apply bernoulliPolynomial_congr
  intro m _
  exact (seededEdgeSearch_value G x Q m ω hω).symm

end RandomizedDecisionCovariance
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section SeedRevealmentBounds
attribute [local instance] Classical.propDecidable Classical.decEq

theorem seededEdgeSearch_reads_endpoints (G : BondGraph V E) (x : V) (Q : Finset E)
    (m : Finset V) (ω : Finset E) (i : E) (a b : V) (he : G i = s(a,b))
    (hi : (seededEdgeSearch G x Q.card Q m).reads ω i) :
    (∃ y ∈ m, Conn G (ω:Set E) a y) ∨ (∃ y ∈ m, Conn G (ω:Set E) b y) := by
  obtain ⟨z,hz,r,hr,hrz⟩ := seededEdgeSearch_reads G x Q.card Q m ω i hi
  rw [he] at hz
  rcases (by simpa using hz : z = a ∨ z = b) with rfl | rfl
  · exact Or.inl ⟨r,hr,conn_symm G _ hrz⟩
  · exact Or.inr ⟨r,hr,conn_symm G _ hrz⟩

theorem seededEdgeSearch_mean_revealment_le (G : BondGraph V E) (x : V)
    (Q : Finset E) (F : Finset V) (p h : unitInterval) (i : E) (a b : V) (he : G i = s(a,b)) :
    bernoulliPolynomial F (fun m => (seededEdgeSearch G x Q.card Q m).revealment p i) h ≤
      bernoulliPolynomial Q (fun ω => finiteSeedProbability G F ω a h) p +
      bernoulliPolynomial Q (fun ω => finiteSeedProbability G F ω b h) p := by
  simp_rw [EdgeQueryTree.revealment_eq_probability _ (seededEdgeSearch_valid G x Q.card Q _)]
  rw [←bernoulliPolynomial_commute,←bernoulliPolynomial_add]
  apply bernoulliPolynomial_mono _ _ _ p p.2
  intro ω _
  unfold finiteSeedProbability
  rw [←bernoulliPolynomial_add]
  apply bernoulliPolynomial_mono _ _ _ h h.2
  intro m _
  have hr := seededEdgeSearch_reads_endpoints G x Q m ω i a b he
  by_cases hread : (seededEdgeSearch G x Q.card Q m).reads ω i
  · rcases hr hread with ha | hb
    · simp only [ite_eq_left hread,ite_eq_left ha]
      split_ifs <;> norm_num
    · simp only [ite_eq_left hread,ite_eq_left hb]
      split_ifs <;> norm_num
  · simp only [ite_eq_right hread]
    split_ifs <;> norm_num

 

theorem finiteSeedProbability_component (G : BondGraph V E) (Q : Finset E) (F : Finset V)
    (x : V) (hF : insert x (searchVertices G Q) ⊆ F)
    (ω : Finset E) (hω : ω ⊆ Q) (h : ℝ) :
    finiteSeedProbability G F ω x h = 1-(1-h)^(finiteRootComponent G ω x).card := by
  let C := finiteRootComponent G ω x
  have hCF : C ⊆ F := finiteRootComponent_subset G Q F x ω hω hF
  have he (m : Finset V) : (∃ y ∈ m, Conn G (ω:Set E) x y) ↔ m ∩ C ≠ ∅ := by
    rw [Finset.nonempty_iff_ne_empty.symm]
    constructor
    · rintro ⟨y,hy,hxy⟩
      exact ⟨y,Finset.mem_inter.mpr ⟨hy,by change y ∈ (C:Set V); simpa only [C,coe_finiteRootComponent,cluster,Set.mem_ofPred_eq] using hxy⟩⟩
    · rintro ⟨y,hy⟩
      refine ⟨y,(Finset.mem_inter.mp hy).1,?_⟩
      have hm : y ∈ (C:Set V) := (Finset.mem_inter.mp hy).2
      simpa only [C,coe_finiteRootComponent,cluster,Set.mem_ofPred_eq] using hm
  calc
    _ = bernoulliPolynomial F (fun m => 1-(if m ∩ C = ∅ then 1 else 0)) h := by
      apply bernoulliPolynomial_congr
      intro m _
      by_cases hm : m ∩ C = ∅
      · have hn : ¬∃ y ∈ m, Conn G (ω:Set E) x y := fun hc => (he m).mp hc hm
        simp only [hm,hn,ite_false,ite_true,sub_self]
      · have hy := (he m).mpr hm
        simp only [hm,hy,ite_false,ite_true,sub_zero]
    _ = 1-bernoulliPolynomial F (fun m => if m ∩ C = ∅ then 1 else 0) h := by
      rw [bernoulliPolynomial_sub,bernoulliPolynomial_const]
    _ = _ := by rw [bernoulliPolynomial_restrict C F hCF (fun m => if m = ∅ then 1 else 0) h,
      bernoulliPolynomial_empty_indicator]

end SeedRevealmentBounds
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section GhostFractionalPower
attribute [local instance] Classical.propDecidable Classical.decEq

theorem one_sub_pow_one_sub_le_power (h : unitInterval) (n : ℕ) (α : ℝ)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    1-(1-(h:ℝ))^n ≤ (h:ℝ)^α*(n:ℝ)^α := by
  rw [←Real.mul_rpow h.2.1 (Nat.cast_nonneg _)]
  by_cases ht : (h:ℝ)*n ≤ 1
  · exact (one_sub_pow_one_sub_le h n).trans (Real.self_le_rpow_of_le_one (mul_nonneg h.2.1 (Nat.cast_nonneg _)) ht hα1)
  · have ht' : 1 ≤ (h:ℝ)*n := (lt_of_not_ge ht).le
    exact (sub_le_self _ (pow_nonneg (sub_nonneg.mpr h.2.2) _)).trans (Real.one_le_rpow ht' hα)

theorem markedConnection_le_cluster_power (G : BondGraph V E) (Q : Finset E)
    (x : V) (h p : unitInterval) (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hfin : ∀ᵐ ω ∂law p, (cluster G ω x).Finite)
    (hi : Integrable (fun ω => ((cluster G ω x).ncard:ℝ)^α) (law p)) :
    markedConnectionPolynomial G Q x h p ≤ (h:ℝ)^α*(∫ ω, ((cluster G ω x).ncard:ℝ)^α ∂law p) := by
  rw [markedConnection_integral,←integral_const_mul]
  apply integral_mono_ae
  · exact integrable_finite_local Q p _ (by intro ω; simp only [Set.inter_assoc,Set.inter_self])
  · exact hi.const_mul _
  · filter_upwards [hfin] with ω hω
    apply (one_sub_pow_one_sub_le_power h _ α hα hα1).trans
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg h.2.1 _)
    apply Real.rpow_le_rpow (Nat.cast_nonneg _) _ hα
    exact_mod_cast Set.ncard_le_ncard (fun y hy => conn_mono G Set.inter_subset_left hy) hω

theorem finiteSeedProbability_expectation (G : BondGraph V E) (Q : Finset E) (F : Finset V)
    (x : V) (hF : insert x (searchVertices G Q) ⊆ F) (h p : ℝ) :
    bernoulliPolynomial Q (fun ω => finiteSeedProbability G F ω x h) p =
      markedConnectionPolynomial G Q x h p := by
  rw [markedConnection_component_polynomial]
  apply bernoulliPolynomial_congr
  intro ω hω
  exact finiteSeedProbability_component G Q F x hF ω hω h

theorem finiteSeedProbability_le_cluster_power (G : BondGraph V E) (Q : Finset E) (F : Finset V)
    (x : V) (hF : insert x (searchVertices G Q) ⊆ F) (h p : unitInterval)
    (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hfin : ∀ᵐ ω ∂law p, (cluster G ω x).Finite)
    (hi : Integrable (fun ω => ((cluster G ω x).ncard:ℝ)^α) (law p)) :
    bernoulliPolynomial Q (fun ω => finiteSeedProbability G F ω x h) p ≤
      (h:ℝ)^α*(∫ ω, ((cluster G ω x).ncard:ℝ)^α ∂law p) := by
  rw [finiteSeedProbability_expectation G Q F x hF]
  exact markedConnection_le_cluster_power G Q x h p α hα hα1 hfin hi

end GhostFractionalPower
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section MonotoneDecisionRusso
attribute [local instance] Classical.propDecidable Classical.decEq

theorem sum_coordinateVariation_eq_deriv (Q : Finset E) (f : Finset E → ℝ)
    (hf : Monotone f) (p : ℝ) :
    (∑ i ∈ Q, coordinateVariation Q p f i) = deriv (bernoulliPolynomial Q f) p := by
  rw [(hasDerivAt_bernoulliPolynomial Q f p).deriv]
  apply Finset.sum_congr rfl
  intro i _
  apply bernoulliPolynomial_congr
  intro ω _
  exact abs_of_nonneg (sub_nonneg.mpr (hf (Finset.subset_insert _ _)))

theorem EdgeQueryTree.randomized_covariance_le_deriv (Q : Finset E) (F : Finset V)
    (p h : unitInterval) (f : Finset E → ℝ) (hf : Monotone f)
    (trees : Finset V → EdgeQueryTree E) (ht : ∀ m ⊆ F, (trees m).Valid Q)
    (R : ℝ) (hR : ∀ i ∈ Q, bernoulliPolynomial F (fun m => (trees m).revealment p i) h ≤ R) :
    |finiteCovariance Q p f (fun ω => bernoulliPolynomial F (fun m => (trees m).value ω) h)| ≤
      R*((p:ℝ)*(1-(p:ℝ)))*deriv (bernoulliPolynomial Q f) p := by
  apply (randomized_covariance_bound Q F p h f trees ht).trans
  calc
    _ ≤ ∑ i ∈ Q, R*((p:ℝ)*(1-(p:ℝ))*coordinateVariation Q p f i) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_right (hR i hi)
        (mul_nonneg (mul_nonneg p.2.1 (sub_nonneg.mpr p.2.2)) (coordinateVariation_nonneg Q p f i))
    _ = _ := by simp only [←mul_assoc,←Finset.mul_sum,sum_coordinateVariation_eq_deriv Q f hf]

 

theorem seededEdgeSearch_revealment_of_moments (G : BondGraph V E) (Q : Finset E)
    (x : V) (p h : unitInterval) (α C : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hfin : ∀ y, ∀ᵐ ω ∂law p, (cluster G ω y).Finite)
    (hI : ∀ y, Integrable (fun ω => ((cluster G ω y).ncard:ℝ)^α) (law p))
    (hC : ∀ y, (∫ ω, ((cluster G ω y).ncard:ℝ)^α ∂law p) ≤ C) :
    ∀ i ∈ Q, bernoulliPolynomial (insert x (searchVertices G Q))
      (fun m => (seededEdgeSearch G x Q.card Q m).revealment p i) h ≤ 2*C*(h:ℝ)^α := by
  intro i hi
  obtain ⟨⟨a,b⟩,he⟩ := Quot.exists_rep (G i)
  have he' : G i = s(a,b) := he.symm
  have hFa : insert a (searchVertices G Q) ⊆ insert x (searchVertices G Q) :=
    Finset.insert_subset_iff.mpr ⟨Finset.mem_insert_of_mem (mem_searchVertices G hi (by rw [he']; simp)),Finset.subset_insert _ _⟩
  have hFb : insert b (searchVertices G Q) ⊆ insert x (searchVertices G Q) :=
    Finset.insert_subset_iff.mpr ⟨Finset.mem_insert_of_mem (mem_searchVertices G hi (by rw [he']; simp)),Finset.subset_insert _ _⟩
  have ha := finiteSeedProbability_le_cluster_power G Q _ a hFa h p α hα hα1 (hfin a) (hI a)
  have hb := finiteSeedProbability_le_cluster_power G Q _ b hFb h p α hα hα1 (hfin b) (hI b)
  have hca := mul_le_mul_of_nonneg_left (hC a) (Real.rpow_nonneg h.2.1 α)
  have hcb := mul_le_mul_of_nonneg_left (hC b) (Real.rpow_nonneg h.2.1 α)
  have hr := seededEdgeSearch_mean_revealment_le G x Q (insert x (searchVertices G Q)) p h i a b he'
  linarith

theorem finiteSeed_covariance_upper (G : BondGraph V E) (Q : Finset E) (x : V)
    (p h : unitInterval) (α C : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hfin : ∀ y, ∀ᵐ ω ∂law p, (cluster G ω y).Finite)
    (hI : ∀ y, Integrable (fun ω => ((cluster G ω y).ncard:ℝ)^α) (law p))
    (hC : ∀ y, (∫ ω, ((cluster G ω y).ncard:ℝ)^α ∂law p) ≤ C)
    (f : Finset E → ℝ) (hf : Monotone f) :
    |finiteCovariance Q p f (fun ω => finiteSeedProbability G (insert x (searchVertices G Q)) ω x h)| ≤
      (2*C*(h:ℝ)^α)*((p:ℝ)*(1-(p:ℝ)))*deriv (bernoulliPolynomial Q f) p := by
  have hc := EdgeQueryTree.randomized_covariance_le_deriv Q (insert x (searchVertices G Q)) p h f hf
    (fun m => seededEdgeSearch G x Q.card Q m) (fun _ _ => seededEdgeSearch_valid G x Q.card Q _)
    (2*C*(h:ℝ)^α) (seededEdgeSearch_revealment_of_moments G Q x p h α C hα hα1 hfin hI hC)
  convert hc using 2
  apply finiteCovariance_congr_right
  intro ω hω
  exact finiteSeedProbability_tree G Q _ x h ω hω

end MonotoneDecisionRusso
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ClusterTailCovariance
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def finiteClusterTailIndicator (G : BondGraph V E) (x : V) (n : ℕ)
    (ω : Finset E) : ℝ := if n ≤ (finiteRootComponent G ω x).card then 1 else 0

noncomputable def finiteClusterTail (G : BondGraph V E) (Q : Finset E) (x : V) (n : ℕ) (p : ℝ) : ℝ :=
  bernoulliPolynomial Q (finiteClusterTailIndicator G x n) p

theorem finiteClusterTailIndicator_mono (G : BondGraph V E) (x : V) (n : ℕ) :
    Monotone (finiteClusterTailIndicator G x n) := by
  intro ω η hωη
  have hc := Finset.card_le_card (finiteRootComponent_mono G hωη x)
  unfold finiteClusterTailIndicator
  split_ifs <;> norm_num
  omega

theorem finiteClusterTail_nonneg (G : BondGraph V E) (Q : Finset E) (x : V) (n : ℕ) (p : unitInterval) :
    0 ≤ finiteClusterTail G Q x n p := by
  apply bernoulliPolynomial_nonneg _ _ p p.2
  intro ω _
  unfold finiteClusterTailIndicator
  split_ifs <;> norm_num

theorem finiteClusterTail_deriv_nonneg (G : BondGraph V E) (Q : Finset E) (x : V) (n : ℕ) (p : unitInterval) :
    0 ≤ deriv (finiteClusterTail G Q x n) p := by
  change 0 ≤ deriv (bernoulliPolynomial Q (finiteClusterTailIndicator G x n)) p
  rw [←sum_coordinateVariation_eq_deriv Q _ (finiteClusterTailIndicator_mono G x n)]
  exact Finset.sum_nonneg (fun i _ => coordinateVariation_nonneg Q p _ i)

 

theorem finiteSeed_covariance_lower (G : BondGraph V E) (Q : Finset E) (x : V)
    (n : ℕ) (p h : unitInterval) (hn : 1 ≤ (h:ℝ)*n) (B : ℝ)
    (hB : markedConnectionPolynomial G Q x h p ≤ B) :
    (1/2-B)*finiteClusterTail G Q x n p ≤ finiteCovariance Q p
      (finiteClusterTailIndicator G x n)
      (fun ω => finiteSeedProbability G (insert x (searchVertices G Q)) ω x h) := by
  have hprod : (1:ℝ)/2*finiteClusterTail G Q x n p ≤
      bernoulliPolynomial Q (fun ω => finiteClusterTailIndicator G x n ω*
        finiteSeedProbability G (insert x (searchVertices G Q)) ω x h) p := by
    rw [finiteClusterTail,←bernoulliPolynomial_const_mul]
    apply bernoulliPolynomial_mono _ _ _ p p.2
    intro ω hω
    rw [finiteSeedProbability_component G Q _ x le_rfl ω hω]
    unfold finiteClusterTailIndicator
    by_cases hsize : n ≤ (finiteRootComponent G ω x).card
    · simp only [ite_eq_left hsize,mul_one,one_mul]
      apply one_sub_pow_one_sub_ge_half
      exact hn.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hsize) h.2.1)
    · simp only [ite_eq_right hsize,mul_zero,zero_mul,le_refl]
  have hmean := finiteSeedProbability_expectation G Q (insert x (searchVertices G Q)) x le_rfl (h:ℝ) p
  unfold finiteCovariance
  rw [hmean]
  change _ ≤ _-finiteClusterTail G Q x n p*markedConnectionPolynomial G Q x h p
  have hm := mul_le_mul_of_nonneg_left hB (finiteClusterTail_nonneg G Q x n p)
  nlinarith

end ClusterTailCovariance
end Percolation

end OAI
