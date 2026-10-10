import Mathlib
import OAI.Probability.Ballisticity.Estimates.OccupationSampling
import OAI.Probability.Ballisticity.Estimates.LocalRadiusOrder
import OAI.Probability.Ballisticity.Stationary.EpisodePotentialIteration
import OAI.Probability.Ballisticity.Stationary.EpisodeMeanDrop
import OAI.Probability.Ballisticity.Crossings.BadCrossingLaw

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience
namespace OperationalConstants
variable {d : ℕ} {ν : Measure (Row d)} {e f : Direction d} {D : ℝ}

lemma radius_nonneg (C : OperationalConstants ν e f D) :
    0 ≤ episodeScaleRadius ν e f C.sfloor :=
  (fluctuationRadius_pos _ _ _).le

noncomputable def activeCount (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N : ℕ) (ω : Environment d) : ℕ :=
  EpisodeChainLedger.number (k:=C.k) e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N ω N

noncomputable def stagesAt (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N : ℕ) (ω : Environment d) (i : ℕ) : ℕ :=
  EpisodeChainLedger.stepMark (k:=C.k) e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N ω i

noncomputable def dropAt (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N : ℕ) (ω : Environment d) (i : ℕ) : ℝ :=
  EpisodeChainLedger.dropMark (k:=C.k) e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N ω i

noncomputable def injectionCost (C : OperationalConstants ν e f D) : ℝ :=
  ((BoundedInjection.injectionMultiplier (episodeScaleRadius ν e f C.sfloor)*C.k+1:ℕ)*(-Real.log C.κ))

lemma height_pos (C : OperationalConstants ν e f D) :
    ∀ s, C.sfloor ≤ s → 0 < episodeStageH C.χ C.b s := by
  intro s hs
  have hpos : 0<s := lt_of_lt_of_le zero_lt_one (C.hs.trans hs)
  exact_mod_cast (mul_pos hpos (Real.exp_pos _)).trans_le (C.height s hs)

lemma cost_nonneg (C : OperationalConstants ν e f D) : 0 ≤ C.injectionCost :=
  EpisodeChainLedger.injection_cost_nonneg (k:=C.k) (episodeScaleRadius ν e f) C.sfloor C.κ C.hκ0 C.hκ1

lemma finite_charge (C : OperationalConstants ν e f D) :
    ∃ L : ℕ, 0<L ∧ C.injectionCost ≤ 2*C.b*L := by
  obtain ⟨L,hL⟩ := exists_nat_gt (max 1 (C.injectionCost/(2*C.b)))
  refine ⟨L,?_,?_⟩
  · have : (0:ℝ)<L := lt_trans zero_lt_one ((le_max_left _ _).trans_lt hL)
    exact_mod_cast this
  · have := (div_le_iff₀ (show 0<2*C.b by nlinarith [C.hb])).mp
      ((le_max_right _ _).trans hL.le)
    nlinarith

theorem conditional_episode_drops [IsProbabilityMeasure ν]
    (C : OperationalConstants ν e f D) (hef : e.1≠f.1) (hD : 0≤D)
    (N : ℕ) (hN : C.sfloor ≤ (N:ℝ)) (hlarge : 32*C.b ≤ (1/2:ℝ)*Real.log (N:ℝ))
    (hmass : (N:ℝ)^(-D) ≤ (environmentLaw ν).real (badCrossingEvent e N (1/2)))
    (L : ℕ) (hL : 0<L) (hcharge : C.injectionCost ≤ 2*C.b*L) :
    let Q := (environmentLaw ν)[|badCrossingEvent e N (1/2)]
    (3/8*Real.log (N:ℝ) ≤ C.injectionCost*(∫ ω, (C.activeCount hef N ω:ℝ) ∂Q)) ∧
    ((∫ ω, (C.activeCount hef N ω:ℝ) ∂Q) ≤ Real.log (N:ℝ)/(16*C.b)+1) ∧
    (1/4*Real.log (N:ℝ) ≤ ∫ ω, ∑ i∈Finset.range N,
      if C.stagesAt hef N ω i ≤ L then C.dropAt hef N ω i else 0 ∂Q) := by
  let Q := (environmentLaw ν)[|badCrossingEvent e N (1/2)]
  have hN0 : 0<N := by exact_mod_cast lt_of_lt_of_le zero_lt_one (C.hs.trans hN)
  have hpos := badCrossingEvent_pos e N (1/2) D (environmentLaw ν) hN0 hmass
  have : IsProbabilityMeasure Q := cond_isProbabilityMeasure hpos
  have hκQ : ∀ᵐ ω ∂Q, ∀ y u, C.κ ≤ (ω y).1 u :=
    (cond_absolutelyContinuous (μ:=environmentLaw ν) (s:=badCrossingEvent e N (1/2))).ae_le C.rows
  have hpositive : ∀ᵐ ω ∂environmentLaw ν,
      0<(crossingQuenched (realPosition (step e)) 0 N ω).toReal := by
    filter_upwards [C.rows] with ω hω
    apply ENNReal.toReal_pos
    · exact ne_of_gt ((ENNReal.pow_pos (ENNReal.coe_pos.mpr C.hκ0) N).trans_le
        (coordinate_survival_lower e ω C.κ (fun y => hω y e) N))
    · exact crossingQuenched_ne_top _ _ _ _
  have hkl := badCrossing_cond_entropy e N (1/2) D (environmentLaw ν) hN0 hmass
  have hj := actual_expected_stages (k:=C.k) ν e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.K D (1/2) C.radius_nonneg N C.hs hN
    C.hf.le C.hg C.hb C.hK hD C.height C.stages Q hkl C.coeff C.small hlarge
  have hh := EpisodeChainLedger.mean_episode_drops_local (k:=C.k) e f hef
    (episodeScaleRadius ν e f) C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N
    C.order C.hf.le C.hb (lt_of_lt_of_le zero_lt_one C.hs) C.height_pos
    C.κ C.hκ0 C.hκ1 (lt_of_lt_of_le (by norm_num) C.hk) C.hbκ Q hκQ (1/2)
    (badCrossing_cond_drop e N (1/2) (environmentLaw ν) hN0 hpositive) hj L hL hcharge
  dsimp only [activeCount,injectionCost,stagesAt,dropAt]
  dsimp only [Q] at hh
  refine ⟨?_,?_,?_⟩
  · convert hh.1 using 1
    ring
  · convert hh.2.1 using 1
    ring
  · have hn : (1/2:ℝ)/2 = 1/4 := by norm_num
    rw [hn] at hh
    exact hh.2.2

end OperationalConstants
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience

lemma episodeInputLaw_environment {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i) :
    (episodeInputLaw e ν Q t ht).map (fun X => X.1.1)=Q := by
  change Measure.map (Prod.fst ∘ Prod.fst) _=Q
  rw [←Measure.map_map measurable_fst measurable_fst]
  unfold episodeInputLaw
  rw [Measure.map_fst_prod,measure_univ,one_smul]
  exact Measure.fst_compProd Q (globalEpisodeAnchors e t ht)

lemma episodeInputLaw_env_integral {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (F : Environment d → ℝ) (hF : Measurable F) :
    (∫ X, F X.1.1 ∂episodeInputLaw e ν Q t ht)=(∫ ω, F ω ∂Q) := by
  have hh := integral_map ((measurable_fst.comp measurable_fst).aemeasurable)
    hF.aestronglyMeasurable (μ:=episodeInputLaw e ν Q t ht)
  change (∫ y, F y ∂Measure.map (fun X => X.1.1) (episodeInputLaw e ν Q t ht)) = _ at hh
  rw [episodeInputLaw_environment] at hh
  exact hh.symm

namespace EpisodeChainLedger
variable {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
  (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ)
local notation "T" => episodeBoundary (k:=k) e f hef r fexp g χ b sfloor hR N
local notation "M" => number (k:=k) e f hef r fexp g χ b sfloor hR N
local notation "j" => stepMark (k:=k) e f hef r fexp g χ b sfloor hR N

noncomputable def arrayTime (ω : Environment d) (i : ℤ) := T ω i.toNat
noncomputable def arrayStages (ω : Environment d) (i : ℤ) :=
  if i<0 then 0 else j ω i.toNat
local notation "t" => arrayTime (k:=k) e f hef r fexp g χ b sfloor hR N
local notation "s" => arrayStages (k:=k) e f hef r fexp g χ b sfloor hR N

lemma arrayTime_measurable (i : ℤ) : Measurable (fun ω => t ω i) :=
  episodeBoundary_measurable (k:=k) e f hef r fexp g χ b sfloor hR N i.toNat
lemma arrayStages_measurable (i : ℤ) : Measurable (fun ω => s ω i) := by
  unfold arrayStages
  split
  · exact measurable_const
  · exact stepMark_measurable (k:=k) e f hef r fexp g χ b sfloor hR N i.toNat

lemma arrayTime_neg (ω : Environment d) (i : ℤ) (hi : i≤0) : t ω i=0 := by
  simp only [arrayTime,Int.toNat_eq_zero.mpr hi,episodeBoundary]

lemma arrayTime_nat (ω : Environment d) (i : ℕ) : t ω i=T ω i := by
  simp only [arrayTime,Int.toNat_natCast]

lemma arrayTime_terminal (ω : Environment d) (i : ℕ) (hi : M ω N ≤ i) : t ω i = N := by
  rw [arrayTime_nat]
  have hn : ¬ T ω i < N := by
    rw [active_iff_lt_number (k:=k) e f hef r fexp g χ b sfloor hR N ω i]
    exact not_lt.mpr hi
  exact le_antisymm (episodeBoundary_le (k:=k) e f hef r fexp g χ b sfloor hR N ω i) (Nat.le_of_not_lt hn)

lemma arrayStages_nat (ω : Environment d) (i : ℕ) : s ω i=j ω i := by
  simp only [arrayStages,Int.natCast_nonneg,not_lt.mpr,ite_false,Int.toNat_natCast]

lemma arrayStages_terminal (ω : Environment d) (i : ℕ) (hi : M ω N ≤ i) : s ω i = 0 := by
  rw [arrayStages_nat]
  have hn : ¬ T ω i < N := by
    rw [active_iff_lt_number (k:=k) e f hef r fexp g χ b sfloor hR N ω i]
    exact not_lt.mpr hi
  simp only [stepMark,ite_eq_right hn]

lemma operational_raw_mass (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (Q : Measure (Environment d)) [IsFiniteMeasure Q] :
    (actualOccupationRaw e ν Q t s (arrayTime_measurable (k:=k) e f hef r fexp g χ b sfloor hR N) N (fun ω => M ω N)).real Set.univ=
      ∫ ω, (M ω N:ℝ) ∂Q := by
  unfold actualOccupationRaw
  have hM : Measurable (fun X : EpisodeInput e => M X.1.1 N) :=
    (number_measurable (k:=k) e f hef r fexp g χ b sfloor hR N N).comp (measurable_fst.comp measurable_fst)
  rw [StationaryCompact.episodeOccupationRaw_mass N _ _
    (actualArrayMap_measurable e t s (arrayTime_measurable (k:=k) e f hef r fexp g χ b sfloor hR N)
      (arrayStages_measurable (k:=k) e f hef r fexp g χ b sfloor hR N)) _
    hM
    (fun X => number_le (k:=k) e f hef r fexp g χ b sfloor hR N X.1.1 N) _ StationaryCompact.shift_continuous.measurable]
  exact episodeInputLaw_env_integral e ν Q t _ _
    ((measurable_of_countable (fun n : ℕ => (n:ℝ))).comp (number_measurable (k:=k) e f hef r fexp g χ b sfloor hR N N))

lemma operational_mass_positive (Q : Measure (Environment d)) [IsProbabilityMeasure Q] (hN : 0<N) :
    0<∫ ω, (M ω N:ℝ) ∂Q := by
  have hh := integral_mono (integrable_const (1:ℝ))
    (number_integrable (k:=k) e f hef r fexp g χ b sfloor hR N Q N) (fun ω => by
      change (1:ℝ) ≤ (M ω N:ℝ)
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (number_positive (k:=k) e f hef r fexp g χ b sfloor hR N ω hN)))
  simp only [integral_const,probReal_univ,one_smul] at hh
  exact lt_of_lt_of_le zero_lt_one hh

end EpisodeChainLedger
end DirectionalTransience

end

end OAI
