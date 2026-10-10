import Mathlib
import OAI.Analysis.HardSphere.Allocation.Allocation
import OAI.Analysis.HardSphere.PathBounds.InteractingVisits

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.FreeVisits
open HardSphere.Wiener HardSphere.BathSlice HardSphere.Lattice HardSphere.CellOrbital

def visitorCount {n K : ℕ} (L : Length) (E : Set (ConfigurationPath 1 L))
    (v : DiscreteTorus K) (ω : ConfigurationPath n L) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i : Fin n ↦ onePathAt i ω∈E ∧ pathVisitsBall L 12 (siteCenter L v) i ω)).card

lemma visitorCount_sum {n K : ℕ} (L : Length) (A : Finset (DiscreteTorus K))
    (E : Set (ConfigurationPath 1 L)) (ω : ConfigurationPath n L) :
    (∑v∈A,visitorCount L E v ω)=defectiveTotalVisits L A E ω := by
  classical
  simp only [visitorCount,Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : onePathAt i ω∈E
  · simp only [hi,true_and,pathVisitedSites,ite_eq_left,Finset.card_filter]
  · simp only [hi,false_and,ite_false,Finset.sum_const_zero,pathVisitedSites]

lemma visitorCount_measurable {n K : ℕ} (L : Length) {E : Set (ConfigurationPath 1 L)}
    (hE : MeasurableSet E) (v : DiscreteTorus K) : Measurable (visitorCount (n:=n) L E v) := by
  classical
  have he : visitorCount (n:=n) L E v=(fun ω ↦ ∑i : Fin n, if onePathAt i ω∈E ∧ pathVisitsBall L 12 (siteCenter L v) i ω then (1:ℕ) else 0) := by
    funext ω
    simp only [visitorCount,Finset.card_filter]
  rw [he]
  apply Finset.measurable_fun_sum
  intro i _
  have hi : MeasurableSet {ω : ConfigurationPath n L | onePathAt i ω∈E} := hE.preimage (onePathAt_continuous i).measurable
  exact measurable_const.ite (hi.inter (pathVisitsBall_isClosed L 12 (siteCenter L v) i).measurableSet) measurable_const

lemma defectiveTotalVisits_measurable {n K : ℕ} (L : Length) (A : Finset (DiscreteTorus K))
    {E : Set (ConfigurationPath 1 L)} (hE : MeasurableSet E) : Measurable (defectiveTotalVisits (n:=n) L A E) := by
  have he : defectiveTotalVisits (n:=n) L A E=fun ω ↦ ∑v∈A,visitorCount L E v ω := by
    funext ω; exact (visitorCount_sum L A E ω).symm
  rw [he]
  exact Finset.measurable_fun_sum _ (fun v _ ↦ visitorCount_measurable L hE v)

lemma joint_visitor_sum {n K : ℕ} (L : Length) (A : Finset (DiscreteTorus K))
    (E : Set (ConfigurationPath 1 L)) {H : ℝ} {ω : ConfigurationPath n L}
    (h : ∀v∈A,H≤(visitorCount L E v ω:ℝ)) :
    H*(A.card:ℝ)≤(defectiveTotalVisits L A E ω:ℝ) := by
  rw [←visitorCount_sum L A E ω,Nat.cast_sum]
  have hs := Finset.sum_le_sum h
  simpa only [Finset.sum_const,nsmul_eq_mul,mul_comm] using hs

lemma joint_visitors_markov {n K : ℕ} (L : Length) (A : Finset (DiscreteTorus K))
    {E : Set (ConfigurationPath 1 L)} (hE : MeasurableSet E)
    (μ : Measure (ConfigurationPath n L)) {η H Q : ℝ} (hη : 0≤η)
    (hmgf : (∫⁻ω,ENNReal.ofReal (Real.exp (η*(defectiveTotalVisits L A E ω:ℝ))) ∂μ)≤
      ENNReal.ofReal (Real.exp (Q*(A.card:ℝ)))) :
    μ {ω | ∀v∈A,H≤(visitorCount L E v ω:ℝ)}≤ENNReal.ofReal (Real.exp ((Q-η*H)*(A.card:ℝ))) := by
  let F := fun ω : ConfigurationPath n L ↦ ENNReal.ofReal (Real.exp (η*(defectiveTotalVisits L A E ω:ℝ)))
  have hc : Measurable (fun k : ℕ ↦ (k:ℝ)) := measurable_of_countable _
  have hF : Measurable F := ((measurable_const.mul (hc.comp (defectiveTotalVisits_measurable L A hE))).exp).ennreal_ofReal
  have hp : ENNReal.ofReal (Real.exp (η*(H*(A.card:ℝ))))≠0 := ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
  have hm := meas_ge_le_lintegral_div (μ:=μ) hF.aemeasurable hp ENNReal.ofReal_ne_top
  calc
    _ ≤ μ {ω | ENNReal.ofReal (Real.exp (η*(H*(A.card:ℝ))))≤F ω} := by
      apply measure_mono
      intro ω hω
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left (joint_visitor_sum L A E hω) hη
    _ ≤ _ := hm
    _ ≤ ENNReal.ofReal (Real.exp (Q*(A.card:ℝ)))/ENNReal.ofReal (Real.exp (η*(H*(A.card:ℝ)))) := ENNReal.div_le_div_right hmgf _
    _ = _ := by
      rw [←ENNReal.ofReal_div_of_pos (Real.exp_pos _),←Real.exp_sub]
      congr 2
      ring

end HardSphere.FreeVisits

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Groups
open Wiener CellOrbital PathCutoff FreeVisits
attribute [local instance] Classical.propDecidable

lemma centeredCell_distance {L : Length} {c x : Torus L} (hx : x∈centeredCell L c) :
    torusDistance L x c≤1 := by
  have hd (j : Fin 3) : dist (x j) (c j)≤(1/2:ℝ) := by
    rw [dist_eq_norm,←centered_rep_abs]
    exact abs_le.mpr ⟨by linarith [(hx j).1], (hx j).2.le⟩
  unfold torusDistance
  apply Real.sqrt_le_one.mpr
  calc
    _ ≤ ∑ _j : Fin 3,(1/4:ℝ) := Finset.sum_le_sum (fun j _ ↦ by nlinarith [dist_nonneg (x:=x j) (y:=c j),hd j])
    _ ≤ 1 := by norm_num

@[simp] lemma intervalTime_zero_one (s : Time) : intervalTime 0 1 s=s := by
  apply Subtype.ext
  simp [intervalTime]

lemma smallDiameter_distance {L : Length} (ω : ConfigurationPath 1 L)
    (h : intervalDiameter 0 1 ω≤1) (s q : Time) : torusDistance L (ω s 0) (ω q 0)≤1 := by
  have hh := (intervalDistance_le 0 1 s q ω).trans h
  simpa only [intervalTime_zero_one] using hh

def longVisitors {N : ℕ} {L : Length} (c : Torus L) (ω : ConfigurationPath N L) : Finset (Fin N) :=
  Finset.univ.filter (fun i ↦ pathVisitsBall L 12 c i ω ∧ 1 < intervalDiameter 0 1 (onePathAt i ω))

def visitors {N : ℕ} {L : Length} (c : Torus L) (ω : ConfigurationPath N L) : Finset (Fin N) :=
  Finset.univ.filter (fun i ↦ pathVisitsBall L 12 c i ω)

structure Certificate {N K : ℕ} [Nontrivial (Fin N)] {L : Length}
    (m : ℕ) (r R C S s₀ ell θ H D : ℝ) (u : Time) (v : Fin 3→Fin K)
    (ω : ConfigurationPath N L) : Prop where
  low : ell*D≤(centeredCount L (gridCenter L v) (ω 0):ℝ)
  closeY : ((localCloseLabels L s₀ (gridCenter L v) (ω 0)).card:ℝ)<θ*D
  closeZ : ((localCloseLabels L s₀ (gridCenter L v) (ω 1)).card:ℝ)<θ*D
  visit : ((visitors (gridCenter L v) ω).card:ℝ)≤H*D
  regular : ∀i,pathVisitsBall L 12 (gridCenter L v) i ω→Regular m r R C u S (onePathAt i ω)
  long : ((longVisitors (gridCenter L v) ω).card:ℝ)<θ*D

lemma eligible_of_not_discarded {N K : ℕ} [Nontrivial (Fin N)] {L : Length}
    (m : ℕ) (r R C S s₀ : ℝ) (u : Time) (v : Fin 3→Fin K) (ω : ConfigurationPath N L)
    (hreg : ∀i,pathVisitsBall L 12 (gridCenter L v) i ω→Regular m r R C u S (onePathAt i ω))
    (i : Fin N) (hy : ω 0 i∈centeredCell L (gridCenter L v))
    (hY : i∉localCloseLabels L s₀ (gridCenter L v) (ω 0))
    (hZ : i∉localCloseLabels L s₀ (gridCenter L v) (ω 1))
    (hshort : i∉longVisitors (gridCenter L v) ω) : Eligible m r R C S s₀ u v i ω := by
  have hyc := centeredCell_distance hy
  have hv : pathVisitsBall L 12 (gridCenter L v) i ω := ⟨0,by linarith⟩
  have hsmall : intervalDiameter 0 1 (onePathAt i ω)≤1 := by
    by_contra! h
    exact hshort (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv,h⟩)
  have hd (s : Time) : torusDistance L (ω s i) (ω 0 i)≤1 := smallDiameter_distance (onePathAt i ω) hsmall s 0
  have hc (s : Time) : torusDistance L (ω s i) (gridCenter L v)≤2 := by
    have hh := torusDistance_triangle' L (ω s i) (ω 0 i) (gridCenter L v)
    linarith [hd s]
  have hNY : s₀<nearestParticleDistance L (ω 0) i := by
    by_contra! hh
    apply hY
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by linarith,hh⟩
  have hNZ : s₀<nearestParticleDistance L (ω 1) i := by
    by_contra! hh
    apply hZ
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by linarith [hc 1],hh⟩
  refine ⟨⟨hy,by linarith [hc 1],?_⟩,hreg i hv,?_⟩
  · intro j hji
    exact ⟨hNY.trans_le (nearestParticleDistance_le L (ω 0) i j hji),
      hNZ.trans_le (nearestParticleDistance_le L (ω 1) i j hji)⟩
  · intro s
    exact (hc s).trans (by norm_num)

lemma certificate_eligible_count {N K : ℕ} [Nontrivial (Fin N)] {L : Length}
    (m : ℕ) (r R C S s₀ ell θ H D : ℝ) (u : Time) (v : Fin 3→Fin K)
    (ω : ConfigurationPath N L) (h : Certificate m r R C S s₀ ell θ H D u v ω) :
    (ell-3*θ)*D≤((eligibleList m r R C S s₀ u v ω).card:ℝ) := by
  let E := eligibleList m r R C S s₀ u v ω
  let A := localCloseLabels L s₀ (gridCenter L v) (ω 0)
  let B := localCloseLabels L s₀ (gridCenter L v) (ω 1)
  let T := longVisitors (gridCenter L v) ω
  have hsub : Finset.univ.filter (fun i ↦ ω 0 i∈centeredCell L (gridCenter L v))⊆((E∪A)∪B)∪T := by
    intro i hi
    by_cases he : i∈E
    · simp [he]
    by_cases ha : i∈A
    · simp [ha]
    by_cases hb : i∈B
    · simp [hb]
    by_cases ht : i∈T
    · simp [ht]
    exfalso
    exact he (Finset.mem_filter.mpr ⟨Finset.mem_univ _,eligible_of_not_discarded m r R C S s₀ u v ω
      h.regular i (Finset.mem_filter.mp hi).2 ha hb ht⟩)
  have hcard : centeredCount L (gridCenter L v) (ω 0)≤E.card+A.card+B.card+T.card := by
    apply (Finset.card_le_card hsub).trans
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add_right
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)) _)
  have hc : (centeredCount L (gridCenter L v) (ω 0):ℝ)≤(E.card:ℝ)+(A.card:ℝ)+(B.card:ℝ)+(T.card:ℝ) := by exact_mod_cast hcard
  have h1 := h.low
  have h2 := h.closeY
  have h3 := h.closeZ
  have h4 := h.long
  change _≤(E.card:ℝ)
  change (A.card:ℝ)<θ*D at h2
  change (B.card:ℝ)<θ*D at h3
  change (T.card:ℝ)<θ*D at h4
  nlinarith

end HardSphere.Groups

end
end

end

end OAI
