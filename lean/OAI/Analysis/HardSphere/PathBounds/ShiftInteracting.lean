import Mathlib
import OAI.Analysis.HardSphere.PathBounds.InteractingVisits

namespace OAI

section

section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.ShiftVisits
open HardSphere.Wiener HardSphere.Lattice HardSphere.CellOrbital HardSphere.BathSlice HardSphere.FreeVisits
attribute [local irreducible] freeTrajectory
def defectiveTotalVisits {n K : ℕ} (L : Length) (c : Torus L) (A : Finset (DiscreteTorus K))
    (D : Set (ConfigurationPath 1 L)) (ω : ConfigurationPath n L) : ℕ := by
  classical
  exact ∑ i, if onePathAt i ω∈D then (pathVisitedSites L (center L c) A i ω).card else 0

lemma pathVisitedSites_onePathAt {n K : ℕ} (L : Length) (c : Torus L) (A : Finset (DiscreteTorus K))
    (i : Fin n) (ω : ConfigurationPath n L) :
    pathVisitedSites L (center L c) A 0 (onePathAt i ω)=pathVisitedSites L (center L c) A i ω := by
  simp only [pathVisitedSites,pathVisitsBall,onePathAt,oneConfiguration,ContinuousMap.coe_mk]
  rfl

lemma exp_defectiveTotalVisits {n K : ℕ} (L : Length) (c : Torus L) (A : Finset (DiscreteTorus K))
    (D : Set (ConfigurationPath 1 L)) {η : ℝ} (hη : 0≤η) (ω : ConfigurationPath n L) :
    ENNReal.ofReal (Real.exp (η*(defectiveTotalVisits L c A D ω : ℝ)))=
      ∏ i, (1+singleDefect L c A η D (onePathAt i ω)) := by
  classical
  simp only [defectiveTotalVisits,Nat.cast_sum,Finset.mul_sum,Real.exp_sum,
    ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ (Real.exp_pos _).le)]
  apply Finset.prod_congr rfl
  intro i _
  rw [singleDefect,pathVisitedSites_onePathAt]
  have hx : 0≤η*(if onePathAt i ω∈D then ((pathVisitedSites L (center L c) A i ω).card:ℝ) else 0) := by positivity
  have he : 0≤Real.exp (η*(if onePathAt i ω∈D then ((pathVisitedSites L (center L c) A i ω).card:ℝ) else 0))-1 := sub_nonneg.mpr (Real.one_le_exp_iff.mpr hx)
  simp only [Nat.cast_ite,Nat.cast_zero]
  rw [←ENNReal.ofReal_one,←ENNReal.ofReal_add zero_le_one he]
  congr 1
  ring

theorem interacting_visit_mgf {η₀ : ℝ} (hη₀ : 0≤η₀) :
    ∃ Cdel Cfree Csp αstar : ℝ,
      0<Cdel ∧ 0<Cfree ∧ 0<Csp ∧ 0<αstar ∧
    ∀ (n K : ℕ) [NeZero K] (L : Length), L.val=(K:ℝ) → ∀ r D : ℝ,
      D=(n:ℝ)/L.val^3 → 1≤D → αstar≤D*r → 0<r →
      (n:ℝ)*(2*Real.pi*r)^3≤L.val^3/2 →
    ∀ (g : Jet n L), IsGroundVector n L r g →
    ∀ (c : Torus L) (A : Finset (DiscreteTorus K)) {t η ε : ℝ},
      0<t → t≤2 → 0≤η → η≤η₀ → 0≤ε →
    ∀ E : Set (ConfigurationPath 1 L), MeasurableSet E →
      (∀ω,reverseConfigurationPath 1 L ω∈E ↔ ω∈E) →
      (∀ y : Torus L, coordinateWiener 1 {w | freeTrajectory 1 L t w (oneConfiguration y)∈E}≤ENNReal.ofReal ε) →
      Real.exp (t*Cdel*D*r)*(Cfree*η*ε^(1/3:ℝ))≤1 →
      (∫⁻ ω, ENNReal.ofReal (Real.exp (η*(defectiveTotalVisits L c A E ω:ℝ)))
        ∂groundPathLaw n L r t g) ≤
        ENNReal.ofReal (Real.exp (Csp*(Real.exp (t*Cdel*D*r)*(Cfree*η*ε^(1/3:ℝ)))*D*(A.card:ℝ))) := by
  classical
  obtain ⟨Cdel,hCdel,hdel⟩ := ground_product_one_add
  obtain ⟨Cfree,hCfree,hfree⟩ := free_single_defect_bound hη₀
  obtain ⟨Csp,αstar,hCsp,hα,hsp⟩ := spatial_count_mgf_enn
  refine ⟨Cdel,Cfree,Csp,αstar,hCdel,hCfree,hCsp,hα,?_⟩
  intro n K inst L hL r D hDeq hD hαr hr hs g hg c A t η ε ht ht2 hη hη0 hε E hE hrev hprob hz1
  let z := Real.exp (t*Cdel*D*r)*(Cfree*η*ε^(1/3:ℝ))
  have hz : 0≤z := by positivity
  have hsize : 1≤L.val := by rw [hL]; exact_mod_cast (NeZero.pos K)
  let := hg.groundPathLaw_probability ht.le
  by_cases hA : A.Nonempty
  · let B := A.image (center L c)
    have hB : B.Nonempty := hA.image _
    have hDexp : t*Cdel*(n:ℝ)*r/L.val^3=t*Cdel*D*r := by rw [hDeq]; ring
    calc
      _ = ∫⁻ ω,∏i,(1+singleDefect L c A η E (onePathAt i ω)) ∂groundPathLaw n L r t g :=
        lintegral_congr (exp_defectiveTotalVisits L c A E hη)
      _ ≤ ∫⁻ X,∏i,(1+ENNReal.ofReal (Real.exp (t*Cdel*(n:ℝ)*r/L.val^3))*
          oneFreeExpectation t (singleDefect L c A η E) (X i)) ∂groundPositionLaw n L g :=
        hdel n L r t hr ht hs g hg _ (singleDefect_measurable L c A η hE) (singleDefect_reverse L c A η hrev)
      _ ≤ ∫⁻ X,ENNReal.ofReal (Real.exp (z*weightedSiteCount L B X)) ∂groundPositionLaw n L g := by
        apply lintegral_mono
        intro X
        apply le_trans _ (product_one_add_exp_le L B hB hz X)
        apply Finset.prod_le_prod
        intro i _
        gcongr
        have H := hfree L hL c A ht ht2 hη hη0 hε E hE hprob (X i)
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

end HardSphere.ShiftVisits

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.ShiftVisits
open HardSphere.Wiener HardSphere.BathSlice HardSphere.Lattice HardSphere.CellOrbital HardSphere.FreeVisits

def visitorCount {n K : ℕ} (L : Length) (c : Torus L) (E : Set (ConfigurationPath 1 L))
    (v : DiscreteTorus K) (ω : ConfigurationPath n L) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i : Fin n ↦ onePathAt i ω∈E ∧ pathVisitsBall L 12 (center L c v) i ω)).card

lemma visitorCount_sum {n K : ℕ} (L : Length) (c : Torus L) (A : Finset (DiscreteTorus K))
    (E : Set (ConfigurationPath 1 L)) (ω : ConfigurationPath n L) :
    (∑v∈A,visitorCount L c E v ω)=defectiveTotalVisits L c A E ω := by
  classical
  simp only [visitorCount,Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : onePathAt i ω∈E
  · simp only [hi,true_and,pathVisitedSites,ite_eq_left,Finset.card_filter]
  · simp only [hi,false_and,ite_false,Finset.sum_const_zero,pathVisitedSites]

lemma visitorCount_measurable {n K : ℕ} (L : Length) (c : Torus L) {E : Set (ConfigurationPath 1 L)}
    (hE : MeasurableSet E) (v : DiscreteTorus K) : Measurable (visitorCount (n:=n) L c E v) := by
  classical
  have he : visitorCount (n:=n) L c E v=(fun ω ↦ ∑i : Fin n, if onePathAt i ω∈E ∧ pathVisitsBall L 12 (center L c v) i ω then (1:ℕ) else 0) := by
    funext ω
    simp only [visitorCount,Finset.card_filter]
  rw [he]
  apply Finset.measurable_fun_sum
  intro i _
  have hi : MeasurableSet {ω : ConfigurationPath n L | onePathAt i ω∈E} := hE.preimage (onePathAt_continuous i).measurable
  exact measurable_const.ite (hi.inter (pathVisitsBall_isClosed L 12 (center L c v) i).measurableSet) measurable_const

lemma defectiveTotalVisits_measurable {n K : ℕ} (L : Length) (c : Torus L) (A : Finset (DiscreteTorus K))
    {E : Set (ConfigurationPath 1 L)} (hE : MeasurableSet E) : Measurable (defectiveTotalVisits (n:=n) L c A E) := by
  have he : defectiveTotalVisits (n:=n) L c A E=fun ω ↦ ∑v∈A,visitorCount L c E v ω := by
    funext ω; exact (visitorCount_sum L c A E ω).symm
  rw [he]
  exact Finset.measurable_fun_sum _ (fun v _ ↦ visitorCount_measurable L c hE v)

lemma joint_visitor_sum {n K : ℕ} (L : Length) (c : Torus L) (A : Finset (DiscreteTorus K))
    (E : Set (ConfigurationPath 1 L)) {H : ℝ} {ω : ConfigurationPath n L}
    (h : ∀v∈A,H≤(visitorCount L c E v ω:ℝ)) :
    H*(A.card:ℝ)≤(defectiveTotalVisits L c A E ω:ℝ) := by
  rw [←visitorCount_sum L c A E ω,Nat.cast_sum]
  have hs := Finset.sum_le_sum h
  simpa only [Finset.sum_const,nsmul_eq_mul,mul_comm] using hs

lemma joint_visitors_markov {n K : ℕ} (L : Length) (c : Torus L) (A : Finset (DiscreteTorus K))
    {E : Set (ConfigurationPath 1 L)} (hE : MeasurableSet E)
    (μ : Measure (ConfigurationPath n L)) {η H Q : ℝ} (hη : 0≤η)
    (hmgf : (∫⁻ω,ENNReal.ofReal (Real.exp (η*(defectiveTotalVisits L c A E ω:ℝ))) ∂μ)≤
      ENNReal.ofReal (Real.exp (Q*(A.card:ℝ)))) :
    μ {ω | ∀v∈A,H≤(visitorCount L c E v ω:ℝ)}≤ENNReal.ofReal (Real.exp ((Q-η*H)*(A.card:ℝ))) := by
  let F := fun ω : ConfigurationPath n L ↦ ENNReal.ofReal (Real.exp (η*(defectiveTotalVisits L c A E ω:ℝ)))
  have hc : Measurable (fun k : ℕ ↦ (k:ℝ)) := measurable_of_countable _
  have hF : Measurable F := ((measurable_const.mul (hc.comp (defectiveTotalVisits_measurable L c A hE))).exp).ennreal_ofReal
  have hp : ENNReal.ofReal (Real.exp (η*(H*(A.card:ℝ))))≠0 := ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
  have hm := meas_ge_le_lintegral_div (μ:=μ) hF.aemeasurable hp ENNReal.ofReal_ne_top
  calc
    _ ≤ μ {ω | ENNReal.ofReal (Real.exp (η*(H*(A.card:ℝ))))≤F ω} := by
      apply measure_mono
      intro ω hω
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left (joint_visitor_sum L c A E hω) hη
    _ ≤ _ := hm
    _ ≤ ENNReal.ofReal (Real.exp (Q*(A.card:ℝ)))/ENNReal.ofReal (Real.exp (η*(H*(A.card:ℝ)))) := ENNReal.div_le_div_right hmgf _
    _ = _ := by
      rw [←ENNReal.ofReal_div_of_pos (Real.exp_pos _),←Real.exp_sub]
      congr 2
      ring

end HardSphere.ShiftVisits

end
end

end

end OAI
