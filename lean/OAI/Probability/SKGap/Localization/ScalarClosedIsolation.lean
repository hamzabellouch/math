import Mathlib
import OAI.Probability.SKGap.Localization.ScalarEmpirical

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
open Real Set
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ENNReal BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
open Set Filter Topology
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal
namespace SKGap

theorem scalar_closed_isolation {j T smin : ℝ} (hj : 0 < j) (hj1 : j < 1)
    (hT : 0 ≤ T) (hsmin : 0 < smin) {C : Set ScalarPoint} (hC : IsClosed C)
    (hne : ∀ p ∈ C, p.2.1 ∈ Icc 0 T → p.2.2 = 0 → p.1 ≠ scalarCurve j p.2.1) :
    ∃ a > 0, ∃ δ > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ hn : 0 < n, ∀ t ∈ Icc 0 T,
      ∀ σ ∈ Icc 0 (min δ 1), ∀ E : Set (Fin n → ℝ), MeasurableSet E →
      (∀ y ∈ E, @scalarEmpirical (Fin n) _ ⟨⟨0,hn⟩⟩ y t σ ∈ C) →
      (∀ y ∈ E, smin ≤ scalarS j (@scalarEmpirical (Fin n) _ ⟨⟨0,hn⟩⟩ y t σ)) →
      (∫⁻ y in E, ENNReal.ofReal (@scalarIntegrand (Fin n) _ ⟨⟨0,hn⟩⟩ j t σ y)) ≤
        ENNReal.ofReal (exp (-a*(n:ℝ))) := by
  obtain ⟨R,hR,hTail⟩ := scalar_uniform_tail hj.le hT hsmin 1
  let K := scalarBox j R T smin ∩ C
  have hK : IsCompact K := (isCompact_scalarBox j R T smin).inter_right hC
  have hmom : K ⊆ scalarMomentDomain R := fun p hp => ⟨hp.1.1.1,mem_univ _⟩
  obtain ⟨a,ha,δ,hδ,N,hN⟩ := scalar_compact_isolation hj hj1 hR.le hK hmom
    (fun p hp => hp.1.1.2.1.1) (fun p hp => hp.1.1.2.2.1)
    (fun p hp => hsmin.trans_le hp.1.2) (fun p hp hz => hne p hp.2 hp.1.1.2.1 hz)
  let b := min a 1
  have hb : 0 < b := lt_min ha zero_lt_one
  obtain ⟨M,hM⟩ := absorb_finite_exponential_factor 2 (half_pos hb)
  refine ⟨b/2,half_pos hb,δ,hδ,max N M,?_⟩
  intro n hn hn' t ht σ hσ E hE hforbid hs
  let : Nonempty (Fin n) := ⟨⟨0,hn'⟩⟩
  have hσ' : σ ∈ Icc (0:ℝ) 1 := ⟨hσ.1,hσ.2.trans (min_le_right _ _)⟩
  let B : Set (Fin n → ℝ) := {y | ∑ i, (y i)^2 ≤ (n:ℝ)*R}
  have hB : MeasurableSet B := isClosed_le (by fun_prop) continuous_const |>.measurableSet
  have hc := hN n (le_trans (le_max_left _ _) hn) hn' (fun y => scalarEmpirical y t σ)
    (E ∩ B) (hE.inter hB) (fun y hy => ⟨⟨⟨⟨empirical_momentBall y hR.le
      (by simpa only [Fintype.card_fin] using (show ∑ i, (y i)^2 ≤ (n:ℝ)*R from hy.2)),ht,hσ'⟩,
      hs y hy.1⟩,hforbid y hy.1⟩,hσ.2.trans (min_le_left _ _)⟩)
    (fun _ _ => rfl) (fun _ hy => hy.2)
  have hc' : (∫⁻ y in E ∩ B, ENNReal.ofReal (scalarIntegrand j t σ y)) ≤
      ENNReal.ofReal (exp (-b*(n:ℝ))) := by
    have hab : exp (-a*(n:ℝ)) ≤ exp (-b*(n:ℝ)) := exp_le_exp.mpr (by
      have hh := mul_le_mul_of_nonneg_right (min_le_left a 1) (Nat.cast_nonneg (α := ℝ) n)
      dsimp [b]; linarith only [hh])
    simpa only [scalarIntegrand, Fintype.card_fin] using hc.trans (ENNReal.ofReal_le_ofReal hab)
  have htail := hTail n hn' t ht σ hσ' (E ∩ Bᶜ) (hE.inter hB.compl)
    (fun y hy => hs y hy.1) (fun y hy => le_of_lt (not_le.mp hy.2))
  have he : exp (-(1:ℝ)*(n:ℝ)) ≤ exp (-b*(n:ℝ)) := exp_le_exp.mpr (by
    have hh := mul_le_mul_of_nonneg_right (min_le_right a 1) (Nat.cast_nonneg (α := ℝ) n)
    dsimp [b]; linarith only [hh])
  have htotal := (lintegral_split_le volume (fun y => ENNReal.ofReal (scalarIntegrand j t σ y)) E B).trans
    (add_le_add hc' (htail.trans (ENNReal.ofReal_le_ofReal he)))
  have hadd : ENNReal.ofReal (exp (-b*(n:ℝ)))+ENNReal.ofReal (exp (-b*(n:ℝ))) =
      ENNReal.ofReal (2*exp ((n:ℝ)*(-b))) := by
    rw [← ENNReal.ofReal_add (exp_pos _).le (exp_pos _).le]
    congr 1
    ring_nf
  rw [hadd] at htotal
  refine htotal.trans (ENNReal.ofReal_le_ofReal ?_)
  convert hM n (le_trans (le_max_right _ _) hn) (-b) using 1
  congr 1
  ring

lemma scalar_neighborhood_forbidden {j t₀ T : ℝ} {U : Set ScalarPoint}
    (hU : IsOpen U) (hcurve : ∀ t ∈ Icc t₀ T, (scalarCurve j t,(t,0)) ∈ U) :
    IsClosed ({p : ScalarPoint | t₀ ≤ p.2.1} ∩ Uᶜ) ∧
      ∀ p ∈ ({p : ScalarPoint | t₀ ≤ p.2.1} ∩ Uᶜ), p.2.1 ∈ Icc 0 T →
        p.2.2 = 0 → p.1 ≠ scalarCurve j p.2.1 := by
  refine ⟨(isClosed_le continuous_const (by fun_prop)).inter hU.isClosed_compl,?_⟩
  intro p hp ht hz he
  apply hp.2
  have h := hcurve p.2.1 ⟨hp.1,ht.2⟩
  have hp' : p = (scalarCurve j p.2.1,(p.2.1,0)) := by
    apply Prod.ext he
    exact Prod.ext rfl hz
  rwa [hp']

lemma scalar_smalltime_forbidden {j q₀ : ℝ} (hj : 0 < j) (hj1 : j < 1) (hq : 0 < q₀) :
    ∃ T > 0, IsClosed {p : ScalarPoint | q₀ ≤ scalarQMoment p.1} ∧
      (∀ p ∈ {p : ScalarPoint | q₀ ≤ scalarQMoment p.1}, p.2.1 ∈ Icc 0 T →
        p.2.2 = 0 → p.1 ≠ scalarCurve j p.2.1) ∧
      (∀ p ∈ {p : ScalarPoint | q₀ ≤ scalarQMoment p.1}, 0 ≤ p.2.1 →
        j*q₀ ≤ scalarS j p) := by
  let T := q₀*(1-j)/4
  have hT : 0 < T := by dsimp [T]; positivity
  refine ⟨T,hT,isClosed_le continuous_const (continuous_scalarQMoment.comp continuous_fst),?_,?_⟩
  · intro p hp ht _ he
    have hqspec := scalarQ_spec hj hj1 ht.1
    have heq : scalarQMoment p.1 = scalarQ j p.2.1 := by
      rw [he]
      exact hqspec.1.symm
    have hsmall : p.2.1/(1-j) ≤ q₀/4 := by
      apply (div_le_iff₀ (by linarith : 0 < 1-j)).mpr
      dsimp [T] at ht
      linarith only [ht.2]
    change q₀ ≤ scalarQMoment p.1 at hp
    rw [heq] at hp
    have hh := hqspec.2.2.trans hsmall
    change q₀ ≤ scalarQ j p.2.1 at hp
    linarith
  · intro p hp ht
    exact (mul_le_mul_of_nonneg_left hp hj.le).trans (scalar_consistency ht)

end SKGap

namespace SKGap

theorem scalar_rate_ii {j t₀ T : ℝ} (hj : 0 < j) (hj1 : j < 1)
    (ht₀ : 0 < t₀) (hT : t₀ ≤ T) {U : Set ScalarPoint} (hU : IsOpen U)
    (hcurve : ∀ t ∈ Icc t₀ T, (scalarCurve j t,(t,0)) ∈ U) :
    ∃ a > 0, ∃ δ > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ hn : 0 < n,
      ∀ t ∈ Icc t₀ T, ∀ σ ∈ Icc 0 (min δ 1),
      ∀ E : Set (Fin n → ℝ), MeasurableSet E →
      (∀ y ∈ E, @scalarEmpirical (Fin n) _ ⟨⟨0,hn⟩⟩ y t σ ∉ U) →
      (∫⁻ y in E, ENNReal.ofReal (@scalarIntegrand (Fin n) _ ⟨⟨0,hn⟩⟩ j t σ y)) ≤
        ENNReal.ofReal (exp (-a*(n:ℝ))) := by
  obtain ⟨hC,hne⟩ := scalar_neighborhood_forbidden hU hcurve
  obtain ⟨a,ha,δ,hδ,N,hN⟩ := scalar_closed_isolation hj hj1 (ht₀.le.trans hT) ht₀ hC hne
  refine ⟨a,ha,δ,hδ,N,?_⟩
  intro n hn hn' t ht σ hσ E hE hbad
  let : Nonempty (Fin n) := ⟨⟨0,hn'⟩⟩
  apply hN n hn hn' t ⟨ht₀.le.trans ht.1,ht.2⟩ σ hσ E hE
    (fun y hy => ⟨ht.1,hbad y hy⟩)
  intro y _
  unfold scalarS scalarEmpirical
  dsimp only
  have hq := mul_nonneg hj.le (scalarQMoment_bounds (empiricalLaw y)).1
  nlinarith [sq_nonneg σ,ht.1]

theorem scalar_rate_iii {j q₀ : ℝ} (hj : 0 < j) (hj1 : j < 1) (hq₀ : 0 < q₀) :
    ∃ t₀ > 0, ∃ δ > 0, ∃ a > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ hn : 0 < n,
      ∀ t ∈ Icc 0 t₀, ∀ σ ∈ Icc 0 (min δ 1),
      ∀ E : Set (Fin n → ℝ), MeasurableSet E →
      (∀ y ∈ E, q₀ ≤ scalarQMoment (@empiricalLaw (Fin n) _ ⟨⟨0,hn⟩⟩ y)) →
      (∫⁻ y in E, ENNReal.ofReal (@scalarIntegrand (Fin n) _ ⟨⟨0,hn⟩⟩ j t σ y)) ≤
        ENNReal.ofReal (exp (-a*(n:ℝ))) := by
  obtain ⟨T,hT,hC,hne,hfloor⟩ := scalar_smalltime_forbidden hj hj1 hq₀
  obtain ⟨a,ha,δ,hδ,N,hN⟩ := scalar_closed_isolation hj hj1 hT.le (mul_pos hj hq₀) hC hne
  refine ⟨T,hT,δ,hδ,a,ha,N,?_⟩
  intro n hn hn' t ht σ hσ E hE hbad
  let : Nonempty (Fin n) := ⟨⟨0,hn'⟩⟩
  exact hN n hn hn' t ht σ hσ E hE hbad (fun y hy => hfloor (scalarEmpirical y t σ) (hbad y hy) ht.1)

end SKGap

noncomputable section
open MeasureTheory ProbabilityTheory Real Filter Set
open scoped Topology NNReal ENNReal BoundedContinuousFunction

end
end
end
end
end
end
end
end
end

end OAI
