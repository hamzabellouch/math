import Mathlib
import OAI.Probability.SKGap.Localization.ScalarEmpirical
import OAI.Probability.SKGap.Gaussian.SquareTail

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
noncomputable section
open MeasureTheory ProbabilityTheory Real Filter Set
open scoped Topology NNReal ENNReal BoundedContinuousFunction
namespace SKGap

theorem gaussian_compact_tail_rate {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) {P : X → ProbabilityMeasure ℝ} {d s ψ : X → ℝ}
    (hP : ContinuousOn P K) (hd : ContinuousOn d K) (hs : ContinuousOn s K)
    (hψ : ContinuousOn ψ K) (hpos : ∀ x ∈ K, 0 < s x) (R : ℝ)
    {α ν : ℝ} (hα : 0 < α) (hν : 0 < ν)
    (hαs : ∀ x ∈ K, α < 1/(4*s x))
    (hW : ∀ ε > 0, ∀ x ∈ K, ∃ f : ℝ →ᵇ ℝ, ψ x-(∫ y, f y ∂P x)+
      log (∫ y, exp (f y) ∂gaussianReal (d x) (s x).toNNReal) < ε) :
    ∃ R₁ : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∀ hn : 0 < n, ∀ z : (Fin n → ℝ) → X,
      ∀ E : Set (Fin n → ℝ), MeasurableSet E →
      (∀ y ∈ E, z y ∈ K) →
      (∀ y ∈ E, P (z y) = @empiricalLaw (Fin n) _ ⟨⟨0,hn⟩⟩ y) →
      (∀ y ∈ E, ∑ i, (y i)^2 ≤ (n:ℝ)*R) →
      (∀ y ∈ E, (n:ℝ)*ν ≤ ∑ i, squareTail R₁ (y i)) →
      (∫⁻ y in E, ENNReal.ofReal (exp ((n:ℝ)*ψ (z y))*productNormal (d (z y)) (s (z y)) y)) ≤
        ENNReal.ofReal (exp (-(α*ν/2)*(n:ℝ))) := by
  classical
  have hav : 0 < α*ν := mul_pos hα hν
  obtain ⟨C,f,hC⟩ := finite_gaussian_test_cover hK hP hd hs hψ hpos R (α*ν/8)
    (hW _ (by positivity))
  have hinc (x : K) : ∀ᶠ r : ℝ in atTop,
      log (∫ y, exp (f x y+α*squareTail r y) ∂gaussianReal (d x) (s x).toNNReal) ≤
        log (∫ y, exp (f x y) ∂gaussianReal (d x) (s x).toNNReal)+α*ν/8 := by
    have hp : (0:ℝ≥0) < (s x).toNNReal := Real.toNNReal_pos.mpr (hpos x x.2)
    have ha : α < 1/(4*((s x).toNNReal:ℝ)) := by
      simpa only [Real.coe_toNNReal _ (hpos x x.2).le] using hαs x x.2
    have h := (tendsto_gaussian_tail_tilt (f x) (d := d x) hp hα.le ha).log
      (tiltedNormal_mass_pos (f x) (d x) (s x).toNNReal).ne'
    exact (h.eventually_lt_const (by linarith :
      log (∫ y, exp (f x y) ∂gaussianReal (d x) (s x).toNNReal) <
      log (∫ y, exp (f x y) ∂gaussianReal (d x) (s x).toNNReal)+α*ν/8)).mono
        (fun _ hr => hr.le)
  have hall : ∀ᶠ r : ℝ in atTop, ∀ x ∈ C,
      log (∫ y, exp (f x y+α*squareTail r y) ∂gaussianReal (d x) (s x).toNNReal) ≤
        log (∫ y, exp (f x y) ∂gaussianReal (d x) (s x).toNNReal)+α*ν/8 :=
    (eventually_all_finset C).mpr (fun x _ => hinc x)
  obtain ⟨R₁,hR₁⟩ := hall.exists
  obtain ⟨N,hN⟩ := absorb_finite_exponential_factor C.card (show 0 < α*ν/4 by positivity)
  refine ⟨R₁,N,?_⟩
  intro n hn hn' z E hE hz hemp hmom htail
  let : Nonempty (Fin n) := ⟨⟨0,hn'⟩⟩
  have hh := gaussian_covered_tail_laplace C f (fun x : K => d x) (fun x : K => s x)
    (fun x _ => hpos x x.2) (fun y => d (z y)) (fun y => s (z y)) (fun y => ψ (z y))
    R (α*ν/8) (α*ν/8) α ν R₁ hα.le hE (fun y hy => hpos (z y) (hz y hy))
    (by simpa only [Fintype.card_fin] using hmom) (by simpa only [Fintype.card_fin] using htail)
    (fun x _ => integrable_gaussian_tail_test (f x) (Real.toNNReal_pos.mpr (hpos x x.2)) hα.le
      (by simpa only [Real.coe_toNNReal _ (hpos x x.2).le] using hαs x x.2) R₁)
    hR₁ (fun y hy => by
      obtain ⟨x,hx,hcx⟩ := hC (z y) (hz y hy)
      rw [hemp y hy] at hcx
      exact ⟨x,hx,hcx⟩)
  simp only [Fintype.card_fin] at hh
  refine hh.trans (ENNReal.ofReal_le_ofReal ?_)
  convert hN n hn (α*ν/8+α*ν/8-α*ν) using 1
  congr 1
  ring

end SKGap

namespace SKGap
lemma squareTail_antitone {R₁ R₂ : ℝ} (hR : R₁ ≤ R₂) (y : ℝ) :
    squareTail R₂ y ≤ squareTail R₁ y := by
  unfold squareTail
  split_ifs <;> try positivity
  · exact le_rfl
  · exact (not_lt_of_ge hR (lt_of_lt_of_le (by assumption) (le_of_not_gt (by assumption)))).elim

theorem scalar_rate_iv {j t₀ T ν : ℝ} (hj : 0 < j) (hj1 : j < 1)
    (ht₀ : 0 < t₀) (hT : t₀ ≤ T) (hν : 0 < ν) :
    ∃ R₁ : ℝ, ∃ a > 0, ∃ N : ℕ, ∀ R₂ ≥ R₁, ∀ n ≥ N, ∀ hn : 0 < n,
      ∀ t ∈ Icc t₀ T, ∀ σ ∈ Icc 0 1,
      ∀ E : Set (Fin n → ℝ), MeasurableSet E →
      (∀ y ∈ E, (n:ℝ)*ν ≤ ∑ i, squareTail R₂ (y i)) →
      (∫⁻ y in E, ENNReal.ofReal (@scalarIntegrand (Fin n) _ ⟨⟨0,hn⟩⟩ j t σ y)) ≤
        ENNReal.ofReal (exp (-a*(n:ℝ))) := by
  have hT0 : 0 ≤ T := ht₀.le.trans hT
  obtain ⟨R,hR,hTail⟩ := scalar_uniform_tail hj.le hT0 ht₀ 1
  let K := scalarBox j R T t₀
  let α := 1/(8*(T+1+j))
  have hα : 0 < α := by dsimp [α]; positivity
  have hs (p : ScalarPoint) (hp : p ∈ K) : 0 < scalarS j p := ht₀.trans_le hp.2
  have hmom : K ⊆ scalarMomentDomain R := fun _ hp => ⟨hp.1.1,mem_univ _⟩
  have hαs (p : ScalarPoint) (hp : p ∈ K) : α < 1/(4*scalarS j p) := by
    have hq := (scalarQMoment_bounds p.1).2
    have hz := hp.1.2.2
    have ht := hp.1.2.1
    have hsup : scalarS j p ≤ T+1+j := by
      unfold scalarS
      have hmul := mul_le_mul_of_nonneg_left hq hj.le
      nlinarith [sq_nonneg p.2.2,hz.1,hz.2,ht.2]
    have hsp := hs p hp
    dsimp [α]
    apply one_div_lt_one_div_of_lt (by positivity : 0 < 4*scalarS j p)
    nlinarith [hs p hp]
  obtain ⟨R₁,N,hN⟩ := gaussian_compact_tail_rate (isCompact_scalarBox j R T t₀)
    (P := fun p : ScalarPoint => p.1) continuous_fst.continuousOn
    (continuous_scalarD j).continuousOn (continuous_scalarS j).continuousOn
    (continuousOn_scalarPsi_of_pos hj.le hR.le hmom hs) hs R hα hν hαs
    (fun ε hε p hp => scalar_weak_test (hmom hp) hj hj1 hp.1.2.1.1 (hs p hp) hε)
  let b := min (α*ν/2) 1
  have hb : 0 < b := lt_min (by positivity) zero_lt_one
  obtain ⟨M,hM⟩ := absorb_finite_exponential_factor 2 (half_pos hb)
  refine ⟨R₁,b/2,half_pos hb,max N M,?_⟩
  intro R₂ hR₂ n hn hn' t ht σ hσ E hE htail
  let : Nonempty (Fin n) := ⟨⟨0,hn'⟩⟩
  have hsE (y : Fin n → ℝ) : t₀ ≤ scalarS j (scalarEmpirical y t σ) := by
    unfold scalarS scalarEmpirical
    dsimp only
    have hq := mul_nonneg hj.le (scalarQMoment_bounds (empiricalLaw y)).1
    nlinarith [sq_nonneg σ,ht.1]
  let B : Set (Fin n → ℝ) := {y | ∑ i, (y i)^2 ≤ (n:ℝ)*R}
  have hB : MeasurableSet B := isClosed_le (by fun_prop) continuous_const |>.measurableSet
  have hc := hN n (le_trans (le_max_left _ _) hn) hn' (fun y => scalarEmpirical y t σ)
    (E ∩ B) (hE.inter hB) (fun y hy => ⟨⟨empirical_momentBall y hR.le
      (by simpa only [Fintype.card_fin] using (show ∑ i, (y i)^2 ≤ (n:ℝ)*R from hy.2)),
        ⟨ht₀.le.trans ht.1,ht.2⟩,hσ⟩,hsE y⟩) (fun _ _ => rfl) (fun _ hy => hy.2)
    (fun y hy => (htail y hy.1).trans (Finset.sum_le_sum (fun i _ => squareTail_antitone hR₂ (y i))))
  have hc' : (∫⁻ y in E ∩ B, ENNReal.ofReal (scalarIntegrand j t σ y)) ≤
      ENNReal.ofReal (exp (-b*(n:ℝ))) := by
    have hab : exp (-(α*ν/2)*(n:ℝ)) ≤ exp (-b*(n:ℝ)) := exp_le_exp.mpr (by
      have hh := mul_le_mul_of_nonneg_right (min_le_left (α*ν/2) 1) (Nat.cast_nonneg (α := ℝ) n)
      dsimp [b]; linarith only [hh])
    simpa only [scalarIntegrand,Fintype.card_fin] using hc.trans (ENNReal.ofReal_le_ofReal hab)
  have htail' := hTail n hn' t ⟨ht₀.le.trans ht.1,ht.2⟩ σ hσ (E ∩ Bᶜ) (hE.inter hB.compl)
    (fun y _ => hsE y) (fun _ hy => le_of_lt (not_le.mp hy.2))
  have he : exp (-(1:ℝ)*(n:ℝ)) ≤ exp (-b*(n:ℝ)) := exp_le_exp.mpr (by
    have hh := mul_le_mul_of_nonneg_right (min_le_right (α*ν/2) 1) (Nat.cast_nonneg (α := ℝ) n)
    dsimp [b]; linarith only [hh])
  have htotal := (lintegral_split_le volume (fun y => ENNReal.ofReal (scalarIntegrand j t σ y)) E B).trans
    (add_le_add hc' (htail'.trans (ENNReal.ofReal_le_ofReal he)))
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

end SKGap
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
