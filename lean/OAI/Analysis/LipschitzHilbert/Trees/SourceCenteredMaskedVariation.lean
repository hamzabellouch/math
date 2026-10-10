import OAI.Analysis.LipschitzHilbert.Trees.SourceMaskedVariationTail
import OAI.Analysis.LipschitzHilbert.Trees.SourceCenteredCoefficient
import OAI.Analysis.LipschitzHilbert.Trees.SourceBadEventUnion
import OAI.Analysis.LipschitzHilbert.Estimates.VariationDifference

namespace OAI

/-! Symmetric frozen coefficients in the actual masked synthesis.
The exact three-cutoff identity gives a fixed three-event loss, with no
assumption about the measure of selector boundary sets. -/

noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators Topology ENNReal FourierTransform ComplexConjugate
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]
variable (P : SourceLatticePacket N κ ι)
  (c : ∀ j, ι j → κ → ℂ)
  (alt : ∀ j, ι j → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j u k, planarProfileConstant (alt j u k) (2*P.order) ≤ P.profileBound)
  (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
  (T : ∀ j, ι j → SlopeBox) (L A t y : ℝ)

def physicalCenteredMaskedBand (j : Fin N) (x : ℝ) : EuclideanSpace ℂ κ :=
  WithLp.toLp 2 (fun k => ∑ u : ι j,
    (conj (c j u k)*P.physicalCenteredCoefficient t t d v g j u k)*
      ((T j u).mask L A (x,y+t*x):ℂ)*
      (P.withProfile alt hAlt).physicalPacket t j u k (x,y+t*x))

def physicalCenteredMaskedVariation (x : ℝ) : ℝ :=
  cubicVariation (packetPartialSum
    (fun j => P.physicalCenteredMaskedBand c alt hAlt d v g T L A t y j x)) N

theorem physicalCenteredMaskedBand_continuous (j : Fin N) :
    Continuous (P.physicalCenteredMaskedBand c alt hAlt d v g T L A t y j) := by
  apply (PiLp.continuous_toLp 2 (fun _ : κ => ℂ)).comp
  apply continuous_pi
  intro k
  apply continuous_finsetSum
  intro u _
  have hline : Continuous (fun x : ℝ => (x,y+t*x)) := by fun_prop
  exact (continuous_const.mul (Complex.continuous_ofReal.comp
    (((T j u).mask_continuous L A).comp hline))).mul
      (((P.withProfile alt hAlt).physicalPacket t j u k).continuous.comp hline)

theorem physicalCenteredMaskedVariation_continuous :
    Continuous (P.physicalCenteredMaskedVariation c alt hAlt d v g T L A t y) := by
  apply continuous_cubicVariation _ _ N
  intro n
  apply continuous_finsetSum
  intro j _
  by_cases hj : j.val < n
  · simpa only [ite_eq_left hj] using
      P.physicalCenteredMaskedBand_continuous c alt hAlt d v g T L A t y j
  · simp only [ite_eq_right hj]
    exact continuous_const

theorem physicalCenteredMaskedBand_eq (hd : ∀ j, 0 ≤ d j)
    (hv : Measurable v) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (j : Fin N) (x : ℝ) :
    P.physicalCenteredMaskedBand c alt hAlt d v g T L A t y j x =
      P.physicalMaskedBand c alt hAlt (fun j => t+d j) v g T L A t y j x+
      P.physicalMaskedBand c alt hAlt (fun j => d j-t) (fun z => -v z) g T L A t y j x-
      P.physicalMaskedBand c alt hAlt (fun _ => 0) (fun _ => 0) g T L A t y j x := by
  ext k
  simp only [physicalCenteredMaskedBand,physicalMaskedBand,WithLp.ofLp_toLp,
    PiLp.add_apply,PiLp.sub_apply]
  rw [← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro u _
  rw [P.physicalCenteredCoefficient_eq t t d hd v hv g hg hg1]
  simp only [PiLp.add_apply,PiLp.sub_apply]
  ring

private theorem partial_add_sub {E : Type*} [AddCommGroup E]
    (F G H : Fin N → E) (n : ℕ) :
    packetPartialSum (fun j => F j+G j-H j) n =
      packetPartialSum F n+packetPartialSum G n-packetPartialSum H n := by
  unfold packetPartialSum
  rw [← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

theorem physicalCenteredMaskedPartial_eq (hd : ∀ j, 0 ≤ d j)
    (hv : Measurable v) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1) (x : ℝ) (n : ℕ) :
    packetPartialSum (fun j => P.physicalCenteredMaskedBand c alt hAlt d v g T L A t y j x) n =
      packetPartialSum (fun j => P.physicalMaskedBand c alt hAlt (fun j => t+d j) v g T L A t y j x) n+
      packetPartialSum (fun j => P.physicalMaskedBand c alt hAlt (fun j => d j-t) (fun z => -v z) g T L A t y j x) n-
      packetPartialSum (fun j => P.physicalMaskedBand c alt hAlt (fun _ => 0) (fun _ => 0) g T L A t y j x) n := by
  have hband : (fun j => P.physicalCenteredMaskedBand c alt hAlt d v g T L A t y j x) =
      fun j => P.physicalMaskedBand c alt hAlt (fun j => t+d j) v g T L A t y j x+
        P.physicalMaskedBand c alt hAlt (fun j => d j-t) (fun z => -v z) g T L A t y j x-
        P.physicalMaskedBand c alt hAlt (fun _ => 0) (fun _ => 0) g T L A t y j x := by
    funext j
    exact P.physicalCenteredMaskedBand_eq c alt hAlt d v g T L A t y hd hv hg hg1 j x
  rw [hband]
  exact partial_add_sub _ _ _ n

private theorem cubic_variation_add_sub_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (F G H : ℕ → E) (n : ℕ) :
    cubicVariation (fun k => F k+G k-H k) n ≤
      cubicVariation F n+cubicVariation G n+cubicVariation H n := by
  have heq : (fun k => F k+G k-H k) = fun k => (F k+G k)+(-H k) := by
    funext k
    exact sub_eq_add_neg _ _
  rw [heq]
  apply (cubicVariation_add_le (fun k => F k+G k) (fun k => -H k) n).trans
  rw [cubicVariation_neg]
  exact add_le_add (cubicVariation_add_le F G n) le_rfl

theorem physicalCenteredMaskedVariation_le (hd : ∀ j, 0 ≤ d j)
    (hv : Measurable v) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1) (x : ℝ) :
    P.physicalCenteredMaskedVariation c alt hAlt d v g T L A t y x ≤
      P.physicalMaskedVariation c alt hAlt (fun j => t+d j) v g T L A t y x+
      P.physicalMaskedVariation c alt hAlt (fun j => d j-t) (fun z => -v z) g T L A t y x+
      P.physicalMaskedVariation c alt hAlt (fun _ => 0) (fun _ => 0) g T L A t y x := by
  have heq := funext (P.physicalCenteredMaskedPartial_eq c alt hAlt d v g T L A t y hd hv hg hg1 x)
  unfold physicalCenteredMaskedVariation
  rw [heq]
  exact cubic_variation_add_sub_le _ _ _ N

/-- The fixed three-cutoff loss costs one extra polynomial power and
one unit in the exponential rate. -/
theorem physical_centered_masked_variation_tail (hVariation : LepingleInput)
    {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 ≤ hi)
    (q J A cone : ℝ) (hq : 0 ≤ q) (hJ : 0 ≤ J) (hA : 1 < A) (hcone : 0 ≤ cone) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : SourceLatticePacket N κ ι),
      P.constant ≤ L^q →
    ∀ (c : ∀ j, ι j → κ → ℂ) (hc : ∀ j u k, ‖c j u k‖ ≤ 1)
      (alt : ∀ j, ι j → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j u k, planarProfileConstant (alt j u k) (2*P.order) ≤ P.profileBound)
      (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ) (_hv : Measurable v)
      (g : ℝ×ℝ → EuclideanSpace ℂ κ) (_hg : Measurable g) (_hg1 : ∀ z, ‖g z‖ ≤ 1),
      (∀ j, 0 ≤ d j) → Monotone d →
      (∀ j u k y xi, |xi| < (lo/P.topLength)*(2:ℝ)^j.val →
        𝓕 ((P.frozenProfile c hc).raw 0 j u k y) xi = 0) →
      (∀ j u k y xi, (hi/P.topLength)*(2:ℝ)^j.val < |xi| →
        𝓕 ((P.frozenProfile c hc).raw 0 j u k y) xi = 0) →
      (∀ j u k y xi, |xi| < (lo/P.topLength)*(2:ℝ)^j.val →
        𝓕 ((P.withProfile alt hAlt).raw 0 j u k y) xi = 0) →
      (∀ j u k y xi, (hi/P.topLength)*(2:ℝ)^j.val < |xi| →
        𝓕 ((P.withProfile alt hAlt).raw 0 j u k y) xi = 0) →
    ∀ (T : ∀ j, ι j → SlopeBox) (t : ℝ),
      (∀ j u, P.length j ≤ (T j u).length) →
      (∀ j u, |t-(T j u).slope| ≤ cone*(T j u).width/P.length j) →
    ∀ (y u H : ℝ), 0 < H → (∀ j (_i : ι j), P.length j ≤ H) →
      Measurable (P.physicalCenteredMaskedVariation c alt hAlt d v g T L A t y) ∧
      (volume.restrict (Ico u (u+H)))
        {x | L^(2*q+7) ≤ |P.physicalCenteredMaskedVariation c alt hAlt d v g T L A t y x|} ≤
          ENNReal.ofReal (Real.exp (-J*L))*ENNReal.ofReal H := by
  filter_upwards [physical_masked_variation_tail hVariation hlo hhi q (J+1) A cone hq
    (by linarith) hA hcone,eventually_source_polynomial_exp 3 0 J (by norm_num),
    eventually_ge_atTop (4:ℝ)] with L htail hdecay hL4
  have hL : 0 < L := by linarith
  simp only [Real.rpow_zero,mul_one] at hdecay
  intro N κ ι _ _ P hP c hc alt hAlt d v hv g hg hg1 hd hmono hAlow hAhigh hSlow hShigh
    T t hshort hcone' y u H hH hwidth
  have hargs := htail N κ ι P hP c hc alt hAlt
  obtain ⟨_hU,hU⟩ := hargs (fun j => t+d j) v hv g hg hg1 (centered_upper_monotone t hmono)
    hAlow hAhigh hSlow hShigh T t hshort hcone' y u H hH hwidth
  obtain ⟨_hD,hD⟩ := hargs (fun j => d j-t) (fun z => -v z) hv.neg g hg hg1
    (centered_lower_monotone t hmono) hAlow hAhigh hSlow hShigh T t hshort hcone' y u H hH hwidth
  obtain ⟨_hT,hT⟩ := hargs (fun _ => 0) (fun _ => 0) measurable_const g hg hg1
    (fun _ _ _ => le_rfl) hAlow hAhigh hSlow hShigh T t hshort hcone' y u H hH hwidth
  let U := {x | L^(2*q+6) ≤ |P.physicalMaskedVariation c alt hAlt (fun j => t+d j) v g T L A t y x|}
  let D := {x | L^(2*q+6) ≤ |P.physicalMaskedVariation c alt hAlt (fun j => d j-t) (fun z => -v z) g T L A t y x|}
  let S := {x | L^(2*q+6) ≤ |P.physicalMaskedVariation c alt hAlt (fun _ => 0) (fun _ => 0) g T L A t y x|}
  have hthreshold : 3*L^(2*q+6) ≤ L^(2*q+7) := by
    calc
      _ ≤ L*L^(2*q+6) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by
        calc
          _ = L^(1:ℝ)*L^(2*q+6) := by rw [Real.rpow_one]
          _ = L^(1+(2*q+6)) := (Real.rpow_add hL _ _).symm
          _ = _ := by congr 1; ring
  have hsub : {x | L^(2*q+7) ≤ |P.physicalCenteredMaskedVariation c alt hAlt d v g T L A t y x|} ⊆ U∪D∪S := by
    intro x hx
    by_contra hn
    have hnU : ¬x ∈ U := fun h => hn (Or.inl (Or.inl h))
    have hnD : ¬x ∈ D := fun h => hn (Or.inl (Or.inr h))
    have hnS : ¬x ∈ S := fun h => hn (Or.inr h)
    have hu : P.physicalMaskedVariation c alt hAlt (fun j => t+d j) v g T L A t y x < L^(2*q+6) :=
      (le_abs_self _).trans_lt (lt_of_not_ge hnU)
    have hv' : P.physicalMaskedVariation c alt hAlt (fun j => d j-t) (fun z => -v z) g T L A t y x < L^(2*q+6) :=
      (le_abs_self _).trans_lt (lt_of_not_ge hnD)
    have hs : P.physicalMaskedVariation c alt hAlt (fun _ => 0) (fun _ => 0) g T L A t y x < L^(2*q+6) :=
      (le_abs_self _).trans_lt (lt_of_not_ge hnS)
    have hc0 := cubicVariation_nonneg
      (packetPartialSum (fun j => P.physicalCenteredMaskedBand c alt hAlt d v g T L A t y j x)) N
    change L^(2*q+7) ≤ |P.physicalCenteredMaskedVariation c alt hAlt d v g T L A t y x| at hx
    change 0 ≤ P.physicalCenteredMaskedVariation c alt hAlt d v g T L A t y x at hc0
    rw [abs_of_nonneg hc0] at hx
    have hb := P.physicalCenteredMaskedVariation_le c alt hAlt d v g T L A t y hd hv hg hg1 x
    linarith
  let mu := volume.restrict (Ico u (u+H))
  have hunion := (measure_union_le (μ := mu) (U∪D) S).trans
    (add_le_add (measure_union_le U D) le_rfl)
  have hsum := add_le_add (add_le_add hU hD) hT
  refine ⟨(P.physicalCenteredMaskedVariation_continuous c alt hAlt d v g T L A t y).measurable,?_⟩
  apply (measure_mono hsub).trans (hunion.trans (hsum.trans ?_))
  calc
    _ = ENNReal.ofReal (3*Real.exp (-(J+1)*L))*ENNReal.ofReal H := by
      rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3)]
      norm_num only [ENNReal.ofReal_ofNat]
      ring
    _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal hdecay) le_rfl

end LipschitzHilbert.SourceLatticePacket

end

end OAI
