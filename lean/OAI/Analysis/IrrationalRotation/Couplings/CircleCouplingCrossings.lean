import OAI.Analysis.IrrationalRotation.Couplings.CircleCouplingConditioning
import OAI.Analysis.IrrationalRotation.Sampling.CircleCharacterDynamics

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
namespace Invariant233.CircleCoupling
open CircleDigitCoupling CircleParameterData OneCoordinateCoupling
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

lemma coordinate_point_eq_tail (hr : ∀ i, 0 < MixedRadix.radices p.q i)
    (side : Bool) (ω : Sample) (hnt : MixedRadix.Nonterminal (digits p hr side ω)) (i : ℕ) :
    p.coordinate i (point p hr side ω) = MixedRadix.tailValue (digits p hr side ω) i := by
  unfold coordinate point MixedRadix.circleValue
  rw [← AddCircle.coe_nsmul, nsmul_eq_mul]
  change CircleParameterData.rep (((p.q i : ℝ) * MixedRadix.ofDigits (digits p hr side ω) : ℝ) : Circle) = _
  rw [show CircleParameterData.rep = (fun x : Circle => (AddCircle.equivIco (1 : ℝ) 0 x : ℝ)) from rfl,
    CircleCharacterDynamics.representative_coe]
  exact MixedRadix.coordinate_eq_tailValue hp.frequency_zero hp.q_pos
    hp.frequency_increasing hp.frequency_divisible _ hnt i

lemma coordinate_point_mem_bin (hr : ∀ i, 0 < MixedRadix.radices p.q i)
    (side : Bool) (ω : Sample) (hnt : MixedRadix.Nonterminal (digits p hr side ω)) (i : ℕ) :
    p.coordinate i (point p hr side ω) ∈ bin (MixedRadix.radices p.q i) (digits p hr side ω i) := by
  rw [coordinate_point_eq_tail hp hr side ω hnt i]
  have h0 := (MixedRadix.tailValue_mem_bin hr (digits p hr side ω) i).1
  refine ⟨h0, ?_⟩
  change MixedRadix.tailValue (digits p hr side ω) i < _
  rw [MixedRadix.tailValue_rec hr]
  apply div_lt_div_of_pos_right _ (by exact_mod_cast hr i)
  linarith [MixedRadix.tailValue_lt_one hr (digits p hr side ω) hnt (i + 1)]

lemma ae_top_posterior_lower (j : ℕ) (hr : ∀ i, 0 < MixedRadix.radices p.q i)
    {s i : ℕ} (hs : 1 ≤ s) (hi : i ∈ p.block s) (which : Bool) :
    ∀ᵐ ω ∂law p j, ∀ u : ℝ,
      p.coordinate i (point p hr false ω) < u → u ≤ 1 - width (p.a s) (p.b s) which →
      ENNReal.ofReal (CouplingMarginalBounds.rho (kappa s) (p.m s) (width (p.a s) (p.b s) which)) / 10 ≤
        posterior p j false i
          (MixedRadix.circleCanonical (MixedRadix.radices p.q) hr (point p hr false ω) i)
          {topLabel which} := by
  have hi0 : i ≠ 0 := by have := (p.mem_block_iff s i).mp hi; omega
  have hidx := p.blockIndex_eq_of_mem hp.m_pos hi
  have hm : (100 : ℝ) ≤ p.m s := by exact_mod_cast (show 100 ≤ p.m s by have := hp.m_ge_200 s hs; omega)
  have ha := hp.coupling_a_bounds s hs
  have hb := hp.coupling_b_bounds s hs
  have hκ := CircleParameterLaws.coupling_kappa_bounds s hs
  have hw : 1 / (p.m s : ℝ) ≤ width (p.a s) (p.b s) which := by
    cases which
    · exact ha.1
    · exact hb.1
  let : NeZero (MixedRadix.radices p.q i) := ⟨Nat.ne_of_gt (hr i)⟩
  filter_upwards [ae_nonterminal_digits hp j hr false, ae_recover_digits hp j hr false] with ω hnt hrec
  intro u hxu hu
  rw [hrec, posterior, ite_eq_right hi0, hidx]
  exact top_posterior_lower hκ.1 hκ.2 hm ha.1 ha.2 hb.1 hb.2
    (tag_bounds j s).1 (tag_bounds j s).2 _ _ which
    (coordinate_point_mem_bin hp hr false ω hnt i) hxu hu (hp.coupling_bin_small hs hi hw)

lemma ae_bottom_posterior_lower (j : ℕ) (hr : ∀ i, 0 < MixedRadix.radices p.q i)
    {s i : ℕ} (hs : 1 ≤ s) (hi : i ∈ p.block s) (which : Bool) :
    ∀ᵐ ω ∂law p j, ∀ u : ℝ,
      u ≤ p.coordinate i (point p hr true ω) → width (p.a s) (p.b s) which ≤ u →
      ENNReal.ofReal (CouplingMarginalBounds.rho (kappa s) (p.m s) (width (p.a s) (p.b s) which)) / 10 ≤
        posterior p j true i
          (MixedRadix.circleCanonical (MixedRadix.radices p.q) hr (point p hr true ω) i)
          {bottomLabel which} := by
  have hi0 : i ≠ 0 := by have := (p.mem_block_iff s i).mp hi; omega
  have hidx := p.blockIndex_eq_of_mem hp.m_pos hi
  have hm : (100 : ℝ) ≤ p.m s := by exact_mod_cast (show 100 ≤ p.m s by have := hp.m_ge_200 s hs; omega)
  have ha := hp.coupling_a_bounds s hs
  have hb := hp.coupling_b_bounds s hs
  have hκ := CircleParameterLaws.coupling_kappa_bounds s hs
  have hw : 1 / (p.m s : ℝ) ≤ width (p.a s) (p.b s) which := by
    cases which
    · exact ha.1
    · exact hb.1
  let : NeZero (MixedRadix.radices p.q i) := ⟨Nat.ne_of_gt (hr i)⟩
  filter_upwards [ae_nonterminal_digits hp j hr true, ae_recover_digits hp j hr true] with ω hnt hrec
  intro u huy hu
  rw [hrec, posterior, ite_eq_right hi0, hidx]
  exact bottom_posterior_lower hκ.1 hκ.2 hm ha.1 ha.2 hb.1 hb.2
    (tag_bounds j s).1 (tag_bounds j s).2 _ _ which
    (coordinate_point_mem_bin hp hr true ω hnt i) huy hu (hp.coupling_bin_small hs hi hw)

end Invariant233.CircleCoupling

end

end OAI
