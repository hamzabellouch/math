import OAI.Analysis.LipschitzHilbert.Estimates.SelectedCoefficientDerivative
import OAI.Analysis.LipschitzHilbert.Estimates.TopPolynomialDecay
import OAI.Analysis.LipschitzHilbert.Trees.SourceLatticeRawData
import OAI.Analysis.LipschitzHilbert.Trees.SourceLatticePolarization
import OAI.Analysis.LipschitzHilbert.Estimates.SelectedTopInterval

namespace OAI

/-! The unconditional horizontal derivative estimate for actual cross-profile
top sums. The lower length cutoff gives the reciprocal scale factor. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

def crossSelectedTopSum (P : SourceLatticePacket N κ ι)
    (alt : ∀ j, ι j → κ → SchwartzMap (ℝ × ℝ) ℂ)
    (hAlt : ∀ j u k, planarProfileConstant (alt j u k) (2 * P.order) ≤ P.profileBound) (s : Finset (Fin N))
    (cutoff : Fin N → ℝ) (v : ℝ × ℝ → ℝ) (g : ℝ × ℝ → EuclideanSpace ℂ κ)
    (x y : ℝ) : EuclideanSpace ℂ κ :=
  ∑ j ∈ s, vectorPacketSynthesis (P.family.mainCoefficient cutoff v g j)
    (fun u k => (P.withProfile alt hAlt).raw 0 j u k y) x

def crossDerivativeConstant (P : SourceLatticePacket N κ ι) (D : ℕ) : ℝ :=
  (P.constant*Real.pi^2)*(4*((16^(8*D+1)*(16^(8*D+1)*P.constant))*(4*Real.pi)^2))

theorem crossSelectedTopSum_horizontal_bound (P : SourceLatticePacket N κ ι)
    (alt : ∀ j, ι j → κ → SchwartzMap (ℝ × ℝ) ℂ)
    (hAlt : ∀ j u k, planarProfileConstant (alt j u k) (2 * P.order) ≤ P.profileBound)
    {K : ℝ} {D : ℕ} (T : SlopeBox) (hK : 0 < K)
    (G : SourceLatticeTopGeometry P T K D)
    (cutoff : Fin N → ℝ) (v : ℝ × ℝ → ℝ) (hv : Measurable v)
    (g : ℝ × ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (s : Finset (Fin N)) (r : ℝ) (hr : 0 < r) (hs : ∀ j ∈ s, r ≤ P.length j)
    (z : ℝ × ℝ) :
    ‖deriv (fun x => P.crossSelectedTopSum alt hAlt s cutoff v g x (z.2-T.slope*z.1)) z.1‖ ≤
      (P.crossDerivativeConstant D/r)*(T.weight K (D:ℝ) z)^8 := by
  let y := z.2-T.slope*z.1
  let w := polynomialWeight T.x (K*T.length) (8*D+1) z.1 *
    polynomialWeight (T.y-T.slope*T.x) (K*T.width) (8*D+1) y
  have hw : 0 < w := mul_pos
    (zero_lt_one.trans_le (polynomialWeight_one_le _ _ _ _))
    (zero_lt_one.trans_le (polynomialWeight_one_le _ _ _ _))
  have hderiv (j : Fin N) (u : ι j) (k : κ) :
      ‖deriv ((P.withProfile alt hAlt).raw 0 j u k y) z.1‖ ≤ (P.constant/P.length j)*
        (lineEnvelope (P.family.centerX j u) (P.length j) (3+2*(8*D+1)) z.1 *
          lineEnvelope (P.family.centerZ j u) P.width (2+2*(8*D+1)) y) := by
    exact (P.withProfile alt hAlt).raw_top_derivative_bound D G.order_le 0 j u k y z.1
  have hb := top_weighted_selected_derivative_bounded
    (P.family.mainCoefficient cutoff v g) (fun j u k => (P.withProfile alt hAlt).raw 0 j u k y) P.family.site P.family.site_injective
    P.family.baseX P.family.baseZ P.topLength P.width T.x (T.y-T.slope*T.x)
    (K*T.length) (K*T.width) z.1 y P.constant (P.constant*Real.pi^2) r (8*D+1)
    P.topLength_pos P.width_pos (mul_pos hK T.length_pos) (mul_pos hK T.width_pos)
    G.length_le G.width_le P.constant_pos.le (mul_pos P.constant_pos (sq_pos_of_pos Real.pi_pos)) hr
    (P.family.mainCoefficient_norm cutoff v hv g hg hg1)
    (fun j u => P.family_centerX_local j u T.x (K * T.length) (G.centerX_le j u))
    (fun j u => P.family_centerZ_local j u (T.y - T.slope * T.x) (K * T.width) (G.centerZ_le j u)) s hs hderiv
  change w*‖deriv (fun x => P.crossSelectedTopSum alt hAlt s cutoff v g x y) z.1‖ ≤ _ at hb
  have hbudget : w*‖deriv (fun x => P.crossSelectedTopSum alt hAlt s cutoff v g x y) z.1‖ ≤
      P.crossDerivativeConstant D/r := by
    convert hb using 1
    unfold crossDerivativeConstant
    ring
  have hinv : w⁻¹ ≤ (T.weight K (D:ℝ) z)^8 := T.inverse_polynomial_le_weight K hK D z
  calc
    _ = w⁻¹*(w*‖deriv (fun x => P.crossSelectedTopSum alt hAlt s cutoff v g x y) z.1‖) := by
      rw [← mul_assoc,inv_mul_cancel₀ hw.ne',one_mul]
    _ ≤ w⁻¹*(P.crossDerivativeConstant D/r) :=
      mul_le_mul_of_nonneg_left hbudget (inv_nonneg.mpr hw.le)
    _ ≤ (T.weight K (D:ℝ) z)^8*(P.crossDerivativeConstant D/r) :=
      mul_le_mul_of_nonneg_right hinv (by have := P.constant_pos; unfold crossDerivativeConstant; positivity)
    _ = _ := mul_comm _ _

theorem source_cross_top_derivative (p : ℝ) (D : ℕ) :
    ∃ L0 : ℝ, 1 ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
      ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type) [Fintype κ] [∀ j, Fintype (ι j)]
        (P : SourceLatticePacket N κ ι), P.constant ≤ L^p →
      ∀ (alt : ∀ j, ι j → κ → SchwartzMap (ℝ × ℝ) ℂ)
        (hAlt : ∀ j u k, planarProfileConstant (alt j u k) (2 * P.order) ≤ P.profileBound)
        (T : SlopeBox) (K : ℝ), 0 < K → SourceLatticeTopGeometry P T K D →
      ∀ (cutoff : Fin N → ℝ) (v : ℝ × ℝ → ℝ), Measurable v →
      ∀ (g : ℝ × ℝ → EuclideanSpace ℂ κ), Measurable g → (∀ z, ‖g z‖ ≤ 1) →
      ∀ (lower upper : ℕ), lower ≤ upper → ∀ r : ℝ, 0 < r →
      (∀ j : Fin N, lower ≤ j.val → j.val < upper → r ≤ P.length j) →
      ∀ z : ℝ × ℝ,
      ‖deriv (fun x => planarPacketInterval (P.family.mainCoefficient cutoff v g)
        (fun j u k t y => (P.withProfile alt hAlt).raw 0 j u k t y) lower upper x (z.2-T.slope*z.1)) z.1‖ ≤
          (L^(2*p+3)/r)*(T.weight K (D:ℝ) z)^8 := by
  let C : ℝ := Real.pi^2*(4*((16^(8*D+1)*16^(8*D+1))*(4*Real.pi)^2))
  refine ⟨max 1 C,le_max_left _ _,?_⟩
  intro L hL N κ ι _ _ P hP alt hAlt T K hK G cutoff v hv g hg hg1 lower upper hlu r hr hs z
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
  have hLpos : 0 < L := zero_lt_one.trans_le hL1
  have hCL : C ≤ L := (le_max_right _ _).trans hL
  have hconst : P.crossDerivativeConstant D ≤ L^(2*p+3) := by
    have hsq := pow_le_pow_left₀ P.constant_pos.le hP 2
    calc
      _ = C*P.constant^2 := by unfold crossDerivativeConstant; dsimp [C]; ring
      _ ≤ L*(L^p)^2 := mul_le_mul hCL hsq (sq_nonneg _) hLpos.le
      _ = L^(2*p+1) := by
        rw [← Real.rpow_mul_natCast hLpos.le]
        calc
          _ = L^(1+p*2) := by rw [Real.rpow_add hLpos,Real.rpow_one]; norm_num
          _ = _ := by congr 1; ring
      _ ≤ L^(2*p+3) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  let selected := Finset.univ.filter (fun j : Fin N => lower ≤ j.val ∧ j.val < upper)
  have hselected (j : Fin N) (hj : j ∈ selected) : r ≤ P.length j := by
    have hj' := (Finset.mem_filter.mp hj).2
    exact hs j hj'.1 hj'.2
  have hb := P.crossSelectedTopSum_horizontal_bound alt hAlt T hK G cutoff v hv g hg hg1 selected r hr hselected z
  have heq : (fun x => planarPacketInterval (P.family.mainCoefficient cutoff v g)
      (fun j u k t y => (P.withProfile alt hAlt).raw 0 j u k t y) lower upper x (z.2-T.slope*z.1)) =
      fun x => P.crossSelectedTopSum alt hAlt selected cutoff v g x (z.2-T.slope*z.1) := by
    funext x
    exact planarPacketInterval_eq_selected (P.family.mainCoefficient cutoff v g) (fun j u k t => (P.withProfile alt hAlt).raw 0 j u k t) lower upper hlu x _
  rw [heq]
  exact hb.trans (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hconst hr.le)
    (by positivity))


end LipschitzHilbert.SourceLatticePacket

end

end OAI
