import OAI.Analysis.LipschitzHilbert.Packets.SourceSelectorDerivative
import OAI.Analysis.LipschitzHilbert.Packets.SourceSupportedWeightedDerivative
import OAI.Analysis.LipschitzHilbert.Packets.SourceSupportedLabeledGeometry
import OAI.Analysis.LipschitzHilbert.Packets.SourceSelectorCoefficientNorm
import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledDerivative

namespace OAI

/-! The horizontal derivative estimate uses the coefficient norm bound
for the original smooth selector. It supplies the horizontal term in the
motion and prediction estimates. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

theorem boundedSelectedTopSum_horizontal_bound_of_supported (P : SourceLatticePacket N κ ι)
    (alt : ∀ j, ι j → κ → SchwartzMap (ℝ × ℝ) ℂ)
    (hAlt : ∀ j u k, planarProfileConstant (alt j u k) (2 * P.order) ≤ P.profileBound)
    {K : ℝ} {D : ℕ} (T : SlopeBox) (hK : 0 < K)
    (G : SourceSupportedLatticeTopGeometry P T K D)
    (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (hcoeff : ∀ j u, ‖coeff j u‖ ≤ P.constant*Real.pi^2)
    (s : Finset (Fin N)) (r : ℝ) (hr : 0 < r) (hs : ∀ j ∈ s, r ≤ P.length j)
    (z : ℝ × ℝ) :
    ‖deriv (fun x => P.boundedSelectedTopSum alt hAlt s coeff x (z.2-T.slope*z.1)) z.1‖ ≤
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
  have hb := top_weighted_selected_derivative_bounded_of_supported
    (coeff) (fun j u k => (P.withProfile alt hAlt).raw 0 j u k y) P.family.site P.family.site_injective
    P.family.baseX P.family.baseZ P.topLength P.width T.x (T.y-T.slope*T.x)
    (K*T.length) (K*T.width) z.1 y P.constant (P.constant*Real.pi^2) r (8*D+1)
    P.topLength_pos P.width_pos (mul_pos hK T.length_pos) (mul_pos hK T.width_pos)
    G.length_le G.width_le P.constant_pos.le (mul_pos P.constant_pos (sq_pos_of_pos Real.pi_pos)) hr
    hcoeff
    (fun j u => P.family_centerX_local j u T.x (K * T.length) (G.centerX_le j u))
    (fun j u => P.family_centerZ_local j u (T.y - T.slope * T.x) (K * T.width) (G.centerZ_le j u)) s hs hderiv
  change w*‖deriv (fun x => P.boundedSelectedTopSum alt hAlt s coeff x y) z.1‖ ≤ _ at hb
  have hbudget : w*‖deriv (fun x => P.boundedSelectedTopSum alt hAlt s coeff x y) z.1‖ ≤
      P.crossDerivativeConstant D/r := by
    convert hb using 1
    unfold crossDerivativeConstant
    ring
  have hinv : w⁻¹ ≤ (T.weight K (D:ℝ) z)^8 := T.inverse_polynomial_le_weight K hK D z
  calc
    _ = w⁻¹*(w*‖deriv (fun x => P.boundedSelectedTopSum alt hAlt s coeff x y) z.1‖) := by
      rw [← mul_assoc,inv_mul_cancel₀ hw.ne',one_mul]
    _ ≤ w⁻¹*(P.crossDerivativeConstant D/r) :=
      mul_le_mul_of_nonneg_left hbudget (inv_nonneg.mpr hw.le)
    _ ≤ (T.weight K (D:ℝ) z)^8*(P.crossDerivativeConstant D/r) :=
      mul_le_mul_of_nonneg_right hinv (by have := P.constant_pos; unfold crossDerivativeConstant; positivity)
    _ = _ := mul_comm _ _

theorem source_bounded_coefficient_derivative_of_supported (p : ℝ) (D : ℕ) :
    ∃ L0 : ℝ, 1 ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
      ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type) [Fintype κ] [∀ j, Fintype (ι j)]
        (P : SourceLatticePacket N κ ι), P.constant ≤ L^p →
      ∀ (alt : ∀ j, ι j → κ → SchwartzMap (ℝ × ℝ) ℂ)
        (hAlt : ∀ j u k, planarProfileConstant (alt j u k) (2 * P.order) ≤ P.profileBound)
        (T : SlopeBox) (K : ℝ), 0 < K → SourceSupportedLatticeTopGeometry P T K D →
      ∀ (coeff : ∀ j, ι j → EuclideanSpace ℂ κ),
        (∀ j u, ‖coeff j u‖ ≤ P.constant*Real.pi^2) →
      ∀ (lower upper : ℕ), lower ≤ upper → ∀ r : ℝ, 0 < r →
      (∀ j : Fin N, lower ≤ j.val → j.val < upper → r ≤ P.length j) →
      ∀ z : ℝ × ℝ,
      ‖deriv (fun x => planarPacketInterval (coeff)
        (fun j u k t y => (P.withProfile alt hAlt).raw 0 j u k t y) lower upper x (z.2-T.slope*z.1)) z.1‖ ≤
          (L^(2*p+3)/r)*(T.weight K (D:ℝ) z)^8 := by
  let C : ℝ := Real.pi^2*(4*((16^(8*D+1)*16^(8*D+1))*(4*Real.pi)^2))
  refine ⟨max 1 C,le_max_left _ _,?_⟩
  intro L hL N κ ι _ _ P hP alt hAlt T K hK G coeff hcoeff lower upper hlu r hr hs z
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
  have hb := P.boundedSelectedTopSum_horizontal_bound_of_supported alt hAlt T hK G coeff hcoeff selected r hr hselected z
  have heq : (fun x => planarPacketInterval (coeff)
      (fun j u k t y => (P.withProfile alt hAlt).raw 0 j u k t y) lower upper x (z.2-T.slope*z.1)) =
      fun x => P.boundedSelectedTopSum alt hAlt selected coeff x (z.2-T.slope*z.1) := by
    funext x
    exact planarPacketInterval_eq_selected (coeff) (fun j u k t => (P.withProfile alt hAlt).raw 0 j u k t) lower upper hlu x _
  rw [heq]
  exact hb.trans (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hconst hr.le)
    (by positivity))


end LipschitzHilbert.SourceLatticePacket

namespace LipschitzHilbert.SourceLabeledLattice

theorem source_selector_top_derivative_of_supported (p : ℝ) (D B : ℕ) :
    ∃ L0 : ℝ, 1 ≤ L0 ∧ (B : ℝ) ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
      ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
        [Fintype κ] [∀ j l, Fintype (Item j l)]
        (P : SourceLabeledLattice N κ Label Item)
        (_hcard : ∀ j, (P.labels j).card ≤ B), P.constant ≤ L^p →
      ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
        (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
        (T : SlopeBox) (K : ℝ), 0 < K → SourceSupportedLabeledTopGeometry P T K D →
      ∀ (selector : ∀ j, P.labels j → κ → ℝ → ℂ),
        (∀ j l k, Measurable (selector j l k)) →
        (∀ j l k s, ‖selector j l k s‖ ≤ 1) →
      ∀ (v : ℝ×ℝ → ℝ), Measurable v →
      ∀ (test : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable test → (∀ z, ‖test z‖ ≤ 1) →
      ∀ (lower upper : ℕ), lower ≤ upper → ∀ r : ℝ, 0 < r →
      (∀ j : Fin N, lower ≤ j.val → j.val < upper → r ≤ P.length j) →
      ∀ z : ℝ×ℝ,
      ‖deriv (fun x => (P.withProfile alt hAlt).rawInterval
        (P.physicalMultiplierCoefficient T.slope selector v test) 0 lower upper
        x (z.2-T.slope*z.1)) z.1‖ ≤
          (L^(2*p+4)/r)*(T.weight K (D:ℝ) z)^8 := by
  classical
  obtain ⟨L1,hL1,hderivative⟩ := SourceLatticePacket.source_bounded_coefficient_derivative_of_supported p D
  refine ⟨max L1 B,hL1.trans (le_max_left _ _),le_max_right _ _,?_⟩
  intro L hLL N κ Label Item _ _ P hcard hP alt hAlt T K hK G selector hs hs1 v hv
    test htest htest1 lower upper hlu r hr hlength z
  have hLpos : 0 < L := zero_lt_one.trans_le (hL1.trans ((le_max_left _ _).trans hLL))
  have hBL : (B:ℝ) ≤ L := (le_max_right _ _).trans hLL
  let Q := P.withProfile alt hAlt
  let coeff := P.physicalMultiplierCoefficient T.slope selector v test
  let y := z.2-T.slope*z.1
  let F := fun b : Fin B =>
    ((P.slotted hcard b).withProfile (P.slottedAlt hcard alt b)
      (P.slottedAlt_bound hcard alt hAlt b)).rawInterval
      (fun j a => coeff j a.1.1 a.1.2) 0 lower upper
  have hdiff (b : Fin B) : DifferentiableAt ℝ (fun x => F b x y) z.1 :=
    lattice_rawInterval_horizontal_differentiable
      ((P.slotted hcard b).withProfile (P.slottedAlt hcard alt b)
        (P.slottedAlt_bound hcard alt hAlt b))
      (fun j a => coeff j a.1.1 a.1.2) 0 lower upper hlu z.1 y
  have hsum : (fun x => Q.rawInterval coeff 0 lower upper x y) =
      fun x => ∑ b : Fin B, F b x y := by
    funext x
    have h := (P.withProfile alt hAlt).sum_slotted_rawInterval hcard coeff 0 lower upper x y
    simp only [P.withProfile_slotted hcard alt hAlt] at h
    convert h.symm using 1
    congr 1
  have hdiffsum : deriv (fun x => Q.rawInterval coeff 0 lower upper x y) z.1 =
      ∑ b : Fin B, deriv (fun x => F b x y) z.1 := by
    rw [hsum]
    exact deriv_fun_sum (fun b _ => hdiff b)
  have hb (b : Fin B) : ‖deriv (fun x => F b x y) z.1‖ ≤
      (L^(2*p+3)/r)*(T.weight K (D:ℝ) z)^8 := by
    have hR : (P.slotted hcard b).constant ≤ L^p := by
      simpa only [P.slotted_constant hcard] using hP
    have hc (j : Fin N) (a : P.SlotItem hcard b j) :
        ‖coeff j a.1.1 a.1.2‖ ≤ (P.slotted hcard b).constant*Real.pi^2 :=
      P.physicalMultiplierCoefficient_norm T.slope selector hs hs1 v hv test htest htest1
        j a.1.1 a.1.2
    exact hderivative L ((le_max_left _ _).trans hLL) N κ (P.SlotItem hcard b)
      (P.slotted hcard b) hR (P.slottedAlt hcard alt b) (P.slottedAlt_bound hcard alt hAlt b)
      T K hK (P.slotted_supportedTopGeometry hcard G b) (fun j a => coeff j a.1.1 a.1.2) hc
      lower upper hlu r hr hlength z
  change ‖deriv (fun x => Q.rawInterval coeff 0 lower upper x y) z.1‖ ≤ _
  rw [hdiffsum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _b : Fin B, (L^(2*p+3)/r)*(T.weight K (D:ℝ) z)^8 :=
      Finset.sum_le_sum (fun b _ => hb b)
    _ = ((B:ℝ)*L^(2*p+3)/r)*(T.weight K (D:ℝ) z)^8 := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      ring
    _ ≤ _ := by
      have hpower : (B:ℝ)*L^(2*p+3) ≤ L^(2*p+4) := by
        calc
          _ ≤ L*L^(2*p+3) := mul_le_mul_of_nonneg_right hBL (Real.rpow_nonneg hLpos.le _)
          _ = L^(2*p+4) := by
            calc
              _ = L^(1:ℝ)*L^(2*p+3) := by rw [Real.rpow_one]
              _ = L^(1+(2*p+3)) := (Real.rpow_add hLpos _ _).symm
              _ = _ := by congr 1; ring
      exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hpower hr.le) (by positivity)

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
