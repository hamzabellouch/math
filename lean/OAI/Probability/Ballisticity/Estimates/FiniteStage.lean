import Mathlib
import OAI.Probability.Ballisticity.Estimates.CellBadEvent

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Classical
namespace DirectionalTransience

theorem actual_finite_stage_estimate {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∃ (κ : ℝ≥0) (lam Cr lamq Cq A : ℝ), 0 < κ ∧
      (∀ᵐ p ∂ν, ∀ u, κ ≤ p.1 u) ∧ 0 < lam ∧ lam ≤ 1 ∧ 0 < Cr ∧
      0 < lamq ∧ lamq ≤ 1 ∧ 0 < Cq ∧ 1 ≤ A ∧
      ∀ k : ℕ, 2 ≤ k → ∃ C c g₀ g₁ : ℝ, 0 < C ∧ ∃ _ : 0 < c,
      c ≤ 1 ∧ 0 < g₀ ∧ 0 < g₁ ∧ ∃ s : ℕ, 0 < s ∧
      ∀ Bstar : ℝ, 0 < Bstar → ∃ W N : ℕ, 0 < W ∧
      ∀ (n L He H m : ℕ) (a G B q Gminus Gplus : ℝ)
        (v w : Fin n → ℕ) (Gs : Fin n → ℝ),
        1 ≤ L → 0 < G → (N:ℝ) ≤ G → 0 < B → B/2 ≤ Bstar →
        (k:ℝ)*L*Real.log (1/(κ:ℝ)) ≤ B/2 → Real.exp (-Bstar) ≤ q →
        (2*A*k)*(m:ℝ) ≤ Bstar →
        (∀ j, W ≤ w j) → (∀ j, 2*cellWidth (w j) m 0 ≤ v j) →
        (∀ j i, i < m → Gs j ≤ c*cellRadius ν e f C (w j) m i/2) →
        (∀ h : ℕ, He < h → h ≤ H → ∃ j, v j ≤ h ∧ h ≤ v j+w j ∧ Gminus ≤ Gs j) →
        (∃ j, v j ≤ H ∧ H ≤ v j+w j ∧ Gplus ≤ Gs j) →
        Gminus ≤ G/2 →
        ENNReal.ofReal (Real.exp (-B)) ≤ ENNReal.ofReal q*
          (ENNReal.ofReal g₀*ENNReal.ofReal g₁*ENNReal.ofReal (Real.exp (-A*k*m))) →
        ∀ π : BudgetProfile (k:=k) e f a G,
        environmentLaw ν (stageBadEvent e f H Gminus Gplus π.val (ENNReal.ofReal (Real.exp (-B)))) ≤
          ENNReal.ofReal ((Real.exp (Cr*k-lam*(B/2)/L)+Cr*k*Real.exp ((B/2)/L)*He /
            fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
              (commonIncrementProcess (realPosition (step e)) f 0) (G/(4*L)))^L) +
          ENNReal.ofReal (Real.exp (Cq*k)*q^lamq) +
          (n:ℝ≥0∞)*((2:ℝ≥0∞)^(m-1)*ENNReal.ofReal (Real.exp (-2*k*m))) := by
  obtain ⟨κ,lam,Cr,hκ,hrows,hlam,hlam1,hCr,hr⟩ := rapid_loss_probability ν hue e f hef htrans
  obtain ⟨lamq,Cq,hlamq,hlamq1,hCq,hq⟩ := fullStream_small_mass_probability ν hue _ (signed_direction_unit e) htrans f.1
  obtain ⟨A,hA,hcells⟩ := actual_cell_no_success ν hue e f hef htrans
  refine ⟨κ,lam,Cr,lamq,Cq,A,hκ,hrows,hlam,hlam1,hCr,hlamq,hlamq1,hCq,hA,fun k hk => ?_⟩
  obtain ⟨C,c,g₀,g₁,hC,hc,hc1,hg₀,hg₁,s,hs,hcb⟩ := hcells k hk
  refine ⟨C,c,g₀,g₁,hC,hc,hc1,hg₀,hg₁,s,hs,fun Bstar hBstar => ?_⟩
  obtain ⟨W,hW,hWbound⟩ := hcb Bstar hBstar
  obtain ⟨Nr,hNr⟩ := hr Bstar hBstar k (by omega)
  obtain ⟨Nq,hNq⟩ := hq Bstar hBstar k (by omega)
  refine ⟨W,max Nq (2*Nr),hW,?_⟩
  intro n L He H m a G B q Gminus Gplus v w Gs hL hG0 hG hB hcap hell hqcap hmb hw hv hGs hcover hgrowth hshortgap hcoef π
  have hGNq : (Nq:ℝ) ≤ G := (show (Nq:ℝ) ≤ (max Nq (2*Nr):ℕ) by exact_mod_cast le_max_left Nq (2*Nr)).trans hG
  have hGNr : (Nr:ℝ) ≤ G-G/2 := by
    have hh : (2:ℝ)*Nr ≤ G := (show (2:ℝ)*Nr ≤ (max Nq (2*Nr):ℕ) by exact_mod_cast le_max_right Nq (2*Nr)).trans hG
    linarith
  have hmass := hNq π.val (π.property.2.mono (fun x hx =>
    (tupleSeparated_coordinate f Nq x).mp (tupleSeparated_mono f hGNq x hx.2))) q hqcap
  have hshort0 := hNr L He a G (G/2) (B/2) hL (by positivity) le_rfl hGNr hell hcap π
  have harg : (G/2)/(2*(L:ℝ))=G/(4*L) := by ring
  rw [harg] at hshort0
  have hshort : environmentLaw ν {ω | relativeBudgetMassENN e f He (G/2) π.val ω < ENNReal.ofReal (Real.exp (-B))} ≤
      ENNReal.ofReal ((Real.exp (Cr*k-lam*(B/2)/L)+Cr*k*Real.exp ((B/2)/L)*He /
        fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
          (commonIncrementProcess (realPosition (step e)) f 0) (G/(4*L)))^L) := by
    apply le_trans _ (ENNReal.ofReal_le_ofReal hshort0)
    rw [Measure.real,ENNReal.ofReal_toReal (measure_ne_top _ _)]
    apply measure_mono
    intro ω hω
    exact hω.trans_le (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith)))
  apply finite_stage_assembly ν e f hef a C c g₀ g₁ A G Gminus Gplus (G/2) hc
    (zero_le_one.trans hA) π He H v w m s hs Gs hv hGs hcover hgrowth (by linarith)
    _ (ENNReal.ofReal q) _ _ _ hcoef hshort hmass
  intro j
  exact hWbound (w j) (hw j) m hmb (v j) (hv j) a (fun _ => π.toLayerProfile) measurable_const

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience

def finestCellWidth (H m : ℕ) : ℕ := H/(4*16^m)

lemma finestCellWidth_lower {H m : ℕ} (hH : 8*16^m ≤ H) :
    H ≤ 8*16^m*finestCellWidth H m := by
  have hpos : 0 < 4*16^m := by positivity
  have hdiv : H/(4*16^m)*(4*16^m) ≤ H := Nat.div_mul_le_self _ _
  have hrem : H < (H/(4*16^m)+1)*(4*16^m) := by simpa only [mul_comm] using Nat.lt_mul_div_succ H hpos
  have htwo : 2 ≤ H/(4*16^m) := (Nat.le_div_iff_mul_le hpos).mpr (by nlinarith)
  dsimp [finestCellWidth]
  nlinarith

lemma finestCellWidth_pos {H m : ℕ} (hH : 8*16^m ≤ H) :
    0 < finestCellWidth H m := by
  apply Nat.div_pos
  · nlinarith [show 0 < 16^m by positivity]
  · positivity

lemma finestCellWidth_start (H m : ℕ) :
    2*cellWidth (finestCellWidth H m) m 0 ≤ H := by
  simp only [cellWidth,Nat.sub_zero]
  have h := Nat.div_mul_le_self H (4*16^m)
  dsimp only [finestCellWidth]
  nlinarith

lemma integer_cells_cover (He H w : ℕ) (hw : 0 < w) :
    ∀ h : ℕ, He ≤ h → h ≤ H →
      ∃ j : Fin ((H-He)/w+1), He+j.val*w ≤ h ∧ h ≤ He+j.val*w+w := by
  intro h hHe hH
  let j := (h-He)/w
  have hj : j < (H-He)/w+1 := by
    have hh : h-He ≤ H-He := Nat.sub_le_sub_right hH He
    exact Nat.lt_succ_of_le (Nat.div_le_div_right hh)
  refine ⟨⟨j,hj⟩,?_,?_⟩
  · have hh := Nat.div_mul_le_self (h-He) w
    dsimp [j] at *
    omega
  · have hh := Nat.lt_mul_div_succ (h-He) hw
    dsimp [j] at *
    nlinarith [Nat.sub_add_cancel hHe]

lemma integer_cells_card (He H w : ℕ) (hw : 0 < w) :
    (((H-He)/w+1:ℕ):ℝ) ≤ (H:ℝ)/w+1 := by
  push_cast
  apply add_le_add _ le_rfl
  apply (le_div_iff₀ (by exact_mod_cast hw : (0:ℝ) < w)).mpr
  exact_mod_cast (Nat.div_mul_le_self (H-He) w).trans (Nat.sub_le H He)

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Classical
namespace DirectionalTransience

lemma fluctuationRadius_scaling_compare {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Ω → ℝ) (hS : Measurable S)
    (hI : Integrable S μ) (hne : 0 < μ {x | S x ≠ 0}) :
    ∃ R : ℝ, 0 < R ∧ ∀ s t c : ℝ,
      fluctuationScale μ S R < t → t ≤ c^2*s → 0 < c → c ≤ 1 →
      fluctuationRadius μ S t ≤ c*fluctuationRadius μ S s := by
  obtain ⟨R,hR,hstrict⟩ := fluctuationScale_eventually_strictMono μ S hS hne
  refine ⟨R,hR,fun s t c ht hts hc hc1 => ?_⟩
  have ht0 : 0 < t := (fluctuationScale_nonneg μ S R).trans_lt ht
  have hs0 : 0 < s := by
    have : 0 < c^2*s := ht0.trans_le hts
    exact (mul_pos_iff.mp this).elim (fun h => h.2) (fun h => False.elim (not_lt_of_ge (sq_nonneg c) h.1))
  have hts' : t ≤ s := hts.trans (by nlinarith [mul_nonneg (show 0 ≤ 1-c^2 by nlinarith) hs0.le])
  obtain ⟨hrt,het⟩ := fluctuationRadius_spec μ S hS hI hne hR ht
  obtain ⟨hrs,hes⟩ := fluctuationRadius_spec μ S hS hI hne hR (ht.trans_le hts')
  have hpos : 0 < fluctuationRadius μ S s := hR.trans hrs
  have hscale := fluctuationScale_scaling μ S hS hne hpos hc hc1
  rw [hes] at hscale
  have hcmp : t ≤ fluctuationScale μ S (c*fluctuationRadius μ S s) := hts.trans hscale
  have hr : R ≤ c*fluctuationRadius μ S s := by
    by_contra hn
    have hh := fluctuationScale_mono μ S hS hne (mul_pos hc hpos) (not_le.mp hn).le
    exact (not_le_of_gt ht) (hcmp.trans hh)
  by_contra hn
  have hh := hstrict hr hrt.le (not_le.mp hn)
  rw [het] at hh
  exact (not_lt_of_ge hcmp) hh

end DirectionalTransience

end

end OAI
