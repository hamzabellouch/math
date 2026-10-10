import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.Ledger
import OAI.MeasureTheory.FalconerCompletion.Angular.ConeUnitCap
import OAI.MeasureTheory.FalconerCompletion.Estimates.ScaleAbout
import OAI.MeasureTheory.FalconerCompletion.Measures.ChainSplit

namespace OAI

/-! Quantitative estimates for the distance-set construction. -/

open _root_.OAI.PlanarFalconer

section
section
namespace GraphLiteralSupport.CurrentFalconer.TreeND
open Set Metric MeasureTheory PlanarFalconer Exceptional
open scoped ENNReal RealInnerProductSpace
attribute [local instance] Classical.propDecidable
variable {d : ℕ}

lemma fullParallelCount_filter (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    (g p : ℕ) (P : CellPath d) (W : ℝ) (w : EuclideanSpace ℝ (Fin d)) :
    fullParallelCount ρ g p P W w =
      ((occupiedCenterCells ρ p (treeCenter P) (10*(d+1)/(2:ℝ)^g)).filter
        fun Q => ‖graphPerpND w (treeCenter Q-treeCenter P)‖ ≤ W).card := by
  classical
  simp only [fullParallelCount,occupiedCenterCells,Finset.filter_filter,mem_ball,and_assoc]

lemma parallel_mean_geometric (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    (ξ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure ξ]
    {g p : ℕ} (hgp : g ≤ p) (P : CellPath d) {W L S R K : ℝ}
    (hW : 0 < W) (hL : 1 ≤ L) (hS : 0 ≤ S) (hK : 0 ≤ K)
    (hmass : ξ univ ≤ 1) (hsphere : ∀ᵐ w ∂ξ, ‖w‖=1)
    (hcap : ∀ w : EuclideanSpace ℝ (Fin d), ‖w‖=1 → ∀ r : ℝ,
      R⁻¹ ≤ r → r ≤ 1 → ξ (ball w r) ≤ ENNReal.ofReal (L*r^S))
    (hcutoff : R⁻¹ ≤ 6*W)
    (hpack : ∀ h, g ≤ h → h ≤ p →
      ((occupiedCenterCells ρ p (treeCenter P) (10*(d+1)/(2:ℝ)^h)).card:ℝ) ≤
        K*((2:ℝ)^(p-h))^S)
    (hM : 1 ≤ 2*L*(6*W*(2:ℝ)^p)^S) :
    (∫ w, (fullParallelCount ρ g p P W w:ℝ) ∂ξ) ≤
      (p-g+1:ℕ)*K*(2*L*(6*W*(2:ℝ)^p)^S) := by
  classical
  let T : ℕ → Finset (CellPath d) := fun h => occupiedCenterCells ρ p (treeCenter P) (10*(d+1)/(2:ℝ)^h)
  let F : CellPath d → Set (EuclideanSpace ℝ (Fin d)) := fun Q =>
    {w | ‖graphPerpND w (treeCenter Q-treeCenter P)‖ ≤ W}
  have hF : ∀ Q, MeasurableSet (F Q) := by
    intro Q
    apply measurableSet_le _ measurable_const
    unfold graphPerpND
    fun_prop
  have hbase := integral_chain_filter_le ξ T F hF hgp hmass
  simp only [fullParallelCount_filter] at ⊢
  apply hbase.trans
  have hlast : ((T p).card:ℝ) ≤ K := by
    simpa only [T,Nat.sub_self,pow_zero,Real.one_rpow,mul_one] using hpack p hgp le_rfl
  have hann : ∀ h ∈ Finset.Ico g p, (∑ Q ∈ T h\T (h+1), ξ.real (F Q)) ≤ K*(2*L*(6*W*(2:ℝ)^p)^S) := by
    intro h hh
    have hgh := (Finset.mem_Ico.mp hh).1
    have hhp := (Finset.mem_Ico.mp hh).2
    have hpoint : ∀ Q ∈ T h\T (h+1), ξ.real (F Q) ≤ 2*L*(6*W*(2:ℝ)^h)^S := by
      intro Q hQ
      obtain ⟨hQh,hQn⟩ := Finset.mem_sdiff.mp hQ
      have hoccup := Finset.mem_filter.mp hQh
      have hn : 10*(d+1)/(2:ℝ)^(h+1) ≤ dist (treeCenter Q) (treeCenter P) := by
        by_contra hn
        apply hQn
        apply Finset.mem_filter.mpr
        exact ⟨hoccup.1,hoccup.2.1,mem_ball.mpr (lt_of_not_ge hn)⟩
      have hvp : 0 < ‖treeCenter Q-treeCenter P‖ := by
        rw [←dist_eq_norm]
        exact lt_of_lt_of_le (by positivity) hn
      have hlower : ((2:ℝ)^(h+1))⁻¹ ≤ ‖treeCenter Q-treeCenter P‖ := by
        rw [←dist_eq_norm]
        apply le_trans _ hn
        rw [inv_eq_one_div]
        apply div_le_div_of_nonneg_right _ (by positivity)
        have hd : (0:ℝ) ≤ d := Nat.cast_nonneg _
        linarith
      have hradius : 3*W/‖treeCenter Q-treeCenter P‖ ≤ 6*W*(2:ℝ)^h := by
        apply (div_le_iff₀ hvp).mpr
        have hh := mul_le_mul_of_nonneg_left hlower (show 0 ≤ 6*W*(2:ℝ)^h by positivity)
        have he : (6*W*(2:ℝ)^h)*((2:ℝ)^(h+1))⁻¹ = 3*W := by rw [pow_succ]; field_simp; ring
        rw [he] at hh
        exact hh
      have hlo : R⁻¹ ≤ 6*W*(2:ℝ)^h := hcutoff.trans
        (le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by norm_num)))
      have hc := cone_mass_bound ξ hL hS hmass hsphere hcap (treeCenter Q-treeCenter P)
        (norm_pos_iff.mp hvp) hW hlo (by positivity) hradius
      exact ENNReal.toReal_le_of_le_ofReal (by positivity) hc
    calc
      _ ≤ ∑ _Q ∈ T h\T (h+1), 2*L*(6*W*(2:ℝ)^h)^S := Finset.sum_le_sum hpoint
      _ = ((T h\T (h+1)).card:ℝ)*(2*L*(6*W*(2:ℝ)^h)^S) := by simp
      _ ≤ ((T h).card:ℝ)*(2*L*(6*W*(2:ℝ)^h)^S) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card (Finset.sdiff_subset : T h\T (h+1) ⊆ T h)) (by positivity)
      _ ≤ (K*((2:ℝ)^(p-h))^S)*(2*L*(6*W*(2:ℝ)^h)^S) :=
        mul_le_mul_of_nonneg_right (hpack h hgh hhp.le) (by positivity)
      _ = K*(2*L*(6*W*(2:ℝ)^p)^S) := by
        have he : ((2:ℝ)^(p-h))^S*(6*W*(2:ℝ)^h)^S = (6*W*(2:ℝ)^p)^S := by
          rw [←Real.mul_rpow (by positivity) (by positivity)]
          congr 1
          rw [show (2:ℝ)^p=(2:ℝ)^(p-h)*(2:ℝ)^h by rw [←pow_add,Nat.sub_add_cancel hhp.le]]
          ring
        calc
          _ = K*(2*L)*(((2:ℝ)^(p-h))^S*(6*W*(2:ℝ)^h)^S) := by ring
          _ = _ := by rw [he]; ring
  calc
    _ ≤ K+∑ _h ∈ Finset.Ico g p, K*(2*L*(6*W*(2:ℝ)^p)^S) := add_le_add hlast (Finset.sum_le_sum hann)
    _ = K+(p-g:ℕ)*(K*(2*L*(6*W*(2:ℝ)^p)^S)) := by simp
    _ ≤ K*(2*L*(6*W*(2:ℝ)^p)^S)+(p-g:ℕ)*(K*(2*L*(6*W*(2:ℝ)^p)^S)) :=
      add_le_add (le_mul_of_one_le_right hK hM) le_rfl
    _ = _ := by push_cast; ring
end GraphLiteralSupport.CurrentFalconer.TreeND
end
end

section
section
namespace GraphLiteralSupport.CurrentFalconer.TreeND
open Set Metric MeasureTheory PlanarFalconer Exceptional
open scoped ENNReal
variable {d : ℕ}

lemma packing_profile_power (m : ℝ → ℝ) {N : ℕ} (hN : 0 < N)
    {h p : ℕ} (hhp : h ≤ p) (e : ℝ) :
    ((2:ℝ)^N)^(m p-m h+e) = ((2:ℝ)^(p-h))^((d:ℝ)/2)*
      ((2:ℝ)^N)^(adjustedProfile (d:=d) m N p-adjustedProfile (d:=d) m N h+e) := by
  have hNp : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [←Real.rpow_natCast_mul (by norm_num),←Real.rpow_natCast_mul (by norm_num),
    ←Real.rpow_natCast_mul (by norm_num),←Real.rpow_add (by norm_num)]
  congr 1
  unfold adjustedProfile
  rw [Nat.cast_sub hhp]
  field_simp
  ring

lemma actual_parallel_mean (d : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (N B : ℕ) (s sig : ℝ) (ρ : Measure (EuclideanSpace ℝ (Fin d))) (m : ℝ → ℝ),
    0 < N → 0 < sig → RegularizedProfileData ρ N B s sig m →
    ∀ (ξ : Measure (EuclideanSpace ℝ (Fin d))), IsFiniteMeasure ξ → ξ univ ≤ 1 →
    (∀ᵐ w ∂ξ, ‖w‖=1) →
    (∀ w : EuclideanSpace ℝ (Fin d), ‖w‖=1 → ∀ r : ℝ,
      ((2:ℝ)^N)⁻¹ ≤ r → r ≤ 1 → ξ (ball w r) ≤ ENNReal.ofReal (((2:ℝ)^N)^sig*r^((d:ℝ)/2))) →
    ∀ g p : ℕ, g ≤ p → p ≤ N → ∀ P : CellPath d, ∀ J : ℕ,
    (∫ w, (fullParallelCount ρ g p P (testWidth N J 0 p sig) w:ℝ) ∂ξ) ≤
      C*(N+1:ℝ)*((2:ℝ)^N)^(height (adjustedProfile (d:=d) m N) g p+
        (1+500*((d:ℝ)/2)+2*(d+1:ℝ))*sig) := by
  let D : ℝ := (22*(d:ℝ)+27)^d
  let C : ℝ := D*2*(12:ℝ)^((d:ℝ)/2)
  have hD : 0 < D := by dsimp [D]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro N B s sig ρ m hN hsig hr ξ hξ hmass hsphere hcap g p hgp hpN P J
  let := hξ
  let R : ℝ := (2:ℝ)^N
  let S : ℝ := (d:ℝ)/2
  let A := adjustedProfile (d:=d) m N
  let K : ℝ := D*R^(height A g p+2*(d+1:ℝ)*sig)
  let W : ℝ := testWidth N J 0 p sig
  have hRp : 0 < R := by positivity
  have hR : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hS : 0 ≤ S := by positivity
  have hL : 1 ≤ R^sig := Real.one_le_rpow hR hsig.le
  have hwide : 1 ≤ R^(500*sig) := Real.one_le_rpow hR (by positivity)
  have hW : 0 < W := by dsimp [W]; rw [testWidth_zero]; positivity
  have hWP : 6*W*(2:ℝ)^p=12*R^(500*sig) := by
    dsimp [W,R]
    rw [testWidth_zero]
    field_simp
    ring
  have hcutoff : R⁻¹ ≤ 6*W := by
    have hpow : ((2:ℝ)^N)⁻¹ ≤ ((2:ℝ)^p)⁻¹ :=
      inv_le_inv₀ (by positivity) (by positivity) |>.mpr (pow_le_pow_right₀ (by norm_num) hpN)
    apply hpow.trans
    dsimp [W]
    rw [testWidth_zero]
    have hh := mul_le_mul_of_nonneg_left hwide (show 0 ≤ 12*((2:ℝ)^p)⁻¹ by positivity)
    nlinarith [show (0:ℝ) < ((2:ℝ)^p)⁻¹ by positivity]
  have hpack : ∀ h, g ≤ h → h ≤ p →
      ((occupiedCenterCells ρ p (treeCenter P) (10*(d+1)/(2:ℝ)^h)).card:ℝ) ≤ K*((2:ℝ)^(p-h))^S := by
    intro h hgh hhp
    have hb := hr.packing h p hhp hpN (treeCenter P) (10*(d+1)) (by positivity)
    have he : (2*(10*(d+1:ℝ))+2*(d:ℝ)+7)^d=D := by dsimp [D]; congr 1; ring
    rw [he,packing_profile_power m hN hhp] at hb
    apply hb.trans
    have hmin := intervalMin_le A hgh hhp
    have he' : R^(A p-A h+2*(d+1:ℝ)*sig) ≤ R^(height A g p+2*(d+1:ℝ)*sig) := by
      apply Real.rpow_le_rpow_of_exponent_le hR
      unfold height
      exact _root_.add_le_add (sub_le_sub_left hmin (A p)) le_rfl
    have hh := mul_le_mul_of_nonneg_left he' (show 0 ≤ D*((2:ℝ)^(p-h))^S by positivity)
    dsimp only [K]
    simpa only [mul_assoc,mul_left_comm,mul_comm] using hh
  have hM : 1 ≤ 2*(R^sig)*(6*W*(2:ℝ)^p)^S := by
    rw [hWP]
    apply one_le_mul_of_one_le_of_one_le
    · exact one_le_mul_of_one_le_of_one_le (by norm_num) hL
    · apply Real.one_le_rpow _ hS
      linarith
  have hm := parallel_mean_geometric ρ ξ hgp P hW hL hS (show 0 ≤ K by positivity)
    hmass hsphere hcap hcutoff hpack hM
  apply hm.trans
  have hn : (p-g+1:ℕ) ≤ (N+1:ℝ) := by exact_mod_cast (show p-g+1 ≤ N+1 by omega)
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hn (show 0 ≤ K by positivity))
    (show 0 ≤ 2*(R^sig)*(6*W*(2:ℝ)^p)^S by positivity)
  apply hh.trans_eq
  rw [hWP]
  dsimp only [K,C]
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 12) (by positivity),←Real.rpow_mul hRp.le]
  have he : R^(height A g p+2*(d+1:ℝ)*sig)*R^sig*R^(500*sig*S) =
      R^(height A g p+(1+500*S+2*(d+1:ℝ))*sig) := by
    rw [←Real.rpow_add hRp,←Real.rpow_add hRp]
    congr 1
    ring
  calc
    _ = (D*2*(12:ℝ)^S)*(N+1)*(R^(height A g p+2*(d+1:ℝ)*sig)*R^sig*R^(500*sig*S)) := by ring
    _ = _ := by rw [he]
end GraphLiteralSupport.CurrentFalconer.TreeND
end
end

section
section
namespace GraphLiteralSupport.CurrentFalconer.TreeND
open Set Metric MeasureTheory PlanarFalconer Exceptional Filter
open scoped ENNReal Topology

theorem uniform_actual_parallel_exceptional (d : ℕ) (sig : ℝ) (hsig : 0 < sig) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (ρ : Measure (EuclideanSpace ℝ (Fin d))) (m : ℝ → ℝ) (B : ℕ) (s : ℝ),
      RegularizedProfileData ρ N B s sig m →
      ∀ (ξ : Measure (EuclideanSpace ℝ (Fin d))), IsFiniteMeasure ξ → ξ univ ≤ 1 →
      (∀ᵐ w ∂ξ, ‖w‖=1) →
      (∀ w : EuclideanSpace ℝ (Fin d), ‖w‖=1 → ∀ r : ℝ,
        ((2:ℝ)^N)⁻¹ ≤ r → r ≤ 1 →
        ξ (ball w r) ≤ ENNReal.ofReal (((2:ℝ)^N)^sig*r^((d:ℝ)/2))) →
      ∀ J g p : ℕ, g ≤ p → p ≤ N → ∀ P : CellPath d, P.length=p →
        0 < ρ (treeCell P) →
        ξ (descriptorGood ρ m N sig (1000*(d+1:ℝ)) J 0 P (.parallel g p))ᶜ ≤
          ENNReal.ofReal (((2:ℝ)^N)^(-sig)) := by
  obtain ⟨C,hC,hmean⟩ := actual_parallel_mean d
  obtain ⟨N₁,h₁⟩ := eventually_atTop.mp (shell_polynomial_subpowerND 1 (2*C) sig hsig)
  refine ⟨max 1 N₁,?_⟩
  intro N hN ρ m B s hr ξ hξ hmass hsphere hcap J g p hgp hpN P hP hpos
  have hNp : 0 < N := by omega
  have hNN : N₁ ≤ N := by omega
  let := hξ
  let R : ℝ := (2:ℝ)^N
  let k : ℝ := height (adjustedProfile (d:=d) m N) g p
  let T : ℝ := R^(k+(1000*(d+1:ℝ))*sig)
  have hRp : 0 < R := by positivity
  have hR : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hT : 0 < T := by positivity
  have hm := hmean N B s sig ρ m hNp hsig hr ξ hξ hmass hsphere hcap g p hgp hpN P J
  have hc : C*(N+1:ℝ) ≤ R^sig := by
    have hh := h₁ N hNN
    simp only [pow_one] at hh
    have hn : (1:ℝ) ≤ N := by exact_mod_cast hNp
    exact (show C*(N+1:ℝ) ≤ 2*C*N by nlinarith).trans hh
  have hm' : (∫ w, (fullParallelCount ρ g p P (testWidth N J 0 p sig) w:ℝ) ∂ξ) ≤ T*R^(-sig) := by
    apply hm.trans
    calc
      _ ≤ R^sig*R^(k+(1+500*((d:ℝ)/2)+2*(d+1:ℝ))*sig) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
      _ = R^(k+(2+500*((d:ℝ)/2)+2*(d+1:ℝ))*sig) := by
        rw [←Real.rpow_add hRp]
        congr 1
        ring
      _ ≤ R^(k+(1000*(d+1:ℝ)-1)*sig) := by
        apply Real.rpow_le_rpow_of_exponent_le hR
        have hd : (0:ℝ) ≤ d := Nat.cast_nonneg _
        nlinarith
      _ = T*R^(-sig) := by
        dsimp [T]
        rw [←Real.rpow_add hRp]
        congr 1
        ring
  have hi : Integrable (fun w => (fullParallelCount ρ g p P (testWidth N J 0 p sig) w:ℝ)) ξ := by
    simp_rw [fullParallelCount_filter]
    exact integrable_finite_test_count ξ _ _ (fun Q _ => by
      change MeasurableSet {w : EuclideanSpace ℝ (Fin d) |
        ‖graphPerpND w (treeCenter Q-treeCenter P)‖ ≤ testWidth N J 0 p sig}
      apply measurableSet_le _ measurable_const
      unfold graphPerpND
      fun_prop)
  have hmark := exceptional_of_mean ξ hi (Filter.Eventually.of_forall (fun w => Nat.cast_nonneg _))
    (S:={w | ‖w‖=1}) hsphere hT (show 0 ≤ R^(-sig) by positivity) hm'
  simpa only [descriptorGood,R,T,k,Set.mem_ofPred_eq] using hmark
end GraphLiteralSupport.CurrentFalconer.TreeND
end
end

section
section
namespace GraphLiteralSupport.CurrentFalconer.TreeND
open Set Metric MeasureTheory PlanarFalconer
open scoped ENNReal

theorem uniform_actual_exceptional_directions (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ sig : ℝ, 0 < sig → ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (ρ : Measure (EuclideanSpace ℝ (Fin d))) (m : ℝ → ℝ) (B : ℕ) (s : ℝ),
      RegularizedProfileData ρ N B s sig m →
      ∀ (ξ : Measure (EuclideanSpace ℝ (Fin d))), IsFiniteMeasure ξ →
      ξ univ ≤ 1 → (∀ᵐ w ∂ξ, ‖w‖=1) →
      (∀ w : EuclideanSpace ℝ (Fin d), ‖w‖=1 → ∀ r : ℝ,
        ((2:ℝ)^N)⁻¹ ≤ r → r ≤ 1 →
        ξ (ball w r) ≤ ENNReal.ofReal (((2:ℝ)^N)^sig*r^((d:ℝ)/2))) →
      ∀ J : ℕ,
      (∀ g p : ℕ, g ≤ p → p ≤ N → ∀ P : CellPath d, P.length=p →
        0 < ρ (treeCell P) →
        ξ (descriptorGood ρ m N sig C J 0 P (.parallel g p))ᶜ ≤
          ENNReal.ofReal (((2:ℝ)^N)^(-sig))) ∧
      (∀ p t : ℕ, p ≤ t → t ≤ N → ∀ P : CellPath d, P.length=p →
        0 < ρ (treeCell P) →
        ξ (descriptorGood ρ m N sig C J 0 P (.projection p t))ᶜ ≤
          ENNReal.ofReal (((2:ℝ)^N)^(-sig)))
 := by
  refine ⟨1000*(d+1:ℝ),by positivity,?_⟩
  intro sig hsig
  obtain ⟨N₁,hparallel⟩ := uniform_actual_parallel_exceptional d sig hsig
  obtain ⟨N₂,hprojection⟩ := uniform_actual_projection_exceptional d sig hsig
  refine ⟨max N₁ N₂,?_⟩
  intro N hN ρ m B s hr ξ hξ hmass hsphere hcap J
  have hN₁ : N₁ ≤ N := (le_max_left _ _).trans hN
  have hN₂ : N₂ ≤ N := (le_max_right _ _).trans hN
  exact ⟨hparallel N hN₁ ρ m B s hr ξ hξ hmass hsphere hcap J,
    hprojection N hN₂ ρ m B s hr ξ hξ hmass hsphere hcap J⟩

end GraphLiteralSupport.CurrentFalconer.TreeND
end
end

end OAI
