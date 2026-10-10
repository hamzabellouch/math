import OAI.NumberTheory.CubicMoment.Estimates.TypeIProductWindow
import OAI.NumberTheory.CubicMoment.Estimates.SquarefreeTypeIMass
import OAI.NumberTheory.CubicMoment.Estimates.ShortOuterLow

namespace OAI

/-! Sum the actual Gauss cutoff window over short outer levels. The
squarefree restriction is justified by the Gauss sum, and the coefficient
mass comes from the published primary-prime input. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem radial_short_outer_window_bound (hpnt : PrimaryPrimePNT)
    {γ : Type*} {W : γ → ℝ → ℂ} (hW : UniformLogWeights W)
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hVor : MetaplecticVoronoiInput a)
    {MV : ℝ} (hMV : MontgomeryVaughanBound MV) (hMean0 : 0 ≤ MV)
    {κ ρ : ℝ} (hκ : 0 < κ) (hρ : ρ ≤ κ/4)
    {A : ℝ} (hA : 0 ≤ A) (k M : ℕ) :
    ∃ C E : ℝ, 0 ≤ C ∧ 0 ≤ E ∧ ∀ (w : Eisenstein → γ)
      (S : Finset Eisenstein) (α : Eisenstein → ℂ) (X Y H T X₀ : ℝ),
      2 ≤ X → 1 ≤ Real.log X → 1 ≤ Y → Real.log X ≤ T → 0 < H → 0 < X₀ →
      ((2*Y ≤ X^(2/5:ℝ) ∧ T ≤ X^(1/100:ℝ)) ∨
        (2*Y ≤ X^(1/3-κ/2) ∧ T ≤ X^(1/6+ρ))) →
      (∀ r ∈ S, primary r) →
      (∀ r ∈ S, α r ≠ 0 → norm r ≤ Y) →
      (∀ r ∈ S, ‖α r‖ ≤ A*((metaplecticPrimaryDivisors r).card:ℝ)^k) →
      ‖∑ r ∈ S, α r*∑ u ∈ primaryElementBall (Real.exp hW.radius*X),
        if r*u ∈ squarefreeProductEnvelope (Real.exp hW.radius*X) then
          productGaussHeightWindowKernel 0 (W (w r)) H T X X₀ (r*u) else 0‖ ≤
        (1+Real.log Y)*(C*X^(5/6-min (1/100) (3*κ/16))+
          E*X^(5/6:ℝ)/(Real.log X)^M) := by
  obtain ⟨D,d,hD,hmass⟩ := squarefree_typeI_coefficient_mass hpnt hA k
  obtain ⟨C,E,hC,hE,hbound⟩ := radial_productTypeICutoffWindow_bound hW
    hVor hMV hMean0 hκ hρ d M hD
  obtain ⟨L,hL,hcount⟩ := shortOuterCount_log_bound
  refine ⟨L*C,L*E,by positivity,by positivity,?_⟩
  intro w S α X Y H T X₀ hX hlog hY hLT hH hX₀ hrange hS hsize hα
  have hXp : 0 < X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have hYp : 0 < Y := zero_lt_one.trans_le hY
  have hYL : 0 ≤ 1+Real.log Y := by linarith [Real.log_nonneg hY]
  let S' := S.filter (fun r => α r ≠ 0 ∧ Squarefree r)
  let f : Eisenstein → ℂ := fun r => α r*∑ u ∈ primaryElementBall (Real.exp hW.radius*X),
    if r*u ∈ squarefreeProductEnvelope (Real.exp hW.radius*X) then
      productGaussHeightWindowKernel 0 (W (w r)) H T X X₀ (r*u) else 0
  have hre : (∑ r ∈ S, f r) = ∑ r ∈ S', f r := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro r hr
    by_cases ha : α r = 0
    · simp only [ha,ne_eq,not_true_eq_false,false_and,ite_false,f,zero_mul]
    · by_cases hs : Squarefree r
      · simp only [ha,ne_eq,not_false_eq_true,hs,and_self,ite_true]
      · simp only [ha,ne_eq,not_false_eq_true,hs,and_false,ite_false]
        dsimp only [f]
        rw [show (∑ u ∈ primaryElementBall (Real.exp hW.radius*X),
          if r*u ∈ squarefreeProductEnvelope (Real.exp hW.radius*X) then
            productGaussHeightWindowKernel 0 (W (w r)) H T X X₀ (r*u) else 0) = 0 from ?_,mul_zero]
        apply Finset.sum_eq_zero
        intro u _
        apply ite_eq_right
        intro hp
        have hsf := (Finset.mem_filter.mp hp).2
        exact hs (fun a ha => hsf a (ha.trans (dvd_mul_right r u)))
  have hS' (r : Eisenstein) (hr : r ∈ S') :
      primary r ∧ Squarefree r ∧ 1 ≤ norm r ∧ norm r ≤ Y := by
    obtain ⟨hr,ha,hs⟩ := Finset.mem_filter.mp hr
    exact ⟨hS r hr,hs,one_le_norm (primary_ne_zero (hS r hr)),hsize r hr ha⟩
  have hpart := typeIMixedDyad_partition S' (show (0:ℝ) < 1 by norm_num)
    (shortOuterCount_covers hYp)
    (fun r hr => by simpa only [one_mul,mul_one] using (hS' r hr).2.2) f
  change ‖∑ r ∈ S, f r‖ ≤ _
  rw [hre,hpart]
  let B := C*X^(5/6-min (1/100) (3*κ/16))+E*X^(5/6:ℝ)/(Real.log X)^M
  have hB : 0 ≤ B := by dsimp [B]; positivity
  calc
    _ ≤ ∑ j ∈ Finset.range (shortOuterCount Y), ‖∑ r ∈ typeIMixedDyad S' 1 j, f r‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range (shortOuterCount Y), B := by
      apply Finset.sum_le_sum
      intro j hj
      let R : ℝ := 2^j
      let U : ℝ := X/R
      let P := typeIMixedDyad S' 1 j
      have hR : 1 ≤ R := one_le_pow₀ (by norm_num)
      have hRp : 0 < R := zero_lt_one.trans_le hR
      have hRY : R ≤ 2*Y := (shortOuterCount_scale hYp (Finset.mem_range.mp hj)).le
      have hrange' : (R ≤ X^(2/5:ℝ) ∧ T ≤ X^(1/100:ℝ)) ∨
          (R ≤ X^(1/3-κ/2) ∧ T ≤ X^(1/6+ρ)) := by
        exact hrange.imp (fun h => ⟨hRY.trans h.1,h.2⟩) (fun h => ⟨hRY.trans h.1,h.2⟩)
      have hRX : R ≤ X := by
        rcases hrange' with h | h
        · exact h.1.trans (by simpa only [Real.rpow_one] using
            Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num : (2/5:ℝ) ≤ 1))
        · exact h.1.trans (by simpa only [Real.rpow_one] using
            Real.rpow_le_rpow_of_exponent_le hX1 (show 1/3-κ/2 ≤ 1 by linarith))
      have hU : 1 ≤ U := (le_div_iff₀ hRp).mpr (by simpa using hRX)
      have hRU : R*U = X := by dsimp [U]; field_simp
      have hP (r : Eisenstein) (hr : r ∈ P) : primary r ∧ R ≤ norm r ∧ norm r ≤ 2*R := by
        obtain ⟨hrS,hrj⟩ := Finset.mem_filter.mp hr
        have hn := typeIMixedDyadIndex_bounds (show (0:ℝ) < 1 by norm_num) (hS' r hrS).2.2.1
        rw [hrj] at hn
        exact ⟨(hS' r hrS).1,by simpa only [one_mul] using hn.1,
          by simpa only [one_mul] using hn.2.le⟩
      have hmassP : (∑ r ∈ P, ‖α r‖) ≤ D*R*(Real.log X)^d :=
        hmass X R P α hR hRX hlog
          (fun r hr => ⟨(hP r hr).1,(hS' r (Finset.mem_filter.mp hr).1).2.1,(hP r hr).2.2⟩)
          (fun r hr => hα r (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).1)
      have he : (∑ r ∈ P, f r) = productTypeICutoffWindow w P α W 0
          (Real.exp hW.radius) X U H T X₀ := by
        rw [productTypeICutoffWindow_fourier w P α W 0 _ _ _ _ _ hH]
        apply Finset.sum_congr rfl
        intro r hr
        dsimp only [f]
        congr 1
        exact typeI_gaussWindow_envelope_row 0 (W (w r)) (Real.exp_pos _).le hR
          (zero_lt_one.trans_le hU) hRU (hW.upper_support (w r)) H T X₀
          (hP r hr).1 (hP r hr).2.1
      rw [he]
      exact hbound w P α X R U T H X₀ hR hU hRU hlog hLT hX₀ hrange' hP hmassP
    _ = (shortOuterCount Y:ℝ)*B := by simp
    _ ≤ (L*(1+Real.log Y))*B := mul_le_mul_of_nonneg_right (hcount Y hY) hB
    _ = _ := by dsimp [B]; ring

end CubicFirstMoment

end

end OAI
