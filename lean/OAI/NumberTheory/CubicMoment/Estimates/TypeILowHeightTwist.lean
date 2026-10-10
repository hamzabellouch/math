import OAI.NumberTheory.CubicMoment.Estimates.LogarithmicPhase
import OAI.NumberTheory.CubicMoment.Estimates.TypeILow

namespace OAI

/-! The low-height Type-I estimate with its actual Mellin phase.
The original height-dependent squarefree model is retained. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma metaplecticAngularSmoothSum_phase (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ)
    {U : ℝ} (hU : 0 < U) (t : ℝ) :
    metaplecticAngularSmoothSum r ℓ W U t =
      mellinPhase t U*metaplecticAngularSmoothSum r ℓ (fun x => W x*mellinPhase t x) U 0 := by
  unfold metaplecticAngularSmoothSum
  rw [←tsum_mul_left]
  apply tsum_congr
  intro u
  have hn : 0 < norm (u:Eisenstein) := norm_pos_of_ne_zero (primary_ne_zero u.property)
  have hphase : mellinPhase t (norm (u:Eisenstein)) =
      mellinPhase t U*mellinPhase t (norm (u:Eisenstein)/U) := by
    rw [←mellinPhase_mul_pos t hU (div_pos hn hU),mul_div_cancel₀ _ hU.ne']
  rw [hphase]
  simp only [mellinPhase,zero_mul,Complex.ofReal_zero,Complex.exp_zero,mul_one]
  ring

def lowTwistedTypeIRow (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ) (U t : ℝ) : ℂ :=
  metaplecticAngularSmoothSum r ℓ W U t-
    mellinPhase t U*angularSmoothModel r ℓ (fun x => W x*mellinPhase t x) U

theorem typeI_low_height_twist
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hV : MetaplecticVoronoiInput a)
    {γ : Type*} {Y : γ → ℝ} {W : γ → ℝ → ℂ} (hW : LogarithmicWeightFamily Y W)
    (ℓ : ℤ) (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ) (-σ-1/6))
    {B A : ℝ} (hB : 1 ≤ B) (hA : 0 ≤ A) (k d : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (w : Eisenstein → γ) (S : Finset Eisenstein)
      (α : Eisenstein → ℂ) (X R U t : ℝ),
      2 ≤ X → B ≤ X → 1 ≤ R → 1 ≤ U → R*U = X → R ≤ X^(51/100:ℝ) →
      (∀ r ∈ S, primary r ∧ R ≤ norm r ∧ norm r ≤ 2*R) →
      (∀ r ∈ S, Y (w r) = X) →
      (∀ r ∈ S, ∀ x : ℝ, B < x → W (w r) x = 0) →
      (∀ r ∈ S, ‖α r‖ ≤ A*((metaplecticPrimaryDivisors r).card:ℝ)^k) →
      |t| ≤ (1+Real.log X)^d →
      ‖∑ r ∈ S, α r*lowTwistedTypeIRow r ℓ (W (w r)) U t‖ ≤
        K*X^(5/6-1/100:ℝ) := by
  obtain ⟨K,hK,hbound⟩ := typeI_low_of_published hV (hW.phase d) ℓ hGamma hB hA k
  refine ⟨K,hK,?_⟩
  intro w S α X R U t hX hBX hR hU hRU hRhi hS hY hcut hα ht
  let v : Eisenstein → logarithmicPhaseIndex Y d := fun r =>
    ⟨(w r,if r ∈ S then t else 0),by
      by_cases hr : r ∈ S
      · simpa only [ite_eq_left hr,hY r hr] using ht
      · simp only [ite_eq_right hr,abs_zero]
        exact pow_nonneg (by linarith [Real.log_nonneg (hW.length_one (w r))]) _⟩
  have hv (r : Eisenstein) (hr : r ∈ S) :
      logarithmicPhaseWeight Y W d (v r) = fun x => W (w r) x*mellinPhase t x := by
    funext x
    simp only [logarithmicPhaseWeight,v,ite_eq_left hr]
  have hb := hbound v S α X R U hX hBX hR hU hRU hRhi hS
    (fun r hr => hY r hr)
    (fun r hr x hx => by simp only [hv r hr,hcut r hr x hx,zero_mul]) hα
  have he : (∑ r ∈ S, α r*lowTwistedTypeIRow r ℓ (W (w r)) U t) =
      mellinPhase t U*∑ r ∈ S, α r*(metaplecticAngularSmoothSum r ℓ
        (logarithmicPhaseWeight Y W d (v r)) U 0-
        angularSmoothModel r ℓ (logarithmicPhaseWeight Y W d (v r)) U) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [hv r hr]
    unfold lowTwistedTypeIRow
    rw [metaplecticAngularSmoothSum_phase r ℓ _ (zero_lt_one.trans_le hU)]
    ring
  rw [he,norm_mul,mellinPhase_norm,one_mul]
  exact hb

end CubicFirstMoment

end

end OAI
