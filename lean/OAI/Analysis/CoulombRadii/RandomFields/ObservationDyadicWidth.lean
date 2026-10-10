import Mathlib
import OAI.Analysis.CoulombRadii.RandomFields.PhysicalRetainedLikelihood

namespace OAI

noncomputable section

section
open MeasureTheory Filter
open scoped BigOperators Topology Classical
namespace NeutralAtom

lemma observationWidthSquareSum_dyadic {r : ℝ} (hr : 0<r) (J : ℕ) :
    observationWidthSquareSum (fun k : Fin J => (r*2^k.val)^(101/100:ℝ))≤
      (4/3:ℝ)*((r^(101/100:ℝ))⁻¹)^2 := by
  have hg : (∑ k : Fin J, (1/4:ℝ)^k.val)≤4/3 := by
    rw [Fin.sum_univ_eq_sum_range]
    have H := geom_sum_mul_neg (1/4:ℝ) J
    have hn := pow_nonneg (by norm_num : (0:ℝ)≤1/4) J
    nlinarith
  have hp := Real.rpow_pos_of_pos hr (101/100:ℝ)
  unfold observationWidthSquareSum
  calc
    _ ≤ ∑ k : Fin J, ((r^(101/100:ℝ))⁻¹)^2*(1/4:ℝ)^k.val := by
      apply Finset.sum_le_sum
      intro k _
      have hpow : (2:ℝ)^k.val≤((2:ℝ)^k.val)^(101/100:ℝ) :=
        Real.self_le_rpow_of_one_le (one_le_pow₀ (by norm_num)) (by norm_num)
      have hwidth : r^(101/100:ℝ)*2^k.val≤(r*2^k.val)^(101/100:ℝ) := by
        rw [Real.mul_rpow hr.le (by positivity)]
        exact mul_le_mul_of_nonneg_left hpow hp.le
      have hi : ((r*2^k.val)^(101/100:ℝ))⁻¹≤(r^(101/100:ℝ)*2^k.val)⁻¹ :=
        (inv_le_inv₀ (Real.rpow_pos_of_pos (by positivity) _) (by positivity)).2 hwidth
      convert pow_le_pow_left₀ (inv_nonneg.mpr (Real.rpow_nonneg (by positivity) _)) hi 2 using 1
      have he : ((2:ℝ)^k.val)⁻¹^2 = (1/4:ℝ)^k.val := by
        rw [← inv_pow, ← pow_mul, show k.val*2=2*k.val from Nat.mul_comm _ _, pow_mul, inv_pow]
        norm_num
      rw [mul_inv_rev, mul_pow, he]
      ring
    _ = ((r^(101/100:ℝ))⁻¹)^2*(∑ k : Fin J, (1/4:ℝ)^k.val) := by rw [Finset.mul_sum]
    _ ≤ ((r^(101/100:ℝ))⁻¹)^2*(4/3:ℝ) :=
      mul_le_mul_of_nonneg_left hg (sq_nonneg _)
    _ = _ := mul_comm _ _

lemma observationWidthSquareSum_retained_dyadic {r : ℝ} (hr : 0<r) (J j : ℕ) :
    observationWidthSquareSum (fun k : RetainedScales J j =>
      (r*2^k.val.val)^(101/100:ℝ))≤
      (4/3:ℝ)*(((r*2^j)^(101/100:ℝ))⁻¹)^2 := by
  let sh : RetainedScales J j → Fin J :=
    fun k => ⟨k.val.val-j, lt_of_le_of_lt (Nat.sub_le _ _) k.val.isLt⟩
  have hs : Function.Injective sh := by
    intro k l h
    apply Subtype.ext
    apply Fin.ext
    have he := congrArg Fin.val h
    dsimp [sh] at he
    have hk := k.property
    have hl := l.property
    omega
  have hg : (∑ k : RetainedScales J j, (1/4:ℝ)^(k.val.val-j))≤4/3 := by
    calc
      _ = ∑ k ∈ Finset.univ.image sh, (1/4:ℝ)^k.val := by
        rw [Finset.sum_image (by intro a _ b _ hab; exact hs hab)]
      _ ≤ ∑ k : Fin J, (1/4:ℝ)^k.val :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => by positivity)
      _ ≤ 4/3 := by
        rw [Fin.sum_univ_eq_sum_range]
        have H := geom_sum_mul_neg (1/4:ℝ) J
        have hn := pow_nonneg (by norm_num : (0:ℝ)≤1/4) J
        nlinarith
  have hp := Real.rpow_pos_of_pos (by positivity : 0<r*2^j) (101/100:ℝ)
  unfold observationWidthSquareSum
  calc
    _ ≤ ∑ k : RetainedScales J j,
        (((r*2^j)^(101/100:ℝ))⁻¹)^2*(1/4:ℝ)^(k.val.val-j) := by
      apply Finset.sum_le_sum
      intro k _
      have heq : r*2^j*2^(k.val.val-j)=r*2^k.val.val := by
        rw [mul_assoc,←pow_add,Nat.add_sub_of_le k.property]
      have hpow : (2:ℝ)^(k.val.val-j)≤((2:ℝ)^(k.val.val-j))^(101/100:ℝ) :=
        Real.self_le_rpow_of_one_le (one_le_pow₀ (by norm_num)) (by norm_num)
      have hfactor : (r*2^k.val.val)^(101/100:ℝ)=
          (r*2^j)^(101/100:ℝ)*((2:ℝ)^(k.val.val-j))^(101/100:ℝ) := by
        rw [←heq]
        exact Real.mul_rpow (by positivity) (by positivity)
      have hwidth : (r*2^j)^(101/100:ℝ)*2^(k.val.val-j)≤(r*2^k.val.val)^(101/100:ℝ) := by
        rw [hfactor]
        exact mul_le_mul_of_nonneg_left hpow hp.le
      have hi : ((r*2^k.val.val)^(101/100:ℝ))⁻¹≤
          ((r*2^j)^(101/100:ℝ)*2^(k.val.val-j))⁻¹ :=
        (inv_le_inv₀ (Real.rpow_pos_of_pos (by positivity) _) (by positivity)).2 hwidth
      convert pow_le_pow_left₀ (inv_nonneg.mpr (Real.rpow_nonneg (by positivity) _)) hi 2 using 1
      have he : ((2:ℝ)^(k.val.val-j))⁻¹^2=(1/4:ℝ)^(k.val.val-j) := by
        rw [←inv_pow,←pow_mul,Nat.mul_comm (k.val.val-j) 2,pow_mul,inv_pow]
        norm_num
      rw [mul_inv_rev,mul_pow,he]
      ring
    _ = (((r*2^j)^(101/100:ℝ))⁻¹)^2*(∑ k : RetainedScales J j, (1/4:ℝ)^(k.val.val-j)) := by
      rw [Finset.mul_sum]
    _ ≤ (((r*2^j)^(101/100:ℝ))⁻¹)^2*(4/3:ℝ) :=
      mul_le_mul_of_nonneg_left hg (sq_nonneg _)
    _ = _ := mul_comm _ _
end NeutralAtom

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace NeutralAtom

theorem physical_dyadicTailEvent_state {n J : ℕ}
    (Z : ℕ) (hZ : 1≤Z) {ψ : Wavefunction n} {g : Gradient n}
    (hd : FormDomain ψ g) (hn : normSquared ψ=1)
    (hmin : ∀ (χ : Wavefunction n) (h : Gradient n), FormDomain χ h → normSquared χ=1 → energy Z ψ g≤energy Z χ h)
    {E D₀ : ℝ} (hbase : energy Z ψ g≤E+D₀)
    {r₀ : ℝ} (hr₀ : 0<r₀) (j : ℕ)
    {B : Set (Fin J → UnorderedArray n)} (hB : MeasurableSet B)
    (hp : 0<(observationLaw J (rawLaw ψ)).real
      (tailObservation (fun k : Fin J => r₀*2^k.val) j ⁻¹' B)) :
    ∃ u : Coulomb.H1Vector n, Coulomb.Antisymmetric u ∧ Coulomb.mass u=1 ∧
      Coulomb.form (Coulomb.atom Z hZ) u≤E+(D₀+observationEventEnergyConstant*
        ((4/3:ℝ)*(((r₀*2^j)^(101/100:ℝ))⁻¹)^2)*
        (1-Real.log ((observationLaw J (rawLaw ψ)).real
          (tailObservation (fun k : Fin J => r₀*2^k.val) j ⁻¹' B)))^5) ∧
      ∀ F : Configuration n → ℝ, Measurable F → (∃ C : ℝ, ∀ x, ‖F x‖≤C) →
      Coulomb.potentialForm (fun x => F ((flattenConfiguration n).symm x)) u=
        ((observationLaw J (rawLaw ψ)).real
          (tailObservation (fun k : Fin J => r₀*2^k.val) j ⁻¹' B))⁻¹*
          ∫ sample, (tailObservation (fun k : Fin J => r₀*2^k.val) j ⁻¹' B).indicator
            (fun z => F z.1) sample ∂observationLaw J (rawLaw ψ) := by
  obtain ⟨u,hu,hum,hue,hlaw⟩ := physical_retainedTailEvent_state Z hZ hd hn hmin hbase
    (fun k : Fin J => r₀*2^k.val) (fun k => by positivity) j hB hp
  refine ⟨u,hu,hum,hue.trans ?_,hlaw⟩
  have := rawLaw_isProbability hd.2.2.1 hn
  have h1 : (observationLaw J (rawLaw ψ)).real
      (tailObservation (fun k : Fin J => r₀*2^k.val) j ⁻¹' B)≤1 := measureReal_le_one
  have hl := Real.log_nonpos hp.le h1
  have hlog : 0≤1-Real.log ((observationLaw J (rawLaw ψ)).real
      (tailObservation (fun k : Fin J => r₀*2^k.val) j ⁻¹' B)) := by linarith
  have hc := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (observationWidthSquareSum_retained_dyadic hr₀ J j)
        observationEventEnergyConstant_pos.le)
      (pow_nonneg hlog 5)
  linarith
end NeutralAtom

end

end OAI
