import Mathlib
import OAI.Probability.LogConcave.Sampling.AnalyticBase

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators ENNReal

theorem TameAt.reindex {S T : Type} [Fintype S] [Fintype T] {d : ℕ}
    (μ : Measure (Point d)) (F : (S → Fin d) → Point d → ℝ)
    (hF : ∀c,PolySmooth (F c)) (e : S ≃ T)
    {k C : ℕ} {R : ℝ≥0∞} (hC : 20≤C) (hf : TameAt μ F k C R) :
    TameAt μ (fun a => F (a ∘ e)) k (4*(C+Fintype.card T+1)) R := by
  intro j n hn
  let q := 4*(C+Fintype.card T+1)
  let D : ℝ≥0∞ := (q:ℝ≥0∞)*ENNReal.ofReal (analyticBase d j n)
  have hq : C+Fintype.card T+1≤q := by dsimp [q]; omega
  have hD2 : 2≤D := by
    simpa only [mul_one] using mul_le_mul' (show (2:ℝ≥0∞)≤q by exact_mod_cast (by omega : 2≤q)) (ofReal_base_one_le d j n)
  have hD : 1≤D := (by norm_num : (1:ℝ≥0∞)≤2).trans hD2
  have hpoint (x : Point d) : spatialEnvelope (fun a => F (a ∘ e)) j x≤
      (2:ℝ)^(j+Fintype.card T)*spatialEnvelope F j x := by
    have hh := spatialTensor_allSplit_relabel F (fun c => (hF c).smooth) e (Equiv.refl (Fin j))
      (List.finRange j) (List.finRange j) (by simp) x _ (TensorEnergy.allSplitBound_envelope _)
    have hb := TensorEnergy.splitEnvelope_le_pow (spatialEnvelope_nonneg F j x) hh
    simpa only [spatialEnvelope,Fintype.card_sum,Fintype.card_fin] using hb
  have hm := hf.with_base j n hn D (mul_le_mul' (by exact_mod_cast (by omega : C≤q)) le_rfl)
  have hs := natural_moment_const_mul (spatialEnvelope_nonneg F j) n
    (by positivity : (0:ℝ)≤2^(j+Fintype.card T)) _ hm
  apply (lintegral_mono (fun x => pow_le_pow_left' (ENNReal.ofReal_le_ofReal (hpoint x)) n)).trans
  apply hs.trans
  apply pow_le_pow_left'
  simp only [ENNReal.ofReal_pow (by norm_num : (0:ℝ)≤2),ENNReal.ofReal_ofNat]
  calc
    _ ≤ D^(j+Fintype.card T)*(D^(C*(j+1))*R^(k+j)) := mul_le_mul' (pow_le_pow_left' hD2 _) le_rfl
    _ = D^(j+Fintype.card T+C*(j+1))*R^(k+j) := by rw [pow_add]; ring
    _ ≤ D^(q*(j+1))*R^(k+j) := by
      apply mul_le_mul' _ le_rfl
      apply pow_le_pow_right₀ hD
      have hh := Nat.mul_le_mul_right (j+1) hq
      nlinarith

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped NNReal

lemma normalizedTensorMajorant_le {a : ℝ} (ha : 0 < a) (n : ℕ) :
    normalizedTensorMajorant n a ≤
      (10*((n:ℝ)+1))^(4*(n+1))*((Real.sqrt a)⁻¹)^(n-2) := by
  let B : ℝ := 10*((n:ℝ)+1)
  have hB : 1≤B := by dsimp [B]; nlinarith [Nat.cast_nonneg (α:=ℝ) n]
  have hnB : (n:ℝ)≤B := by dsimp [B]; nlinarith [Nat.cast_nonneg (α:=ℝ) n]
  have hn1B : (n:ℝ)+1≤B := by dsimp [B]; nlinarith [Nat.cast_nonneg (α:=ℝ) n]
  have hpB : 2*Real.pi^2≤B^2 := by
    have hb10 : 10≤B := by dsimp [B]; nlinarith [Nat.cast_nonneg (α:=ℝ) n]
    nlinarith [Real.pi_lt_four,Real.pi_pos]
  have hfac : (n.factorial:ℝ)≤(n:ℝ)^n := by exact_mod_cast Nat.factorial_le_pow n
  have hfB : (n.factorial:ℝ)≤B^n :=
    hfac.trans (pow_le_pow_left₀ (Nat.cast_nonneg n) hnB n)
  have hhf : ((n.factorial:ℝ)^2)^2≤B^(4*n) := by
    have hh := pow_le_pow_left₀ (by positivity : (0:ℝ)≤n.factorial) hfB 4
    simpa only [←pow_mul,show 2*2=4 from rfl,Nat.mul_comm n 4] using hh
  have hhp : (2*Real.pi^2)^n≤B^(2*n) := by
    simpa only [←pow_mul] using pow_le_pow_left₀ (by positivity : 0≤2*Real.pi^2) hpB n
  have hhn : (((n+1:ℕ):ℝ)^(2*(n+1)))≤B^(2*(n+1)) := by
    simpa only [Nat.cast_add,Nat.cast_one] using pow_le_pow_left₀ (by positivity : 0≤(n:ℝ)+1) hn1B (2*(n+1))
  have hnum : (((n+1:ℕ):ℝ)^(2*(n+1))*(2*Real.pi^2)^n*((n.factorial:ℝ)^2)^2)≤
      B^(8*(n+1)) := by
    calc
      _ ≤ B^(2*(n+1))*B^(2*n)*B^(4*n) :=
        mul_le_mul (mul_le_mul hhn hhp (by positivity) (by positivity)) hhf
          (by positivity) (by positivity)
      _ = B^(2*(n+1)+2*n+4*n) := by rw [pow_add,pow_add]
      _ ≤ _ := pow_le_pow_right₀ hB (by omega)
  have hR : (((Real.sqrt a)⁻¹)^(n-2))^2=(a^(n-2))⁻¹ := by
    calc
      _ = (((Real.sqrt a)⁻¹)^2)^(n-2) := by simp only [←pow_mul]; congr 1; omega
      _ = (a⁻¹)^(n-2) := by rw [inv_pow,Real.sq_sqrt ha.le]
      _ = _ := inv_pow a (n-2)
  unfold normalizedTensorMajorant
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity,?_⟩
  change _≤(B^(4*(n+1))*((Real.sqrt a)⁻¹)^(n-2))^2
  conv_rhs => rw [mul_pow,hR,←pow_mul,show 4*(n+1)*2=8*(n+1) from by omega,←div_eq_mul_inv]
  exact div_le_div_of_nonneg_right hnum (pow_nonneg ha.le _)

end LogConcaveSampling

end

end

end

end OAI
