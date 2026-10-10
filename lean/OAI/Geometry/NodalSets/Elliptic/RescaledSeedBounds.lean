import OAI.Geometry.NodalSets.Elliptic.SeedDerivativeBounds
import OAI.Geometry.NodalSets.Elliptic.SpatialJetFamily
import OAI.Geometry.NodalSets.Elliptic.UniformSmoothBounds

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
open scoped ContDiff
noncomputable section

def rescaledSeed (S0 T0 S : Coord → ℝ) (N s σ : ℝ) (x v : Coord) : ℝ :=
  oscillatorySeed S0 T0 N (x+(N*s)⁻¹ • v) /
    (σ*Real.exp (fderiv ℝ S x v / s))

def rescaledSeedPhase (S0 T0 : Coord → ℝ) (p : Coord × ℝ) (v : Coord) : ℂ :=
  (S0 (p.1+p.2 • v):ℂ)+Complex.I*(T0 (p.1+p.2 • v):ℂ)

def rescaledSeedNormalizer (S : Coord → ℝ) (p : Coord × ℝ) (v : Coord) : ℂ :=
  (Real.exp (-p.2 * fderiv ℝ S p.1 v):ℂ)

lemma rescaledSeedPhase_smooth (S0 T0 : Coord → ℝ)
    (hS0 : ContDiff ℝ ∞ S0) (hT0 : ContDiff ℝ ∞ T0) :
    ContDiff ℝ ∞ (Function.uncurry (rescaledSeedPhase S0 T0)) := by
  have ha : ContDiff ℝ ∞ (fun z : (Coord × ℝ) × Coord ↦ z.1.1+z.1.2 • z.2) :=
    contDiff_fst.fst.add (contDiff_fst.snd.smul contDiff_snd)
  exact (Complex.ofRealCLM.contDiff.comp (hS0.comp ha)).add
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (hT0.comp ha)))

lemma rescaledSeedNormalizer_smooth (S : Coord → ℝ) (hS : ContDiff ℝ ∞ S) :
    ContDiff ℝ ∞ (Function.uncurry (rescaledSeedNormalizer S)) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ S) := hS.fderiv_right (by simp)
  exact Complex.ofRealCLM.contDiff.comp
    ((contDiff_fst.snd.neg.mul ((hd.comp contDiff_fst.fst).clm_apply contDiff_snd)).exp)

lemma rescaledSeed_representation (S0 T0 S : Coord → ℝ) (N s σ : ℝ) (x : Coord) :
    rescaledSeed S0 T0 S N s σ x = fun v ↦ σ⁻¹ *
      (rescaledSeedNormalizer S (x,s⁻¹) v *
        waveExp (rescaledSeedPhase S0 T0 (x,(N*s)⁻¹)) N v).re := by
  funext v
  change oscillatorySeed S0 T0 N (x+(N*s)⁻¹ • v) /
    (σ*Real.exp (fderiv ℝ S x v / s)) = σ⁻¹ *
      ((Real.exp (-s⁻¹ * fderiv ℝ S x v):ℂ) *
        waveExp (rescaledSeedPhase S0 T0 (x,(N*s)⁻¹)) N v).re
  rw [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  have hw : (waveExp (rescaledSeedPhase S0 T0 (x,(N*s)⁻¹)) N v).re =
      oscillatorySeed S0 T0 N (x+(N*s)⁻¹ • v) := by
    simp [waveExp,rescaledSeedPhase,oscillatorySeed,Complex.exp_re]
  rw [hw,neg_mul,Real.exp_neg]
  simp [div_eq_mul_inv,mul_comm,mul_left_comm]

theorem rescaledSeed_derivative_bound (S0 T0 S : Coord → ℝ)
    (hS0 : ContDiff ℝ ∞ S0) (hT0 : ContDiff ℝ ∞ T0) (hS : ContDiff ℝ ∞ S)
    {Q : Set Coord} (hQ : IsCompact Q) (R : ℝ) (k : ℕ) :
    ∃ C > 0, ∀ (N s σ : ℝ), 1 ≤ N → 1 ≤ s → 0 < σ →
      ∀ x ∈ Q, ∀ v : Coord, ‖v‖ ≤ R →
        ‖iteratedFDeriv ℝ k (rescaledSeed S0 T0 S N s σ x) v‖ ≤
          C*N^k*Real.exp (N*S0 (x+(N*s)⁻¹ • v))/σ := by
  have hp := rescaledSeedPhase_smooth S0 T0 hS0 hT0
  have ha := rescaledSeedNormalizer_smooth S hS
  obtain ⟨D,hD,hd⟩ := compact_smooth_derivative_bound (rescaledSeedPhase S0 T0) k
    (fun j _ ↦ (smooth_spatial_iteratedFDeriv _ hp j).continuous)
    (Q ×ˢ Icc (0:ℝ) 1) (hQ.prod isCompact_Icc) R
  obtain ⟨A,hA,ha'⟩ := compact_smooth_derivative_bound (rescaledSeedNormalizer S) k
    (fun j _ ↦ (smooth_spatial_iteratedFDeriv _ ha j).continuous)
    (Q ×ˢ Icc (0:ℝ) 1) (hQ.prod isCompact_Icc) R
  let B : ℝ := (k.factorial:ℝ)*(D+1)^k
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨2^k*A*B,by positivity,?_⟩
  intro N s σ hN hs hσ x hx v hv
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hr : (N*s)⁻¹ ∈ Icc (0:ℝ) 1 :=
    ⟨by positivity,(inv_le_one₀ (mul_pos hN0 hs0)).mpr (one_le_mul_of_one_le_of_one_le hN hs)⟩
  have ht : s⁻¹ ∈ Icc (0:ℝ) 1 := ⟨by positivity,(inv_le_one₀ hs0).mpr hs⟩
  let phi := rescaledSeedPhase S0 T0 (x,(N*s)⁻¹)
  let amp := rescaledSeedNormalizer S (x,s⁻¹)
  have hphi : ContDiff ℝ ∞ phi := hp.comp (contDiff_const.prodMk contDiff_id)
  have hamp : ContDiff ℝ ∞ amp := ha.comp (contDiff_const.prodMk contDiff_id)
  have he (j : ℕ) (hj : j ≤ k) :
      ‖iteratedFDeriv ℝ j (waveExp phi N) v‖ ≤ B*N^j*Real.exp (N*(phi v).re) := by
    apply (waveExp_derivative_bound hphi j v (by linarith : 1 ≤ D+1) hN
      (fun i _ hi ↦ (hd _ ⟨hx,hr⟩ v hv i (hi.trans hj)).trans (by linarith))).trans
    have hf : (j.factorial:ℝ) ≤ k.factorial := by exact_mod_cast Nat.factorial_le hj
    have hpw : (D+1)^j ≤ (D+1)^k := pow_le_pow_right₀ (by linarith) hj
    dsimp [B]
    gcongr
  have hm := mul_derivative_power_bound hamp (waveExp_contDiff hphi N) k v hA.le hN0.le
    (fun j hj ↦ (ha' _ ⟨hx,ht⟩ v hv j hj).trans
      (le_mul_of_one_le_right hA.le (one_le_pow₀ hN))) he
  have hre : ContDiff ℝ ∞ (fun z ↦ (amp z*waveExp phi N z).re) :=
    Complex.reCLM.contDiff.comp (hamp.mul (waveExp_contDiff hphi N))
  rw [rescaledSeed_representation]
  change ‖iteratedFDeriv ℝ k (fun z ↦ σ⁻¹ • (amp z*waveExp phi N z).re) v‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' (hre.of_le (by
    exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top))).contDiffAt,norm_smul,
    Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hσ)]
  have hreal := realPart_iterated_norm_le (fun z ↦ amp z*waveExp phi N z) v
    (hamp.mul (waveExp_contDiff hphi N)).contDiffAt k
  have hh := mul_le_mul_of_nonneg_left (hreal.trans hm) (inv_nonneg.mpr hσ.le)
  simpa [phi,rescaledSeedPhase,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using hh

end
end Yau.Geometry

end OAI
