import Mathlib
import OAI.GroupTheory.SimpleAmenable.RandomFields.CovarianceLimit
import OAI.GroupTheory.SimpleAmenable.RandomFields.CompactSignalEnergy

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section SourceSignalRemainder
open Classical Filter
open scoped Topology

noncomputable def sourceSignalDelta (D : ℕ) (η : ℝ) (n : ℕ) : ℝ :=
  38880/((D:ℝ)*Real.sqrt ((2:ℝ)^n*η))

noncomputable def sourceSignalError (A B Cv Ca Cr η κ : ℝ) (D n : ℕ) : ℝ :=
  Real.sqrt A*(Cv*η*(1+sourceSignalDelta D η n)+Ca*sourceSignalDelta D η n)+
    Real.sqrt B*Real.sqrt (κ+(1/4:ℝ)^n)*(Cr*Ca)

theorem sourceSignalDelta_nonneg (D n : ℕ) (η : ℝ) : 0 ≤ sourceSignalDelta D η n := by
  unfold sourceSignalDelta; positivity

theorem sourceSignalDelta_tendsto {D : ℕ} (hD : 0<D) {η : ℝ} (hη : 0<η) :
    Tendsto (sourceSignalDelta D η) atTop (nhds 0) := by
  have ht := (tendsto_pow_atTop_atTop_of_one_lt (show (1:ℝ)<2 by norm_num)).atTop_mul_const hη
  have hd : (0:ℝ)<D := by exact_mod_cast hD
  have ht' := (Real.tendsto_sqrt_atTop.comp ht).const_mul_atTop hd
  have hh := ht'.inv_tendsto_atTop.const_mul 38880
  change Tendsto (fun n => 38880/((D:ℝ)*Real.sqrt ((2:ℝ)^n*η))) atTop (nhds 0)
  simpa only [div_eq_mul_inv,mul_zero,Function.comp_apply,Pi.inv_apply] using hh

theorem sourceSignalDelta_bound {D n i : ℕ} {η : ℝ} (hD : 0<D) (hη : 0<η)
    (hi : n ≤ i) : 38880/((D:ℝ)*Real.sqrt ((2:ℝ)^i*η)) ≤ sourceSignalDelta D η n := by
  have hd : (0:ℝ)<D := by exact_mod_cast hD
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hi) hη.le)) hd.le

theorem sourceSignalError_nonneg {A B Cv Ca Cr η κ : ℝ} (hCv : 0≤Cv) (hCa : 0≤Ca)
    (hCr : 0≤Cr) (hη : 0≤η) (D n : ℕ) : 0 ≤ sourceSignalError A B Cv Ca Cr η κ D n := by
  unfold sourceSignalError
  positivity [sourceSignalDelta_nonneg D n η]

theorem sourceSignalError_tendsto {D : ℕ} (hD : 0<D) (A B Cv Ca Cr κ : ℝ)
    {η : ℝ} (hη : 0<η) :
    Tendsto (sourceSignalError A B Cv Ca Cr η κ D) atTop
      (nhds (Real.sqrt A*Cv*η+Real.sqrt B*Cr*Ca*Real.sqrt κ)) := by
  have hδ := sourceSignalDelta_tendsto hD hη
  have hs : Tendsto (fun n : ℕ => (1/4:ℝ)^n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hh := ((hδ.const_add 1).const_mul (Cv*η) |>.add (hδ.const_mul Ca) |>.const_mul (Real.sqrt A)).add
    (((hs.const_add κ).sqrt.const_mul (Real.sqrt B)).mul_const (Cr*Ca))
  change Tendsto (fun n => Real.sqrt A*(Cv*η*(1+sourceSignalDelta D η n)+Ca*sourceSignalDelta D η n)+
    Real.sqrt B*Real.sqrt (κ+(1/4:ℝ)^n)*(Cr*Ca)) atTop _
  simpa only [mul_zero,add_zero,mul_one,mul_assoc,mul_left_comm,mul_comm] using hh

theorem sourceSignalBound_tendsto {D : ℕ} (hD : 0<D) (A B Cv Ca Cr C κ : ℝ)
    {η : ℝ} (hη : 0<η) :
    Tendsto (fun n => C/(1+sourceDyadicMass n)+sourceSignalError A B Cv Ca Cr η κ D n)
      atTop (nhds (Real.sqrt A*Cv*η+Real.sqrt B*Cr*Ca*Real.sqrt κ)) := by
  have hm : Tendsto (fun n => 1+sourceDyadicMass n) atTop atTop :=
    tendsto_atTop_mono (fun n => by linarith : ∀n,sourceDyadicMass n ≤ 1+sourceDyadicMass n) sourceDyadicMass_tendsto
  have ht := hm.inv_tendsto_atTop.const_mul C
  have ht' : Tendsto (fun n => C/(1+sourceDyadicMass n)) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Pi.inv_apply] using ht
  simpa only [zero_add] using ht'.add (sourceSignalError_tendsto hD A B Cv Ca Cr κ hη)

end SourceSignalRemainder

section PolygonSignalInverse
open Classical Filter Matrix
open scoped Topology

theorem sourceFlagMatrix_inverse_signal {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (ψ χ : (ℝ×ℝ) → ℝ)
    (hψ : ContDiff ℝ 2 ψ) (hsψ : HasCompactSupport ψ) (q K L : ℝ)
    (hL : 0<L) (hKL : K+2 ≤ L)
    (hcompact : ∀x,K ≤ ‖x‖ → ψ x=0)
    (hχ : ∀x,χ x∈Set.Icc (0:ℝ) 1)
    (hχ₁ : ∀x,‖x‖ ≤ K+2 → χ x=1)
    (hχc : ∀x,L ≤ ‖x‖ → χ x=0) :
    ∃C₁ C₂ : ℝ,0≤C₁ ∧ 0≤C₂ ∧ ∀η : ℝ,0<η → η≤1 → ∀κ : ℝ,0<κ →
      ∀ε : ℝ,0<ε → ∀ᶠn : ℕ in atTop,
        ∀T : Finset (FlagSite a m D v),
          flagBoxFinset hD (mul_pos (sourceDyadicN_pos n) hL)⊆T →
          finiteL2Norm (((1 : Matrix T T ℝ)+(Matrix.of (fun (z w : T) => sourceFlagMatrix (v:=v) χ ((D:ℝ)^4/5) η κ n z.val w.val)))⁻¹*ᵥ
            (fun z : T => flagSignalDifference (v:=v) hD g (fun x => q+ψ x) (sourceDyadicN n) z.val)) ≤
              C₁*η+C₂*Real.sqrt κ+ε := by
  obtain ⟨R,Q,Cv,Ca,hR,hQ,hCv,hCa,happrox⟩ :=
    polygon_signal_approx_identity (v:=v) hD g ψ χ hψ hsψ q K L hL hKL hcompact hχ hχ₁ hχc
  obtain ⟨C,hC,henergy⟩ := compactSignal_energy (v:=v) hD g ψ hψ hsψ q
  let A := flagVolumeConstant m D L
  let B := flagExceptionalConstant a m D L
  let Cr := flagRowSumConstant D
  have hA : 0≤A := by dsimp [A,flagVolumeConstant]; positivity
  have hB : 0≤B := by dsimp [B,flagExceptionalConstant]; positivity
  have hCr : 0≤Cr := by dsimp [Cr,flagRowSumConstant]; positivity
  refine ⟨Real.sqrt A*Cv,Real.sqrt B*Cr*Ca,by positivity,by positivity,
    fun η hη hη₁ κ hκ ε hε => ?_⟩
  have ht := sourceSignalBound_tendsto hD A B Cv Ca Cr C κ hη
  have ht' := ht.eventually_lt_const
    (show Real.sqrt A*Cv*η+Real.sqrt B*Cr*Ca*Real.sqrt κ <
      (Real.sqrt A*Cv)*η+(Real.sqrt B*Cr*Ca)*Real.sqrt κ+ε by linarith)
  filter_upwards [ht',sourceDyadic_radius_eventually Q,sourceDyadic_radius_eventually (36/η),
    sourceDyadic_fine_eventually (max R 1) hκ] with n hn hQN hrad hf
  intro T hJT
  let N := sourceDyadicN n
  have hN : 0<N := sourceDyadicN_pos n
  have hN₁ : 1≤N := sourceDyadicN_one_le n
  have h2N : (2:ℝ)^n≤N := by
    unfold N sourceDyadicN
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hQN' : Q≤N := hQN.trans h2N
  let J := flagBoxFinset (a:=a) (m:=m) (v:=v) hD (mul_pos hN hL)
  let h := flagSignalDifference (v:=v) hD g (fun x => q+ψ x) N
  let M : ℕ → Matrix T T ℝ := fun i => (fun (z w : T) => flagAveragingMatrix (a:=a) (m:=m) (D:=D) (v:=v) χ ((D:ℝ)^4/5) N ((2:ℝ)^i) η κ z.val w.val)
  have hd : (0:ℝ)<D := by exact_mod_cast hD
  have hρ : 0<(D:ℝ)^4/5 := by positivity
  have hM (i : ℕ) (hi : i∈sourceDyadicIndices n) : (M i).PosSemidef :=
    (flagAveragingMatrix_posSemidef χ hρ hN (by positivity) hκ).submatrix (fun z : T => z.val)
  have he (i : ℕ) (hi : i∈sourceDyadicIndices n) :
      finiteL2Norm (M i*ᵥ(fun z : T => h z)-(fun z : T => h z)) ≤
        sourceSignalError A B Cv Ca Cr η κ D n := by
    have his := sourceDyadic_scale_bounds hi
    have hiv := (Finset.mem_Icc.mp hi).1
    have hri : 36≤(2:ℝ)^i*η := by
      apply (div_le_iff₀ hη).mp
      exact hrad.trans (pow_le_pow_right₀ (by norm_num) hiv)
    have hfR := (le_max_left R 1).trans (hf i hi)
    have hf1 := (le_max_right R 1).trans (hf i hi)
    have hline : 1≤2*κ/((2:ℝ)^i/N) := by
      rw [mul_div_assoc]
      linarith
    obtain ⟨hesupp,herr⟩ := happrox N ((2:ℝ)^i) η κ hN₁ hQN' his.1 his.2.1 hη hη₁ hκ hri hline hfR
    let ei := fun z => (∑w∈J,flagAveragingMatrix χ ((D:ℝ)^4/5) N ((2:ℝ)^i) η κ z w*h w)-h z
    have hee := finite_support_error_energy J T hJT
      (flagAveragingMatrix χ ((D:ℝ)^4/5) N ((2:ℝ)^i) η κ) h
      (by
        intro z w hw
        rw [flagAveragingMatrix_box_support hD χ hL hN hχc _ _ _ _ z w (Or.inr hw),zero_mul])
      ei (fun _ => rfl) hesupp
    let δ := 38880/((D:ℝ)*Real.sqrt ((2:ℝ)^i*η))
    have hc : 0≤Cv*η*(1+δ)+Ca*δ := by dsimp [δ]; positivity
    have hκs : 0≤κ+(2:ℝ)^i/N := by positivity
    have hb : finiteL2Norm (M i*ᵥ(fun z : T => h z)-(fun z : T => h z)) ≤
        Real.sqrt A*(Cv*η*(1+δ)+Ca*δ)+Real.sqrt (B*(κ+(2:ℝ)^i/N))*(Cr*Ca) := by
      apply finiteL2Norm_le_of_energy hA (mul_nonneg hB hκs) hc (mul_nonneg hCr hCa)
      rw [hee]
      exact herr
    rw [Real.sqrt_mul hB] at hb
    refine hb.trans ?_
    have hd := sourceSignalDelta_bound hD hη hiv
    change δ ≤ sourceSignalDelta D η n at hd
    dsimp only [sourceSignalError]
    gcongr
    exact his.2.2
  have hs := finite_weighted_resolvent (sourceDyadicIndices n) M hM
    (sourceDyadicWeight_nonneg n) (sourceSignalError_nonneg hCv hCa hCr hη.le D n)
    (fun z : T => h z) he
  have hnorm : finiteL2Norm (fun z : T => h z) ≤ C := by
    apply (sq_le_sq₀ (finiteL2Norm_nonneg _) hC).mp
    rw [finiteL2Norm_sq]
    rw [show (∑i : T,h i.val^2) = ∑i∈T,h i^2 from Finset.sum_coe_sort T (fun i => h i^2)]
    exact henergy N hN₁ T
  have hmatrix : (sourceDyadicWeight n • ∑i∈sourceDyadicIndices n,M i)=
      (fun (z w : T) => sourceFlagMatrix (v:=v) χ ((D:ℝ)^4/5) η κ n z.val w.val) := by
    ext z w
    simp only [Matrix.smul_apply,smul_eq_mul,Matrix.sum_apply]
    simp only [M,N,sourceFlagMatrix]
  dsimp only at hs
  rw [hmatrix] at hs
  change _ ≤ finiteL2Norm (fun z : T => h z)/(1+sourceDyadicMass n)+_ at hs
  refine hs.trans ((add_le_add ?_ le_rfl).trans hn.le)
  apply div_le_div_of_nonneg_right hnorm
  linarith [sourceDyadicMass_nonneg n]

end PolygonSignalInverse

end SimpleAmenable
end
end

end OAI
