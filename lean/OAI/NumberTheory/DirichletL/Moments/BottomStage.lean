import OAI.NumberTheory.DirichletL.Moments.EligibleEnergy
import OAI.NumberTheory.DirichletL.Moments.RadialEligibleEnergy
import OAI.NumberTheory.DirichletL.Moments.InductionEnergy

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentBottomStage
open CenteredMomentEligibleEnergy CenteredMomentRadialEligibleEnergy
open CenteredMomentInductionEnergy CenteredMomentAbsoluteEnergy QuadraticInitialBound
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι]

 def positiveEnergy (s:Data ι) (r:Radial) : ℝ :=
  CenteredMomentInductionEnergy.energy s.η s.m s.A s.t s.W₁ s.W₂ s.slots s.coefficient s.P
    s.X₁ s.X₂ r.keep r.profile r.scale

 def profileMass (s:Data ι) (B₁ B₂:ℝ) : ℝ :=
  ((128*max 0 s.b₁*B₁)*(128*max 0 s.b₂*B₂)*(∏i,128*max 0 (s.hi i)*s.M i))^2

 theorem actual_absolute (s:Data ι) (r:Radial) (B₁ B₂:ℝ) (hB₁:0≤B₁) (hB₂:0≤B₂)
    (hW₁:∀x,‖s.W₁ x‖≤B₁) (hW₂:∀x,‖s.W₂ x‖≤B₂) :
    positiveEnergy s r≤diagonalControl r.profile*max 1 r.scale*profileMass s B₁ B₂*
      (s.X₁*s.X₂*∏i,s.P i) := by
  have hs₁:Function.support s.W₁⊆Set.Iic (max 0 s.b₁):=
    by
      intro x hx
      change x≤max 0 s.b₁
      have hs:x≤s.b₁:=s.support₁ hx
      exact hs.trans (le_max_right 0 s.b₁)
  have hs₂:Function.support s.W₂⊆Set.Iic (max 0 s.b₂):=
    by
      intro x hx
      change x≤max 0 s.b₂
      have hs:x≤s.b₂:=s.support₂ hx
      exact hs.trans (le_max_right 0 s.b₂)
  have hN:∀i,∀I∈s.slots i,s.coefficient i I≠0 →
      (Ideal.absNorm I:ℝ)≤max 0 (s.hi i)*s.P i:=by
    intro i I hI hn
    have hw:s.W i ((Ideal.absNorm I:ℝ)/s.P i)≠0:=by
      intro hw
      apply hn
      simp only [Data.coefficient,hw,mul_zero]
    have hs:=s.support i hw
    exact (div_le_iff₀ (s.P_pos i)).mp (hs.2.trans (le_max_right _ _))
  have hh:=energy_absolute s.η s.m s.A s.t s.W₁ s.W₂
    (max 0 s.b₁) (max 0 s.b₂) B₁ B₂ s.X₁ s.X₂ (le_max_left _ _) (le_max_left _ _) hB₁ hB₂
    s.X₁_pos s.X₂_pos hs₁ hs₂ hW₁ hW₂
    s.slots s.coefficient s.P (fun i=>max 0 (s.hi i)) s.M s.P_pos
    (fun i=>le_max_left _ _) (fun i=>zero_le_one.trans (s.M_ge_one i)) s.coefficient_bound
    hN r.keep r.profile r.scale r.scale_pos
  exact hh.trans_eq (by unfold profileMass;ring)

 theorem actual_bottom_band (s:Data ι) (r:Radial) (B₁ B₂:ℝ) (hB₁:0≤B₁) (hB₂:0≤B₂)
    (hW₁:∀x,‖s.W₁ x‖≤B₁) (hW₂:∀x,‖s.W₂ x‖≤B₂)
    (Z m M σ:ℝ) (hZ:1<Z) (hK:1≤r.scale) (hm:m≤σ)
    (hrow:r.scale≤Z^m) (hsource:s.X₁*s.X₂*∏i,s.P i≤Z^M) :
    positiveEnergy s r≤(diagonalControl r.profile*profileMass s B₁ B₂)*Z^(M+σ) := by
  have hh:=actual_absolute s r B₁ B₂ hB₁ hB₂ hW₁ hW₂
  rw [max_eq_right hK] at hh
  have hp:0≤profileMass s B₁ B₂:=sq_nonneg _
  have hd:0≤diagonalControl r.profile:=diagonalControl_nonneg _
  have hs:0≤s.X₁*s.X₂*∏i,s.P i:=(mul_pos (mul_pos s.X₁_pos s.X₂_pos)
    (Finset.prod_pos (fun i _=>s.P_pos i))).le
  have hpow:r.scale*(s.X₁*s.X₂*∏i,s.P i)≤Z^(M+σ):=by
    apply (mul_le_mul hrow hsource hs (Real.rpow_nonneg (by linarith) _)).trans
    rw [←Real.rpow_add (zero_lt_one.trans hZ)]
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  apply hh.trans
  calc
    _=(diagonalControl r.profile*profileMass s B₁ B₂)*(r.scale*(s.X₁*s.X₂*∏i,s.P i)):=by ring
    _≤_:=mul_le_mul_of_nonneg_left hpow (mul_nonneg hd hp)

end SevenEighths.CenteredMomentBottomStage

end

end OAI
