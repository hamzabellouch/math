import OAI.NumberTheory.DirichletL.Moments.BottomStage

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentCoreFloor
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentHeckeSlots
open CenteredMomentRetainedEnergy CenteredMomentInductionEnergy
open CenteredMomentPositiveSummability
open CenteredMomentRadialEligibleEnergy (Radial)
open QuadraticInitialBound ConcreteTraceCRT
local notation "O" => HeckeFamily.O

 def zeroRow (η:Character) (m A z:O) (t:ℝ) (W₁ W₂:ℝ→ℂ) (X₁ X₂:ℝ):ℂ :=
  (Real.sqrt (X₁*X₂):ℂ)⁻¹*(rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂)

 def zeroEnergy (η:Character) (m A:O) (t:ℝ) (W₁ W₂:ℝ→ℂ) (X₁ X₂:ℝ) (r:Radial):ℝ :=
  ∑'z:O,if r.keep z then ‖zeroRow η m A z t W₁ W₂ X₁ X₂‖^2*
    (r.profile (‖eisEmbedding z‖^2/r.scale)).re else 0

 theorem zero_energy_eq (η:Character) (m A:O) (t:ℝ) (W₁ W₂:ℝ→ℂ) (X₁ X₂:ℝ) (r:Radial):
    zeroEnergy η m A t W₁ W₂ X₁ X₂ r=
    energy η m A t W₁ W₂ (fun _:Fin 0=>∅) (fun _:Fin 0=>0) (fun _:Fin 0=>1)
      X₁ X₂ r.keep r.profile r.scale:=by
  simp [zeroEnergy,energy,zeroRow,positiveSlotRow]

 theorem zero_absolute (η:Character) (m A:O) (t:ℝ) (W₁ W₂:ℝ→ℂ)
    (b₁ b₂ B₁ B₂ X₁ X₂:ℝ) (hb₁:0≤b₁)(hb₂:0≤b₂)(hB₁:0≤B₁)(hB₂:0≤B₂)
    (hX₁:0<X₁)(hX₂:0<X₂)(hs₁:Function.support W₁⊆Set.Iic b₁)
    (hs₂:Function.support W₂⊆Set.Iic b₂)(hW₁:∀x,‖W₁ x‖≤B₁)(hW₂:∀x,‖W₂ x‖≤B₂)
    (r:Radial):
    zeroEnergy η m A t W₁ W₂ X₁ X₂ r≤
      diagonalControl r.profile*max 1 r.scale*((128*b₁*B₁)*(128*b₂*B₂))^2*(X₁*X₂):=by
  rw [zero_energy_eq]
  have h:=energy_absolute (ι:=Fin 0) η m A t W₁ W₂ b₁ b₂ B₁ B₂ X₁ X₂
    hb₁ hb₂ hB₁ hB₂ hX₁ hX₂ hs₁ hs₂ hW₁ hW₂
    (fun _=>∅) (fun _=>0) (fun _=>1) (fun _=>1) (fun _=>1)
    (by simp) (by simp) (by simp) (by simp) (by simp)
    r.keep r.profile r.scale r.scale_pos
  simpa only [Fin.prod_univ_zero,mul_one,mul_assoc] using h

 theorem zero_padded_core (η:Character) (mask A:O) (t:ℝ) (W₁ W₂:ℝ→ℂ)
    (b₁ b₂ B₁ B₂:ℝ) (hb₁:0≤b₁)(hb₂:0≤b₂)(hB₁:0≤B₁)(hB₂:0≤B₂)
    (hs₁:Function.support W₁⊆Set.Iic b₁)(hs₂:Function.support W₂⊆Set.Iic b₂)
    (hW₁:∀x,‖W₁ x‖≤B₁)(hW₂:∀x,‖W₂ x‖≤B₂)
    (r:Radial)(Z m q n₁ n₂ ρ δ:ℝ)(hZ:1<Z)(hm:0≤m)(hq:0≤q)
    (hscale:r.scale=Z^m)(hfloor:m+q≤ρ)(hcore:n₁+n₂≤m+q+δ):
    zeroEnergy η mask A t W₁ W₂ (Z^n₁) (Z^n₂) r≤
      (diagonalControl r.profile*((128*b₁*B₁)*(128*b₂*B₂))^2)*Z^(m+q+ρ+δ):=by
  have hZ0:0<Z:=zero_lt_one.trans hZ
  have h:=zero_absolute η mask A t W₁ W₂ b₁ b₂ B₁ B₂ (Z^n₁) (Z^n₂)
    hb₁ hb₂ hB₁ hB₂ (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _)
    hs₁ hs₂ hW₁ hW₂ r
  rw [hscale,max_eq_right (Real.one_le_rpow hZ.le hm)] at h
  have hp:Z^m*(Z^n₁*Z^n₂)≤Z^(m+q+ρ+δ):=by
    rw [←Real.rpow_add hZ0,←Real.rpow_add hZ0]
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  apply h.trans
  calc
    _=(diagonalControl r.profile*((128*b₁*B₁)*(128*b₂*B₂))^2)*(Z^m*(Z^n₁*Z^n₂)):=by ring
    _≤_:=mul_le_mul_of_nonneg_left hp (mul_nonneg (diagonalControl_nonneg _) (sq_nonneg _))

 theorem whole_slot_norm {ι:Type*}[Fintype ι][DecidableEq ι]
    (η:Character)(m A z:O)(t:ℝ)(W₁ W₂:ℝ→ℂ)(X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)
    (S:ι→Finset (Ideal O))(β:ι→Ideal O→ℂ)(P:ι→ℝ)(hP:∀i,0<P i):
    ‖positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂‖^2=
      ‖zeroRow η m A z t W₁ W₂ X₁ X₂‖^2 *
        (∏i,‖rowSlot η m A z (S i) (β i) t‖^2/P i):=by
  have hp:0<∏i,P i:=Finset.prod_pos (fun i _=>hP i)
  unfold positiveSlotRow zeroRow
  rw [CenteredMomentDivisorRawEnergy.normalized_norm_sq _ (mul_pos (mul_pos hX₁ hX₂) hp),
    CenteredMomentDivisorRawEnergy.normalized_norm_sq _ (mul_pos hX₁ hX₂)]
  rw [norm_mul,norm_prod,mul_pow,Finset.prod_div_distrib,Finset.prod_pow]
  ring

 theorem slot_energy_reduction {ι:Type*}[Fintype ι][DecidableEq ι]
    (η:Character)(m A:O)(t:ℝ)(W₁ W₂:ℝ→ℂ)(b₁ b₂ X₁ X₂:ℝ)
    (hs₁:Function.support W₁⊆Set.Iic b₁)(hs₂:Function.support W₂⊆Set.Iic b₂)
    (hX₁:0<X₁)(hX₂:0<X₂)(S:ι→Finset (Ideal O))(β:ι→Ideal O→ℂ)
    (P:ι→ℝ)(hP:∀i,0<P i)(r:Radial)(E:ℝ)
    (hslots:∀z,r.keep z→(∏i,‖rowSlot η m A z (S i) (β i) t‖^2/P i)≤E):
    energy η m A t W₁ W₂ S β P X₁ X₂ r.keep r.profile r.scale≤
      E*zeroEnergy η m A t W₁ W₂ X₁ X₂ r:=by
  obtain ⟨B,hB⟩:=product_bounded (ι:=Fin 0) η m A t (Real.sqrt (X₁*X₂):ℂ)⁻¹
    W₁ W₂ b₁ b₂ X₁ X₂ hs₁ hs₂ hX₁ hX₂ (fun _=>∅) (fun _=>0)
  have hz:∀z,‖zeroRow η m A z t W₁ W₂ X₁ X₂‖≤B:=by
    simpa [zeroRow] using hB
  have hsum:=bounded_radial_summable _ B hz r.keep r.profile r.scale r.scale_pos
  obtain ⟨B',hB'⟩:=product_bounded η m A t (Real.sqrt (X₁*X₂*∏i,P i):ℂ)⁻¹
    W₁ W₂ b₁ b₂ X₁ X₂ hs₁ hs₂ hX₁ hX₂ S β
  have hspos:=bounded_radial_summable _ B' hB' r.keep r.profile r.scale r.scale_pos
  change Summable (fun z:O=>if r.keep z then
    ‖positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂‖^2*
      (r.profile (‖eisEmbedding z‖^2/r.scale)).re else 0) at hspos
  unfold energy zeroEnergy
  rw [←tsum_mul_left]
  apply hspos.tsum_le_tsum _ (hsum.mul_left E)
  intro z
  by_cases hk:r.keep z
  · simp only [ite_eq_left hk]
    rw [whole_slot_norm η m A z t W₁ W₂ X₁ X₂ hX₁ hX₂ S β P hP]
    have hb:=mul_le_mul_of_nonneg_left (hslots z hk)
      (sq_nonneg ‖zeroRow η m A z t W₁ W₂ X₁ X₂‖)
    have hh:=mul_le_mul_of_nonneg_right hb (r.nonneg z)
    nlinarith only [hh]
  · simp [hk]

end SevenEighths.CenteredMomentCoreFloor

end

end OAI
