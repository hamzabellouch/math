import OAI.NumberTheory.DirichletL.Moments.PositiveSummability

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentInductionEnergy
open HeckeFamily CenteredMomentAbsoluteEnergy CenteredMomentPositiveSummability
open CenteredMomentCounting CenteredMomentHeckeExpansion CenteredMomentHeckeHeight
open CenteredMomentHeckeSlots CenteredMomentRetainedEnergy
open QuadraticInitialBound ConcreteTraceCRT
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

def energy (η:Character) (m A:O) (t:ℝ) (W₁ W₂:ℝ→ℂ)
    (S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) (P:ι→ℝ) (X₁ X₂:ℝ)
    (keep:O→Prop) (Φ:𝓢(ℝ,ℂ)) (K:ℝ) : ℝ :=
  ∑'z:O,if keep z then ‖positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂‖^2*
    (Φ (‖eisEmbedding z‖^2/K)).re else 0

lemma plain_absolute (η:Character) (m A z:O) (t:ℝ) (W:ℝ→ℂ) (b B X:ℝ)
    (hb:0≤b) (hB:0≤B) (hX:0<X) (hs:Function.support W⊆Set.Iic b)
    (hW:∀x,‖W x‖≤B) : ‖rowTwistedSum η m A z W t X‖≤(128*b*B)*X := by
  rw [rowTwistedSum_eq_weight]
  have hh:=norm_tsum_ideal_ball (fun I:Ideal O=>rowWeight η m A z t I*W ((Ideal.absNorm I:ℝ)/X))
    (b*X) B (mul_nonneg hb hX.le) hB (by change rowWeight η m A z t (0:Ideal O)*_=0; rw [map_zero,zero_mul])
    (fun I=>by rw [norm_mul]; exact (mul_le_mul (rowWeight_norm_le_one_all η m A z t I)
      (hW _) (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
    (fun I hi=>(div_le_iff₀ hX).mp (hs (right_ne_zero_of_mul hi)))
  convert hh using 1 ; ring

omit [DecidableEq ι] in
lemma positive_squared_absolute (η:Character) (m A z:O) (t:ℝ) (W₁ W₂:ℝ→ℂ)
    (b₁ b₂ B₁ B₂ X₁ X₂:ℝ) (hb₁:0≤b₁) (hb₂:0≤b₂) (hB₁:0≤B₁) (hB₂:0≤B₂)
    (hX₁:0<X₁) (hX₂:0<X₂) (hs₁:Function.support W₁⊆Set.Iic b₁)
    (hs₂:Function.support W₂⊆Set.Iic b₂) (hW₁:∀x,‖W₁ x‖≤B₁) (hW₂:∀x,‖W₂ x‖≤B₂)
    (S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) (P b B:ι→ℝ)
    (hP:∀i,0<P i) (hb:∀i,0≤b i) (hB:∀i,0≤B i)
    (hβ:∀i,∀I∈S i,‖β i I‖≤B i)
    (hN:∀i,∀I∈S i,β i I≠0 → (Ideal.absNorm I:ℝ)≤b i*P i) :
    ‖positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂‖^2≤
      ((128*b₁*B₁)*(128*b₂*B₂)*(∏i,128*b i*B i))^2*(X₁*X₂*∏i,P i) := by
  let L:ℝ:=(128*b₁*B₁)*(128*b₂*B₂)*(∏i,128*b i*B i)
  let T:ℝ:=X₁*X₂*∏i,P i
  have hL:0≤L:=mul_nonneg (mul_nonneg (by positivity) (by positivity))
    (Finset.prod_nonneg (fun i _=>mul_nonneg (mul_nonneg (by norm_num) (hb i)) (hB i)))
  have hT:0<T:=mul_pos (mul_pos hX₁ hX₂) (Finset.prod_pos (fun i _=>hP i))
  have hsum:‖(rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂)*
      ∏i,rowSlot η m A z (S i) (β i) t‖≤L*T := by
    rw [norm_mul,norm_mul,norm_prod]
    have hp:=Finset.prod_le_prod₀ (s:=Finset.univ) (fun i _=>norm_nonneg (rowSlot η m A z (S i) (β i) t))
      (fun i _=>rowSlot_bound η m A z (S i) (β i) t (b i*P i) (B i)
        (mul_nonneg (hb i) (hP i).le) (hB i) (hβ i) (hN i))
    have hq:=mul_le_mul
      (mul_le_mul (plain_absolute η m A z t W₁ b₁ B₁ X₁ hb₁ hB₁ hX₁ hs₁ hW₁)
        (plain_absolute η m A z t W₂ b₂ B₂ X₂ hb₂ hB₂ hX₂ hs₂ hW₂) (norm_nonneg _) (by positivity))
      hp (by positivity) (by positivity)
    apply hq.trans_eq
    simp only [mul_left_comm (B _) (b _),mul_assoc,Finset.prod_mul_distrib]
    dsimp [L,T]
    simp only [Finset.prod_mul_distrib]
    ring
  unfold positiveSlotRow
  rw [CenteredMomentDivisorRawEnergy.normalized_norm_sq _ hT]
  calc
    _≤(L*T)^2/T:=div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hsum 2) hT.le
    _=L^2*T:=by field_simp

omit [DecidableEq ι] in
theorem energy_absolute (η:Character) (m A:O) (t:ℝ) (W₁ W₂:ℝ→ℂ)
    (b₁ b₂ B₁ B₂ X₁ X₂:ℝ) (hb₁:0≤b₁) (hb₂:0≤b₂) (hB₁:0≤B₁) (hB₂:0≤B₂)
    (hX₁:0<X₁) (hX₂:0<X₂) (hs₁:Function.support W₁⊆Set.Iic b₁)
    (hs₂:Function.support W₂⊆Set.Iic b₂) (hW₁:∀x,‖W₁ x‖≤B₁) (hW₂:∀x,‖W₂ x‖≤B₂)
    (S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) (P b B:ι→ℝ)
    (hP:∀i,0<P i) (hb:∀i,0≤b i) (hB:∀i,0≤B i)
    (hβ:∀i,∀I∈S i,‖β i I‖≤B i)
    (hN:∀i,∀I∈S i,β i I≠0 → (Ideal.absNorm I:ℝ)≤b i*P i)
    (keep:O→Prop) (Φ:𝓢(ℝ,ℂ)) (K:ℝ) (hK:0<K) :
    energy η m A t W₁ W₂ S β P X₁ X₂ keep Φ K≤
      diagonalControl Φ*max 1 K*
        (((128*b₁*B₁)*(128*b₂*B₂)*(∏i,128*b i*B i))^2*(X₁*X₂*∏i,P i)) := by
  let E:ℝ:=((128*b₁*B₁)*(128*b₂*B₂)*(∏i,128*b i*B i))^2*(X₁*X₂*∏i,P i)
  have hE:0≤E:=mul_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg hX₁.le hX₂.le)
    (Finset.prod_nonneg (fun i _=>(hP i).le)))
  have hp (z:O):‖positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂‖^2≤E:=
    positive_squared_absolute η m A z t W₁ W₂ b₁ b₂ B₁ B₂ X₁ X₂ hb₁ hb₂ hB₁ hB₂
      hX₁ hX₂ hs₁ hs₂ hW₁ hW₂ S β P b B hP hb hB hβ hN
  have hs:=bounded_radial_summable
    (fun z:O=>positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂) (Real.sqrt E)
    (fun z=>Real.le_sqrt_of_sq_le (hp z)) keep Φ K hK
  have hbnd:=hs.tsum_le_tsum (g:=fun z:O=>E*‖Φ (‖eisEmbedding z‖^2/K)‖) (fun z=>by
    split_ifs
    · exact (mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (sq_nonneg _)).trans
        (mul_le_mul_of_nonneg_right (hp z) (norm_nonneg _))
    · positivity) ((radial_norm_summable Φ K hK).mul_left E)
  rw [tsum_mul_left] at hbnd
  exact hbnd.trans ((mul_le_mul_of_nonneg_left (radial_weight_lattice_bound_all Φ K hK) hE).trans_eq (mul_comm _ _))

end SevenEighths.CenteredMomentInductionEnergy

end

end OAI
