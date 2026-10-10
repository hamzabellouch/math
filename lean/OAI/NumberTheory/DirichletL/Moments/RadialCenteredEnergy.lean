import OAI.NumberTheory.DirichletL.Moments.RadialEligibleEnergy
import OAI.NumberTheory.DirichletL.Moments.DivisorRawEnergy

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentRadialCenteredEnergy
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentRadialEligibleEnergy
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorRawEnergy
open CenteredMomentDivisorExtraction CenteredMomentDivisorRowEnergy CenteredMomentDivisorRectangle
open CenteredMomentHeckeSlots CenteredMomentPositiveSummability CenteredMomentActiveAllocation
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

def centeredChildEnergy (s:Data ι) (r:Radial) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))):ℝ:=
  ∑'z:O,r.weight z*‖residualCenteredRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
    s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂)‖^2

lemma centered_child_summable (s:Data ι) (r:Radial) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))):
    Summable (fun z:O=>r.weight z*‖residualCenteredRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
      s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂)‖^2):=by
  have hN (j:Fin 2):(0:ℝ)<Ideal.absNorm (selectedPlain D a j):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (selectedDivisor_ne_zero D Finset.univ a (Sum.inr j)))
  let c:ℂ:=(Real.sqrt ((s.X₁*s.X₂/selectedNorm D a)*∏i:liveIndices D a,s.P i):ℂ)⁻¹
  obtain ⟨BX,hBX⟩:=product_bounded s.η s.m s.A s.t c s.W₁ s.W₂ s.b₁ s.b₂
    (s.X₁/Ideal.absNorm (selectedPlain D a 0)) (s.X₂/Ideal.absNorm (selectedPlain D a 1))
    s.support₁ s.support₂ (div_pos s.X₁_pos (hN 0)) (div_pos s.X₂_pos (hN 1))
    (fun i:liveIndices D a=>s.slots i) (fun i:liveIndices D a=>s.coefficient i)
  obtain ⟨BY,hBY⟩:=product_bounded s.η s.m s.A s.t c s.W₁ s.W₂ s.b₁ s.b₂
    (s.Y₁/Ideal.absNorm (selectedPlain D a 0)) (s.Y₂/Ideal.absNorm (selectedPlain D a 1))
    s.support₁ s.support₂ (div_pos s.Y₁_pos (hN 0)) (div_pos s.Y₂_pos (hN 1))
    (fun i:liveIndices D a=>s.slots i) (fun i:liveIndices D a=>s.coefficient i)
  have hF (z:O):‖residualCenteredRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
      s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂)‖≤BX+BY:=by
    unfold residualCenteredRow centeredSlotRow
    change ‖c*((_ - _)*_)‖≤_
    rw [sub_mul,mul_sub]
    exact (norm_sub_le _ _).trans (add_le_add (hBX z) (hBY z))
  have hs:=bounded_radial_summable _ (BX+BY) hF r.keep r.profile r.scale r.scale_pos
  convert hs using 1
  funext z
  unfold Radial.weight
  split_ifs <;> ring

lemma centered_child_nonneg (s:Data ι) (r:Radial) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))):0≤centeredChildEnergy s r D a:=
  tsum_nonneg (fun z=>mul_nonneg (r.weight_nonneg z) (sq_nonneg _))

def restrict (r:Radial) (p:O→Prop):Radial:={r with keep:=fun z=>r.keep z ∧ p z}

 theorem centered_child_split (s:Data ι) (r:Radial) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))) (p:O→Prop):
    centeredChildEnergy s r D a=centeredChildEnergy s (restrict r p) D a+
      centeredChildEnergy s (restrict r (fun z=>¬p z)) D a:=by
  unfold centeredChildEnergy
  rw [←Summable.tsum_add (centered_child_summable s (restrict r p) D a)
    (centered_child_summable s (restrict r (fun z=>¬p z)) D a)]
  apply tsum_congr
  intro z
  by_cases hk:r.keep z <;> by_cases hp:p z <;> simp [Radial.weight,restrict,hk,hp]

 theorem actual_source_centered (N:ℕ) (hslots:Fintype.card ι≤N) (ε:ℝ) (hε:0<ε):
    ∃C:ℝ,0<C ∧ ∀(s:Data ι) (r:Radial) (D:Ideal O),Squarefree D →
      energy s r D≤C*(Ideal.absNorm D:ℝ)^ε*
        ∑a∈s.toSource.active D,((∏i∈frozenIndices D a,s.M i)^2/formalReductionFactor D a s.P)*
          centeredChildEnergy s r D a:=by
  obtain ⟨C,hC,hbase⟩:=active_allocated_energy (ι:=ι) N hslots ε hε
  refine ⟨C,hC,?_⟩
  intro s r D hD
  have hraw:0<s.X₁*s.X₂*∏i,s.P i:=mul_pos (mul_pos s.X₁_pos s.X₂_pos)
    (Finset.prod_pos (fun i _=>s.P_pos i))
  apply Real.tsum_le_of_sum_le (fun z=>mul_nonneg (r.weight_nonneg z) (sq_nonneg _))
  intro rows
  have hb:=hbase s.η s.m s.A s.t s.slots s.coefficient D hD s.W₁ s.W₂ s.b₁ s.b₂
    s.X₁ s.X₂ s.Y₁ s.Y₂ s.support₁ s.support₂ s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos
    rows (fun z=>r.weight z/(s.X₁*s.X₂*∏i,s.P i)) (fun z _=>div_nonneg (r.weight_nonneg z) hraw.le)
  have he (z:O) (x:ℂ):(r.weight z/(s.X₁*s.X₂*∏i,s.P i))*‖x‖^2=
      r.weight z*‖(Real.sqrt (s.X₁*s.X₂*∏i,s.P i):ℂ)⁻¹*x‖^2:=by
    rw [normalized_norm_sq _ hraw];ring
  simp_rw [he] at hb
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  apply Finset.sum_le_sum
  intro a ha
  have hf:0≤(∏i∈frozenIndices D a,s.M i)^2/formalReductionFactor D a s.P:=
    div_nonneg (sq_nonneg _) (mul_pos (selectedNorm_pos D a) (Finset.prod_pos (fun i _=>s.P_pos i))).le
  calc
    _≤∑z∈rows,r.weight z*((∏i∈frozenIndices D a,s.M i)^2/formalReductionFactor D a s.P)*
      ‖residualCenteredRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
        s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂)‖^2:=by
      apply Finset.sum_le_sum
      intro z hz
      have hh:=mul_le_mul_of_nonneg_left
        (allocated_raw_energy s.η s.m s.A z s.t s.slots s.prime s.coefficient s.M s.P
          (fun i=>(zero_le_one.trans (s.M_ge_one i))) s.P_pos s.coefficient_bound D a s.W₁ s.W₂
          s.b₁ s.b₂ s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) s.support₁ s.support₂
          s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos (mul_pos s.X₁_pos s.X₂_pos)) (r.weight_nonneg z)
      convert hh using 1 ; ring
    _=((∏i∈frozenIndices D a,s.M i)^2/formalReductionFactor D a s.P)*
      ∑z∈rows,r.weight z*‖residualCenteredRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
        s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂)‖^2:=by rw [Finset.mul_sum];apply Finset.sum_congr rfl;intros;ring
    _≤_:=mul_le_mul_of_nonneg_left (sum_le_hasSum rows
      (fun z _=>mul_nonneg (r.weight_nonneg z) (sq_nonneg _)) (centered_child_summable s r D a).hasSum) hf

 theorem actual_source_from_centered_children (N:ℕ) (hslots:Fintype.card ι≤N) (ε:ℝ) (hε:0<ε):
    ∃C:ℝ,0<C ∧ ∀(s:Data ι) (r:Radial) (D:Ideal O),Squarefree D → ∀E:ℝ,0≤E →
      (∀a∈s.toSource.active D,centeredChildEnergy s r D a≤E) →
      energy s r D≤C*(Ideal.absNorm D:ℝ)^ε*s.profileFactor*E*
        ∑a∈s.toSource.active D,1/formalReductionFactor D a s.P:=by
  obtain ⟨C,hC,hbound⟩:=actual_source_centered N hslots ε hε
  refine ⟨C,hC,?_⟩
  intro s r D hD E hE hchild
  apply (hbound s r D hD).trans
  calc
    _≤C*(Ideal.absNorm D:ℝ)^ε*∑a∈s.toSource.active D,
        (s.profileFactor/formalReductionFactor D a s.P)*E:=by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      apply Finset.sum_le_sum
      intro a ha
      have hp:(∏i∈frozenIndices D a,s.M i)≤∏i,s.M i:=
        Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
          (fun i _=>zero_le_one.trans (s.M_ge_one i)) (fun i _ _=>s.M_ge_one i)
      have hsq:(∏i∈frozenIndices D a,s.M i)^2≤s.profileFactor:=by
        have hh:=pow_le_pow_left₀ (Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.M_ge_one i))) hp 2
        have hf:1≤2*(max 1 s.b₁*max 1 s.b₂):=by
          have ht:=one_le_mul_of_one_le_of_one_le (le_max_left 1 s.b₁) (le_max_left 1 s.b₂)
          linarith
        exact hh.trans (le_mul_of_one_le_left (sq_nonneg _) hf)
      exact mul_le_mul (div_le_div_of_nonneg_right hsq (s.reduction_pos D a).le)
        (hchild a ha) (centered_child_nonneg s r D a) (div_nonneg s.profile_nonneg (s.reduction_pos D a).le)
    _=_:=by
      simp only [div_eq_mul_inv,one_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring

end SevenEighths.CenteredMomentRadialCenteredEnergy

end

end OAI
