import OAI.NumberTheory.DirichletL.Moments.CommonMaskExpansion
import OAI.NumberTheory.DirichletL.Hecke.DeletionBounds
import OAI.NumberTheory.DirichletL.Moments.LiveCapacity

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentEnergyReferenceDeletionBudget
open HeckeFamily CenteredMomentCommonMaskExpansion CenteredMomentReflectionMass
open CenteredMomentReflectionDeletion UniqueFactorizationMonoid
local notation "O"=>HeckeFamily.O

lemma product_norm_ge_one (D:Finset (Ideal O))(hD:∀I∈D,Prime I):
    (1:ℝ)≤(∏I∈D,I).absNorm:=by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (subset_product_nonzero D hD))

lemma weighted_inverse_sqrt (I:Ideal O)(hI:I≠0)(t:ℝ)(ht:t≤1/2):
    weight I*(I.absNorm:ℝ)^t≤1:=by
  have hn:(1:ℝ)≤I.absNorm:=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hp:(0:ℝ)<I.absNorm:=zero_lt_one.trans_le hn
  rw [weight,Real.sqrt_eq_rpow,←Real.rpow_neg hp.le,←Real.rpow_add hp]
  exact Real.rpow_le_one_of_one_le_of_nonpos hn (by linarith)

lemma powerset_square_subpower (eps:ℝ)(heps:0<eps):
    ∃C:ℝ,0<C ∧ ∀(R:Finset (Ideal O))(_hR:∀I∈R,Prime I),
      (R.powerset.card:ℝ)^2≤C*((∏I∈R,I).absNorm:ℝ)^eps:=by
  obtain ⟨C,hC,hb⟩:=HeckeDeletionBounds.constant_pow_primeSupport_bound 4 eps (by norm_num) heps
  refine ⟨C,hC,?_⟩
  intro R hR
  have hf:normalizedFactors (∏I∈R,I)=R.val:=by
    simpa using normalizedFactors_prod_of_prime (m:=R.val) hR
  have hs:IdealMobiusDivisorSum.primeSupport (∏I∈R,I)=R:=by
    simp [IdealMobiusDivisorSum.primeSupport,hf]
  have hh:=hb (∏I∈R,I) (subset_product_nonzero R hR)
  rw [hs] at hh
  convert hh using 1
  rw [Finset.card_powerset,Nat.cast_pow,Nat.cast_ofNat,←pow_mul, mul_comm R.card 2,pow_mul]
  norm_num

variable {α:Type*}

lemma weighted_uniform_term (R D₁ D₂:Finset (Ideal O))
    (hR:∀I∈R,Prime I)(hD₁:D₁⊆R)(hD₂:D₂⊆R)(J:Finset α)
    (b M:α→ℝ)(hM:∀i∈J,0≤M i)(t:ℝ)(ht:t≤1/2):
    uniformMajorant R D₁ D₂ J b M*((∏I∈D₂,I).absNorm:ℝ)^t≤
      ∏i∈J,(Real.sqrt (max 1 (b i))*M i)*(∑I∈R,weight I):=by
  have hn₂:=subset_product_nonzero D₂ (fun I hi=>hR I (hD₂ hi))
  have hw₁:weight (∏I∈D₁,I)≤1:=by
    simpa using weighted_inverse_sqrt (∏I∈D₁,I)
      (subset_product_nonzero D₁ (fun I hi=>hR I (hD₁ hi))) 0 (by norm_num)
  have hw₂:=weighted_inverse_sqrt (∏I∈D₂,I) hn₂ t ht
  have hprod:0≤∏i∈J,(Real.sqrt (max 1 (b i))*M i)*(∑I∈R,weight I):=
    Finset.prod_nonneg (fun i hi=>mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hM i hi))
      (Finset.sum_nonneg (fun I _=>weight_nonneg I)))
  unfold uniformMajorant
  calc
    _=(weight (∏I∈D₁,I)*(weight (∏I∈D₂,I)*((∏I∈D₂,I).absNorm:ℝ)^t))*
        (∏i∈J,(Real.sqrt (max 1 (b i))*M i)*(∑I∈R,weight I)):=by ring
    _≤1*(∏i∈J,(Real.sqrt (max 1 (b i))*M i)*(∑I∈R,weight I)):=
      mul_le_mul_of_nonneg_right
        ((mul_le_mul hw₁ hw₂ (mul_nonneg (weight_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) t))
          zero_le_one).trans_eq (one_mul 1)) hprod
    _=_:=one_mul _

lemma signed_weighted_term (χ:Character)(R D₁ D₂:Finset (Ideal O))
    (hR:∀I∈R,Prime I)(hD₁:D₁⊆R)(hD₂:D₂⊆R)(J:Finset α)
    (pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P b M:α→ℝ)
    (hp:∀i∈J,∀I∈pool i,Prime I)(hP:∀i∈J,0<P i)(hM:∀i∈J,0≤M i)
    (hβ:∀i∈J,∀I∈pool i,‖β i I‖≤M i)
    (hs:∀i∈J,∀I∈pool i,β i I≠0→(I.absNorm:ℝ)≤b i*P i)
    (t:ℝ)(ht:t≤1/2):
    ‖signedCoefficient χ R D₁ D₂ J pool β P‖*((∏I∈D₂,I).absNorm:ℝ)^t≤
      ∏i∈J,(Real.sqrt (max 1 (b i))*M i)*(∑I∈R,weight I):=by
  have hn₂:=subset_product_nonzero D₂ (fun I hi=>hR I (hD₂ hi))
  have hw₁:weight (∏I∈D₁,I)≤1:=by
    simpa using weighted_inverse_sqrt (∏I∈D₁,I)
      (subset_product_nonzero D₁ (fun I hi=>hR I (hD₁ hi))) 0 (by norm_num)
  have hw₂:=weighted_inverse_sqrt (∏I∈D₂,I) hn₂ t ht
  have hprod:0≤∏i∈J,(Real.sqrt (max 1 (b i))*M i)*(∑I∈R,weight I):=
    Finset.prod_nonneg (fun i hi=>mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hM i hi))
      (Finset.sum_nonneg (fun I _=>weight_nonneg I)))
  apply (mul_le_mul_of_nonneg_right
    (signedCoefficient_uniform χ R hR D₁ D₂ hD₁ hD₂ J pool β P b M hp hP hM hβ hs)
    (Real.rpow_nonneg (Nat.cast_nonneg _) t)).trans
  unfold uniformMajorant
  calc
    _=(weight (∏I∈D₁,I)*(weight (∏I∈D₂,I)*((∏I∈D₂,I).absNorm:ℝ)^t))*
        (∏i∈J,(Real.sqrt (max 1 (b i))*M i)*(∑I∈R,weight I)):=by ring
    _≤1*(∏i∈J,(Real.sqrt (max 1 (b i))*M i)*(∑I∈R,weight I)):=
      mul_le_mul_of_nonneg_right
        ((mul_le_mul hw₁ hw₂ (mul_nonneg (weight_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) t))
          zero_le_one).trans_eq (one_mul 1)) hprod
    _=_:=one_mul _

lemma slot_majorant_mass (R:Finset (Ideal O))(hR:∀I∈R,Prime I)
    (F:Finset α)(b M:α→ℝ)(hM:∀i∈F,0≤M i):
    (∑J∈F.powerset,∏i∈J,(Real.sqrt (max 1 (b i))*M i)*(∑I∈R,weight I))≤
      (∏i∈F,max 1 (Real.sqrt (max 1 (b i))*M i))*(∏I∈R,localMass I)^F.card:=by
  rw [←Finset.prod_one_add]
  have he:1+∑I∈R,weight I≤∏I∈R,localMass I:=
    (one_add_sum_weight R).trans (deletion_le_euler R hR)
  have hp (i:α)(hi:i∈F):1+(Real.sqrt (max 1 (b i))*M i)*(∑I∈R,weight I)≤
      max 1 (Real.sqrt (max 1 (b i))*M i)*(∏I∈R,localMass I):=by
    have h1:=le_max_left 1 (Real.sqrt (max 1 (b i))*M i)
    have h2:=le_max_right 1 (Real.sqrt (max 1 (b i))*M i)
    have hs:0≤∑I∈R,weight I:=Finset.sum_nonneg (fun I _=>weight_nonneg I)
    nlinarith
  calc
    _≤∏i∈F,max 1 (Real.sqrt (max 1 (b i))*M i)*(∏I∈R,localMass I):=
      Finset.prod_le_prod₀ (fun i hi=>add_nonneg zero_le_one
        (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hM i hi))
          (Finset.sum_nonneg (fun I _=>weight_nonneg I)))) hp
    _=_:=by rw [Finset.prod_mul_distrib,Finset.prod_const]

theorem weighted_uniform_mass_subpower (F:Finset α)(b M:α→ℝ)(hM:∀i∈F,0≤M i)
    (eps:ℝ)(heps:0<eps):
    ∃C:ℝ,0<C ∧ ∀(R:Finset (Ideal O))(_hR:∀I∈R,Prime I),
      ∀t:ℝ,t≤1/2→
      (∑D₁∈R.powerset,∑D₂∈R.powerset,∑J∈F.powerset,
        uniformMajorant R D₁ D₂ J b M*((∏I∈D₂,I).absNorm:ℝ)^t)≤
        C*((∏I∈R,I).absNorm:ℝ)^eps:=by
  obtain ⟨Cc,hCc,hcard⟩:=powerset_square_subpower (eps/2) (by linarith)
  let delta:=eps/(2*((F.card:ℝ)+1))
  have hd:0<delta:=div_pos heps (by positivity)
  obtain ⟨Ce,hCe,heuler⟩:=euler_mass_subpower delta hd
  let A:ℝ:=∏i∈F,max 1 (Real.sqrt (max 1 (b i))*M i)
  have hA:0<A:=Finset.prod_pos (fun i _=>lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  refine ⟨Cc*A*Ce^F.card,by positivity,?_⟩
  intro R hR t ht
  have hsum:(∑D₁∈R.powerset,∑D₂∈R.powerset,∑J∈F.powerset,
      uniformMajorant R D₁ D₂ J b M*((∏I∈D₂,I).absNorm:ℝ)^t)≤
      (R.powerset.card:ℝ)^2*(∑J∈F.powerset,
        ∏i∈J,(Real.sqrt (max 1 (b i))*M i)*(∑I∈R,weight I)):=by
    calc
      _≤∑D₁∈R.powerset,∑D₂∈R.powerset,∑J∈F.powerset,
          ∏i∈J,(Real.sqrt (max 1 (b i))*M i)*(∑I∈R,weight I):=by
        apply Finset.sum_le_sum;intro D₁ hD₁
        apply Finset.sum_le_sum;intro D₂ hD₂
        apply Finset.sum_le_sum;intro J hJ
        have hJF:=Finset.mem_powerset.mp hJ
        exact weighted_uniform_term R D₁ D₂ hR (Finset.mem_powerset.mp hD₁)
          (Finset.mem_powerset.mp hD₂) J b M (fun i hi=>hM i (hJF hi)) t ht
      _=_:=by simp only [Finset.sum_const,nsmul_eq_mul];ring
  let N:ℝ:=(∏I∈R,I).absNorm
  have hN:1≤N:=product_norm_ge_one R hR
  have hN0:0<N:=zero_lt_one.trans_le hN
  have hmass:0≤∑J∈F.powerset,∏i∈J,(Real.sqrt (max 1 (b i))*M i)*(∑I∈R,weight I):=by
    exact Finset.sum_nonneg (fun J hJ=>Finset.prod_nonneg (fun i hi=>mul_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) (hM i ((Finset.mem_powerset.mp hJ) hi)))
      (Finset.sum_nonneg (fun I _=>weight_nonneg I))))
  have hpow:(∏I∈R,localMass I)^F.card≤Ce^F.card*N^(eps/2):=by
    calc
      _≤(Ce*N^delta)^F.card:=pow_le_pow_left₀
        (Finset.prod_nonneg (fun I hi=>localMass_nonneg I (hR I hi))) (heuler R hR) _
      _=Ce^F.card*N^(delta*(F.card:ℝ)):=by rw [mul_pow,←Real.rpow_mul_natCast hN0.le]
      _≤_:=mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN (by
        dsimp [delta]
        rw [div_mul_eq_mul_div]
        apply (div_le_iff₀ (by positivity:0<2*((F.card:ℝ)+1))).mpr
        nlinarith)) (by positivity)
  calc
    _≤(R.powerset.card:ℝ)^2*(A*(∏I∈R,localMass I)^F.card):=
      hsum.trans (mul_le_mul_of_nonneg_left (slot_majorant_mass R hR F b M hM) (sq_nonneg _))
    _≤(Cc*N^(eps/2))*(A*(Ce^F.card*N^(eps/2))):=
      mul_le_mul (hcard R hR) (mul_le_mul_of_nonneg_left hpow hA.le)
        (mul_nonneg hA.le (pow_nonneg (Finset.prod_nonneg (fun I hi=>localMass_nonneg I (hR I hi))) _))
        (by positivity)
    _=(Cc*A*Ce^F.card)*N^eps:=by
      rw [show (Cc*N^(eps/2))*(A*(Ce^F.card*N^(eps/2)))=
        (Cc*A*Ce^F.card)*(N^(eps/2)*N^(eps/2)) by ring,←Real.rpow_add hN0]
      congr 2
      ring

theorem weighted_signed_mass_subpower (F:Finset α)(b M:α→ℝ)(hM:∀i∈F,0≤M i)
    (eps:ℝ)(heps:0<eps):
    ∃C:ℝ,0<C ∧ ∀(R:Finset (Ideal O))(_hR:∀I∈R,Prime I)
      (χ:Character)(pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ),
      (∀i∈F,∀I∈pool i,Prime I)→(∀i∈F,0<P i)→
      (∀i∈F,∀I∈pool i,‖β i I‖≤M i)→
      (∀i∈F,∀I∈pool i,β i I≠0→(I.absNorm:ℝ)≤b i*P i)→
      ∀t:ℝ,t≤1/2→
      (∑D₁∈R.powerset,∑D₂∈R.powerset,∑J∈F.powerset,
        ‖signedCoefficient χ R D₁ D₂ J pool β P‖*((∏I∈D₂,I).absNorm:ℝ)^t)≤
        C*((∏I∈R,I).absNorm:ℝ)^eps:=by
  obtain ⟨C,hC,hbound⟩:=weighted_uniform_mass_subpower F b M hM eps heps
  refine ⟨C,hC,?_⟩
  intro R hR χ pool β P hp hP hβ hs t ht
  apply le_trans _ (hbound R hR t ht)
  apply Finset.sum_le_sum;intro D₁ hD₁
  apply Finset.sum_le_sum;intro D₂ hD₂
  apply Finset.sum_le_sum;intro J hJ
  have hJF:=Finset.mem_powerset.mp hJ
  exact mul_le_mul_of_nonneg_right
    (signedCoefficient_uniform χ R hR D₁ D₂ (Finset.mem_powerset.mp hD₁)
      (Finset.mem_powerset.mp hD₂) J pool β P b M
      (fun i hi=>hp i (hJF hi)) (fun i hi=>hP i (hJF hi))
      (fun i hi=>hM i (hJF hi)) (fun i hi=>hβ i (hJF hi))
      (fun i hi=>hs i (hJF hi))) (Real.rpow_nonneg (Nat.cast_nonneg _) t)

end SevenEighths.CenteredMomentEnergyReferenceDeletionBudget

end

end OAI
