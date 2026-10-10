import OAI.NumberTheory.DirichletL.Descent.CanonicalLongSource
import OAI.NumberTheory.DirichletL.Descent.GeneratorTransport
import OAI.NumberTheory.DirichletL.Descent.SecondNormalizedEnergy

namespace OAI

noncomputable section

open scoped BigOperators Classical
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve FirstPassCubeLabels SecondPassArithmetic
open InverseSecondFibers IdealMobiusDivisorSum InverseInitialClippedColumns
local notation "O"=>ActualEisensteinCubic.O

theorem child_ball_unit_mem (u:Oˣ)(R:ℝ)(k:O) :
    (u:O)*k∈nonzeroChildFrequencyBall 1 R ↔ k∈nonzeroChildFrequencyBall 1 R := by
  simp only [mem_nonzeroChildFrequencyBall 1 one_ne_zero,one_mul,
    GaussGeneratorTransport.norm_eisEmbedding_unit_mul]

theorem child_ball_unit_sum {A:Type*}[AddCommMonoid A](u:Oˣ)(R:ℝ)(f:O→A) :
    ∑k∈nonzeroChildFrequencyBall 1 R,f ((u:O)*k)=
      ∑k∈nonzeroChildFrequencyBall 1 R,f k := by
  apply Finset.sum_bij (fun k _=>(u:O)*k)
  · intro k hk
    exact (child_ball_unit_mem u R k).mpr hk
  · intro x hx y hy he
    exact mul_left_cancel₀ u.ne_zero he
  · intro y hy
    refine ⟨((u⁻¹:Oˣ):O)*y,(child_ball_unit_mem u⁻¹ R y).mpr hy,?_⟩
    rw [←mul_assoc,←Units.val_mul,mul_inv_cancel,Units.val_one,one_mul]
  · intros
    rfl

variable {ι σ:Type*}[DecidableEq ι]
  (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,goodLambda∉Ideal.span {p i})

theorem canonical_ball_generator_energy
    (pool:Finset ι)(Ψ:O→*ℂ)(m:O)(I:Ideal O)(hI:primaryGenerator I≠0)
    (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)(W:ℝ→ℂ)(X K:ℝ) :
    (∑k∈nonzeroChildFrequencyBall 1 K,
      ‖finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (primaryGenerator I) k slots lists a W X‖^2)=
    ∑k∈nonzeroChildFrequencyBall 1 K,
      ‖finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (idealGenerator I) k slots lists a W X‖^2 := by
  obtain ⟨u,hu⟩:=generator_eq_unit_primary I (idealGenerator I) (span_idealGenerator I) hI
  let P:O→ℝ:=fun k=>
    ‖finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (primaryGenerator I) k slots lists a W X‖^2
  have hrot:=child_ball_unit_sum (u^4) K P
  have he (k:O):
      ‖finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (idealGenerator I) k slots lists a W X‖^2=
      P (((u^4:Oˣ):O)*k) := by
    rw [hu,finiteCanonicalMarkedRow_label_transfer]
    rfl
  simp only [he]
  exact hrot.symm

theorem normalized_energy_le_actual_family
    (pool:Finset ι)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (labels:Finset (Ideal O))(hlabels:∀I∈labels,primaryGenerator I≠0)
    (weight:Ideal O→ℝ)(C:ℝ)(hC:0≤C)(hw:∀I∈labels,0≤weight I ∧ weight I≤C)
    (W:ℝ→ℂ)(X Z F K:ℝ)(hZ:0<Z)(hK:0<K) :
    normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels
      (nonzeroChildFrequencyBall 1 K) weight W X Z F ≤
      Z^(-F)*C*rowFamilyEnergy labels (fun I k=>
        finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (idealGenerator I) k slots lists a W X) K := by
  have hn:‖((Z^(-F/2):ℝ):ℂ)‖^2=Z^(-F) := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hZ _),
      ←Real.rpow_mul_natCast hZ.le]
    congr 1
    ring
  unfold normalizedColumnEnergy
  simp only [norm_mul,mul_pow,hn,←Finset.mul_sum]
  have he : (∑ I∈labels,weight I*(Z^(-F)*∑k∈nonzeroChildFrequencyBall 1 K,
      ‖finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (primaryGenerator I) k slots lists a W X‖^2))=
      Z^(-F)*(∑ I∈labels,weight I*∑k∈nonzeroChildFrequencyBall 1 K,
      ‖finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (primaryGenerator I) k slots lists a W X‖^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intros
    ring
  rw [he]
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hZ.le _)
  rw [rowFamilyEnergy,Complex.re_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro I hI
  rw [canonical_ball_generator_energy p hp hcop hg pool Ψ m I (hlabels I hI)]
  have hball:=finite_nonzero_row_energy_le_majorant
    (fun k=>finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (idealGenerator I) k slots lists a W X)
    (nonzeroChildFrequencyBall 1 K) K hK
    (by intro k hk
        rw [←eisEmbedding_norm_sq_eq_absNorm_span]
        simpa only [one_mul] using ((mem_nonzeroChildFrequencyBall 1 one_ne_zero K k).mp hk).2)
    (by intro k hk hn
        have hh:=((mem_nonzeroChildFrequencyBall 1 one_ne_zero K k).mp hk).1
        simp only [hn,mul_zero,map_zero,norm_zero,pow_succ,lt_self_iff_false] at hh)
  exact (mul_le_mul_of_nonneg_right (hw I hI).2 (Finset.sum_nonneg (fun _ _=>sq_nonneg _))).trans
    (mul_le_mul_of_nonneg_left hball hC)

end SevenEighths.InverseMoment

end

end OAI
