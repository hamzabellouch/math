import OAI.Analysis.ModularRecovery.FourierOperators

namespace OAI

/-! Spatial Tomita conjugation and modular covariance. -/

universe u

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace StandardModularData

def jConjugate (S : StandardModularData H) (a : H →L[ℂ] H) : H →L[ℂ] H where
  toFun h := S.J (a (S.J h))
  map_add' _ _ := by simp only [map_add]
  map_smul' z h := by
    simp only [map_smulₛₗ,starRingEnd_self_apply,RingHom.id_apply]
  cont := S.J.continuous.comp (a.continuous.comp S.J.continuous)

@[simp] lemma jConjugate_apply (S : StandardModularData H) (a : H →L[ℂ] H) (h : H) :
    S.jConjugate a h = S.J (a (S.J h)) := rfl

@[simp] lemma jConjugate_involutive (S : StandardModularData H) (a : H →L[ℂ] H) :
    S.jConjugate (S.jConjugate a) = a := by
  ext h
  simp only [S.jConjugate_apply]
  rw [S.conjugation h,S.conjugation (a h)]

lemma normalizedFourier_on_dense (S : StandardModularData H) (t : ℝ)
    (ht : 0 < (kernelFourier t).re) (b : S.M.commutant.toStarSubalgebra) (x : H) :
    (S.normalizedFourier t b:H →L[ℂ] H) (S.D.unitary t (S.J x)) =
      S.D.unitary t (S.J ((star (b:H →L[ℂ] H)) x)) := by
  refine (commutant_cyclic S.M S.xi S.separating).induction ?_ ?_ x
  · rintro v ⟨c,hc,rfl⟩
    let c' : S.M.commutant.toStarSubalgebra := ⟨c,hc⟩
    have he := congrArg (fun a : S.M.toStarSubalgebra => (a:H →L[ℂ] H) S.xi)
      (S.normalizedFourier_mul t ht (star c') b)
    change (S.normalizedFourier t (star c'*b):H →L[ℂ] H) S.xi =
      (S.normalizedFourier t b:H →L[ℂ] H) ((S.normalizedFourier t (star c'):H →L[ℂ] H) S.xi) at he
    simp only [S.normalizedFourier_xi t (kernelFourier_ne_zero ht),star_mul,star_star] at he
    exact he.symm
  · exact isClosed_eq
      ((S.normalizedFourier t b:H →L[ℂ] H).continuous.comp ((S.D.unitary t).continuous.comp S.J.continuous))
      ((S.D.unitary t).continuous.comp (S.J.continuous.comp (star (b:H →L[ℂ] H)).continuous))

lemma normalizedFourier_spatial (S : StandardModularData H) (t : ℝ)
    (ht : 0 < (kernelFourier t).re) (b : S.M.commutant.toStarSubalgebra) :
    (S.normalizedFourier t b:H →L[ℂ] H) = S.sigma t (S.jConjugate (star (b:H →L[ℂ] H))) := by
  ext h
  have he := S.normalizedFourier_on_dense t ht b (S.J (S.D.unitary (-t) h))
  rw [S.conjugation] at he
  have hu : S.D.unitary t (S.D.unitary (-t) h) = h := by
    change (S.D.unitary t*S.D.unitary (-t)) h = h
    rw [S.D.unitary_mul_neg]
    rfl
  rw [hu] at he
  exact he

lemma sigma_jConjugate_mem (S : StandardModularData H) (t : ℝ)
    (ht : 0 < (kernelFourier t).re) (b : H →L[ℂ] H) (hb : b ∈ S.M.commutant) :
    S.sigma t (S.jConjugate b) ∈ S.M := by
  let c : S.M.commutant.toStarSubalgebra := ⟨star b,star_mem hb⟩
  have he := S.normalizedFourier_spatial t ht c
  change (S.normalizedFourier t c:H →L[ℂ] H) = S.sigma t (S.jConjugate (star (star b))) at he
  rw [star_star] at he
  exact he ▸ (S.normalizedFourier t c).property

@[simp] lemma sigma_zero (S : StandardModularData H) (a : H →L[ℂ] H) : S.sigma 0 a = a := by
  simp only [sigma,neg_zero,S.D.unitary_zero,one_mul,mul_one]

lemma jConjugate_mem (S : StandardModularData H) (b : H →L[ℂ] H) (hb : b ∈ S.M.commutant) :
    S.jConjugate b ∈ S.M := by
  have hp : 0 < (kernelFourier 0).re := by
    rw [kernelFourier_zero,Complex.ofReal_re]
    exact kernelMass_pos
  simpa only [S.sigma_zero] using S.sigma_jConjugate_mem 0 hp b hb

lemma jConjugate_mem_commutant (S : StandardModularData H) (a : H →L[ℂ] H) (ha : a ∈ S.M) :
    S.jConjugate a ∈ S.M.commutant := by
  apply S.commutantData.jConjugate_mem a
  change a ∈ S.M.commutant.commutant
  simpa only [VonNeumannAlgebra.commutant_commutant] using ha

lemma sigma_mem_of_fourier_positive (S : StandardModularData H) (t : ℝ)
    (ht : 0 < (kernelFourier t).re) (a : H →L[ℂ] H) (ha : a ∈ S.M) :
    S.sigma t a ∈ S.M := by
  have hh := S.sigma_jConjugate_mem t ht (S.jConjugate a) (S.jConjugate_mem_commutant a ha)
  simpa only [S.jConjugate_involutive] using hh

end StandardModularData
end BoundedRecovery

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace StandardModularData

lemma sigma_add_time (S : StandardModularData H) (s t : ℝ) (a : H →L[ℂ] H) :
    S.sigma (s+t) a = S.sigma s (S.sigma t a) := by
  simp only [sigma,S.D.unitary_add,neg_add_rev,mul_assoc]

lemma modular_covariance (S : StandardModularData H) (t : ℝ) (a : H →L[ℂ] H) (ha : a ∈ S.M) :
    S.D.unitary t * a * S.D.unitary (-t) ∈ S.M := by
  obtain ⟨d,hd,hdt⟩ := kernelFourier_positive_near_zero
  have hlocal (r : ℝ) (hr : |r| < d) (b : H →L[ℂ] H) (hb : b ∈ S.M) : S.sigma r b ∈ S.M :=
    S.sigma_mem_of_fourier_positive r (hdt r hr) b hb
  have hiterate (r : ℝ) (hr : |r| < d) (n : ℕ) : S.sigma ((n:ℝ)*r) a ∈ S.M := by
    induction n with
    | zero => simpa only [Nat.cast_zero,zero_mul,S.sigma_zero] using ha
    | succ n ih =>
      rw [Nat.cast_succ,add_mul,one_mul,add_comm,S.sigma_add_time]
      exact hlocal r hr _ ih
  obtain ⟨n,hn⟩ := exists_nat_gt (|t|/d+1)
  have hnpos : 0 < (n:ℝ) := by have := div_nonneg (abs_nonneg t) hd.le; linarith
  have hdiv : |t/(n:ℝ)| < d := by
    rw [abs_div,abs_of_pos hnpos,div_lt_iff₀ hnpos]
    have he : |t|/d < (n:ℝ) := by linarith
    have hh := (div_lt_iff₀ hd).mp he
    nlinarith
  have hh := hiterate (t/(n:ℝ)) hdiv n
  have he : (n:ℝ)*(t/(n:ℝ)) = t := by field_simp
  rwa [he] at hh

lemma modular_covariance_iff (S : StandardModularData H) (t : ℝ) (a : H →L[ℂ] H) :
    S.sigma t a ∈ S.M ↔ a ∈ S.M := by
  constructor
  · intro ha
    have hh := S.modular_covariance (-t) (S.sigma t a) ha
    change S.sigma (-t) (S.sigma t a) ∈ S.M at hh
    simpa only [← S.sigma_add_time,neg_add_cancel,S.sigma_zero] using hh
  · exact S.modular_covariance t a

end StandardModularData
end BoundedRecovery

end
end

end OAI
