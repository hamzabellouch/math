import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.FermionicCoefficients
import OAI.Analysis.CoulombRadii.FormDomain.WeakFourierDerivative

namespace OAI

section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexConjugate ContDiff BigOperators
noncomputable section
namespace Coulomb
namespace H1Vector
variable {n:ℕ}
def valueL2 (u:H1Vector n) (s:Spins n) : Lp ℂ 2 (volume:Measure (Configuration n)) :=
  (u.value_L2 s).toLp (u.value s)
def gradientL2 (u:H1Vector n) (s:Spins n) (a:Fin n × Fin 3) : Lp ℂ 2 (volume:Measure (Configuration n)) :=
  (u.partial_L2 s a).toLp (u.gradient s a)
lemma valueL2_ae (u:H1Vector n) (s:Spins n) : (u.valueL2 s:Configuration n → ℂ)=ᵐ[volume]u.value s :=
  (u.value_L2 s).coeFn_toLp
lemma gradientL2_ae (u:H1Vector n) (s:Spins n) (a:Fin n × Fin 3) :
    (u.gradientL2 s a:Configuration n → ℂ)=ᵐ[volume]u.gradient s a :=
  (u.partial_L2 s a).coeFn_toLp
lemma mass_eq_norm (u:H1Vector n) : mass u=∑ s,‖u.valueL2 s‖^2 := by
  apply Finset.sum_congr rfl
  intro s _
  rw [l2_norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [u.valueL2_ae s] with x hx
  rw [hx]
lemma kinetic_eq_norm (u:H1Vector n) : kinetic u=(1/2:ℝ)*∑ s,∑ a,‖u.gradientL2 s a‖^2 := by
  unfold kinetic
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro a _
  rw [l2_norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [u.gradientL2_ae s a] with x hx
  rw [hx]
lemma weak_partial_L2 (u:H1Vector n) (s:Spins n) (a:Fin n × Fin 3)
    (φ:Configuration n → ℝ) (hφ:ContDiff ℝ ∞ φ) (hc:HasCompactSupport φ) :
    (∫ x,(fderiv ℝ φ x (EuclideanSpace.single a 1):ℂ)*u.valueL2 s x)=
      -(∫ x,(φ x:ℂ)*u.gradientL2 s a x) := by
  have h1:(∫ x,(fderiv ℝ φ x (EuclideanSpace.single a 1):ℂ)*u.valueL2 s x)=
      ∫ x,u.value s x*(fderiv ℝ φ x (EuclideanSpace.single a 1):ℂ) := by
    apply integral_congr_ae
    filter_upwards [u.valueL2_ae s] with x hx
    rw [hx,mul_comm]
  have h2:(∫ x,(φ x:ℂ)*u.gradientL2 s a x)=∫ x,u.gradient s a x*(φ x:ℂ) := by
    apply integral_congr_ae
    filter_upwards [u.gradientL2_ae s a] with x hx
    rw [hx,mul_comm]
  rw [h1,h2]
  exact u.weak_partial s a φ hφ hc

def ofL2 (v:Spins n → Lp ℂ 2 (volume:Measure (Configuration n)))
    (g:Spins n → (Fin n × Fin 3) → Lp ℂ 2 (volume:Measure (Configuration n)))
    (hw:∀ s a (φ:Configuration n → ℝ),ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x,(fderiv ℝ φ x (EuclideanSpace.single a 1):ℂ)*v s x)=-(∫ x,(φ x:ℂ)*g s a x)) : H1Vector n where
  value:=fun s => v s
  gradient:=fun s a => g s a
  value_L2:=fun s => Lp.memLp (v s)
  partial_L2:=fun s a => Lp.memLp (g s a)
  weak_partial:=by
    intro s a φ hφ hc
    simpa only [mul_comm] using hw s a φ hφ hc
lemma ofL2_valueL2 (v:Spins n → Lp ℂ 2 (volume:Measure (Configuration n)))
    (g:Spins n → (Fin n × Fin 3) → Lp ℂ 2 (volume:Measure (Configuration n))) hw (s:Spins n) :
    (ofL2 v g hw).valueL2 s=v s := by
  apply Lp.ext
  exact (Lp.memLp (v s)).coeFn_toLp
lemma ofL2_gradientL2 (v:Spins n → Lp ℂ 2 (volume:Measure (Configuration n)))
    (g:Spins n → (Fin n × Fin 3) → Lp ℂ 2 (volume:Measure (Configuration n))) hw (s:Spins n) (a:Fin n × Fin 3) :
    (ofL2 v g hw).gradientL2 s a=g s a := by
  apply Lp.ext
  exact (Lp.memLp (g s a)).coeFn_toLp
end H1Vector

lemma antisymmetric_iff_valueL2 {n:ℕ} (u:H1Vector n) : Antisymmetric u ↔
    ∀ (p:Equiv.Perm (Fin n)) (s:Spins n),
      Lp.compMeasurePreservingₗᵢ ℂ (permute p) (permute_measurePreserving p) (u.valueL2 (s ∘ p))=
        ((p.sign:ℤ):ℂ) • u.valueL2 s := by
  constructor
  · intro ha p s
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving (u.valueL2 (s ∘ p)) (permute_measurePreserving p),
      (permute_measurePreserving p).quasiMeasurePreserving.ae (u.valueL2_ae (s ∘ p)),
      Lp.coeFn_smul ((p.sign:ℤ):ℂ) (u.valueL2 s),u.valueL2_ae s,ha p s] with x h1 h2 h3 h4 h5
    change Lp.compMeasurePreserving (permute p) (permute_measurePreserving p) (u.valueL2 (s ∘ p)) x = _
    rw [h1,h3]
    change u.valueL2 (s ∘ p) (permute p x) = ((p.sign:ℤ):ℂ) * u.valueL2 s x
    rw [h2,h4]
    exact h5
  · intro ha p s
    have he:=Lp.ext_iff.mp (ha p s)
    filter_upwards [he,Lp.coeFn_compMeasurePreserving (u.valueL2 (s ∘ p)) (permute_measurePreserving p),
      (permute_measurePreserving p).quasiMeasurePreserving.ae (u.valueL2_ae (s ∘ p)),
      Lp.coeFn_smul ((p.sign:ℤ):ℂ) (u.valueL2 s),u.valueL2_ae s] with x he h1 h2 h3 h4
    change Lp.compMeasurePreserving (permute p) (permute_measurePreserving p) (u.valueL2 (s ∘ p)) x = _ at he
    rw [h1,h3] at he
    change u.valueL2 (s ∘ p) (permute p x) = ((p.sign:ℤ):ℂ) * u.valueL2 s x at he
    rwa [h2,h4] at he

lemma antisymmetric_strong_limit {n:ℕ} (u:ℕ → H1Vector n) (v:H1Vector n)
    (ha:∀ k,Antisymmetric (u k))
    (hv:∀ s,Tendsto (fun k => (u k).valueL2 s) atTop (𝓝 (v.valueL2 s))) : Antisymmetric v := by
  rw [antisymmetric_iff_valueL2]
  intro p s
  have h1:=((Lp.compMeasurePreservingₗᵢ ℂ (permute p) (permute_measurePreserving p)).continuous.tendsto
    (v.valueL2 (s ∘ p))).comp (hv (s ∘ p))
  have h2:=(hv s).const_smul (((p.sign:ℤ):ℂ))
  exact tendsto_nhds_unique h1 (by
    convert h2 using 1
    apply funext
    intro k
    exact (antisymmetric_iff_valueL2 (u k)).mp (ha k) p s)
end Coulomb
end

end
section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology FourierTransform ComplexConjugate BigOperators ContDiff
noncomputable section
namespace Coulomb
lemma memlp_real_inner_integrable {X:Type*} [MeasurableSpace X] {μ:Measure X}
    {f g:X → ℂ} (hf:MemLp f 2 μ) (hg:MemLp g 2 μ) : Integrable (fun x => inner ℝ (f x) (g x)) μ := by
  apply (hf.norm.integrable_sq.add hg.norm.integrable_sq).mono'
    (hf.aestronglyMeasurable.inner hg.aestronglyMeasurable)
  exact Eventually.of_forall fun x => by
    have hb:=norm_inner_le_norm (𝕜:=ℝ) (f x) (g x)
    have hs:=sq_nonneg (‖f x‖-‖g x‖)
    change ‖inner ℝ (f x) (g x)‖ ≤ ‖f x‖^2+‖g x‖^2
    nlinarith [sq_nonneg ‖f x‖,sq_nonneg ‖g x‖]
lemma l2_weakDeriv_skew {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {u du v dv:Lp ℂ 2 (volume:Measure E)} (a:E)
    (hu:∀ φ:E → ℝ,ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x,(fderiv ℝ φ x a:ℂ)*u x)=-(∫ x,(φ x:ℂ)*du x))
    (hv:∀ φ:E → ℝ,ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x,(fderiv ℝ φ x a:ℂ)*v x)=-(∫ x,(φ x:ℂ)*dv x)) :
    inner ℂ du v= -inner ℂ u dv := by
  rw [←(Lp.fourierTransformₗᵢ E ℂ).inner_map_map du v,
    ←(Lp.fourierTransformₗᵢ E ℂ).inner_map_map u dv,L2.inner_def,L2.inner_def,←integral_neg]
  apply integral_congr_ae
  filter_upwards [l2_weakDeriv_fourier a hu,l2_weakDeriv_fourier a hv] with ξ h1 h2
  change inner ℂ ((𝓕 du:Lp ℂ 2 (volume:Measure E)) ξ) ((𝓕 v:Lp ℂ 2 (volume:Measure E)) ξ)=
    -inner ℂ ((𝓕 u:Lp ℂ 2 (volume:Measure E)) ξ) ((𝓕 dv:Lp ℂ 2 (volume:Measure E)) ξ)
  rw [h1,h2]
  simp only [RCLike.inner_apply,map_mul,map_ofNat,Complex.conj_ofReal,Complex.conj_I]
  ring

lemma h1_green {n:ℕ} (u v:H1Vector n) (s:Spins n) (a:Fin n × Fin 3) :
    (∫ x,inner ℝ (u.gradient s a x) (v.value s x)) =
      -(∫ x,inner ℝ (u.value s x) (v.gradient s a x)) := by
  have H:=l2_weakDeriv_skew (EuclideanSpace.single a (1:ℝ)) (u.weak_partial_L2 s a) (v.weak_partial_L2 s a)
  have HH:=congrArg Complex.re H
  rw [L2.inner_def,L2.inner_def,Complex.neg_re] at HH
  change RCLike.re (∫ x,inner ℂ (u.gradientL2 s a x) (v.valueL2 s x))=
    -RCLike.re (∫ x,inner ℂ (u.valueL2 s x) (v.gradientL2 s a x)) at HH
  rw [←integral_re (L2.integrable_inner (u.gradientL2 s a) (v.valueL2 s)),
    ←integral_re (L2.integrable_inner (u.valueL2 s) (v.gradientL2 s a))] at HH
  convert HH using 1
  · apply integral_congr_ae
    filter_upwards [u.gradientL2_ae s a,v.valueL2_ae s] with x hx hy
    rw [hx,hy]
    rfl
  · congr 1
    apply integral_congr_ae
    filter_upwards [u.valueL2_ae s,v.gradientL2_ae s a] with x hx hy
    rw [hx,hy]
    rfl

lemma h1_multiplier_ibp {n:ℕ} (u:H1Vector n) (s:Spins n) (a:Fin n × Fin 3)
    (F:Configuration n → ℝ) (hF:ContDiff ℝ ∞ F) (B D:ℝ)
    (hB:∀ x,|F x|≤B) (hD:∀ b x,|fderiv ℝ F x (EuclideanSpace.single b 1)|≤D) :
    (∫ x,fderiv ℝ F x (EuclideanSpace.single a 1)*‖u.value s x‖^2)=
      -2*(∫ x,F x*inner ℝ (u.value s x) (u.gradient s a x)) := by
  let v:=u.smoothMul F hF B D hB hD
  have H:=h1_green u v s a
  have hcross:Integrable (fun x => F x*inner ℝ (u.value s x) (u.gradient s a x)) := by
    have h:Integrable (fun x => inner ℝ ((F x:ℂ)*u.value s x) (u.gradient s a x)) :=
      memlp_real_inner_integrable (v.value_L2 s) (u.partial_L2 s a)
    simpa only [←Complex.real_smul,real_inner_smul_left] using h
  have hder:Integrable (fun x => fderiv ℝ F x (EuclideanSpace.single a 1)*‖u.value s x‖^2) := by
    have h:= memlp_real_inner_integrable (u.value_L2 s)
      (memLp_two_real_mul (u.value_L2 s) ((hF.continuous_fderiv (by simp)).clm_apply continuous_const) (hD a))
    simpa only [←Complex.real_smul,real_inner_smul_right,real_inner_self_eq_norm_sq] using h
  have hl:(∫ x,inner ℝ (u.gradient s a x) (v.value s x))=
      ∫ x,F x*inner ℝ (u.value s x) (u.gradient s a x) := by
    apply integral_congr_ae
    filter_upwards [] with x
    change inner ℝ (u.gradient s a x) ((F x:ℂ)*u.value s x)=_
    rw [←Complex.real_smul,real_inner_smul_right,real_inner_comm]
  have hr:(∫ x,inner ℝ (u.value s x) (v.gradient s a x))=
      (∫ x,fderiv ℝ F x (EuclideanSpace.single a 1)*‖u.value s x‖^2)+
      ∫ x,F x*inner ℝ (u.value s x) (u.gradient s a x) := by
    change (∫ x,inner ℝ (u.value s x) ((fderiv ℝ F x (EuclideanSpace.single a 1):ℂ)*u.value s x+(F x:ℂ)*u.gradient s a x))=_
    simp only [inner_add_right,←Complex.real_smul,real_inner_smul_right,real_inner_self_eq_norm_sq]
    exact integral_add hder hcross
  rw [hl,hr] at H
  linarith
end Coulomb
end

end

end OAI
