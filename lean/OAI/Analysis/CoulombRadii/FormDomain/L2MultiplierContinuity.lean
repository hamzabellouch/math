import Mathlib
import OAI.Analysis.CoulombRadii.FormDomain.Add
import OAI.Analysis.CoulombRadii.FormDomain.L2TightCompact
import OAI.Analysis.CoulombRadii.FieldAnalysis.FiniteSubsequence
import OAI.Analysis.CoulombRadii.FormDomain.H1VectorL2

namespace OAI

section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexConjugate BigOperators
noncomputable section
namespace Coulomb
variable {X:Type*} [MeasurableSpace X] {μ:Measure X}
lemma real_multiplier_inner (f:X → ℝ) (u v U V:Lp ℂ 2 μ)
    (hu:(U:X → ℂ)=ᵐ[μ]fun x => (f x:ℂ)*u x)
    (hv:(V:X → ℂ)=ᵐ[μ]fun x => (f x:ℂ)*v x) :
    inner ℂ v U=inner ℂ V u := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hu,hv] with x hx hy
  simp only [RCLike.inner_apply,hx,hy,map_mul,Complex.conj_ofReal]
  ring
lemma real_multiplier_quadratic (f:X → ℝ) (u U:Lp ℂ 2 μ)
    (hu:(U:X → ℂ)=ᵐ[μ]fun x => (f x:ℂ)*u x) :
    (inner ℂ u U).re=∫ x,f x*‖u x‖^2 ∂μ := by
  rw [L2.inner_def]
  change RCLike.re (∫ x,inner ℂ (u x) (U x) ∂μ)=_
  rw [←integral_re (L2.integrable_inner (𝕜:=ℂ) u U)]
  apply integral_congr_ae
  filter_upwards [hu] with x hx
  rw [hx]
  change (((f x:ℂ)*u x)*conj (u x)).re=f x*‖u x‖^2
  rw [mul_assoc,Complex.mul_conj]
  simp [Complex.normSq_eq_norm_sq,-Complex.ofReal_pow]

lemma real_multiplier_quadratic_diff_bound (f:X → ℝ) (u v U V:Lp ℂ 2 μ)
    (hu:(U:X → ℂ)=ᵐ[μ]fun x => (f x:ℂ)*u x)
    (hv:(V:X → ℂ)=ᵐ[μ]fun x => (f x:ℂ)*v x) :
    |(inner ℂ u U).re-(inner ℂ v V).re|≤(‖U‖+‖V‖)*‖u-v‖ := by
  have he : inner ℂ u U-inner ℂ v V=inner ℂ (u-v) U+inner ℂ V (u-v) := by
    rw [inner_sub_left,inner_sub_right,←real_multiplier_inner f u v U V hu hv,
      ←real_multiplier_inner f v v V V hv hv]
    abel
  calc
    |(inner ℂ u U).re-(inner ℂ v V).re|=|(inner ℂ u U-inner ℂ v V).re|:=rfl
    _ ≤ ‖inner ℂ u U-inner ℂ v V‖ := Complex.abs_re_le_norm _
    _ ≤ ‖inner ℂ (u-v) U‖+‖inner ℂ V (u-v)‖ := by rw [he]; exact norm_add_le _ _
    _ ≤ ‖u-v‖*‖U‖+‖V‖*‖u-v‖ := add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ = (‖U‖+‖V‖)*‖u-v‖ := by ring
lemma real_multiplier_quadratic_tendsto (f:X → ℝ) (u:ℕ → Lp ℂ 2 μ) (v:Lp ℂ 2 μ)
    (U:ℕ → Lp ℂ 2 μ) (V:Lp ℂ 2 μ)
    (hu:∀ k,(U k:X → ℂ)=ᵐ[μ]fun x => (f x:ℂ)*u k x)
    (hv:(V:X → ℂ)=ᵐ[μ]fun x => (f x:ℂ)*v x)
    (hconv:Tendsto u atTop (𝓝 v)) (C:ℝ) (hC:∀ k,‖U k‖≤C) :
    Tendsto (fun k => ∫ x,f x*‖u k x‖^2 ∂μ) atTop (𝓝 (∫ x,f x*‖v x‖^2 ∂μ)) := by
  simp_rw [←real_multiplier_quadratic f _ _ hv]
  have H:Tendsto (fun k => (inner ℂ (u k) (U k)).re-(inner ℂ v V).re) atTop (𝓝 0) := by
    apply squeeze_zero_norm (a:=fun k => (C+‖V‖)*‖u k-v‖)
    · intro k
      exact (real_multiplier_quadratic_diff_bound f (u k) v (U k) V (hu k) hv).trans
        (mul_le_mul_of_nonneg_right (add_le_add (hC k) (le_refl ‖V‖)) (norm_nonneg _))
    · have h:=((hconv.sub_const v).norm.const_mul (C+‖V‖))
      simpa using h
  have he: Tendsto (fun k => (inner ℂ (u k) (U k)).re) atTop (𝓝 (inner ℂ v V).re) :=
    (tendsto_sub_nhds_zero_iff).mp H
  simpa only [real_multiplier_quadratic f _ _ (hu _)] using he
end Coulomb
end

end
section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexConjugate BigOperators
noncomputable section
namespace Coulomb
variable {n:ℕ}
lemma H1Vector.hardy_multiplier_memLp (u:H1Vector n) (s:Spins n) (i:Fin n) (R:HardyCoordinates n i) :
    MemLp (fun x => (hardyCoulomb i R x:ℂ)*u.valueL2 s x) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm
    (((measurable_hardyCoulomb i R).complex_ofReal.aestronglyMeasurable).mul
      (Lp.memLp (u.valueL2 s)).aestronglyMeasurable)).mpr
  apply (u.hardy s i R).1.congr
  filter_upwards [u.valueL2_ae s] with x hx
  change (blockRadiusSq i R x)⁻¹*‖u.value s x‖^2 = ‖(hardyCoulomb i R x:ℂ)*u.valueL2 s x‖^2
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs,hardyCoulomb_sq,hx]

def H1Vector.hardyMultiplier (u:H1Vector n) (s:Spins n) (i:Fin n) (R:HardyCoordinates n i) :
    Lp ℂ 2 (volume:Measure (Configuration n)) :=
  (u.hardy_multiplier_memLp s i R).toLp _
lemma H1Vector.hardyMultiplier_ae (u:H1Vector n) (s:Spins n) (i:Fin n) (R:HardyCoordinates n i) :
    (u.hardyMultiplier s i R:Configuration n → ℂ)=ᵐ[volume]fun x => (hardyCoulomb i R x:ℂ)*u.valueL2 s x :=
  (u.hardy_multiplier_memLp s i R).coeFn_toLp
lemma H1Vector.hardyMultiplier_norm_sq (u:H1Vector n) (s:Spins n) (i:Fin n) (R:HardyCoordinates n i) :
    ‖u.hardyMultiplier s i R‖^2≤8*kinetic u := by
  rw [l2_norm_sq_integral]
  have he:(∫ x,‖u.hardyMultiplier s i R x‖^2)=∫ x,(blockRadiusSq i R x)⁻¹*‖u.value s x‖^2 := by
    apply integral_congr_ae
    filter_upwards [u.hardyMultiplier_ae s i R,u.valueL2_ae s] with x hx hy
    simp only [hx,norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs,hardyCoulomb_sq,hy]
  rw [he]
  have hs:(∑ b:Fin 3,∫ x,‖u.gradient s (i,b) x‖^2)≤∑ a:Fin n × Fin 3,∫ x,‖u.gradient s a x‖^2 := by
    rw [Fintype.sum_prod_type]
    exact Finset.single_le_sum (f:=fun j:Fin n => ∑ b:Fin 3,∫ x:Configuration n,‖u.gradient s (j,b) x‖^2)
      (fun j _ => Finset.sum_nonneg fun b _ => integral_nonneg fun x => sq_nonneg _) (Finset.mem_univ i)
  have ht:(∑ a,∫ x,‖u.gradient s a x‖^2)≤∑ t,∑ a,∫ x,‖u.gradient t a x‖^2 :=
    Finset.single_le_sum (f:=fun t:Spins n => ∑ a:Fin n × Fin 3,∫ x:Configuration n,‖u.gradient t a x‖^2)
      (fun t _ => Finset.sum_nonneg fun a _ => integral_nonneg fun x => sq_nonneg _) (Finset.mem_univ s)
  have hh:=(u.hardy s i R).2
  unfold kinetic
  linarith
lemma H1Vector.hardyMultiplier_norm_le (u:H1Vector n) (s:Spins n) (i:Fin n) (R:HardyCoordinates n i)
    {K:ℝ} (hK:kinetic u≤K) : ‖u.hardyMultiplier s i R‖≤Real.sqrt (8*K) := by
  have hp:0≤8*K:=mul_nonneg (by norm_num) ((kinetic_nonneg u).trans hK)
  apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt hp]
  exact (u.hardyMultiplier_norm_sq s i R).trans (mul_le_mul_of_nonneg_left hK (by norm_num))
lemma hardy_form_strong_tendsto (u:ℕ → H1Vector n) (v:H1Vector n) (s:Spins n) (i:Fin n) (R:HardyCoordinates n i)
    (hv:Tendsto (fun k => (u k).valueL2 s) atTop (𝓝 (v.valueL2 s)))
    (K:ℝ) (hK:∀ k,kinetic (u k)≤K) :
    Tendsto (fun k => ∫ x,hardyCoulomb i R x*‖(u k).value s x‖^2) atTop
      (𝓝 (∫ x,hardyCoulomb i R x*‖v.value s x‖^2)) := by
  have H:=real_multiplier_quadratic_tendsto (hardyCoulomb i R)
    (fun k => (u k).valueL2 s) (v.valueL2 s)
    (fun k => (u k).hardyMultiplier s i R) (v.hardyMultiplier s i R)
    (fun k => (u k).hardyMultiplier_ae s i R) (v.hardyMultiplier_ae s i R) hv
    (Real.sqrt (8*K)) (fun k => (u k).hardyMultiplier_norm_le s i R (hK k))
  have he(w:H1Vector n) : (∫ x,hardyCoulomb i R x*‖w.valueL2 s x‖^2)=
      ∫ x,hardyCoulomb i R x*‖w.value s x‖^2 := by
    apply integral_congr_ae
    filter_upwards [w.valueL2_ae s] with x hx
    rw [hx]
  simpa only [he] using H
end Coulomb
end

end
section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexConjugate ContDiff BigOperators
noncomputable section
namespace Coulomb
lemma h1_bounded_tight_compact {n:ℕ} (u:ℕ → H1Vector n) (K:ℝ)
    (hm:∀ k,mass (u k)=1) (hk:∀ k,kinetic (u k)≤K)
    (hsp:∀ ε:ℝ,0<ε → ∃ A:Set (Configuration n),∃ hA:MeasurableSet A,volume A≠(⊤:ℝ≥0∞) ∧
      ∀ᶠ k in atTop,∀ s,‖cutL2 Aᶜ hA.compl ((u k).valueL2 s)‖≤ε) :
    ∃ v:H1Vector n,mass v=1 ∧ kinetic v≤K ∧ ∃ φ:ℕ → ℕ,StrictMono φ ∧
      (∀ s,Tendsto (fun k => (u (φ k)).valueL2 s) atTop (𝓝 (v.valueL2 s))) ∧
      (∀ s a w,Tendsto (fun k => inner ℂ w ((u (φ k)).gradientL2 s a)) atTop
        (𝓝 (inner ℂ w (v.gradientL2 s a)))) := by
  let : Fact ((2:ℝ≥0∞)≠(⊤:ℝ≥0∞)) := ⟨by norm_num⟩
  have hK:0≤K := (kinetic_nonneg (u 0)).trans (hk 0)
  have huv (k:ℕ) (s:Spins n) : ‖(u k).valueL2 s‖≤1 := by
    have H:=hm k
    rw [H1Vector.mass_eq_norm] at H
    have hh:=Finset.single_le_sum (fun t _ => sq_nonneg ‖(u k).valueL2 t‖) (Finset.mem_univ s)
    nlinarith [norm_nonneg ((u k).valueL2 s)]
  have hgrad (k:ℕ) : ∑ s,∑ a,‖(u k).gradientL2 s a‖^2≤2*K := by
    have H:=hk k
    rw [H1Vector.kinetic_eq_norm] at H
    linarith
  have hgs (k:ℕ) (s:Spins n) : ∑ a,‖(u k).gradientL2 s a‖^2≤2*K :=
    (Finset.single_le_sum (fun t _ => Finset.sum_nonneg fun a _ => sq_nonneg _) (Finset.mem_univ s)).trans (hgrad k)
  obtain ⟨v0,φ,hφ,hv0⟩ := finite_simultaneous_subsequence (fun k s => (u k).valueL2 s) (by
    intro s φ hφ
    apply h1_spatial_tight_subsequence (fun k => (u (φ k)).valueL2 s)
      (fun k a => (u (φ k)).gradientL2 s a) (fun k a => (u (φ k)).weak_partial_L2 s a)
      1 (2*K) (fun k => huv (φ k) s) (fun k => hgs (φ k) s)
    intro ε hε
    obtain ⟨A,hA,hfin,H⟩:=hsp ε hε
    exact ⟨A,hA,hfin,(hφ.tendsto_atTop.eventually H).mono (fun k hk => hk s)⟩)
  let g0:ℕ → (Spins n × (Fin n × Fin 3)) → Lp ℂ 2 (volume:Measure (Configuration n)) :=
    fun k sa => (u (φ k)).gradientL2 sa.1 sa.2
  obtain ⟨g,hg,ψ,hψ,hw⟩:=bounded_finite_hilbert_weak_subsequence g0 (2*K) (by
    intro k
    simpa only [Fintype.sum_prod_type,g0] using hgrad (φ k))
  have hv(s:Spins n) : Tendsto (fun k => (u (φ (ψ k))).valueL2 s) atTop (𝓝 (v0 s)) :=
    (hv0 s).comp hψ.tendsto_atTop
  have hweak(s:Spins n) (a:Fin n × Fin 3) : ∀ (f:Configuration n → ℝ),ContDiff ℝ ∞ f → HasCompactSupport f →
      (∫ x,(fderiv ℝ f x (EuclideanSpace.single a 1):ℂ)*v0 s x)=-(∫ x,(f x:ℂ)*g (s,a) x) := by
    apply weak_l2_derivative_limit (EuclideanSpace.single a 1)
      (fun w => tendsto_const_nhds.inner (hv s)) (hw (s,a))
    exact fun k => (u (φ (ψ k))).weak_partial_L2 s a
  let v:=H1Vector.ofL2 v0 (fun s a => g (s,a)) hweak
  have hvv(s:Spins n) : v.valueL2 s=v0 s := H1Vector.ofL2_valueL2 ..
  have hvg(s:Spins n) (a:Fin n × Fin 3) : v.gradientL2 s a=g (s,a) := H1Vector.ofL2_gradientL2 ..
  refine ⟨v,?_,?_,φ ∘ ψ,hφ.comp hψ,?_,?_⟩
  · have H:Tendsto (fun k => ∑ s,‖(u (φ (ψ k))).valueL2 s‖^2) atTop (𝓝 (∑ s,‖v0 s‖^2)):=
      tendsto_finsetSum _ (fun s _ => (hv s).norm.pow 2)
    have he (k:ℕ) : (∑ s,‖(u (φ (ψ k))).valueL2 s‖^2)=1 := by
      rw [←H1Vector.mass_eq_norm]; exact hm _
    rw [H1Vector.mass_eq_norm]
    simp_rw [hvv]
    exact tendsto_nhds_unique H (by simp only [he]; exact tendsto_const_nhds)
  · rw [H1Vector.kinetic_eq_norm]
    simp_rw [hvg]
    rw [Fintype.sum_prod_type] at hg
    linarith
  · intro s
    simpa only [hvv,Function.comp_def] using hv s
  · intro s a w
    simpa only [hvg,Function.comp_def,g0] using hw (s,a) w
end Coulomb
end

end

end OAI
