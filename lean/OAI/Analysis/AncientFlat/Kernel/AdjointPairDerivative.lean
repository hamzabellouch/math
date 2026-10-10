import OAI.Analysis.AncientFlat.Kernel.AdjointKernel
import OAI.Analysis.AncientFlat.Kernel.SymbolDecay

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff SchwartzMap Laplacian ZeroAtInfty BoundedContinuousFunction
namespace FlatDuality
open BiharmonicKernel InnerProductSpace ParametrixUniqueness FlatSimilarity
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
lemma schwartz_bilap_fun (φ : SchwartzMap V ℂ) :
    ((Δ (Δ φ : SchwartzMap V ℂ) : SchwartzMap V ℂ) : V → ℂ)=Δ (Δ (φ : V → ℂ)) := by
  have he : ((Δ φ : SchwartzMap V ℂ) : V → ℂ)=Δ (φ : V → ℂ) := funext (SchwartzMap.laplacian_apply φ)
  funext x
  rw [SchwartzMap.laplacian_apply,he]
lemma moving_boundedJets {Af Bf : V → ℝ} {d : C₀(V,ℂ)} {u : ℝ → C₀(V,ℂ)}
    (hu : MovesClassically Af Bf d u) {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    BoundedJets 4 (fun x => u t x) := by
  intro n hn
  obtain ⟨M,hM⟩ := hu.2.2.2.1 t ht n hn
  exact ⟨M,(norm_nonneg _).trans (hM 0),hM⟩
variable [MeasurableSpace V] [BorelSpace V]
def deviationTest (c : ℝ) (Af : V → ℝ) (t : ℝ) (φ : SchwartzMap V ℂ) : SchwartzMap V ℂ :=
  SchwartzMap.smulLeftCLM ℂ (movingDeviation c Af t) φ
def potentialTest (Bf : V → ℝ) (t : ℝ) (φ : SchwartzMap V ℂ) : SchwartzMap V ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fun x => Bf (Real.exp (t/4) • x)) φ
def adjointError (c : ℝ) (Af Bf : V → ℝ) (t : ℝ) (φ : SchwartzMap V ℂ) : SchwartzMap V ℂ :=
  Δ (Δ (deviationTest c Af t φ)) + potentialTest Bf t φ
lemma deviationTest_apply {c : ℝ} {Af Bf : V → ℝ} (h : SymbolBounds c Af Bf)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) (φ : SchwartzMap V ℂ) (x : V) :
    deviationTest c Af t φ x=(movingDeviation c Af t x : ℂ)*φ x := by
  simp only [deviationTest,SchwartzMap.smulLeftCLM_apply_apply (h.movingDeviation_temperate ht),Complex.real_smul]
lemma potentialTest_apply {c : ℝ} {Af Bf : V → ℝ} (h : SymbolBounds c Af Bf)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) (φ : SchwartzMap V ℂ) (x : V) :
    potentialTest Bf t φ x=(Bf (Real.exp (t/4) • x) : ℂ)*φ x := by
  simp only [potentialTest,SchwartzMap.smulLeftCLM_apply_apply (h.movingB_temperate ht),Complex.real_smul]
lemma integral_adjoint_cancel {c : ℝ} {Af Bf : V → ℝ} (h : SymbolBounds c Af Bf)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) (φ : SchwartzMap V ℂ) (u : V → ℂ)
    (hu : ContDiff ℝ 4 u) (hb : BoundedJets 4 u) (p : V → ℂ)
    (hp : ∀ x, p x=-((Real.exp (-t)/16*Af (Real.exp (t/4) • x) : ℝ) : ℂ)*Δ (Δ u) x-
      (1/2+(Bf (Real.exp (t/4) • x) : ℂ))*u x) :
    (∫ x, (((c^2*Real.exp (-t)/16 : ℝ) : ℂ)*(Δ (Δ φ : SchwartzMap V ℂ) : SchwartzMap V ℂ) x+
      (1/2:ℂ)*φ x)*u x+φ x*p x) = -(∫ x, adjointError c Af Bf t φ x*u x) := by
  let ψ := deviationTest c Af t φ
  let χ := potentialTest Bf t φ
  let ac : ℂ := ((c^2*Real.exp (-t)/16 : ℝ) : ℂ)
  have hcu : Continuous (Δ (Δ u)) :=
    (ClassicalIBP.contDiff_laplacian _ 0 (ClassicalIBP.contDiff_laplacian _ 2 hu)).continuous
  have hbu : Bounded (Δ (Δ u)) := ((hb.laplacian 2 hu).laplacian 0 (ClassicalIBP.contDiff_laplacian _ 2 hu)).zero
  have h1 := integrable_mul_bounded (Δ (Δ φ : SchwartzMap V ℂ) : SchwartzMap V ℂ).integrable hu.continuous hb.zero
  have h2 := integrable_mul_bounded φ.integrable hcu hbu
  have h3 := integrable_mul_bounded ψ.integrable hcu hbu
  have h4 := integrable_mul_bounded χ.integrable hu.continuous hb.zero
  have hd := integrable_mul_bounded (Δ (Δ ψ : SchwartzMap V ℂ) : SchwartzMap V ℂ).integrable hu.continuous hb.zero
  calc
    _ = ∫ x, ac*((Δ (Δ φ : SchwartzMap V ℂ) : SchwartzMap V ℂ) x*u x-φ x*Δ (Δ u) x)-
        ψ x*Δ (Δ u) x-χ x*u x := by
      apply integral_congr_ae
      filter_upwards with x
      dsimp only [ψ,χ,ac]
      rw [hp,deviationTest_apply h ht,potentialTest_apply h ht]
      simp only [movingDeviation,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_sub,
        Complex.ofReal_pow,Complex.ofReal_ofNat]
      ring
    _ = ac*((∫ x, (Δ (Δ φ : SchwartzMap V ℂ) : SchwartzMap V ℂ) x*u x)-
        (∫ x, φ x*Δ (Δ u) x))-(∫ x, ψ x*Δ (Δ u) x)-(∫ x, χ x*u x) := by
      have h12 : Integrable (fun x => ac*((Δ (Δ φ : SchwartzMap V ℂ) : SchwartzMap V ℂ) x*u x-φ x*Δ (Δ u) x)) := by
        exact (h1.sub h2).const_mul ac
      have h123 : Integrable (fun x => ac*((Δ (Δ φ : SchwartzMap V ℂ) : SchwartzMap V ℂ) x*u x-φ x*Δ (Δ u) x)-ψ x*Δ (Δ u) x) := by
        exact h12.sub h3
      rw [integral_sub h123 h4,integral_sub h12 h3,integral_const_mul,integral_sub h1 h2]
    _ = -(∫ x, adjointError c Af Bf t φ x*u x) := by
      rw [integral_bilaplacian φ u hu hb,integral_bilaplacian ψ u hu hb]
      simp only [sub_self,mul_zero,zero_sub]
      change -_ - _ = -(∫ x, ((Δ (Δ ψ : SchwartzMap V ℂ) : SchwartzMap V ℂ) x+χ x)*u x)
      simp_rw [add_mul]
      rw [integral_add hd h4]
      ring
lemma hasDerivAt_adjoint_pair {c : ℝ} {Af Bf : V → ℝ} (h : SymbolBounds c Af Bf)
    {d : C₀(V,ℂ)} {u : ℝ → C₀(V,ℂ)} (hu : MovesClassically Af Bf d u)
    (ε : ℝ) (hε : 0<ε) (z : V) {t : ℝ} (ht : t∈Ioo (0:ℝ) 1) :
    HasDerivAt (fun s => ∫ x, kernelTest (adjointTime c ε) adjointAmplitude z s x*u s x)
      (-(∫ x, adjointError c Af Bf t
        (adjointSchwartz c ε t z (hε.trans_le (adjointTime_bounds c ε ⟨ht.1.le,ht.2.le⟩).1)) x*u t x)) t := by
  have hp : 0<adjointTime c ε t := hε.trans_le (adjointTime_bounds c ε ⟨ht.1.le,ht.2.le⟩).1
  obtain ⟨p,hp',hpe⟩ := hu.2.2.2.2 t ht
  have hd := hasDerivAt_kernel_pair (adjointTime c ε) adjointAmplitude (contDiff_adjointTime c ε)
    contDiff_adjointAmplitude z hp' hp
  have he := integral_adjoint_cancel h ⟨ht.1.le,ht.2.le⟩ (adjointSchwartz c ε t z hp)
    (fun x => u t x) (hu.2.2.1 t ht) (moving_boundedJets hu ht) (p : V → ℂ) hpe
  simp_rw [←adjointSchwartz_apply c ε t z hp,adjointSchwartz_equation c ε t z hp] at hd
  simp only [ZeroAtInftyContinuousMap.toBCF_apply] at hd
  convert hd using 1
  exact he.symm
end FlatDuality

end

end OAI
