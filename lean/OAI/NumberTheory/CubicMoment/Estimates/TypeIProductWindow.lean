import OAI.NumberTheory.CubicMoment.Estimates.RadialTypeIIntegral
import OAI.NumberTheory.CubicMoment.Estimates.TypeICutoffWindow
import OAI.NumberTheory.CubicMoment.Estimates.TypeIProductFourier
import OAI.NumberTheory.CubicMoment.Estimates.SharpHeightPartition

namespace OAI

/-! Type I for the actual Gauss product envelope at a height window.
The inner smooth weight is the bounded dilation forced by the outer norm. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def productGaussHeightWindowKernel (ℓ : ℤ) (W : ℝ → ℂ) (H T X X₀ : ℝ)
    (n : Eisenstein) : ℂ :=
  theta ℓ n*gauss n*W (norm n/X)*
    heightFourierIntegral (fun t => cutoffHeightMultiplier H t*heightWindow T t)
      (Real.log (norm n)-Real.log X₀)

def productTypeICutoffWindow {γ : Type*} (w : Eisenstein → γ)
    (P : Finset Eisenstein) (α : Eisenstein → ℂ) (W : γ → ℝ → ℂ)
    (ℓ : ℤ) (B X U H T X₀ : ℝ) : ℂ :=
  ∫ t : ℝ, (cutoffHeightMultiplier H t*heightWindow T t*
    Complex.exp ((-Real.log X₀*t:ℝ)*Complex.I))*
      ∑ r ∈ P, α r*∑ u ∈ primaryElementBall (B*U),
        theta ℓ (r*u)*gauss (r*u)*normTwist t (r*u)*W (w r) (norm (r*u)/X)

lemma productGaussHeightWindowKernel_envelope (ℓ : ℤ) (W : ℝ → ℂ) {B X : ℝ}
    (hX : 0 < X) (hW : ∀ x : ℝ, B < x → W x = 0)
    (H T X₀ : ℝ) {n : Eisenstein} (hn : primary n) :
    (if n ∈ squarefreeProductEnvelope (B*X) then productGaussHeightWindowKernel ℓ W H T X X₀ n else 0) =
      productGaussHeightWindowKernel ℓ W H T X X₀ n := by
  by_cases hs : Squarefree n
  · by_cases hsize : norm n ≤ B*X
    · have hm : n ∈ squarefreeProductEnvelope (B*X) :=
        Finset.mem_filter.mpr ⟨mem_primaryElementBall.mpr ⟨hn,hsize⟩,hs⟩
      rw [ite_eq_left hm]
    · have hx : B < norm n/X := (lt_div_iff₀ hX).mpr (lt_of_not_ge hsize)
      simp only [productGaussHeightWindowKernel,hW _ hx,mul_zero,zero_mul,ite_self]
  · simp only [productGaussHeightWindowKernel,gauss_eq_zero_of_not_squarefree hn hs,
      mul_zero,zero_mul,ite_self]

theorem typeI_gaussWindow_envelope_row (ℓ : ℤ) (W : ℝ → ℂ)
    {B X R U : ℝ} (hB : 0 ≤ B) (hR : 1 ≤ R) (hU : 0 < U) (hRU : R*U = X)
    (hW : ∀ x : ℝ, B < x → W x = 0) (H T X₀ : ℝ)
    {r : Eisenstein} (hr : primary r) (hRr : R ≤ norm r) :
    (∑ u ∈ primaryElementBall (B*X),
      if r*u ∈ squarefreeProductEnvelope (B*X) then productGaussHeightWindowKernel ℓ W H T X X₀ (r*u) else 0) =
      ∑ u ∈ primaryElementBall (B*U), productGaussHeightWindowKernel ℓ W H T X X₀ (r*u) := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hX : 0 < X := by rw [←hRU]; positivity
  have hUX : U ≤ X := by rw [←hRU]; exact le_mul_of_one_le_left hU.le hR
  have hsub : primaryElementBall (B*U) ⊆ primaryElementBall (B*X) := by
    intro u hu
    obtain ⟨hup,huB⟩ := mem_primaryElementBall.mp hu
    exact mem_primaryElementBall.mpr ⟨hup,huB.trans (mul_le_mul_of_nonneg_left hUX hB)⟩
  calc
    _ = ∑ u ∈ primaryElementBall (B*X), productGaussHeightWindowKernel ℓ W H T X X₀ (r*u) := by
      apply Finset.sum_congr rfl
      intro u hu
      exact productGaussHeightWindowKernel_envelope ℓ W hX hW H T X₀
        (primary_mul hr (mem_primaryElementBall.mp hu).1)
    _ = _ := by
      symm
      apply Finset.sum_subset hsub
      intro u hu hn
      have hup := (mem_primaryElementBall.mp hu).1
      have huB : B*U < norm u := lt_of_not_ge
        (fun huB => hn (mem_primaryElementBall.mpr ⟨hup,huB⟩))
      have hnX : B*X < norm (r*u) := by
        rw [norm_mul_eq,←hRU]
        calc
          B*(R*U) = R*(B*U) := by ring
          _ < R*norm u := mul_lt_mul_of_pos_left huB hRp
          _ ≤ norm r*norm u := mul_le_mul_of_nonneg_right hRr (norm_nonneg _)
      have hz := hW (norm (r*u)/X) ((lt_div_iff₀ hX).mpr hnX)
      simp only [productGaussHeightWindowKernel,hz,mul_zero,zero_mul]

theorem productTypeICutoffWindow_fourier {γ : Type*} (w : Eisenstein → γ)
    (P : Finset Eisenstein) (α : Eisenstein → ℂ) (W : γ → ℝ → ℂ)
    (ℓ : ℤ) (B X U T X₀ : ℝ) {H : ℝ} (hH : 0 < H) :
    productTypeICutoffWindow w P α W ℓ B X U H T X₀ =
      ∑ r ∈ P, α r*∑ u ∈ primaryElementBall (B*U),
        productGaussHeightWindowKernel ℓ (W (w r)) H T X X₀ (r*u) := by
  let Q := primaryElementBall (B*U)
  let c : Eisenstein × Eisenstein → ℂ := fun q =>
    α q.1*(theta ℓ (q.1*q.2)*gauss (q.1*q.2)*W (w q.1) (norm (q.1*q.2)/X))
  have hb := height_norm_polynomial_integral (P.product Q) c (fun q => q.1*q.2)
    (fun t => cutoffHeightMultiplier H t*heightWindow T t)
    (integrable_cutoffHeightMultiplier_window hH T) (Real.log X₀)
  simp only [Finset.product_eq_sprod,Finset.sum_product] at hb
  calc
    _ = ∫ t : ℝ, (cutoffHeightMultiplier H t*heightWindow T t*
        Complex.exp ((-Real.log X₀*t:ℝ)*Complex.I))*
          ∑ r ∈ P, ∑ u ∈ Q, c (r,u)*normTwist t (r*u) := by
      unfold productTypeICutoffWindow
      apply integral_congr_ae
      filter_upwards with t
      simp only [Finset.mul_sum,c,Q]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro u _
      ring
    _ = ∑ r ∈ P, ∑ u ∈ Q, c (r,u)*
        heightFourierIntegral (fun t => cutoffHeightMultiplier H t*heightWindow T t)
          (Real.log (norm (r*u))-Real.log X₀) := hb.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      dsimp [c,Q,productGaussHeightWindowKernel]
      ring

/-- The original product polynomial is exactly a Type-I polynomial with
uniformly dilated inner weights. No height-dependent weight is introduced. -/
theorem productTypeICutoffWindow_dilate {γ : Type*} {W : γ → ℝ → ℂ}
    (hW : UniformLogWeights W) (w : Eisenstein → γ) (P : Finset Eisenstein)
    (α : Eisenstein → ℂ) (ℓ : ℤ) {X R U : ℝ}
    (hR : 1 ≤ R) (hU : 0 < U) (hRU : R*U = X)
    (hP : ∀ r ∈ P, primary r ∧ R ≤ norm r ∧ norm r ≤ 2*R) :
    ∃ v : Eisenstein → γ × {s : ℝ // 0 < s ∧ |Real.log s| ≤ Real.log 2},
      ∀ H T X₀ : ℝ,
      productTypeICutoffWindow w P α W ℓ (Real.exp hW.radius) X U H T X₀ =
        typeICutoffWindow v P α
          (fun z : γ × {s : ℝ // 0 < s ∧ |Real.log s| ≤ Real.log 2} =>
            fun x => W z.1 (z.2*x)) ℓ U H T X₀ := by
  let δ := {s : ℝ // 0 < s ∧ |Real.log s| ≤ Real.log 2}
  let V : γ × δ → ℝ → ℂ := fun z x => W z.1 (z.2*x)
  have hRp : 0 < R := zero_lt_one.trans_le hR
  let s : Eisenstein → δ := fun r => if hr : r ∈ P then
    ⟨norm r/R,log_dyad_ratio hRp (by norm_num) (hP r hr).2.1 (hP r hr).2.2⟩
    else ⟨1,by simp; exact Real.log_nonneg (by norm_num)⟩
  let v : Eisenstein → γ × δ := fun r => (w r,s r)
  refine ⟨v,?_⟩
  intro H T X₀
  have hv (r : Eisenstein) (hr : r ∈ P) :
      V (v r) = fun x => W (w r) ((norm r/R)*x) := by
    funext x
    simp only [V,v,s,dite_eq_left hr]
  have hcut (r : Eisenstein) (hr : r ∈ P) (x : ℝ)
      (hx : Real.exp hW.radius < x) : V (v r) x = 0 := by
    rw [hv r hr]
    apply hW.upper_support (w r)
    have hratio : 1 ≤ norm r/R := (le_div_iff₀ hRp).mpr (by simpa using (hP r hr).2.1)
    exact hx.trans_le (le_mul_of_one_le_left (by linarith [Real.exp_pos hW.radius]) hratio)
  unfold productTypeICutoffWindow typeICutoffWindow typeIHeightPolynomial
  apply integral_congr_ae
  filter_upwards with t
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  rw [metaplecticAngularSmoothSum_finite r ℓ (V (v r)) hU le_rfl (hcut r hr) t,
    Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  have harg : (norm r/R)*(norm u/U) = norm (r*u)/X := by
    rw [norm_mul_eq,←hRU]
    field_simp
  have hp : normTwist t (r*u) = normTwist t r*mellinPhase t (norm u) :=
    normTwist_mul t (primary_ne_zero (hP r hr).1)
      (primary_ne_zero (mem_primaryElementBall.mp hu).1)
  change α r*(theta ℓ (r*u)*gauss (r*u)*normTwist t (r*u)*W (w r) (norm (r*u)/X)) =
    (α r*normTwist t r)*(V (v r) (norm u/U)*
      (gauss (r*u)*theta ℓ (r*u)*mellinPhase t (norm u)))
  rw [hv r hr]
  dsimp only
  rw [harg,hp]
  ring

/-- Published Type-I height estimates applied to the actual product
weight, in both ordinary and upper height ranges. -/
theorem radial_productTypeICutoffWindow_bound
    {γ : Type*} {W : γ → ℝ → ℂ} (hW : UniformLogWeights W)
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hVor : MetaplecticVoronoiInput a)
    {MV : ℝ} (hMV : MontgomeryVaughanBound MV) (hMean0 : 0 ≤ MV)
    {κ ρ : ℝ} (hκ : 0 < κ) (hρ : ρ ≤ κ/4)
    (B M : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    ∃ C E : ℝ, 0 ≤ C ∧ 0 ≤ E ∧
      ∀ (w : Eisenstein → γ) (P : Finset Eisenstein) (α : Eisenstein → ℂ)
        (X R U T H X₀ : ℝ),
        1 ≤ R → 1 ≤ U → R*U = X → 1 ≤ Real.log X → Real.log X ≤ T →
        0 < X₀ →
        ((R ≤ X^(2/5:ℝ) ∧ T ≤ X^(1/100:ℝ)) ∨
          (R ≤ X^(1/3-κ/2) ∧ T ≤ X^(1/6+ρ))) →
        (∀ r ∈ P, primary r ∧ R ≤ norm r ∧ norm r ≤ 2*R) →
        (∑ r ∈ P, ‖α r‖) ≤ A*R*(Real.log X)^B →
        ‖productTypeICutoffWindow w P α W 0 (Real.exp hW.radius) X U H T X₀‖ ≤
          C*X^(5/6-min (1/100) (3*κ/16))+E*X^(5/6:ℝ)/(Real.log X)^M := by
  have hV := hW.logDilate (Real.log 2) (Real.log_nonneg (by norm_num))
  obtain ⟨C,E,hC,hE,hbound⟩ := radial_typeI_height_integral_of_voronoi hVor hMV hMean0 hV hκ hρ B M hA
  refine ⟨2*C,2*E,by positivity,by positivity,?_⟩
  intro w P α X R U T H X₀ hR hU hRU hlog hLT hX₀ hrange hP hmass
  obtain ⟨v,hv⟩ := productTypeICutoffWindow_dilate hW w P α 0 hR
    (zero_lt_one.trans_le hU) hRU hP
  rw [hv, typeICutoffWindow_endpoints hV v P α 0 (zero_lt_one.trans_le hU)
    (zero_lt_one.trans_le (hlog.trans hLT)) hX₀ H]
  have h₁ := hbound v P α R U T H X₀ hR hU (by simpa only [hRU] using hlog)
    (by simpa only [hRU] using hLT) (by simpa only [hRU] using hrange) hP
    (by simpa only [hRU] using hmass)
  have h₂ := hbound v P α R U T H (2*X₀) hR hU (by simpa only [hRU] using hlog)
    (by simpa only [hRU] using hLT) (by simpa only [hRU] using hrange) hP
    (by simpa only [hRU] using hmass)
  rw [hRU] at h₁ h₂
  apply (norm_sub_le _ _).trans
  exact (add_le_add h₁ h₂).trans_eq (by ring)

end CubicFirstMoment

end

end OAI
