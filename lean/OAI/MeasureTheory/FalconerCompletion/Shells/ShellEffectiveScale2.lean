import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Graphs.AllMaskProductAdmissible2
import OAI.MeasureTheory.FalconerCompletion.Recursion.MaskScale2
import OAI.MeasureTheory.FalconerCompletion.Shells.ShellEffectiveScale

namespace OAI

/-! Dyadic shells and prefix decompositions. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open Filter Real
open scoped Topology

noncomputable def shellEffectiveScaleND (l : ℕ) (R σ : ℝ) : ℝ :=
  R^σ*sourceMaskScaleND l R σ

lemma dyadic_half_sqND (q : ℝ) : ((2:ℝ)^(q/2))^2=(2:ℝ)^q := by
  rw [← Real.rpow_natCast ((2:ℝ)^(q/2)) 2,← Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
  congr 1
  norm_num

lemma shell_effective_scale_upperND {R σ q : ℝ} (l : ℕ) (hR : 0<R)
    (hl : (2:ℝ)^l ≤ (2:ℝ)^(q/2)*R^σ) :
    shellEffectiveScaleND l R σ ≤ max (R^σ) ((2:ℝ)^(q/2)*R^(-48*σ)) := by
  unfold shellEffectiveScaleND sourceMaskScaleND
  rw [mul_max_of_nonneg _ _ (Real.rpow_nonneg hR.le _),mul_one]
  apply max_le_max_left
  calc
    _ ≤ R^σ*(((2:ℝ)^(q/2)*R^σ)*R^(-50*σ)) := by gcongr
    _ = (2:ℝ)^(q/2)*(R^σ*R^σ*R^(-50*σ)) := by ring
    _ = _ := by rw [← Real.rpow_add hR,← Real.rpow_add hR]; congr 2; ring

lemma shell_effective_scale_sqND {R σ q : ℝ} (l : ℕ) (hR : 0<R)
    (hl : (2:ℝ)^l ≤ (2:ℝ)^(q/2)*R^σ) :
    (shellEffectiveScaleND l R σ)^2 ≤ max (R^(2*σ)) ((2:ℝ)^q*R^(-96*σ)) := by
  have hu := shell_effective_scale_upperND l hR hl
  have hn : 0 ≤ shellEffectiveScaleND l R σ :=
    mul_nonneg (Real.rpow_nonneg hR.le _) (sourceMaskScaleND_pos l R σ).le
  have he₁ : (R^σ)^2=R^(2*σ) := by
    rw [← Real.rpow_natCast (R^σ) 2,← Real.rpow_mul hR.le]
    congr 1
    norm_num
    ring
  have he₂ : ((2:ℝ)^(q/2)*R^(-48*σ))^2=(2:ℝ)^q*R^(-96*σ) := by
    rw [mul_pow,dyadic_half_sqND,← Real.rpow_natCast (R^(-48*σ)) 2,← Real.rpow_mul hR.le]
    congr 2
    norm_num
    ring
  rcases le_total (R^σ) ((2:ℝ)^(q/2)*R^(-48*σ)) with h | h
  · rw [max_eq_right h] at hu
    exact (pow_le_pow_left₀ hn hu 2).trans (by rw [he₂]; exact le_max_right _ _)
  · rw [max_eq_left h] at hu
    exact (pow_le_pow_left₀ hn hu 2).trans (by rw [he₁]; exact le_max_left _ _)

lemma shell_scale_regimeND {R σ q c Λ : ℝ} (l : ℕ)
    (hR : 1 ≤ R) (hσ : 0 ≤ σ) (hσ₁ : σ ≤ 1) (hc : 0<c)
    (hl : (2:ℝ)^l ≤ (2:ℝ)^(q/2)*R^σ)
    (hqlo : R^(20*σ) ≤ (2:ℝ)^q) (hqup : (2:ℝ)^q ≤ R^2)
    (hΛ : c*(2:ℝ)^q ≤ Λ) :
    1 ≤ shellEffectiveScaleND l R σ ∧ shellEffectiveScaleND l R σ ≤ R^2 ∧
    c*R^(20*σ) ≤ Λ ∧ (shellEffectiveScaleND l R σ)^2/Λ ≤ c⁻¹*R^(-18*σ) ∧
    (2:ℝ)^(-q)*(sourceMaskScaleND l R σ)^2 ≤ 1 := by
  have hRp : 0<R := zero_lt_one.trans_le hR
  have hQp : 0<(2:ℝ)^q := Real.rpow_pos_of_pos (by norm_num) _
  have hΛp : 0<Λ := (mul_pos hc hQp).trans_le hΛ
  have hRs : 1≤R^σ := Real.one_le_rpow hR hσ
  have hu := shell_effective_scale_upperND l hRp hl
  have hsquare := shell_effective_scale_sqND l hRp hl
  have hhalf : (2:ℝ)^(q/2) ≤ R := by
    nlinarith [dyadic_half_sqND q, Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) (q/2)]
  have hle (u : ℝ) (hu : u ≤ 0) : R^u ≤ 1 := by
    simpa using Real.rpow_le_rpow_of_exponent_le hR hu
  have hnorm : (shellEffectiveScaleND l R σ)^2 ≤ (2:ℝ)^q*R^(-18*σ) := by
    apply hsquare.trans
    apply max_le
    · calc
        R^(2*σ) = R^(20*σ)*R^(-18*σ) := by rw [← Real.rpow_add hRp]; congr 1; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hqlo (Real.rpow_nonneg hRp.le _)
    · exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hR (by linarith)) hQp.le
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact one_le_mul_of_one_le_of_one_le hRs (sourceMaskScaleND_one_le l R σ)
  · apply hu.trans
    apply max_le
    · simpa using Real.rpow_le_rpow_of_exponent_le hR (show σ ≤ (2:ℝ) by linarith)
    · calc
        _ ≤ (2:ℝ)^(q/2) := mul_le_of_le_one_right (by positivity) (hle (-48*σ) (by linarith))
        _ ≤ R := hhalf
        _ ≤ R^2 := by nlinarith
  · exact (mul_le_mul_of_nonneg_left hqlo hc.le).trans hΛ
  · calc
      _ ≤ ((2:ℝ)^q*R^(-18*σ))/(c*(2:ℝ)^q) :=
        div_le_div₀ (by positivity) hnorm (mul_pos hc hQp) hΛ
      _ = _ := by field_simp
  · have hQle : sourceMaskScaleND l R σ ≤ shellEffectiveScaleND l R σ := by
      exact le_mul_of_one_le_left (sourceMaskScaleND_pos l R σ).le hRs
    have hsq : (sourceMaskScaleND l R σ)^2 ≤ (2:ℝ)^q :=
      (pow_le_pow_left₀ (sourceMaskScaleND_pos l R σ).le hQle 2).trans
        (hnorm.trans (mul_le_of_le_one_right hQp.le (hle (-18*σ) (by linarith))))
    rw [Real.rpow_neg (by norm_num : (0:ℝ)≤2)]
    exact (inv_mul_le_one₀ hQp).mpr hsq

theorem shell_scale_regime_eventuallyND {σ c : ℝ} (hσ : 0<σ) (hσ₁ : σ≤1) (hc : 0<c) :
    ∀ᶠ R : ℝ in atTop, ∀ (l : ℕ) (q Λ : ℝ),
      (2:ℝ)^l ≤ (2:ℝ)^(q/2)*R^σ → R^(20*σ) ≤ (2:ℝ)^q → (2:ℝ)^q ≤ R^2 →
      c*(2:ℝ)^q ≤ Λ →
      1 ≤ shellEffectiveScaleND l R σ ∧ shellEffectiveScaleND l R σ ≤ R^2 ∧
      R^σ ≤ Λ ∧ (shellEffectiveScaleND l R σ)^2/Λ ≤ R^(-σ) ∧
      (2:ℝ)^(-q)*(sourceMaskScaleND l R σ)^2 ≤ 1 := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    (tendsto_rpow_atTop (by linarith : (0:ℝ)<17*σ)).eventually_ge_atTop c⁻¹] with R hR hlarge
  intro l q Λ hl hqlo hqup hΛ
  have hRp : 0<R := zero_lt_one.trans_le hR
  obtain ⟨h₁,h₂,h₃,h₄,h₅⟩ := shell_scale_regimeND l hR hσ.le hσ₁ hc hl hqlo hqup hΛ
  refine ⟨h₁,h₂,?_,?_,h₅⟩
  · have hcR : 1 ≤ c*R^(17*σ) := by simpa only [mul_comm] using (inv_le_iff_one_le_mul₀ hc).mp hlarge
    have hRs : R^σ ≤ R^(3*σ) := Real.rpow_le_rpow_of_exponent_le hR (by linarith)
    apply le_trans _ h₃
    calc
      _ ≤ R^(3*σ) := hRs
      _ ≤ (c*R^(17*σ))*R^(3*σ) := le_mul_of_one_le_left (Real.rpow_nonneg hRp.le _) hcR
      _ = _ := by rw [mul_assoc,← Real.rpow_add hRp]; congr 2; ring
  · apply h₄.trans
    calc
      _ ≤ R^(17*σ)*R^(-18*σ) := mul_le_mul_of_nonneg_right hlarge (Real.rpow_nonneg hRp.le _)
      _ = _ := by rw [← Real.rpow_add hRp]; congr 1; ring

lemma shell_source_exponentsND {N l : ℕ} {σ q : ℝ}
    (hl : (l:ℝ) ≤ q/2+σ*N) (hqlo : 20*σ*N ≤ q) (hqup : q ≤ 2*N) :
    (2:ℝ)^l ≤ (2:ℝ)^(q/2)*((2:ℝ)^N)^σ ∧
    ((2:ℝ)^N)^(20*σ) ≤ (2:ℝ)^q ∧ (2:ℝ)^q ≤ ((2:ℝ)^N)^2 := by
  have h₁ : ((2:ℝ)^N)^σ=(2:ℝ)^((N:ℝ)*σ) := by
    rw [← Real.rpow_natCast (2:ℝ) N,← Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
  have h₂ : ((2:ℝ)^N)^(20*σ)=(2:ℝ)^((N:ℝ)*(20*σ)) := by
    rw [← Real.rpow_natCast (2:ℝ) N,← Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
  have h₃ : ((2:ℝ)^N)^2=(2:ℝ)^((N:ℝ)*2) := by
    rw [← Real.rpow_natCast (2:ℝ) N,← Real.rpow_natCast ((2:ℝ)^(N:ℝ)) 2,
      ← Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
    norm_num
  rw [h₁,h₂,h₃,← Real.rpow_add (by norm_num : (0:ℝ)<2),← Real.rpow_natCast (2:ℝ) l]
  exact ⟨Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith),
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith),
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)⟩

end Attempt4PrefixShell
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open Set

lemma shell_pair_frequency_lowerND (a v r D δ : ℝ)
    (hr : (2:ℝ)^v/2 ≤ r) (hD : δ ≤ D*(2:ℝ)^a) (hδ : 0<δ) :
    (δ/2)*(2:ℝ)^(v-a) ≤ r*D := by
  have ha : 0<(2:ℝ)^a := Real.rpow_pos_of_pos (by norm_num) _
  have hv : 0<(2:ℝ)^v := Real.rpow_pos_of_pos (by norm_num) _
  have hDp : 0<D := (mul_pos_iff_of_pos_right ha).mp (hδ.trans_le hD)
  calc
    _ = ((2:ℝ)^v/2)*(δ/(2:ℝ)^a) := by
      rw [Real.rpow_sub (by norm_num : (0:ℝ)<2)]; ring
    _ ≤ ((2:ℝ)^v/2)*D := mul_le_mul_of_nonneg_left
      ((div_le_iff₀ ha).mpr hD) (by positivity)
    _ ≤ r*D := mul_le_mul_of_nonneg_right hr hDp.le

end Attempt4PrefixShell
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open Set MeasureTheory
open scoped ComplexConjugate Topology ContDiff
variable {n : ℕ} {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
local notation "V" => EuclideanSpace ℝ (Fin (n+1))
local notation "Assignment" => ℂ × ((ι ⊕ κ) → List (SphereAmbientND n →L[ℝ] SphereAmbientND n))

theorem source_weighted_shellND (ψ : V → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (kCard : ℕ) (Cderiv : ℕ → ℝ) (σ ε T₀ Bmass Cmask δ K : ℝ)
    (hσ : 0<σ) (hσ₁ : σ≤1) (hCderiv : ∀ m, 0≤Cderiv m)
    (hε : 0<ε) (hδ : 0<δ) (hK : 0<K) :
    ∃ J : ℕ, ∀ᶠ kN : ℕ in Filter.atTop, let R := (2:ℝ)^kN; ∀
      (S : Finset ι) (T : Finset κ)
      (f : V → ι → SmoothFunctionND V) (g : V → κ → SmoothFunctionND V)
      (F G : V → ℂ) (D : ι → ℝ) (E : κ → ℝ),
      max 1 ((S.card+T.card:ℕ):ℝ) ≤ Cmask*(kN:ℝ)^kCard → ∀ (ρ ν : Measure V) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
      (X Y : Set V), MeasurableSet X → MeasurableSet Y → ∀
      (L : ℕ) (M N a v : ℝ), 20*σ*kN ≤ v-a → (L:ℝ) ≤ (v-a)/2+σ*kN → v-a ≤ 2*kN →
      |(M*N)⁻¹| * ((ρ.restrict X).prod (ν.restrict Y)).real univ ≤ R^Bmass →
      (∀ i ∈ S, 1 ≤ D i ∧ D i ≤ sourceMaskScaleND L R σ) →
      (∀ k ∈ T, 1 ≤ E k ∧ E k ≤ sourceMaskScaleND L R σ) →
      (∀ x ∈ X, ∀ i ∈ S, ∀ w, ‖w‖=1 → ‖(f x i).1 w‖ ≤ 1) →
      (∀ y ∈ Y, ∀ k ∈ T, ∀ w, ‖w‖=1 → ‖(g y k).1 w‖ ≤ 1) →
      (∀ x ∈ X, ∀ i ∈ S, ∀ j ≤ 2*(J+1)+n+3, ∀ w, ‖w‖=1 →
        ‖iteratedFDeriv ℝ j (f x i).1 w‖ ≤ Cderiv (2*(J+1)+n+3)*(D i)^j) →
      (∀ y ∈ Y, ∀ k ∈ T, ∀ j ≤ 2*(J+1)+n+3, ∀ w, ‖w‖=1 →
        ‖iteratedFDeriv ℝ j (g y k).1 w‖ ≤ Cderiv (2*(J+1)+n+3)*(E k)^j) →
      (∀ x ∈ X, ∀ y ∈ Y, δ ≤ dist x y*(2:ℝ)^a ∧ dist x y*(2:ℝ)^a ≤ K) →
      (∀ᵐ z ∂(ρ.restrict X).prod (ν.restrict Y),
        ψ =ᶠ[𝓝 ((dist z.1 z.2)⁻¹ • (z.1-z.2))] (fun _ => 1) ∧
        ψ =ᶠ[𝓝 (-((dist z.1 z.2)⁻¹ • (z.1-z.2)))] (fun _ => 0)) →
      (∀ᵐ z ∂(ρ.restrict X).prod (ν.restrict Y), ‖F z.1*conj (G z.2)‖ ≤ 1) →
      Measurable (fun z => (F z.1*conj (G z.2))*
        (pairMaskProductND S T f g z).1 ((dist z.1 z.2)⁻¹ • (z.1-z.2))) →
      ∀ (P : ℝ), (∀ w, ‖ψ w‖ ≤ P) → ∀ (B C : ℕ → Assignment → ℝ),
      (∀ j ≤ J, ∀ p ∈ inverseAngularTermsND j (S.disjSum T),
        Measurable (Function.uncurry (inverseLeftEndpointND S D f F p))) →
      (∀ j ≤ J, ∀ p ∈ inverseAngularTermsND j (S.disjSum T),
        Measurable (Function.uncurry (inverseRightEndpointND T E g G p))) →
      (∀ j ≤ J, ∀ p ∈ inverseAngularTermsND j (S.disjSum T), ∀ x w,
        ‖inverseLeftEndpointND S D f F p x w‖ ≤ B j p) →
      (∀ j ≤ J, ∀ p ∈ inverseAngularTermsND j (S.disjSum T), ∀ y w,
        ‖inverseRightEndpointND T E g G p y w‖ ≤ C j p) →
      ∀ (Ψ : ℝ → ℝ), Integrable (fun r => Ψ (r/(2:ℝ)^v)) →
      (∀ r, 0 ≤ Ψ r) → (∀ r ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ r) → ∀ (BHF : ℝ), 0 ≤ BHF →
      (∀ j ≤ J, ∀ p ∈ inverseAngularTermsND j (S.disjSum T), ∀ ξ,
        sourceAngularHFND (n+1) (canonicalSphereMeasureND V) a v Ψ ψ
          (fun z => spatialEndpointTransformND ((2:ℝ)^a)⁻¹ ρ X M
            (inverseLeftEndpointND S D f F p) (ξ,z))
          (fun z => spatialEndpointTransformND ((2:ℝ)^a)⁻¹ ν Y N
            (inverseRightEndpointND T E g G p) (ξ,z)) ≤ BHF) →
      Integrable (fun r => ‖weightedMaskTransformND S T f g F G ρ ν X Y M N a r‖^2)
        (volume.restrict (Icc ((2:ℝ)^v/2) (2*(2:ℝ)^v))) ∧
      (2:ℝ)^(-a)*(∫ r in Icc ((2:ℝ)^v/2) (2*(2:ℝ)^v),
        ‖weightedMaskTransformND S T f g F G ρ ν X Y M N a r‖^2) ≤
        R^ε*BHF+R^(-T₀) := by
  obtain ⟨J,hMain⟩ := weighted_all_mask_shell_asymptoticND (ι := ι) (κ := κ)
    ψ hψ kCard σ 1 ε T₀ Bmass Cmask δ K hσ (by norm_num) hε hδ hK
  refine ⟨J,?_⟩
  filter_upwards [hMain,
    pair_mask_product_admissibleND (ι := ι) (κ := κ) (n := n)
      (2*(J+1)+n+3) kCard (Cderiv (2*(J+1)+n+3)) Cmask σ (hCderiv _) hσ,
    shell_dyadic_tendstoND.eventually (shell_scale_regime_eventuallyND hσ hσ₁
      (show 0<δ/2 by linarith))] with kN hMainN hproduct hscale
  dsimp only at hMainN ⊢
  intro S T f g F G D E hcard ρ ν hρ hν X Y hX hY L M N a v hqlo hl hqup
    hmass hD hE hf0 hg0 hf hg hsep hcut hFG hsym P hP B C hb hc hB hC
    Ψ hΨ hΨpos hone BHF hBHF hHF
  obtain ⟨hl',hqlo',hqup'⟩ := shell_source_exponentsND hl hqlo hqup
  have hA := hscale L (v-a) ((δ/2)*(2:ℝ)^(v-a)) hl' hqlo' hqup' le_rfl
  apply hMainN S T f g F G D E
    (fun i hi => zero_lt_one.trans_le (hD i hi).1)
    (fun i hi => zero_lt_one.trans_le (hE i hi).1) hcard ρ ν X Y hX hY M N
    (shellEffectiveScaleND L ((2:ℝ)^kN) σ) (sourceMaskScaleND L ((2:ℝ)^kN) σ)
    a v hA.1 hA.2.1 (sourceMaskScaleND_one_le _ _ _) hqup' hmass hA.2.2.2.2
    (fun i hi => (hD i hi).2) (fun i hi => (hE i hi).2) hsep ?_
    hFG hsym P hP B C hb hc hB hC Ψ hΨ hΨpos hone BHF hBHF hHF
  intro r hr
  have hxy : ∀ᵐ z ∂(ρ.restrict X).prod (ν.restrict Y), z.1∈X ∧ z.2∈Y :=
    (Measure.ae_prod_iff_ae_ae (hX.prod hY)).mpr (by
      filter_upwards [ae_restrict_mem hX] with x hx
      filter_upwards [ae_restrict_mem hY] with y hy
      exact ⟨hx,hy⟩)
  filter_upwards [hxy,hcut] with z hz hc
  have hfreq := shell_pair_frequency_lowerND a v r (dist z.1 z.2) δ hr.1
    (hsep z.1 hz.1 z.2 hz.2).1 hδ
  have hsa := hscale L (v-a) (r*dist z.1 z.2) hl' hqlo' hqup' hfreq
  refine ⟨hsa.2.2.1,hsa.2.2.2.1,hc.1,hc.2,?_⟩
  simpa only [one_mul,shellEffectiveScaleND] using
    hproduct S T f g D E (sourceMaskScaleND L ((2:ℝ)^kN) σ) z
      ((le_max_right _ _).trans hcard) hD hE (sourceMaskScaleND_pos _ _ _).le
      (hf0 z.1 hz.1) (hg0 z.2 hz.2) (hf z.1 hz.1) (hg z.2 hz.2)

end Attempt4PrefixShell
end GraphLiteralSupport
end
end

end OAI
