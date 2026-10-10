import OAI.NumberTheory.DirichletL.Inversion.InitialPhysicalMeasure

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialHighFrequencyTail
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open InverseInitialProfile
local notation "O" => ActualEisensteinCubic.O

private theorem finite_sum_le_tsum_subtype (F : Finset O) (P : O → Prop)
    (hF : ∀ h ∈ F, P h) (b : O → ℝ) (hb : ∀ h, 0 ≤ b h)
    (hs : Summable (fun h : {h // P h} => b h.val)) :
    (∑ h ∈ F, b h) ≤ ∑' h : {h // P h}, b h.val := by
  let f : F → {h // P h} := fun h => ⟨h.val, hF h.val h.property⟩
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : {h // P h} => z.val) h)
  rw [← Finset.sum_coe_sort F]
  have ht : Summable (fun h : F => b h.val) := (hasSum_fintype _).summable
  simpa only [tsum_fintype] using
    ht.tsum_le_tsum_of_inj f hf (fun h _ => hb h.val) (fun _ => le_rfl) hs

theorem finite_radial_tail (A : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
    ∀ (Φ : 𝓢(ℝ,ℂ)) (K T Γ : ℝ), 0<K → 0≤T → 0≤Γ →
    ∀ (F : Finset O) (a : O→ℂ),
    (∀h∈F,T≤K*‖eisEmbedding h‖^2) →
    (∀h∈F,‖a h‖≤Γ) →
    ‖∑h∈F,a h*paperRadialFourier Φ (K*‖eisEmbedding h‖^2)‖ ≤
      Γ*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
        ((min 1 K)^2*(1+T)^A) := by
  obtain ⟨s,C,hC,hbound⟩ := paperRadialFourier_lattice_tail A
  refine ⟨s,C,hC,?_⟩
  intro Φ K T Γ hK hT hΓ F a hF ha
  have hsum := finite_sum_le_tsum_subtype F
    (fun h => T ≤ K * ‖eisEmbedding h‖^2) hF
    (fun h => ‖paperRadialFourier Φ (K * ‖eisEmbedding h‖^2)‖)
    (fun _ => norm_nonneg _)
    ((paperRadialFourier_lattice_summable_norm Φ K hK).subtype
      (fun h => T ≤ K * ‖eisEmbedding h‖^2))
  calc
    _ ≤ ∑h∈F,‖a h*paperRadialFourier Φ (K*‖eisEmbedding h‖^2)‖ := norm_sum_le _ _
    _ ≤ ∑h∈F,Γ*‖paperRadialFourier Φ (K*‖eisEmbedding h‖^2)‖ := by
      apply Finset.sum_le_sum
      intro h hh
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (ha h hh) (norm_nonneg _)
    _ = Γ*∑h∈F,‖paperRadialFourier Φ (K*‖eisEmbedding h‖^2)‖ := by rw [Finset.mul_sum]
    _ ≤ Γ*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ /
        ((min 1 K)^2*(1+T)^A)) :=
      mul_le_mul_of_nonneg_left (hsum.trans (hbound Φ K T hK hT)) hΓ
    _ = _ := by ring

theorem physicalKernel_frequency (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ))
    (Z D m C d v n₁ n₂ : ℝ) (h : O) :
    physicalKernel W₁ W₂ Φ Z D m ![C,d,v,‖eisEmbedding h‖^2,n₁,n₂] =
      ((Z^(-D)*Z^m/(d*v*Real.sqrt (n₁*n₂)):ℝ):ℂ)*
      W₁ (C*v*n₁/Z^D)*W₂ (C*v*n₂/Z^D)*
      paperRadialFourier Φ ((Z^m/(d*v^2*n₁*n₂))*‖eisEmbedding h‖^2) := by
  simp [physicalKernel, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

theorem physical_frequency_tail (A : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C₀ : ℝ), 0<C₀ ∧
    ∀ (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ))
      (Z D m C d v n₁ n₂ T Γ : ℝ),
    0<Z → 0<d → 0<v → 0<n₁ → 0<n₂ → 0≤T → 0≤Γ →
    ∀ (F : Finset O) (a : O→ℂ),
    (∀h∈F,T≤(Z^m/(d*v^2*n₁*n₂))*‖eisEmbedding h‖^2) →
    (∀h∈F,‖a h‖≤Γ) →
    ‖∑h∈F,a h*physicalKernel W₁ W₂ Φ Z D m
      ![C,d,v,‖eisEmbedding h‖^2,n₁,n₂]‖ ≤
      Γ*‖((Z^(-D)*Z^m/(d*v*Real.sqrt (n₁*n₂)):ℝ):ℂ)*
        W₁ (C*v*n₁/Z^D)*W₂ (C*v*n₂/Z^D)‖ *
      (C₀*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
        ((min 1 (Z^m/(d*v^2*n₁*n₂)))^2*(1+T)^A) := by
  obtain ⟨s,C₀,hC₀,hbound⟩ := finite_radial_tail A
  refine ⟨s,C₀,hC₀,?_⟩
  intro W₁ W₂ Φ Z D m C d v n₁ n₂ T Γ hZ hd hv hn₁ hn₂ hT hΓ F a hF ha
  let b : ℂ := ((Z^(-D)*Z^m/(d*v*Real.sqrt (n₁*n₂)):ℝ):ℂ)*
        W₁ (C*v*n₁/Z^D)*W₂ (C*v*n₂/Z^D)
  simp_rw [physicalKernel_frequency,←mul_assoc]
  simpa only [b,←mul_assoc] using hbound Φ (Z^m/(d*v^2*n₁*n₂)) T (Γ*‖b‖) (by positivity) hT
    (by positivity) F (fun h=>a h*b) hF (by
      intro h hh
      exact (norm_mul _ _).trans_le (mul_le_mul_of_nonneg_right (ha h hh) (norm_nonneg _)))

theorem correlated_scale_lower (Y C d v n₁ n₂ L : ℝ)
    (hY : 0<Y) (hC : 0<C) (hd : 0<d) (hv : 0<v)
    (hn₁ : 0<n₁) (hn₂ : 0<n₂) (hL : 0<L)
    (h₁ : C*v*n₁≤L) (h₂ : C*v*n₂≤L) :
    Y*C^2/(d*L^2) ≤ Y/(d*v^2*n₁*n₂) := by
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hh := mul_le_mul h₁ h₂ (by positivity) hL.le
  nlinarith [mul_le_mul_of_nonneg_left hh (show 0≤Y*d by positivity)]

end SevenEighths.InverseInitialHighFrequencyTail

end

end OAI
