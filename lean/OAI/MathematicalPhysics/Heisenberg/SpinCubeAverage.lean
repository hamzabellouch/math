import OAI.MathematicalPhysics.Heisenberg.FiniteAverage

namespace OAI

section
noncomputable section
open scoped Classical BigOperators ComplexConjugate
open Filter Topology
namespace Heisenberg
variable {d ℓ : ℕ}

lemma cube_card_pos (d N : ℕ) : (0:ℝ)<(box d N).card := by
  classical
  exact_mod_cast Finset.card_pos.mpr (box_nonempty d N)

def cubeAverage (Λ : Finset (Site d)) (hΛ : Λ.Nonempty) (ω : State d ℓ) : State d ℓ :=
  averageState (fun _ : Λ=>(Λ.card:ℝ)⁻¹) (fun _=>by positivity)
    (by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]; exact mul_inv_cancel₀ (show (Λ.card:ℝ)≠0 by exact_mod_cast Finset.card_ne_zero.mpr hΛ))
    (fun x=>translatedState ω x.val)

lemma cubeAverage_apply (Λ : Finset (Site d)) (hΛ : Λ.Nonempty) (ω : State d ℓ) (A : QuasiLocal d ℓ) :
    (cubeAverage Λ hΛ ω).functional A=(Λ.card:ℂ)⁻¹*∑ x∈Λ,ω.functional (translation d ℓ x A) := by
  classical
  simp only [cubeAverage,averageState_apply,translatedState,ContinuousLinearMap.comp_apply,translationLinear_apply]
  rw [←Finset.mul_sum]
  have hs : (∑ i : Λ,ω.functional (translation d ℓ i.val A))=∑ x∈Λ,ω.functional (translation d ℓ x A) := Finset.sum_coe_sort Λ (fun x=>ω.functional (translation d ℓ x A))
  rw [hs]
  simp only [Complex.ofReal_inv,Complex.ofReal_natCast]

lemma cubeAverage_spinZ (Λ : Finset (Site d)) (hΛ : Λ.Nonempty) (ω : State d ℓ) :
    (cubeAverage Λ hΛ ω).functional (spinZ d ℓ 0)=(Λ.card:ℂ)⁻¹*ω.functional (totalZ Λ) := by
  classical
  rw [cubeAverage_apply]
  simp only [translation_spinZ,add_zero,totalZ,map_sum]

lemma state_selfAdjoint_im (ω : State d ℓ) {A : QuasiLocal d ℓ} (hA : IsSelfAdjoint A) :
    (ω.functional A).im=0 := by
  classical
  have h1:=(ω.positive (A+1)).1
  have h2:=(ω.positive A).1
  simp only [star_add,hA.star_eq,star_one,add_mul,mul_add,mul_one,one_mul,map_add,Complex.add_im,ω.normalized,Complex.one_im] at h1 h2
  linarith

lemma cubeAverage_translation_bound (N r : ℕ) (hr : r≤N) (x : Site d) (hx : x∈box d r)
    (ω : State d ℓ) (A : QuasiLocal d ℓ) :
    ‖(cubeAverage (box d N) (box_nonempty d N) ω).functional (translation d ℓ x A)-
      (cubeAverage (box d N) (box_nonempty d N) ω).functional A‖≤
      (((box d N\box d (N-r)).card:ℝ)/(box d N).card)*(8*‖A‖) := by
  classical
  let Λ:=box d N
  let F:=box d (N-r)
  have hF : F⊆Λ:=box_mono (Nat.sub_le N r)
  have hshift : ∀ y∈F,x+y∈Λ := by
    classical
    intro y hy
    simpa only [Nat.sub_add_cancel hr,add_comm x] using box_add_mem hy hx
  have hbound:=image_sdiff_card_le Λ F x hF hshift
  rw [cubeAverage_apply,cubeAverage_apply,←mul_sub,norm_mul,norm_inv,Complex.norm_natCast]
  have he : (∑ y∈Λ,ω.functional (translation d ℓ y (translation d ℓ x A)))=
      ∑ y∈Λ.image (fun y=>x+y),ω.functional (translation d ℓ y A) := by
    classical
    rw [Finset.sum_image (fun _ _ _ _ he=>add_left_cancel he)]
    apply Finset.sum_congr rfl
    intro y hy
    rw [translation_add,add_comm]
  rw [he]
  have hs:=(Average.norm_sum_sub_le (Λ.image (fun y=>x+y)) Λ
    (fun y=>ω.functional (translation d ℓ y A)) (4*‖A‖) (fun y=>by simpa only [norm_translation] using state_apply_norm_le ω (translation d ℓ y A)))
  have hecard : (((Λ\Λ.image (fun y=>x+y)).card:ℕ):ℝ)=(((Λ.image (fun y=>x+y)\Λ).card:ℕ):ℝ) := by exact_mod_cast sdiff_image_card Λ x
  rw [hecard] at hs
  have hb : ((Λ.image (fun y=>x+y)\Λ).card:ℝ)≤(Λ\F).card := by exact_mod_cast hbound
  have hp : (0:ℝ)<Λ.card:=cube_card_pos d N
  calc _ ≤ (Λ.card:ℝ)⁻¹*((((Λ.image (fun y=>x+y)\Λ).card:ℝ)+((Λ.image (fun y=>x+y)\Λ).card:ℝ))*(4*‖A‖)) := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hp.le)
       _ ≤ (Λ.card:ℝ)⁻¹*(((Λ\F).card+(Λ\F).card:ℝ)*(4*‖A‖)) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (add_le_add hb hb) (by positivity)) (inv_nonneg.mpr hp.le)
       _ = _ := by dsimp [Λ,F]; ring

lemma cubeAverage_limit_TI (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (η : ℕ → State d ℓ)
    (ω : State d ℓ) (hω : ∀ A,Tendsto (fun n=>(cubeAverage (box d (N n)) (box_nonempty d (N n)) (η n)).functional A) atTop (𝓝 (ω.functional A))) : TranslationInvariant ω := by
  classical
  intro x A
  obtain ⟨r,hr⟩:=(eventually_mem_box x).exists
  have hlim : Tendsto (fun n=>(cubeAverage (box d (N n)) (box_nonempty d (N n)) (η n)).functional (translation d ℓ x A)-
      (cubeAverage (box d (N n)) (box_nonempty d (N n)) (η n)).functional A) atTop (𝓝 0) := by
    classical
    apply squeeze_zero_norm' (a:=fun n=>(((box d (N n)\box d (N n-r)).card:ℝ)/(box d (N n)).card)*(8*‖A‖))
    · filter_upwards [hN.eventually (eventually_ge_atTop r)] with n hn
      exact cubeAverage_translation_bound (N n) r hn x hr (η n) A
    · simpa only [Function.comp_def,zero_mul] using ((box_boundary_inner_tendsto d r).comp hN).mul_const (8*‖A‖)
  exact sub_eq_zero.mp (tendsto_nhds_unique ((hω _).sub (hω A)) hlim)

end Heisenberg
end
end

end OAI
