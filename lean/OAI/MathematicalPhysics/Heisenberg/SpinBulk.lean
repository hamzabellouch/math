import OAI.MathematicalPhysics.Heisenberg.SpinTranslations

namespace OAI

section
noncomputable section
open scoped Classical BigOperators ComplexConjugate
open Filter Topology
namespace Heisenberg
variable {d ℓ : ℕ}

lemma translation_totalZ (x : Site d) (Γ : Finset (Site d)) :
    translation d ℓ x (totalZ Γ)=totalZ (Γ.image (fun y=>x+y)) := by
  simp only [totalZ,map_sum,translation_spinZ,Finset.sum_image (fun _ _ _ _ he=>add_left_cancel he)]

lemma translation_evolve (x : Site d) (H : QuasiLocal d ℓ) (z : ℂ) (A : QuasiLocal d ℓ) :
    translation d ℓ x (GibbsStrip.evolve H z A)=GibbsStrip.evolve (translation d ℓ x H) z (translation d ℓ x A) := by
  have hmul (B C : QuasiLocal d ℓ) :
      translation d ℓ x (B * C) = translation d ℓ x B * translation d ℓ x C :=
    (translation d ℓ x).map_mul' B C
  have hsmul (scalar : ℂ) (B : QuasiLocal d ℓ) :
      translation d ℓ x (scalar • B) = scalar • translation d ℓ x B :=
    (translation d ℓ x).toAlgHom.toLinearMap.map_smul scalar B
  simp only [GibbsStrip.evolve, hmul, translation_exp, hsmul]

lemma translation_fieldDynamics (x : Site d) (Γ : Finset (Site d)) (h t : ℝ) (A : QuasiLocal d ℓ) :
    translation d ℓ x (GibbsStrip.evolve (shiftedField Γ h) t A)=
      GibbsStrip.evolve (shiftedField (Γ.image (fun y=>x+y)) h) t (translation d ℓ x A) := by
  simp only [shiftedField_evolve,translation_finiteDynamics,translation_evolve,translation_totalZ]

lemma translated_volume_cancel (x : Site d) (Λ : Finset (Site d)) :
    (Λ.image (fun y=>-x+y)).image (fun y=>x+y)=Λ := by
  rw [Finset.image_image]
  simp only [Function.comp_def,←add_assoc,add_neg_cancel,zero_add]
  exact Finset.image_id'

lemma box_add_mem {N r : ℕ} {x y : Site d} (hx : x∈box d N) (hy : y∈box d r) : x+y∈box d (N+r) := by
  apply (box_mem _ _ _).mpr
  intro i
  exact (abs_add_le (x i) (y i)).trans (by
    simpa only [Nat.cast_add] using add_le_add ((box_mem _ _ _).mp hx i) ((box_mem _ _ _).mp hy i))

lemma box_deep_translate {N r : ℕ} (hr : r≤N) {x : Site d} (hx : x∈box d (N-r)) :
    box d r⊆(box d N).image (fun y=>-x+y) := by
  intro y hy
  refine Finset.mem_image.mpr ⟨x+y,?_,by simp only [←add_assoc,neg_add_cancel,zero_add]⟩
  simpa only [Nat.sub_add_cancel hr] using box_add_mem hx hy

lemma box_boundary_inner_tendsto (d r : ℕ) :
    Tendsto (fun N : ℕ=>((box d N\box d (N-r)).card:ℝ)/((box d N).card:ℝ)) atTop (𝓝 0) := by
  have hn : Tendsto (fun N : ℕ=>N-r) atTop atTop := by
    refine tendsto_atTop.2 (fun b=>?_)
    filter_upwards [eventually_ge_atTop (b+r)] with N hN
    omega
  apply ((box_boundary_ratio_tendsto d r).comp hn).congr'
  filter_upwards [eventually_ge_atTop r] with N hN
  change ((box d (N-r+r)\box d (N-r)).card:ℝ)/((box d (N-r+r)).card:ℝ)=_
  rw [Nat.sub_add_cancel hN]

lemma image_sdiff_card_le (Λ F : Finset (Site d)) (x : Site d)
    (_hF : F⊆Λ) (hshift : ∀ y∈F,x+y∈Λ) :
    ((Λ.image (fun y=>x+y))\Λ).card≤(Λ\F).card := by
  apply le_trans (Finset.card_le_card (show (Λ.image (fun y=>x+y))\Λ⊆(Λ\F).image (fun y=>x+y) from ?_)) Finset.card_image_le
  intro z hz
  obtain ⟨hz,hzout⟩:=Finset.mem_sdiff.mp hz
  obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hz
  exact Finset.mem_image.mpr ⟨y,Finset.mem_sdiff.mpr ⟨hy,fun hyF=>hzout (hshift y hyF)⟩,rfl⟩

lemma sdiff_image_card (Λ : Finset (Site d)) (x : Site d) :
    (Λ\Λ.image (fun y=>x+y)).card=(Λ.image (fun y=>x+y)\Λ).card := by
  rw [Finset.card_sdiff,Finset.card_sdiff,Finset.card_image_of_injective _ (add_right_injective x),Finset.inter_comm]

end Heisenberg
end
end

end OAI
