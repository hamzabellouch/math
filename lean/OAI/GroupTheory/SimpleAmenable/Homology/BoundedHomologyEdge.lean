import Mathlib

namespace OAI

section

section

open CategoryTheory CategoryTheory.Limits

namespace BoundedHomologyEdge

universe u
variable {k G : Type u} [CommRing k] [Group G]

noncomputable abbrev Hmap {A B : Rep k G} (n : ℕ) (f : A ⟶ B) :
    groupHomology A n ⟶ groupHomology B n :=
  (groupHomology.functor k G n).map f

lemma Hmap_comp {A B C : Rep k G} (n : ℕ) (f : A ⟶ B) (g : B ⟶ C) :
    Hmap n (f ≫ g) = Hmap n f ≫ Hmap n g :=
  (groupHomology.functor k G n).map_comp f g

lemma epi_Hmap_zero {A B : Rep k G} (f : A ⟶ B) [Epi f] : Epi (Hmap 0 f) :=
  groupHomology.epi_map_0_of_epi f

lemma exact₂ {X : ShortComplex (Rep k G)} (hX : X.ShortExact) (n : ℕ) :
    (ShortComplex.mk (Hmap n X.f) (Hmap n X.g)
      (by rw [← Hmap_comp, X.zero]; exact (groupHomology.functor k G n).map_zero _ _)).Exact :=
  groupHomology.mapShortComplex₂_exact hX n

lemma exact₁ {X : ShortComplex (Rep k G)} (hX : X.ShortExact) (n : ℕ) :
    (ShortComplex.mk (groupHomology.δ hX (n+1) n rfl) (Hmap n X.f)
      (groupHomology.mapShortComplex₁ hX rfl).zero).Exact :=
  groupHomology.mapShortComplex₁_exact hX rfl

lemma exact₃ {X : ShortComplex (Rep k G)} (hX : X.ShortExact) (n : ℕ) :
    (ShortComplex.mk (Hmap (n+1) X.g) (groupHomology.δ hX (n+1) n rfl)
      (groupHomology.mapShortComplex₃ hX rfl).zero).Exact :=
  groupHomology.mapShortComplex₃_exact hX rfl

lemma epi_Hmap_succ_of_mono {X : ShortComplex (Rep k G)} (hX : X.ShortExact) (n : ℕ)
    [Mono (Hmap n X.f)] : Epi (Hmap (n+1) X.g) := by
  exact (exact₃ hX n).epi_f ((exact₁ hX n).mono_g_iff.mp (show Mono (Hmap n X.f) from inferInstance))

lemma epi_Hmap_succ_of_isZero {X : ShortComplex (Rep k G)} (hX : X.ShortExact) (n : ℕ)
    (h : IsZero (groupHomology X.X₁ n)) : Epi (Hmap (n+1) X.g) := by
  exact (exact₃ hX n).epi_f (h.eq_zero_of_tgt _)

lemma mono_Hmap_of_zero {X : ShortComplex (Rep k G)} (hX : X.ShortExact) (n : ℕ)
    (h : Hmap n X.f = 0) : Mono (Hmap n X.g) :=
  (exact₂ hX n).mono_g_iff.mpr h

lemma isZero_H0_quotient {X : ShortComplex (Rep k G)} (hX : X.ShortExact)
    [Epi (Hmap 0 X.f)] : IsZero (groupHomology X.X₃ 0) := by
  let : Epi X.g := hX.epi_g
  let : Epi (Hmap 0 X.g) := epi_Hmap_zero X.g
  exact IsZero.of_epi_eq_zero (Hmap 0 X.g) ((exact₂ hX 0).epi_f_iff.mp (show Epi (Hmap 0 X.f) from inferInstance))

lemma isIso_right_of_epi_left {A B C : ModuleCat k} (f : A ⟶ B) (g : B ⟶ C)
    [Epi f] [IsIso (f ≫ g)] : IsIso g := by
  let : Mono f := mono_of_mono f g
  let : IsIso f := isIso_of_mono_of_epi f
  exact IsIso.of_isIso_comp_left f g

section TwoKernels
variable {Z₁ Z₂ C₀ C₁ C₂ C₃ : Rep k G}
  {i₁ : Z₁ ⟶ C₁} {p₁ : C₁ ⟶ C₀} {i₂ : Z₂ ⟶ C₂} {p₂ : C₂ ⟶ Z₁}
  {w₁ : i₁ ≫ p₁ = 0} {w₂ : i₂ ≫ p₂ = 0}
  (h₁ : (ShortComplex.mk i₁ p₁ w₁).ShortExact)
  (h₂ : (ShortComplex.mk i₂ p₂ w₂).ShortExact)
  (e : C₃ ⟶ Z₂) [Epi e]

lemma isIso_H0_i₂ [IsIso (Hmap 0 (e ≫ i₂))] : IsIso (Hmap 0 i₂) := by
  let : Epi (Hmap 0 e) := epi_Hmap_zero e
  let : IsIso (Hmap 0 e ≫ Hmap 0 i₂) := by rw [← Hmap_comp]; infer_instance
  exact isIso_right_of_epi_left (Hmap 0 e) (Hmap 0 i₂)

include h₂

lemma isZero_H0_kernel [IsIso (Hmap 0 (e ≫ i₂))] :
    IsZero (groupHomology Z₁ 0) := by
  let : IsIso (Hmap 0 i₂) := isIso_H0_i₂ e
  exact isZero_H0_quotient h₂

include h₁

lemma H1_isIso [IsIso (Hmap 0 (e ≫ i₂))]
    (hodd : Hmap 1 (p₂ ≫ i₁) = 0) : IsIso (Hmap 1 p₁) := by
  let : IsIso (Hmap 0 i₂) := isIso_H0_i₂ e
  let : Epi (Hmap 1 p₂) := epi_Hmap_succ_of_mono h₂ 0
  have hi : Hmap 1 i₁ = 0 := zero_of_epi_comp (Hmap 1 p₂) (by
    rw [← Hmap_comp]; exact hodd)
  let : Mono (Hmap 1 p₁) := mono_Hmap_of_zero h₁ 1 hi
  let : Epi (Hmap 1 p₁) := epi_Hmap_succ_of_isZero h₁ 0 (isZero_H0_kernel h₂ e)
  exact isIso_of_mono_of_epi (Hmap 1 p₁)

lemma H2_epi_of_isZero [IsIso (Hmap 0 (e ≫ i₂))]
    (hperfect : IsZero (groupHomology C₂ 1)) : Epi (Hmap 2 p₁) := by
  let : IsIso (Hmap 0 i₂) := isIso_H0_i₂ e
  let : Epi (Hmap 1 p₂) := epi_Hmap_succ_of_mono h₂ 0
  have hz : IsZero (groupHomology Z₁ 1) := IsZero.of_epi (Hmap 1 p₂) hperfect
  exact epi_Hmap_succ_of_isZero h₁ 1 hz

lemma H2_epi_of_epi [IsIso (Hmap 0 (e ≫ i₂))]
    [Epi (Hmap 1 (e ≫ i₂))] : Epi (Hmap 2 p₁) := by
  let : IsIso (Hmap 0 i₂) := isIso_H0_i₂ e
  let : Epi (Hmap 1 p₂) := epi_Hmap_succ_of_mono h₂ 0
  let : Epi (Hmap 1 e ≫ Hmap 1 i₂) := by rw [← Hmap_comp]; infer_instance
  let : Epi (Hmap 1 i₂) := epi_of_epi (Hmap 1 e) (Hmap 1 i₂)
  have hp : Hmap 1 p₂ = 0 := (exact₂ h₂ 1).epi_f_iff.mp inferInstance
  have hz : IsZero (groupHomology Z₁ 1) := IsZero.of_epi_eq_zero (Hmap 1 p₂) hp
  exact epi_Hmap_succ_of_isZero h₁ 1 hz

end TwoKernels

section ThreeKernels
variable {Z₁ Z₂ Z₃ C₀ C₁ C₂ C₃ C₄ C₅ : Rep k G}
  {i₁ : Z₁ ⟶ C₁} {p₁ : C₁ ⟶ C₀} {i₂ : Z₂ ⟶ C₂} {p₂ : C₂ ⟶ Z₁}
  {i₃ : Z₃ ⟶ C₃} {p₃ : C₃ ⟶ Z₂}
  {w₁ : i₁ ≫ p₁ = 0} {w₂ : i₂ ≫ p₂ = 0} {w₃ : i₃ ≫ p₃ = 0}
  (h₁ : (ShortComplex.mk i₁ p₁ w₁).ShortExact)
  (h₂ : (ShortComplex.mk i₂ p₂ w₂).ShortExact)
  (h₃ : (ShortComplex.mk i₃ p₃ w₃).ShortExact)
  (e₄ : C₄ ⟶ Z₃) [Epi e₄] (d₅ : C₅ ⟶ C₄) (w₅ : d₅ ≫ e₄ = 0)

include w₅

lemma isZero_H0_third_kernel [Epi (Hmap 0 d₅)] :
    IsZero (groupHomology Z₃ 0) := by
  let : Epi (Hmap 0 e₄) := epi_Hmap_zero e₄
  have he : Hmap 0 e₄ = 0 := zero_of_epi_comp (Hmap 0 d₅) (by
    rw [← Hmap_comp, w₅]; exact (groupHomology.functor k G 0).map_zero _ _)
  exact IsZero.of_epi_eq_zero (Hmap 0 e₄) he

include h₁ h₂ h₃

lemma H2_isIso [IsIso (Hmap 0 (p₃ ≫ i₂))] [IsIso (Hmap 1 (p₃ ≫ i₂))]
    [Epi (Hmap 0 d₅)] (hodd : Hmap 2 (p₂ ≫ i₁) = 0) : IsIso (Hmap 2 p₁) := by
  let : Epi p₃ := h₃.epi_g
  let : Epi (Hmap 2 p₁) := H2_epi_of_epi h₁ h₂ p₃
  have hz : IsZero (groupHomology Z₃ 0) := isZero_H0_third_kernel e₄ d₅ w₅
  let : Epi (Hmap 1 p₃) := epi_Hmap_succ_of_isZero h₃ 0 hz
  let : IsIso (Hmap 1 p₃ ≫ Hmap 1 i₂) := by rw [← Hmap_comp]; infer_instance
  let : IsIso (Hmap 1 i₂) := isIso_right_of_epi_left (Hmap 1 p₃) (Hmap 1 i₂)
  let : Epi (Hmap 2 p₂) := epi_Hmap_succ_of_mono h₂ 1
  have hi : Hmap 2 i₁ = 0 := zero_of_epi_comp (Hmap 2 p₂) (by
    rw [← Hmap_comp]; exact hodd)
  let : Mono (Hmap 2 p₁) := mono_Hmap_of_zero h₁ 2 hi
  exact isIso_of_mono_of_epi (Hmap 2 p₁)
end ThreeKernels

section KernelWindow

lemma exact_of_comp_mono {𝒞 : Type*} [Category 𝒞] [HasZeroMorphisms 𝒞]
    {A B C D : 𝒞} (f : A ⟶ B) (g : B ⟶ C) (i : C ⟶ D) [Mono i]
    (w : f ≫ g = 0) (w' : f ≫ (g ≫ i) = 0)
    (h : (ShortComplex.mk f (g ≫ i) w').Exact) :
    (ShortComplex.mk f g w).Exact := by
  let φ : ShortComplex.mk f g w ⟶ ShortComplex.mk f (g ≫ i) w' :=
    { τ₁ := 𝟙 A, τ₂ := 𝟙 B, τ₃ := i, comm₁₂ := by simp, comm₂₃ := by simp }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr h

lemma kernel_shortExact {A B : Rep k G} (f : A ⟶ B) [Epi f] :
    (ShortComplex.mk (kernel.ι f) f (kernel.condition f)).ShortExact :=
  { exact := ShortComplex.exact_kernel f, mono_f := inferInstance, epi_g := inferInstance }

variable {C₀ C₁ C₂ C₃ C₄ C₅ : Rep k G}
  (d₁ : C₁ ⟶ C₀) (d₂ : C₂ ⟶ C₁) (d₃ : C₃ ⟶ C₂) (d₄ : C₄ ⟶ C₃) (d₅ : C₅ ⟶ C₄)
  (w₂ : d₂ ≫ d₁ = 0) (w₃ : d₃ ≫ d₂ = 0) (w₄ : d₄ ≫ d₃ = 0) (w₅ : d₅ ≫ d₄ = 0)

noncomputable def lift₂ := kernel.lift d₁ d₂ w₂

@[simp] lemma lift₂_ι : lift₂ d₁ d₂ w₂ ≫ kernel.ι d₁ = d₂ := kernel.lift_ι _ _ _

include w₃ in
lemma comp_lift₂_zero : d₃ ≫ lift₂ d₁ d₂ w₂ = 0 := by
  apply zero_of_comp_mono (kernel.ι d₁)
  simpa only [Category.assoc, lift₂_ι] using w₃

noncomputable def lift₃ :=
  kernel.lift (lift₂ d₁ d₂ w₂) d₃ (comp_lift₂_zero d₁ d₂ d₃ w₂ w₃)

@[simp] lemma lift₃_ι : lift₃ d₁ d₂ d₃ w₂ w₃ ≫ kernel.ι (lift₂ d₁ d₂ w₂) = d₃ :=
  kernel.lift_ι _ _ _

include w₄ in
lemma comp_lift₃_zero : d₄ ≫ lift₃ d₁ d₂ d₃ w₂ w₃ = 0 := by
  apply zero_of_comp_mono (kernel.ι (lift₂ d₁ d₂ w₂))
  simpa only [Category.assoc, lift₃_ι] using w₄

noncomputable def lift₄ :=
  kernel.lift (lift₃ d₁ d₂ d₃ w₂ w₃) d₄ (comp_lift₃_zero d₁ d₂ d₃ d₄ w₂ w₃ w₄)

@[simp] lemma lift₄_ι : lift₄ d₁ d₂ d₃ d₄ w₂ w₃ w₄ ≫
    kernel.ι (lift₃ d₁ d₂ d₃ w₂ w₃) = d₄ := kernel.lift_ι _ _ _

include w₅ in
lemma comp_lift₄_zero : d₅ ≫ lift₄ d₁ d₂ d₃ d₄ w₂ w₃ w₄ = 0 := by
  apply zero_of_comp_mono (kernel.ι (lift₃ d₁ d₂ d₃ w₂ w₃))
  simpa only [Category.assoc, lift₄_ι] using w₅

lemma epi_lift₂ (h : (ShortComplex.mk d₂ d₁ w₂).Exact) : Epi (lift₂ d₁ d₂ w₂) :=
  h.epi_kernelLift

lemma epi_lift₃ (h : (ShortComplex.mk d₃ d₂ w₃).Exact) : Epi (lift₃ d₁ d₂ d₃ w₂ w₃) := by
  have hh : (ShortComplex.mk d₃ (lift₂ d₁ d₂ w₂)
      (comp_lift₂_zero d₁ d₂ d₃ w₂ w₃)).Exact := by
    apply exact_of_comp_mono d₃ (lift₂ d₁ d₂ w₂) (kernel.ι d₁)
      (comp_lift₂_zero d₁ d₂ d₃ w₂ w₃) (by simpa using w₃)
    simpa using h
  exact hh.epi_kernelLift

lemma epi_lift₄ (h : (ShortComplex.mk d₄ d₃ w₄).Exact) :
    Epi (lift₄ d₁ d₂ d₃ d₄ w₂ w₃ w₄) := by
  have hh : (ShortComplex.mk d₄ (lift₃ d₁ d₂ d₃ w₂ w₃)
      (comp_lift₃_zero d₁ d₂ d₃ d₄ w₂ w₃ w₄)).Exact := by
    apply exact_of_comp_mono d₄ (lift₃ d₁ d₂ d₃ w₂ w₃) (kernel.ι (lift₂ d₁ d₂ w₂))
      (comp_lift₃_zero d₁ d₂ d₃ d₄ w₂ w₃ w₄) (by simpa using w₄)
    simpa using h
  exact hh.epi_kernelLift

lemma chain_H2_epi [Epi d₁]
    (h₁ : (ShortComplex.mk d₂ d₁ w₂).Exact)
    (h₂ : (ShortComplex.mk d₃ d₂ w₃).Exact)
    [IsIso (Hmap 0 d₃)] (hz : IsZero (groupHomology C₂ 1)) : Epi (Hmap 2 d₁) := by
  let : Epi (lift₂ d₁ d₂ w₂) := epi_lift₂ d₁ d₂ w₂ h₁
  let : Epi (lift₃ d₁ d₂ d₃ w₂ w₃) := epi_lift₃ d₁ d₂ d₃ w₂ w₃ h₂
  let : IsIso (Hmap 0 (lift₃ d₁ d₂ d₃ w₂ w₃ ≫ kernel.ι (lift₂ d₁ d₂ w₂))) := by
    simpa only [lift₃_ι] using (inferInstance : IsIso (Hmap 0 d₃))
  exact H2_epi_of_isZero (kernel_shortExact d₁) (kernel_shortExact (lift₂ d₁ d₂ w₂))
    (lift₃ d₁ d₂ d₃ w₂ w₃) hz

lemma chain_H1_isIso [Epi d₁]
    (h₁ : (ShortComplex.mk d₂ d₁ w₂).Exact)
    (h₂ : (ShortComplex.mk d₃ d₂ w₃).Exact)
    [IsIso (Hmap 0 d₃)] (hodd : Hmap 1 d₂ = 0) : IsIso (Hmap 1 d₁) := by
  let : Epi (lift₂ d₁ d₂ w₂) := epi_lift₂ d₁ d₂ w₂ h₁
  let : Epi (lift₃ d₁ d₂ d₃ w₂ w₃) := epi_lift₃ d₁ d₂ d₃ w₂ w₃ h₂
  let : IsIso (Hmap 0 (lift₃ d₁ d₂ d₃ w₂ w₃ ≫ kernel.ι (lift₂ d₁ d₂ w₂))) := by
    simpa only [lift₃_ι] using (inferInstance : IsIso (Hmap 0 d₃))
  apply H1_isIso (kernel_shortExact d₁) (kernel_shortExact (lift₂ d₁ d₂ w₂))
    (lift₃ d₁ d₂ d₃ w₂ w₃)
  simpa only [lift₂_ι] using hodd

include w₅ in

lemma chain_H2_isIso [Epi d₁]
    (h₁ : (ShortComplex.mk d₂ d₁ w₂).Exact)
    (h₂ : (ShortComplex.mk d₃ d₂ w₃).Exact)
    (h₃ : (ShortComplex.mk d₄ d₃ w₄).Exact)
    [IsIso (Hmap 0 d₃)] [IsIso (Hmap 1 d₃)] [Epi (Hmap 0 d₅)]
    (hodd : Hmap 2 d₂ = 0) : IsIso (Hmap 2 d₁) := by
  let : Epi (lift₂ d₁ d₂ w₂) := epi_lift₂ d₁ d₂ w₂ h₁
  let : Epi (lift₃ d₁ d₂ d₃ w₂ w₃) := epi_lift₃ d₁ d₂ d₃ w₂ w₃ h₂
  let : Epi (lift₄ d₁ d₂ d₃ d₄ w₂ w₃ w₄) := epi_lift₄ d₁ d₂ d₃ d₄ w₂ w₃ w₄ h₃
  let : IsIso (Hmap 0 (lift₃ d₁ d₂ d₃ w₂ w₃ ≫ kernel.ι (lift₂ d₁ d₂ w₂))) := by
    simpa only [lift₃_ι] using (inferInstance : IsIso (Hmap 0 d₃))
  let : IsIso (Hmap 1 (lift₃ d₁ d₂ d₃ w₂ w₃ ≫ kernel.ι (lift₂ d₁ d₂ w₂))) := by
    simpa only [lift₃_ι] using (inferInstance : IsIso (Hmap 1 d₃))
  apply H2_isIso (kernel_shortExact d₁) (kernel_shortExact (lift₂ d₁ d₂ w₂))
    (kernel_shortExact (lift₃ d₁ d₂ d₃ w₂ w₃))
    (lift₄ d₁ d₂ d₃ d₄ w₂ w₃ w₄) d₅ (comp_lift₄_zero d₁ d₂ d₃ d₄ d₅ w₂ w₃ w₄ w₅)
  simpa only [lift₂_ι] using hodd
end KernelWindow

end BoundedHomologyEdge

end

end

end OAI
