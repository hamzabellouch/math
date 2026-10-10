import Mathlib

namespace OAI

section
noncomputable section
                                      
section

namespace MaximalSeshadri.AnalyticNode
noncomputable section

open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem analytic_square_root {f : E → ℂ} {p : E}
    (hf : AnalyticAt ℂ f p) (hfp : f p ≠ 0) :
    ∃ g : E → ℂ, AnalyticAt ℂ g p ∧ g p ≠ 0 ∧ ∀ z, (g z)^2 = f z := by
  have hsquare (w : ℂ) : w.sqrt^2 = w := by
    rw [Complex.sqrt, ← Complex.cpow_nat_mul]
    norm_num
  have hs : AnalyticAt ℂ Complex.sqrt 1 := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [Complex.isOpen_slitPlane.mem_nhds Complex.one_mem_slitPlane] with z hz
    exact Complex.differentiableAt_sqrt hz
  let g : E → ℂ := fun z => Complex.sqrt (f z / f p) * Complex.sqrt (f p)
  have heq (z : E) : (g z)^2 = f z := by
    simp only [g, mul_pow, hsquare]
    exact div_mul_cancel₀ _ hfp
  refine ⟨g, ?_, ?_, heq⟩
  · have hquot : AnalyticAt ℂ (fun z => f z / f p) p := hf.div_const
    have han : AnalyticAt ℂ Complex.sqrt (f p / f p) := by simpa [hfp] using hs
    have hcomp : AnalyticAt ℂ (fun z => Complex.sqrt (f z / f p)) p :=
      AnalyticAt.comp (g := Complex.sqrt) (f := fun z => f z / f p) han hquot
    exact hcomp.mul analyticAt_const
  · intro hz
    apply hfp
    rw [← heq p, hz, zero_pow (by decide)]

lemma exists_nonzero_shear (a b c : ℂ) (h : b^2 - 4*a*c ≠ 0) :
    ∃ t : ℂ, a + t*b + t^2*c ≠ 0 := by
  by_cases ha : a ≠ 0
  · exact ⟨0, by simpa using ha⟩
  have ha : a = 0 := not_ne_iff.mp ha
  have hb : b ≠ 0 := by
    intro hb
    simp [ha, hb] at h
  by_cases hbc : b+c ≠ 0
  · exact ⟨1, by simpa [ha] using hbc⟩
  refine ⟨-1, ?_⟩
  have hbc : b+c = 0 := not_ne_iff.mp hbc
  intro heq
  simp only [ha, zero_add, neg_mul, one_mul, neg_one_sq, one_mul] at heq
  apply hb
  linear_combination (hbc - heq) / 2

def nodeLinear (a b d : ℂ) : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
  ((2*a) • ContinuousLinearMap.fst ℂ ℂ ℂ +
    (b+d) • ContinuousLinearMap.snd ℂ ℂ ℂ).prod
    ((2*a) • ContinuousLinearMap.fst ℂ ℂ ℂ +
      (b-d) • ContinuousLinearMap.snd ℂ ℂ ℂ)

lemma nodeLinear_apply (a b d : ℂ) (z : ℂ × ℂ) :
    nodeLinear a b d z = (2*a*z.1 + (b+d)*z.2, 2*a*z.1 + (b-d)*z.2) := rfl

lemma nodeLinear_bijective (a b d : ℂ) (ha : a ≠ 0) (hd : d ≠ 0) :
    Function.Bijective (nodeLinear a b d) := by
  have hi : Function.Injective (nodeLinear a b d) := by
    change Function.Injective (nodeLinear a b d).toLinearMap
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    have h₁ := congrArg Prod.fst hz
    have h₂ := congrArg Prod.snd hz
    change 2*a*z.1+(b+d)*z.2 = 0 at h₁
    change 2*a*z.1+(b-d)*z.2 = 0 at h₂
    have hzz : 2*d*z.2 = 0 := by linear_combination h₁-h₂
    have hz₂ : z.2 = 0 := (mul_eq_zero.mp hzz).resolve_left (mul_ne_zero (by norm_num) hd)
    rw [hz₂, mul_zero, add_zero] at h₁
    have hz₁ : z.1 = 0 := (mul_eq_zero.mp h₁).resolve_left (mul_ne_zero (by norm_num) ha)
    exact Prod.ext hz₁ hz₂
  exact ⟨hi, (LinearMap.injective_iff_surjective (f := (nodeLinear a b d).toLinearMap)).mp hi⟩

theorem analytic_node_inverse
    (a b c : (ℂ × ℂ) → ℂ)
    (ha : AnalyticAt ℂ a 0) (hb : AnalyticAt ℂ b 0) (hc : AnalyticAt ℂ c 0)
    (ha₀ : a 0 ≠ 0) (hdisc : (b 0)^2 - 4*a 0*c 0 ≠ 0) :
    ∃ (ψ : (ℂ × ℂ) → (ℂ × ℂ)) (u : (ℂ × ℂ) → ℂ),
      ψ 0 = 0 ∧ AnalyticAt ℂ ψ 0 ∧ AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧
      (∀ᶠ z in 𝓝 0, a (ψ z)*(ψ z).1^2 + b (ψ z)*(ψ z).1*(ψ z).2 +
        c (ψ z)*(ψ z).2^2 = u z*z.1*z.2) ∧
      (∃ e : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ), HasFDerivAt ψ (e : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) 0) ∧
      ∃ V : Set (ℂ × ℂ), IsOpen V ∧ 0 ∈ V ∧ Set.InjOn ψ V := by
  let Δ : (ℂ × ℂ) → ℂ := fun z => (b z)^2-4*a z*c z
  have hΔ : AnalyticAt ℂ Δ 0 := (hb.pow 2).sub ((analyticAt_const.mul ha).mul hc)
  obtain ⟨d, hd, hd₀, hd₂⟩ := analytic_square_root hΔ hdisc
  let H : (ℂ × ℂ) → (ℂ × ℂ) := fun z =>
    (2*a z*z.1+(b z+d z)*z.2, 2*a z*z.1+(b z-d z)*z.2)
  have hH₀ : H 0 = 0 := by simp [H]
  have hH : AnalyticAt ℂ H 0 := by
    exact (((analyticAt_const.mul ha).mul analyticAt_fst).add
      ((hb.add hd).mul analyticAt_snd)).prod
      (((analyticAt_const.mul ha).mul analyticAt_fst).add
        ((hb.sub hd).mul analyticAt_snd))
  have hder : HasFDerivAt H (nodeLinear (a 0) (b 0) (d 0)) 0 := by
    have hfst := ((hasFDerivAt_const (2 : ℂ) (0 : ℂ × ℂ)).mul
      ha.differentiableAt.hasFDerivAt).mul
      (ContinuousLinearMap.fst ℂ ℂ ℂ).hasFDerivAt
    have hplus := (hb.differentiableAt.hasFDerivAt.add
      hd.differentiableAt.hasFDerivAt).mul (ContinuousLinearMap.snd ℂ ℂ ℂ).hasFDerivAt
    have hminus := (hb.differentiableAt.hasFDerivAt.sub
      hd.differentiableAt.hasFDerivAt).mul (ContinuousLinearMap.snd ℂ ℂ ℂ).hasFDerivAt
    apply ((hfst.add hplus).prodMk (hfst.add hminus)).congr_fderiv
    ext <;> simp [nodeLinear]
  let e : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ) :=
    (LinearEquiv.ofBijective (nodeLinear (a 0) (b 0) (d 0)).toLinearMap
      (nodeLinear_bijective _ _ _ ha₀ hd₀)).toContinuousLinearEquiv
  have hder' : HasFDerivAt H (e : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) 0 := hder
  have hcont : ContDiffAt ℂ ω H 0 := hH.contDiffAt
  have hn : (ω : WithTop ℕ∞) ≠ 0 := by simp
  let T := hcont.toOpenPartialHomeomorph H hder' hn
  let ψ := hcont.localInverse hder' hn
  have hψ₀ : ψ 0 = 0 := by
    simpa only [hH₀] using hcont.localInverse_apply_image hder' hn
  have hψ : AnalyticAt ℂ ψ 0 := by
    simpa only [hH₀] using (hcont.to_localInverse hder' hn).analyticAt
  have htarget : (0 : ℂ × ℂ) ∈ T.target := by
    simpa only [hH₀] using hcont.image_mem_toOpenPartialHomeomorph_target hder' hn
  have hright : ∀ᶠ z in 𝓝 0, H (ψ z) = z := by
    filter_upwards [T.open_target.mem_nhds htarget] with z hz
    exact T.right_inv hz
  let u : (ℂ × ℂ) → ℂ := fun z => (4*a (ψ z))⁻¹
  have haψ : AnalyticAt ℂ (fun z => a (ψ z)) 0 :=
    ha.comp_of_eq hψ hψ₀
  have hua : AnalyticAt ℂ u 0 := (analyticAt_const.mul haψ).inv (by simp [hψ₀, ha₀])
  refine ⟨ψ,u,hψ₀,hψ,hua,by simp [u,hψ₀,ha₀], ?_,
    ⟨e.symm, ?_⟩, T.target,T.open_target,htarget,T.symm.injOn⟩
  swap
  · have hderψ : HasFDerivAt H (e : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) (ψ 0) := by
      simpa only [hψ₀] using hder'
    have hc := hderψ.comp (0 : ℂ × ℂ) hψ.differentiableAt.hasFDerivAt
    have hi : HasFDerivAt (fun z => H (ψ z)) (ContinuousLinearMap.id ℂ (ℂ × ℂ)) 0 :=
      (hasFDerivAt_id (0 : ℂ × ℂ)).congr_of_eventuallyEq hright
    have heq := hc.unique hi
    apply hψ.differentiableAt.hasFDerivAt.congr_fderiv
    apply ContinuousLinearMap.ext
    intro v
    apply e.injective
    simpa using DFunLike.congr_fun heq v
  have haneq : ∀ᶠ z in 𝓝 0, a (ψ z) ≠ 0 := haψ.continuousAt.eventually_ne
    (by simpa [hψ₀] using ha₀)
  filter_upwards [hright, haneq] with z hz haz
  have hprod : (H (ψ z)).1*(H (ψ z)).2 = 4*a (ψ z)*
      (a (ψ z)*(ψ z).1^2 + b (ψ z)*(ψ z).1*(ψ z).2 + c (ψ z)*(ψ z).2^2) := by
    have heq := hd₂ (ψ z)
    dsimp only [Δ] at heq
    dsimp only [H]
    linear_combination -(ψ z).2^2 * heq
  rw [hz] at hprod
  dsimp only [u]
  field_simp [haz]
  linear_combination -hprod

def shearLinear (t : ℂ) : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
  (ContinuousLinearMap.fst ℂ ℂ ℂ).prod
    (t • ContinuousLinearMap.fst ℂ ℂ ℂ + ContinuousLinearMap.snd ℂ ℂ ℂ)

lemma shearLinear_apply (t : ℂ) (z : ℂ × ℂ) :
    shearLinear t z = (z.1, t*z.1+z.2) := rfl

lemma shearLinear_bijective (t : ℂ) : Function.Bijective (shearLinear t) := by
  constructor
  · intro z w h
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    change z.1 = w.1 at h₁
    change t*z.1+z.2 = t*w.1+w.2 at h₂
    exact Prod.ext h₁ (by rw [h₁] at h₂; exact add_left_cancel h₂)
  · intro z
    exact ⟨(z.1, z.2-t*z.1), by simp [shearLinear_apply]⟩

theorem analytic_node_normal_form
    (a b c : (ℂ × ℂ) → ℂ)
    (ha : AnalyticAt ℂ a 0) (hb : AnalyticAt ℂ b 0) (hc : AnalyticAt ℂ c 0)
    (hdisc : (b 0)^2 - 4*a 0*c 0 ≠ 0) :
    ∃ (ψ : (ℂ × ℂ) → (ℂ × ℂ)) (u : (ℂ × ℂ) → ℂ),
      ψ 0 = 0 ∧ AnalyticAt ℂ ψ 0 ∧ AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧
      (∀ᶠ z in 𝓝 0, a (ψ z)*(ψ z).1^2 + b (ψ z)*(ψ z).1*(ψ z).2 +
        c (ψ z)*(ψ z).2^2 = u z*z.1*z.2) ∧
      (∃ e : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ), HasFDerivAt ψ (e : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) 0) ∧
      ∃ V : Set (ℂ × ℂ), IsOpen V ∧ 0 ∈ V ∧ Set.InjOn ψ V := by
  obtain ⟨t, ht⟩ := exists_nonzero_shear (a 0) (b 0) (c 0) hdisc
  let S : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ) :=
    (LinearEquiv.ofBijective (shearLinear t).toLinearMap
      (shearLinear_bijective t)).toContinuousLinearEquiv
  have hS (z : ℂ × ℂ) : S z = (z.1,t*z.1+z.2) := rfl
  let A : (ℂ × ℂ) → ℂ := fun z => a (S z)+t*b (S z)+t^2*c (S z)
  let B : (ℂ × ℂ) → ℂ := fun z => b (S z)+2*t*c (S z)
  let C : (ℂ × ℂ) → ℂ := fun z => c (S z)
  have hSA : AnalyticAt ℂ A 0 := by
    exact ((ha.comp_of_eq (S.analyticAt 0) (map_zero S)).add
      (analyticAt_const.mul (hb.comp_of_eq (S.analyticAt 0) (map_zero S)))).add
      (analyticAt_const.mul (hc.comp_of_eq (S.analyticAt 0) (map_zero S)))
  have hSB : AnalyticAt ℂ B 0 := by
    exact (hb.comp_of_eq (S.analyticAt 0) (map_zero S)).add
      (analyticAt_const.mul (hc.comp_of_eq (S.analyticAt 0) (map_zero S)))
  have hSC : AnalyticAt ℂ C 0 := hc.comp_of_eq (S.analyticAt 0) (map_zero S)
  have hA₀ : A 0 ≠ 0 := by simpa [A] using ht
  have hABC : (B 0)^2-4*A 0*C 0 ≠ 0 := by
    have heq : (B 0)^2-4*A 0*C 0 = (b 0)^2-4*a 0*c 0 := by simp [A,B,C]; ring
    rwa [heq]
  obtain ⟨ψ,u,hψ₀,hψ,hu,hu₀,heq,⟨e,he⟩,V,hV,hV₀,hinj⟩ :=
    analytic_node_inverse A B C hSA hSB hSC hA₀ hABC
  refine ⟨S ∘ ψ,u,by simp [hψ₀],(S.analyticAt (ψ 0)).comp hψ,hu,hu₀,?_,
    ⟨e.trans S, ?_⟩,V,hV,hV₀,?_⟩
  · filter_upwards [heq] with z hz
    convert hz using 1
    simp only [Function.comp_apply,A,B,C,hS]
    ring
  · exact S.hasFDerivAt.comp 0 he
  · intro z hz w hw h
    exact hinj hz hw (S.injective h)

end
end MaximalSeshadri.AnalyticNode

end


end
end

end OAI
