import Mathlib
import OAI.Analysis.Conductivity.Walls.CriticalWall

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix Filter Topology

lemma wallPrimitive_tsupport_surface {K : Set (ℝ×ℝ)} (hK : IsClosed K)
    {r : Box3 → ℝ} (hr : tsupport r⊆Prod.fst ⁻¹' K) :
    tsupport (wallPrimitive r)⊆Prod.fst ⁻¹' K := by
  apply closure_minimal _ (hK.preimage continuous_fst)
  intro p hp
  by_contra hn
  have hz (t : ℝ) : r (p.1,t*p.2)=0 :=
    image_eq_zero_of_notMem_tsupport (fun (hh : (p.1,t*p.2) ∈ tsupport r) =>
      (show p.1∉K from hn) (@hr (p.1,t*p.2) hh))
  exact hp (by simp [wallPrimitive,hz])

lemma wallQuotient_tsupport_surface {K : Set (ℝ×ℝ)} (hK : IsClosed K)
    {r : Box3 → ℝ} (hr : tsupport r⊆Prod.fst ⁻¹' K) :
    tsupport (wallQuotient r)⊆Prod.fst ⁻¹' K := by
  apply closure_minimal _ (hK.preimage continuous_fst)
  intro p hp
  by_contra hn
  have hz (t : ℝ) : wallDerivative r (p.1,t*p.2)=0 := by
    dsimp [wallDerivative]
    rw [fderiv_of_notMem_tsupport ℝ (fun (hh : (p.1,t*p.2) ∈ tsupport r) =>
      (show p.1∉K from hn) (@hr (p.1,t*p.2) hh))]
    rfl
  exact hp (by simp [wallQuotient,hz])

lemma wallParticularTensor_tsupport_surface {K : Set (ℝ×ℝ)} (hK : IsClosed K)
    {χ v r₁ r₂ : Box3 → ℝ}
    (hr₁ : tsupport r₁⊆Prod.fst ⁻¹' K) (hr₂ : tsupport r₂⊆Prod.fst ⁻¹' K) :
    tsupport (wallParticularTensor χ v r₁ r₂)⊆
      (fun x : Coord3 => (boxCoordinates x).1) ⁻¹' K := by
  have hA := wallPrimitive_tsupport_surface hK hr₁
  have hd : tsupport (wallAlong (1,0) (fun p => wallPrimitive r₁ p*wallDerivative v p))⊆
      Prod.fst ⁻¹' K :=
    (tsupport_fderiv_apply_subset ℝ ((1,0),0)).trans (tsupport_mul_subset_left.trans hA)
  have hG : tsupport (wallParticularNumerator (1,0) v r₁ r₂)⊆Prod.fst ⁻¹' K := by
    apply (tsupport_sub _ _).trans
    apply union_subset
    · exact wallPrimitive_tsupport_surface hK ((tsupport_sub _ _).trans (union_subset hr₂ hd))
    · exact tsupport_mul_subset_left.trans hA
  have hQ := wallQuotient_tsupport_surface hK hG
  apply closure_minimal _ (hK.preimage (continuous_fst.comp boxCoordinates.continuous))
  intro x hx
  by_contra hn
  have ha₀ : wallPrimitive r₁ (boxCoordinates x)=0 :=
    image_eq_zero_of_notMem_tsupport (fun hh => hn (hA hh))
  have hq₀ : wallQuotient (wallParticularNumerator (1,0) v r₁ r₂) (boxCoordinates x)=0 :=
    image_eq_zero_of_notMem_tsupport (fun hh => hn (hQ hh))
  apply hx
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [wallParticularTensor,wallMatrix,ha₀,hq₀]

def wallParticularResidual (χ v r₁ r₂ : Box3 → ℝ) (j : Fin 2) (x : Coord3) : ℝ :=
  ![r₁ (boxCoordinates x),r₂ (boxCoordinates x)] j-
    symmetricSource (wallParticularTensor χ v r₁ r₂) (wallCoordinatePair v) j x

lemma wallParticularResidual_off_one {χ v r₁ r₂ : Box3 → ℝ}
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ) (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (h₁ : ContDiff ℝ (↑(⊤ : ℕ∞)) r₁) (h₂ : ContDiff ℝ (↑(⊤ : ℕ∞)) r₂)
    (hz : ∀ q,wallDerivative v (q,0)=0)
    (hne : ∀ p∈tsupport χ,wallQuotient (wallDerivative v) p≠0)
    {x : Coord3} (hx : χ =ᶠ[𝓝 (boxCoordinates x)] (fun _ => 1)) (j : Fin 2) :
    x∉tsupport (wallParticularResidual χ v r₁ r₂ j) := by
  apply notMem_tsupport_iff_eventuallyEq.mpr
  have hp : ∀ᶠ y in 𝓝 x,χ =ᶠ[𝓝 (boxCoordinates y)] (fun _ => 1) :=
    boxCoordinates.continuous.continuousAt.eventually hx.eventually_nhds
  filter_upwards [hp] with y hy
  have he := wallParticularTensor_source_eq hχ hv h₁ h₂ hz hne y hy
  fin_cases j
  · change r₁ (boxCoordinates y)-symmetricSource (wallParticularTensor χ v r₁ r₂) (wallCoordinatePair v) 0 y=0
    rw [he.1,sub_self]
  · change r₂ (boxCoordinates y)-symmetricSource (wallParticularTensor χ v r₁ r₂) (wallCoordinatePair v) 1 y=0
    rw [he.2,sub_self]

theorem exists_uniform_particular_residual_gap {χ : Box3 → ℝ}
    {K : Set (ℝ×ℝ)} {S : Set Box3}
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ) (hsχ : HasCompactSupport χ)
    (hK : IsClosed K) (hS : IsCompact S)
    (hcore : ∀ q∈K,χ =ᶠ[𝓝 (q,0)] (fun _ => 1)) :
    ∃ δ : ℝ,0<δ ∧ ∀ (v r₁ r₂ : Box3 → ℝ),
      ContDiff ℝ (↑(⊤ : ℕ∞)) v → ContDiff ℝ (↑(⊤ : ℕ∞)) r₁ →
      ContDiff ℝ (↑(⊤ : ℕ∞)) r₂ → (∀ q,wallDerivative v (q,0)=0) →
      (∀ p∈tsupport χ,wallQuotient (wallDerivative v) p≠0) →
      tsupport r₁⊆S∩Prod.fst ⁻¹' K → tsupport r₂⊆S∩Prod.fst ⁻¹' K →
      ∀ (j : Fin 2) (x : Coord3),x∈tsupport (wallParticularResidual χ v r₁ r₂ j) →
        δ≤|(boxCoordinates x).2| := by
  let O : Set Box3 := {p | χ =ᶠ[𝓝 p] (fun _ => 1)}
  have ho : IsOpen O := isOpen_iff_mem_nhds.mpr (fun p hp => hp.eventually_nhds)
  let T : Set Box3 := ((S∪tsupport χ)∩Prod.fst ⁻¹' K)∩Oᶜ
  have hT : IsCompact T :=
    ((hS.union hsχ).inter_right (hK.preimage continuous_fst)).inter_right ho.isClosed_compl
  have hn (p : Box3) (hp : p∈T) : p.2≠0 := by
    intro hz
    have he : p=(p.1,0) := Prod.ext rfl hz
    have hon : χ =ᶠ[𝓝 p] (fun _ => 1) := by
      rw [he]
      exact hcore p.1 hp.1.2
    exact hp.2 hon
  obtain ⟨δ,hδ,hlo⟩ := hT.exists_forall_le' continuous_snd.abs.continuousOn
    (fun p hp => abs_pos.mpr (hn p hp))
  refine ⟨δ,hδ,?_⟩
  intro v r₁ r₂ hv h₁ h₂ hz hne hr₁ hr₂ j x hx
  have hr (j : Fin 2) : tsupport (fun x : Coord3 => ![r₁ (boxCoordinates x),r₂ (boxCoordinates x)] j)⊆
      boxCoordinates ⁻¹' (S∩Prod.fst ⁻¹' K) := by
    fin_cases j
    · exact (tsupport_comp_subset_preimage r₁ boxCoordinates.continuous).trans (preimage_mono hr₁)
    · exact (tsupport_comp_subset_preimage r₂ boxCoordinates.continuous).trans (preimage_mono hr₂)
  have hH := (wallParticularTensor_compact hsχ (v:=v) (r₁:=r₁) (r₂:=r₂)).2
  have hHK := wallParticularTensor_tsupport_surface hK
    (hr₁.trans inter_subset_right) (hr₂.trans inter_subset_right) (χ:=χ) (v:=v)
  have hres := tsupport_sub (fun x : Coord3 => ![r₁ (boxCoordinates x),r₂ (boxCoordinates x)] j)
    (symmetricSource (wallParticularTensor χ v r₁ r₂) (wallCoordinatePair v) j) hx
  apply hlo
  refine ⟨?_,?_⟩
  · rcases hres with h | h
    · have h := hr j h
      exact ⟨Or.inl h.1,h.2⟩
    · have h := symmetricSource_tsupport _ _ j h
      exact ⟨Or.inr (hH h),hHK h⟩
  · intro hc
    exact wallParticularResidual_off_one hχ hv h₁ h₂ hz hne hc j hx

end ScalarConductivity



namespace ScalarConductivity
open Set MeasureTheory Matrix Filter Topology

theorem wallParticularResidual_moments {χ v r₁ r₂ : Box3 → ℝ}
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ) (hsχ : HasCompactSupport χ)
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (h₁ : ContDiff ℝ (↑(⊤ : ℕ∞)) r₁) (h₂ : ContDiff ℝ (↑(⊤ : ℕ∞)) r₂)
    (hs₁ : HasCompactSupport r₁) (hs₂ : HasCompactSupport r₂)
    (hne : ∀ p∈tsupport χ,wallQuotient (wallDerivative v) p≠0) :
    let R := wallParticularResidual χ v r₁ r₂
    let u := wallCoordinatePair v
    (∀ j,ContDiff ℝ (↑(⊤ : ℕ∞)) (R j)) ∧
    (∀ j,HasCompactSupport (R j)) ∧
    (∫ x,R 0 x)=(∫ x : Coord3,r₁ (boxCoordinates x)) ∧
    (∫ x,R 1 x)=(∫ x : Coord3,r₂ (boxCoordinates x)) ∧
    (∫ x,u x 1*R 0 x-u x 0*R 1 x)=
      (∫ x : Coord3,u x 1*r₁ (boxCoordinates x)-u x 0*r₂ (boxCoordinates x)) := by
  dsimp only
  let H := wallParticularTensor χ v r₁ r₂
  let u := wallCoordinatePair v
  obtain ⟨hsm,hcmp,_,hm₁,hm₂,hm₃⟩ := wallParticularTensor_weak_moments hχ hsχ hv h₁ h₂ hne
  have hr₁ : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => r₁ (boxCoordinates x)) := h₁.comp boxCoordinates.contDiff
  have hr₂ : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => r₂ (boxCoordinates x)) := h₂.comp boxCoordinates.contDiff
  have hs₁' : HasCompactSupport (fun x => r₁ (boxCoordinates x)) :=
    hs₁.comp_homeomorph boxCoordinates.toHomeomorph
  have hs₂' : HasCompactSupport (fun x => r₂ (boxCoordinates x)) :=
    hs₂.comp_homeomorph boxCoordinates.toHomeomorph
  have hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u := wallCoordinatePair_smooth hv
  have hu₀ := contDiff_pi.mp hu 0
  have hu₁ := contDiff_pi.mp hu 1
  have hI₁ := hr₁.continuous.integrable_of_hasCompactSupport (μ:=volume) hs₁'
  have hI₂ := hr₂.continuous.integrable_of_hasCompactSupport (μ:=volume) hs₂'
  have hS₁ := (hsm 0).continuous.integrable_of_hasCompactSupport (μ:=volume) (hcmp 0)
  have hS₂ := (hsm 1).continuous.integrable_of_hasCompactSupport (μ:=volume) (hcmp 1)
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro j
    fin_cases j
    · exact hr₁.sub (hsm 0)
    · exact hr₂.sub (hsm 1)
  · intro j
    fin_cases j
    · exact hs₁'.sub (hcmp 0)
    · exact hs₂'.sub (hcmp 1)
  · change (∫ x,r₁ (boxCoordinates x)-symmetricSource H u 0 x)=_
    rw [integral_sub hI₁ hS₁,hm₁,sub_zero]
  · change (∫ x,r₂ (boxCoordinates x)-symmetricSource H u 1 x)=_
    rw [integral_sub hI₂ hS₂,hm₂,sub_zero]
  · have hI : Integrable (fun x => u x 1*r₁ (boxCoordinates x)-u x 0*r₂ (boxCoordinates x)) :=
      ((hu₁.mul hr₁).continuous.integrable_of_hasCompactSupport hs₁'.mul_left).sub
        ((hu₀.mul hr₂).continuous.integrable_of_hasCompactSupport hs₂'.mul_left)
    have hS : Integrable (fun x => u x 1*symmetricSource H u 0 x-u x 0*symmetricSource H u 1 x) :=
      ((hu₁.mul (hsm 0)).continuous.integrable_of_hasCompactSupport (hcmp 0).mul_left).sub
        ((hu₀.mul (hsm 1)).continuous.integrable_of_hasCompactSupport (hcmp 1).mul_left)
    have he : (fun x => u x 1*wallParticularResidual χ v r₁ r₂ 0 x-
        u x 0*wallParticularResidual χ v r₁ r₂ 1 x)=
        fun x => (u x 1*r₁ (boxCoordinates x)-u x 0*r₂ (boxCoordinates x))-
          (u x 1*symmetricSource H u 0 x-u x 0*symmetricSource H u 1 x) := by
      funext x
      simp only [wallParticularResidual,Matrix.cons_val_zero,Matrix.cons_val_one]
      ring
    change (∫ x,u x 1*wallParticularResidual χ v r₁ r₂ 0 x-
      u x 0*wallParticularResidual χ v r₁ r₂ 1 x)=_
    rw [he,integral_sub hI hS,hm₃,sub_zero]

end ScalarConductivity

end

end OAI
