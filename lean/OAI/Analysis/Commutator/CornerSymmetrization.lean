import Mathlib
import OAI.Analysis.Commutator.StageAverage

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace Topology

open ContinuousLinearMap MeasureTheory MeasureTheory.Measure

namespace Kadison.CornerSymmetrization

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def vectorState (Ω : H) (a : H →L[ℂ] H) : ℂ := inner ℂ Ω (a Ω)

def CornerElement (D P : StarSubalgebra ℂ (H →L[ℂ] H)) (Ω : H) (t : ℂ)
    (x : H →L[ℂ] H) : Prop :=
  x∈P ∧ ∃ e : H →L[ℂ] H, e∈D ∧ IsStarProjection e ∧ vectorState Ω e=t ∧ e*x=x ∧ x*e=x

lemma vectorState_conj (U : H ≃ₗᵢ[ℂ] H) (Ω : H) (hΩ : U Ω=Ω) (a : H →L[ℂ] H) :
    vectorState Ω (U.conjStarAlgEquiv a)=vectorState Ω a := by
  have hi : U.symm Ω=Ω := by
    apply U.injective
    rw [LinearIsometryEquiv.apply_symm_apply,hΩ]
  change inner ℂ Ω (U (a (U.symm Ω)))=inner ℂ Ω (a Ω)
  rw [hi]
  calc
    inner ℂ Ω (U (a Ω)) = inner ℂ (U Ω) (U (a Ω)) := by rw [hΩ]
    _ = inner ℂ Ω (a Ω) := U.inner_map_map Ω (a Ω)

lemma cornerElement_map (D P : StarSubalgebra ℂ (H →L[ℂ] H)) (Ω : H) (t : ℂ)
    (U : H ≃ₗᵢ[ℂ] H) (hΩ : U Ω=Ω)
    (hD : ∀ a∈D, U.conjStarAlgEquiv a∈D) (hP : ∀ a∈P, U.conjStarAlgEquiv a∈P)
    {x : H →L[ℂ] H} (hx : CornerElement D P Ω t x) :
    CornerElement D P Ω t (U.conjStarAlgEquiv x) := by
  obtain ⟨hx,e,he,hp,ht,hel,her⟩ := hx
  refine ⟨hP x hx,U.conjStarAlgEquiv e,hD e he,?_,?_,?_,?_⟩
  · exact hp.map U.conjStarAlgEquiv
  · rw [vectorState_conj U Ω hΩ,ht]
  · simpa only [map_mul] using congrArg U.conjStarAlgEquiv hel
  · simpa only [map_mul] using congrArg U.conjStarAlgEquiv her

lemma commutator_conj_norm (α : (H →L[ℂ] H) ≃⋆ₐ[ℂ] (H →L[ℂ] H))
    (G a : H →L[ℂ] H) :
    ‖α G*a-a*α G‖=‖G*α.symm a-α.symm a*G‖ := by
  calc
    _ = ‖α (G*α.symm a-α.symm a*G)‖ := by
      simp only [map_sub,map_mul,StarAlgEquiv.apply_symm_apply]
    _ = _ := StarAlgEquiv.norm_map α _

lemma commutator_adjoint_norm (G a : H →L[ℂ] H) :
    ‖G.adjoint*a-a*G.adjoint‖=‖G*star a-star a*G‖ := by
  have h : G.adjoint*a-a*G.adjoint = -star (G*star a-star a*G) := by
    simp only [star_sub,star_mul,star_star,neg_sub]
    rfl
  rw [h,norm_neg,norm_star]

lemma cornerElement_star (D P : StarSubalgebra ℂ (H →L[ℂ] H)) (Ω : H) (t : ℂ)
    {x : H →L[ℂ] H} (hx : CornerElement D P Ω t x) :
    CornerElement D P Ω t (star x) := by
  obtain ⟨hx,e,he,hp,ht,hel,her⟩ := hx
  refine ⟨star_mem hx,e,he,hp,ht,?_,?_⟩
  · simpa only [star_mul,hp.isSelfAdjoint.star_eq] using congrArg star her
  · simpa only [star_mul,hp.isSelfAdjoint.star_eq] using congrArg star hel

lemma fixed_projection_right (U : H ≃ₗᵢ[ℂ] H) (Q : H →L[ℂ] H)
    (hQ : IsSelfAdjoint Q) (hU : (U:H →L[ℂ] H)*Q=Q) :
    Q*(U:H →L[ℂ] H)=Q := by
  have h := congrArg star hU
  simp only [star_mul,hQ.star_eq] at h
  have hu : star (U:H →L[ℂ] H)*(U:H →L[ℂ] H)=1 := by
    rw [LinearIsometryEquiv.star_eq_symm]
    ext x
    change U.symm (U x)=x
    exact U.symm_apply_apply x
  have h' := congrArg (fun a : H →L[ℂ] H => a*(U:H →L[ℂ] H)) h
  rw [mul_assoc,hu,mul_one] at h'
  exact h'.symm

lemma fixed_compressed_conjugate (U : H ≃ₗᵢ[ℂ] H) (Q s G : H →L[ℂ] H)
    (hQ : IsSelfAdjoint Q) (hU : (U:H →L[ℂ] H)*Q=Q)
    (hs : (U:H →L[ℂ] H)*s=s*(U:H →L[ℂ] H)) :
    Q*(U.conjStarAlgEquiv G*s-s*U.conjStarAlgEquiv G)*Q=Q*(G*s-s*G)*Q := by
  let u : H →L[ℂ] H := U
  let v : H →L[ℂ] H := U.symm
  have huv : u*v=1 := by ext x; exact U.apply_symm_apply x
  have hvu : v*u=1 := by ext x; exact U.symm_apply_apply x
  have hQu : Q*u=Q := fixed_projection_right U Q hQ hU
  have hvQ : v*Q=Q := by
    have h := congrArg (fun a => v*a) hU
    change v*(u*Q)=v*Q at h
    rw [←mul_assoc,hvu,one_mul] at h
    exact h.symm
  have hvs : v*s=s*v := by
    have h := congrArg (fun a => v*a*v) hs
    change v*(u*s)*v=v*(s*u)*v at h
    have hss : v*(u*s)*v=s*v := by rw [←mul_assoc v u s,hvu,one_mul]
    have htt : v*(s*u)*v=v*s := by
      calc
        _ = (v*s)*(u*v) := by noncomm_ring
        _ = v*s := by rw [huv,mul_one]
    rw [hss,htt] at h
    exact h.symm
  change Q*(u*G*v*s-s*(u*G*v))*Q=Q*(G*s-s*G)*Q
  simp only [mul_sub,sub_mul]
  congr 1
  · calc
      Q*(u*G*v*s)*Q = Q*u*G*(v*s)*Q := by noncomm_ring
      _ = Q*G*(s*v)*Q := by rw [hQu,hvs]
      _ = Q*G*s*(v*Q) := by noncomm_ring
      _ = Q*(G*s)*Q := by rw [hvQ]; noncomm_ring
  · calc
      Q*(s*(u*G*v))*Q=Q*(s*u)*G*(v*Q) := by noncomm_ring
      _ = Q*(u*s)*G*Q := by rw [←hs,hvQ]
      _ = Q*(s*G)*Q := by rw [←mul_assoc,hQu]; noncomm_ring

lemma conj_symm (U : H ≃ₗᵢ[ℂ] H) : U.symm.conjStarAlgEquiv=U.conjStarAlgEquiv.symm := by
  apply StarAlgEquiv.ext
  intro a
  apply U.conjStarAlgEquiv.injective
  change U.conjStarAlgEquiv (U.symm.conjStarAlgEquiv a)=U.conjStarAlgEquiv (U.conjStarAlgEquiv.symm a)
  rw [StarAlgEquiv.apply_symm_apply]
  ext x
  change U (U.symm (a (U (U.symm x))))=a x
  simp only [LinearIsometryEquiv.apply_symm_apply]

variable (Γ : ℕ → Type*) [∀ n, Group (Γ n)] [∀ n, TopologicalSpace (Γ n)]
  [∀ n, IsTopologicalGroup (Γ n)] [∀ n, CompactSpace (Γ n)]
  [∀ n, MeasurableSpace (Γ n)] [∀ n, BorelSpace (Γ n)]

variable (U : ∀ n, Γ n →* (H ≃ₗᵢ[ℂ] H))
  (hU : ∀ n x, Continuous fun g => U n g x)
  (hnest : ∀ i j, i≤j → ∀ g : Γ i, ∃ k : Γ j, U j k=U i g)

variable (μ : ∀ n, Measure (Γ n)) [∀ n, IsProbabilityMeasure (μ n)] [∀ n, IsMulLeftInvariant (μ n)]

variable (D P : StarSubalgebra ℂ (H →L[ℂ] H)) (Ω : H) (t : ℂ)
  (hΩ : ∀ n g, U n g Ω=Ω)
  (hD : ∀ n g a, a∈D → (U n g).conjStarAlgEquiv a∈D)
  (hP : ∀ n g a, a∈P → (U n g).conjStarAlgEquiv a∈P)

variable (G : H →L[ℂ] H) (ε : ℝ) (hε : 0≤ε)
  (hGD : ∀ a∈D, G*a=a*G)
  (hC : ∀ x, CornerElement D P Ω t x → ‖G*x-x*G‖≤ε*‖x‖)

variable (Q s : H →L[ℂ] H) (hQ : IsSelfAdjoint Q)
  (hUQ : ∀ n g, (U n g:H →L[ℂ] H)*Q=Q)
  (hUs : ∀ n g, (U n g:H →L[ℂ] H)*s=s*(U n g:H →L[ℂ] H))

include hU hnest μ hΩ hD hP hε hGD hC hQ hUQ hUs in
theorem exists_symmetrization : ∃ V : H →L[ℂ] H,
    ‖V‖≤‖G‖ ∧ (∀ n g, V*(U n g:H →L[ℂ] H)=(U n g:H →L[ℂ] H)*V) ∧
    (∀ a∈D, V*a=a*V) ∧
    (∀ x, CornerElement D P Ω t x → ‖V*x-x*V‖≤ε*‖x‖) ∧
    (∀ x, CornerElement D P Ω t x → ‖V.adjoint*x-x*V.adjoint‖≤ε*‖x‖) ∧
    Q*(V*s-s*V)*Q=Q*(G*s-s*G)*Q := by
  let ι := Sum {a : H →L[ℂ] H // a∈D} {x : H →L[ℂ] H // CornerElement D P Ω t x}
  let a : ι → H →L[ℂ] H := Sum.elim Subtype.val Subtype.val
  let C : ι → ℝ := Sum.elim (fun _ => 0) (fun x => ε*‖x.val‖)
  have hC₀ : ∀ i, 0≤C i := by
    intro i
    cases i with
    | inl x => exact le_rfl
    | inr x => exact mul_nonneg hε (norm_nonneg _)
  have hstar (n : ℕ) (g : Γ n) : (U n g).conjStarAlgEquiv.symm=(U n g⁻¹).conjStarAlgEquiv := by
    rw [map_inv,LinearIsometryEquiv.inv_def,conj_symm]
  have hb : ∀ n g i, ‖CompactAverage.conjugate (U n) G g*a i-a i*CompactAverage.conjugate (U n) G g‖≤C i := by
    intro n g i
    change ‖(U n g).conjStarAlgEquiv G*a i-a i*(U n g).conjStarAlgEquiv G‖≤C i
    rw [commutator_conj_norm,hstar]
    cases i with
    | inl x =>
      change ‖G*(U n g⁻¹).conjStarAlgEquiv x.val-(U n g⁻¹).conjStarAlgEquiv x.val*G‖≤0
      rw [hGD _ (hD n g⁻¹ x.val x.property),sub_self,norm_zero]
    | inr x =>
      change ‖G*(U n g⁻¹).conjStarAlgEquiv x.val-(U n g⁻¹).conjStarAlgEquiv x.val*G‖≤ε*‖x.val‖
      simpa only [StarAlgEquiv.norm_map] using hC _
        (cornerElement_map D P Ω t (U n g⁻¹) (hΩ n g⁻¹) (hD n g⁻¹) (hP n g⁻¹) x.property)
  obtain ⟨V,hV,hVU,hVC,hVQ⟩ := CompactAverage.exists_stage_average Γ U hU hnest μ G a C hC₀ hb Q Q s
    (fun n g => fixed_compressed_conjugate (U n g) Q s G hQ (hUQ n g) (hUs n g))
  have hVC' : ∀ x, CornerElement D P Ω t x → ‖V*x-x*V‖≤ε*‖x‖ := by
    intro x hx
    exact hVC (Sum.inr ⟨x,hx⟩)
  refine ⟨V,hV,hVU,?_,hVC',?_,hVQ⟩
  · intro x hx
    have h := hVC (Sum.inl ⟨x,hx⟩)
    change ‖V*x-x*V‖≤0 at h
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))
  · intro x hx
    rw [commutator_adjoint_norm]
    simpa only [norm_star] using hVC' (star x) (cornerElement_star D P Ω t hx)

end Kadison.CornerSymmetrization

end

end
end

end OAI
