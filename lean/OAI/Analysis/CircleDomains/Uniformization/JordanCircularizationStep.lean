import OAI.Analysis.CircleDomains.Uniformization.PrincipalJordanCircleMap
import OAI.Analysis.CircleDomains.Uniformization.ConformalJordanCapImage
import OAI.Analysis.CircleDomains.Transfer.SourceAnchor

namespace OAI

/-! One exact Koebe circularization step on a finite family of disjoint
Jordan holes. The selected hole becomes round, all other holes are the
actual conformal images, and the entire exterior is carried bijectively
onto the new exterior. -/
open Set Function Metric
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma exists_jordan_circularization_step_full {I : Type*} [Finite I]
    (H : I → ℂ ≃ₜ ℂ)
    (hdisj : Pairwise (Disjoint on fun i => closure (jordanInterior (H i)))) (j : I) :
    ∃ (K : I → ℂ ≃ₜ ℂ) (F : Sphere → Sphere) (c : ℂ) (r : ℝ),
      0<r ∧ IsPrincipalNormalized F ∧
      Pairwise (Disjoint on fun i => closure (jordanInterior (K i))) ∧
      jordanInterior (K j)=ball c r ∧
      (∀ i, i≠j → F '' closedTerminalCap (H i)=closedTerminalCap (K i)) ∧
      IsConformalEquivalence F (closedTerminalCap (H j))ᶜ
        ((((↑) : ℂ → Sphere) '' closedBall c r)ᶜ) ∧
      IsConformalEquivalence F (openCompletedRegion H) (openCompletedRegion K) := by
  classical
  obtain ⟨F,c,r,hr,hnorm,hF⟩ := exists_principal_jordan_circle_map (H j)
  let D := ((↑) : ℂ → Sphere) '' closedBall c r
  have hS : IsOpen (closedTerminalCap (H j))ᶜ :=
    (isCompact_closedTerminalCap (H j)).isClosed.isOpen_compl
  have hinf : ∞ ∈ (closedTerminalCap (H j))ᶜ := by
    rintro ⟨z,_hz,he⟩
    exact OnePoint.coe_ne_infty z he
  have hold := disjoint_closedTerminalCaps H hdisj
  have hinside (i : I) (hi : i≠j) :
      closedTerminalCap (H i) ⊆ (closedTerminalCap (H j))ᶜ := by
    intro p hp hpj
    exact Set.disjoint_left.mp (hold hi) hp hpj
  have himages (i : I) (hi : i≠j) :
      ∃ K : ℂ ≃ₜ ℂ, F '' closedTerminalCap (H i)=closedTerminalCap K :=
    exists_conformal_jordan_cap_image hF.1 hS hF.bijOn.injOn hinf hnorm.1 (H i)
      (hinside i hi)
  let J := roundJordanAt c r hr
  let K : I → ℂ ≃ₜ ℂ := fun i => if hi : i=j then J else (himages i hi).choose
  have hKj : K j=J := by simp [K]
  have hselected : closedTerminalCap (K j)=D := by
    rw [hKj]
    exact congrArg (fun S : Set ℂ => ((↑) : ℂ → Sphere) '' S)
      (roundJordanAt_closure c r hr)
  have hother (i : I) (hi : i≠j) :
      F '' closedTerminalCap (H i)=closedTerminalCap (K i) := by
    simpa only [K,dite_eq_right hi] using (himages i hi).choose_spec
  have hout (i : I) (hi : i≠j) : closedTerminalCap (K i) ⊆ Dᶜ := by
    rw [← hother i hi]
    rintro _ ⟨p,hp,rfl⟩
    exact hF.bijOn.mapsTo (hinside i hi hp)
  have hnew : Pairwise (Disjoint on fun i => closedTerminalCap (K i)) := by
    intro i k hik
    change Disjoint (closedTerminalCap (K i)) (closedTerminalCap (K k))
    by_cases hij : i=j
    · subst i
      rw [hselected]
      exact Set.disjoint_left.mpr (fun p hp hk => hout k hik.symm hk hp)
    by_cases hkj : k=j
    · subst k
      rw [hselected]
      exact Set.disjoint_left.mpr (fun p hp hk => hout i hij hp hk)
    apply Set.disjoint_left.mpr
    intro p hp hk
    rw [← hother i hij] at hp
    rw [← hother k hkj] at hk
    obtain ⟨x,hx,rfl⟩ := hp
    obtain ⟨y,hy,he⟩ := hk
    have hyx : y=x := hF.bijOn.injOn (hinside k hkj hy) (hinside i hij hx) he
    exact Set.disjoint_left.mp (hold hik) hx (hyx ▸ hy)
  have hnewplane : Pairwise (Disjoint on fun i => closure (jordanInterior (K i))) := by
    intro i k hik
    exact Set.disjoint_left.mpr (fun z hz hk =>
      Set.disjoint_left.mp (hnew hik) ⟨z,hz,rfl⟩ ⟨z,hk,rfl⟩)
  have hsource : openCompletedRegion H ⊆ (closedTerminalCap (H j))ᶜ := by
    intro p hp hpj
    exact hp (mem_iUnion.mpr ⟨j,hpj⟩)
  have himage : F '' openCompletedRegion H=openCompletedRegion K := by
    apply Set.Subset.antisymm
    · rintro _ ⟨x,hx,rfl⟩ hy
      obtain ⟨i,hi⟩ := mem_iUnion.mp hy
      by_cases hij : i=j
      · subst i
        rw [hselected] at hi
        exact hF.bijOn.mapsTo (hsource hx) hi
      · rw [← hother i hij] at hi
        obtain ⟨z,hz,he⟩ := hi
        have hzx : z=x := hF.bijOn.injOn (hinside i hij hz) (hsource hx) he
        exact hx (mem_iUnion.mpr ⟨i,hzx ▸ hz⟩)
    · intro y hy
      have hyout : y ∈ Dᶜ := by
        intro hyd
        exact hy (mem_iUnion.mpr ⟨j,hselected.symm ▸ hyd⟩)
      obtain ⟨x,hxS,hxy⟩ := hF.bijOn.surjOn hyout
      refine ⟨x,?_,hxy⟩
      intro hx
      obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      by_cases hij : i=j
      · exact hxS (hij ▸ hi)
      · apply hy
        apply mem_iUnion.mpr
        refine ⟨i,?_⟩
        rw [← hother i hij, ← hxy]
        exact mem_image_of_mem F hi
  refine ⟨K,F,c,r,hr,hnorm,hnewplane,?_,hother,hF,?_⟩
  · rw [hKj]
    exact roundJordanAt_interior c r hr
  · rw [← himage]
    exact isConformalEquivalence_of_injOn (fun p hp => hF.1 p (hsource hp))
      (isOpen_openCompletedRegion H) (hF.bijOn.injOn.mono hsource)

lemma exists_jordan_circularization_step {I : Type*} [Finite I]
    (H : I → ℂ ≃ₜ ℂ)
    (hdisj : Pairwise (Disjoint on fun i => closure (jordanInterior (H i)))) (j : I) :
    ∃ (K : I → ℂ ≃ₜ ℂ) (F : Sphere → Sphere) (c : ℂ) (r : ℝ),
      0<r ∧ IsPrincipalNormalized F ∧
      Pairwise (Disjoint on fun i => closure (jordanInterior (K i))) ∧
      jordanInterior (K j)=ball c r ∧
      (∀ i, i≠j → F '' closedTerminalCap (H i)=closedTerminalCap (K i)) ∧
      IsConformalEquivalence F (openCompletedRegion H) (openCompletedRegion K) := by
  obtain ⟨K,F,c,r,hr,hn,hd,hs,ho,_,hf⟩ :=
    exists_jordan_circularization_step_full H hdisj j
  exact ⟨K,F,c,r,hr,hn,hd,hs,ho,hf⟩

end CircleDomainRigidity

end

end OAI
