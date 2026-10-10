import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CalibratedMatrixError
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.MediatorSimple

namespace OAI

/-! The rational contact coordinates control the complete physical hopping
matrix in the electron index order, including every nonedge entry. -/

noncomputable section
namespace ContinuumCoulomb.ContactCalibratedGeometry
open ContactMediator MediatorIteration

theorem full_matrix_error (d : SquareLatticeHeisenberg) (W G P m : ℕ)
    (σ : GlobalSite d ≃ Fin (m+1)) {q : ℚ} (hq : 0 < q)
    (ℓ : GlobalEdge d → ℚ) (hP : 7200 ≤ P)
    (hℓ : ∀ a, (ℓ a : ℝ) ∈ Set.Icc (1-contactLengthTolerance) (1+contactLengthTolerance))
    {freq D Dfar scale τ L ε₀ ε : ℝ}
    (hfreq : 0 < freq) (hD : 5 ≤ D) (hDfar : 2 ≤ Dfar)
    (hleak : 2*localLeakageBound freq D ≤ localDualMass freq/2)
    (hDq : D ≤ (9/10:ℝ)*q) (hfarq : Dfar ≤ (6/5:ℝ)*q)
    (hscale : 0 ≤ scale) (hτ : 0 ≤ τ) (hε : 0 ≤ ε)
    (K : GlobalEdge d → ℝ) (hK : ∀ a, 0 ≤ K a)
    (hL : ∀ x y, ‖point d P q ℓ x-point d P q ℓ y‖ ≤ L)
    (hres : ∀ a, |scale*planarHopping ((q:ℝ)*ℓ a)-
      coulombHoppingTarget freq τ (K a) ((q:ℝ)*ℓ a)| ≤ ε₀)
    (hbudget : ∀ a, ε₀+(scale*(planarHoppingLipschitzConstant:ℝ)+
      coulombTargetLipschitzConstant freq τ (K a))*((q:ℝ)*(72*((P:ℝ)+1)⁻¹)) ≤ ε)
    (i j : Fin (m+1)) :
    let F := finalGraph d.bonds W G
    let u := fun x => point d P q ℓ (σ.symm x)
    ‖((scale*planarHoppingMatrix u i j:ℝ):ℂ)-
      HubbardGlobal.graphHoppingMatrix m (fun a => σ (F.left a)) (fun a => σ (F.right a))
        (fun a => (-(coulombHoppingTarget freq τ (K a)
          ‖u (σ (F.left a))-u (σ (F.right a))‖):ℝ)) i j‖ ≤
      scale*planarHoppingUpperConstant*(L+1)*Real.exp (-Dfar)+ε := by
  intro F u
  have hloop (a : GlobalEdge d) : σ (F.left a) ≠ σ (F.right a) :=
    fun he => finalGraph_noLoops d.bonds W G a (σ.injective he)
  have hsimple : ∀ a b : GlobalEdge d, a ≠ b →
      ¬(σ (F.left a)=σ (F.left b) ∧ σ (F.right a)=σ (F.right b)) ∧
      ¬(σ (F.left a)=σ (F.right b) ∧ σ (F.right a)=σ (F.left b)) := by
    intro a b hab
    have hs := (finalGraph_simple d.bonds W G).hypothesis a b hab
    exact ⟨fun h => hs.1 ⟨σ.injective h.1,σ.injective h.2⟩,
      fun h => hs.2 ⟨σ.injective h.1,σ.injective h.2⟩⟩
  apply HubbardGlobal.planarHoppingMatrix_calibrated_error m
    (fun a => σ (F.left a)) (fun a => σ (F.right a)) u hloop hsimple hscale hDfar hε
    (fun x y => hL _ _) ?_ _ ?_ i j
  · intro x y hxy hn
    have hraw : σ.symm x ≠ σ.symm y := fun h => hxy (σ.symm.injective h)
    have hnon : Nonedge d W G (σ.symm x) (σ.symm y) := by
      rintro ⟨a,ha⟩
      rcases ha with ⟨hax,hay⟩ | ⟨hay,hax⟩
      · exact (hn a).1 ⟨(σ.apply_symm_apply x).symm.trans (congrArg σ hax).symm,
          (σ.apply_symm_apply y).symm.trans (congrArg σ hay).symm⟩
      · exact (hn a).2 ⟨(σ.apply_symm_apply x).symm.trans (congrArg σ hax).symm,
          (σ.apply_symm_apply y).symm.trans (congrArg σ hay).symm⟩
    exact hfarq.trans (by simpa only [u,dist_eq_norm] using
      (nonedge_separation d W G P hq ℓ hP hℓ _ _ hraw hnon).le)
  · intro a
    have hr := calibrated_edge_residual d W G P hq ℓ hP hℓ hfreq hD hleak hDq
      hscale hτ K hK hres a (finalGraph_noLoops d.bonds W G a)
    simpa only [u,Equiv.symm_apply_apply,dist_eq_norm] using hr.trans (hbudget a)

end ContinuumCoulomb.ContactCalibratedGeometry

end

end OAI
