import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.SparsePulseCurves
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarPerturbations

namespace OAI

/-! A branch's sparse local pulse curves determine the actual autonomous
material flow, including its complete intervening stationary cells. -/

noncomputable section
namespace ForcedComputation.PlanarRouting
open ShearFlows Set

theorem sparse_suspension {H : FieldExpr} (hH : H.Valid)
    (hP : CubePeriodic 1 (SpatialExpression.spatialValue H))
    {Φ : ℝ → Space → Space}
    (hΦ : IsMaterialFlow 1 (fun y => SpatialExpression.suspensionField H y.2) Φ)
    {m n N : ℕ} (hN : 0 < N) (hn : n ≤ N)
    {J : Fin m → Fin n} (hJ : StrictMono J)
    (p : Fin (m + 1) → Plane) (γ : Fin m → ℝ → Plane) (cuts : ℕ → ℝ)
    (hzero : cuts 0 = 0) (hone : cuts N = 1)
    (hcuts : ∀ i < N, cuts i ≤ cuts (i + 1))
    (hstart : ∀ k, γ k (cuts (J k).val) = p k.castSucc)
    (hfinish : ∀ k, γ k (cuts ((J k).val + 1)) = p k.succ)
    (hc : ∀ k, ContinuousOn (γ k) (Icc (cuts (J k).val) (cuts ((J k).val + 1))))
    (hd : ∀ k s, s ∈ Ico (cuts (J k).val) (cuts ((J k).val + 1)) →
      HasDerivAt (γ k) (planarSlice H s (γ k s)) s)
    (hz : ∀ i < N, (∀ k, (J k).val ≠ i) →
      ∀ s ∈ Ico (cuts i) (cuts (i + 1)), planarSlice H s (sparseAnchor J p i) = 0)
    {S : Set Plane} (hS : S ⊆ clockRectangle.carrier) (hp : ∀ k, p k ∈ S)
    (hmem : ∀ k s, s ∈ Icc (cuts (J k).val) (cuts ((J k).val + 1)) → γ k s ∈ S) :
    Φ 1 (atHeight (p 0) 0) = atHeight (p (Fin.last m)) 1 ∧
      ∀ s ∈ Icc (0 : ℝ) 1, horizontal (Φ s (atHeight (p 0) 0)) ∈ S := by
  have hcurve (i : ℕ) (s : ℝ) (hs : s ∈ Icc (cuts i) (cuts (i + 1))) :
      sparseCurve J p γ i s ∈ S := sparseCurve_mem hJ p γ cuts hp hmem i s hs
  have h := suspension_chain hH hP hΦ (N := N) (cuts := cuts)
    (γ := sparseCurve J p γ) (p := sparseAnchor J p) (x := atHeight (p 0) 0) hzero
    (by rw [sparseAnchor_zero]) hcuts
    (fun i _ => (sparseCurve_endpoints hJ p γ cuts hstart hfinish i).1)
    (fun i _ => (sparseCurve_endpoints hJ p γ cuts hstart hfinish i).2)
    (fun i _ => sparseCurve_continuousOn hJ p γ cuts hc i)
    (fun i hi s hs => sparseCurve_ode hJ p γ cuts (planarSlice H) hd i s hs
      (fun hne => hz i hi hne s hs))
    (fun i _ s hs => unitSpatialClock_one (hS (hcurve i s ⟨hs.1, hs.2.le⟩)))
  constructor
  · have he := h.1 N le_rfl
    rw [hone, sparseAnchor_after_last J p hn] at he
    exact he
  · exact suspension_chain_mem hN hzero hone hcuts h.2 (fun i _ s hs => hcurve i s hs)

end ForcedComputation.PlanarRouting

end

end OAI
