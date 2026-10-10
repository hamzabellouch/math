import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.RationalContactMatrix
import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourceHoppingBudget
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.HubbardTolerance

namespace OAI

/-! Polynomial precision suffices for the entire rational contact hopping
matrix. Both the coordinate error and the nonedge tail are paid explicitly. -/

noncomputable section
namespace ContinuumCoulomb.ContactCalibratedGeometry
open ContactMediator MediatorIteration

theorem exists_full_matrix_offsets {a freq : ℝ} (ha : 0 < a) (hfreq : 0 < freq) :
    ∃ qN qC : ℕ, 1 ≤ qN ∧ 1 ≤ qC ∧
      ∀ (N k A S p pc h : ℕ), 2 ≤ N →
      qN+S+p+1 ≤ 5*k → qC+30*k+A+S+p+2 ≤ h → p+2 ≤ pc →
      ∀ (d : SquareLatticeHeisenberg) (W G m : ℕ) (σ : GlobalSite d ≃ Fin (m+1))
        (q : ℚ), 0 < q → (q:ℝ) ≤ (N:ℝ)^S →
      ∀ (ℓ : GlobalEdge d → ℚ), 7200 ≤ N^h →
      (∀ e, (ℓ e:ℝ) ∈ Set.Icc (1-contactLengthTolerance) (1+contactLengthTolerance)) →
      ∀ (D Dfar τ : ℝ), 5 ≤ D → 2 ≤ Dfar →
      35*(k:ℝ)*Real.log N ≤ Dfar → D ≤ (9/10:ℝ)*q → Dfar ≤ (6/5:ℝ)*q →
      2*localLeakageBound freq D ≤ localDualMass freq/2 → 0 ≤ τ → τ ≤ 1 →
      ∀ K : GlobalEdge d → ℝ, (∀ e, 0 ≤ K e) → (∀ e, K e ≤ (N:ℝ)^A) →
      (∀ x y, ‖point d (N^h) q ℓ x-point d (N^h) q ℓ y‖ ≤ 2*(N:ℝ)^S) →
      (∀ e, |(a*((N:ℝ)^k)^30)*planarHopping ((q:ℝ)*ℓ e)-
        coulombHoppingTarget freq τ (K e) ((q:ℝ)*ℓ e)| ≤ 1/((N:ℝ)^pc+1)) →
      ∀ i j : Fin (m+1),
      let F := finalGraph d.bonds W G
      let u := fun x => point d (N^h) q ℓ (σ.symm x)
      ‖(((a*((N:ℝ)^k)^30)*planarHoppingMatrix u i j:ℝ):ℂ)-
        HubbardGlobal.graphHoppingMatrix m (fun e => σ (F.left e)) (fun e => σ (F.right e))
          (fun e => (-(coulombHoppingTarget freq τ (K e)
            ‖u (σ (F.left e))-u (σ (F.right e))‖):ℝ)) i j‖ ≤ ((N:ℝ)^p)⁻¹ := by
  obtain ⟨qN,hqN,hnonedge⟩ := exists_nonedge_hopping_offset ha
  obtain ⟨qC,hqC,hcoordinate⟩ := exists_contact_coordinate_offset ha freq
  refine ⟨qN,qC,hqN,hqC,?_⟩
  intro N k A S p pc h hN hk hh hpc d W G m σ q hq hqS ℓ hP hℓ
    D Dfar τ hD hDfar hfar hDq hfarq hleak hτ hτ1 K hK hKA hdiam hres i j
  have hNR : (2:ℝ) ≤ N := by exact_mod_cast hN
  have hqR : (0:ℝ) ≤ q := by exact_mod_cast hq.le
  have hscale : 0 ≤ a*((N:ℝ)^k)^30 := mul_nonneg ha.le (pow_nonneg (pow_nonneg (Nat.cast_nonneg _) _) _)
  have hbudget (e : GlobalEdge d) := hcoordinate k A S (p+1) h pc (by omega) (by omega)
    N τ (K e) q hNR hτ hτ1 (hK e) (hKA e) hqR hqS
  have hbudget' (e : GlobalEdge d) : 1/((N:ℝ)^pc+1)+
      ((a*((N:ℝ)^k)^30)*(planarHoppingLipschitzConstant:ℝ)+
        coulombTargetLipschitzConstant freq τ (K e))*
        ((q:ℝ)*(72*(((N^h:ℕ):ℝ)+1)⁻¹)) ≤ ((N:ℝ)^(p+1))⁻¹ := by
    simpa only [Nat.cast_pow] using hbudget e
  have hm := full_matrix_error d W G (N^h) m σ hq ℓ hP hℓ hfreq hD hDfar hleak
    hDq hfarq hscale hτ (inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg _) _)) K hK
    hdiam hres hbudget' i j
  have hn := hnonedge S (p+1) k (by omega) N Dfar hNR hfar
  exact hm.trans ((add_le_add hn le_rfl).trans (by
    simpa only [two_mul] using double_inverse_power_le hNR p))

end ContinuumCoulomb.ContactCalibratedGeometry

end

end OAI
