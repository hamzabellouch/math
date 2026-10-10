import OAI.MeasureTheory.Falconer.Estimates.RoundedEndpointGain
import OAI.MeasureTheory.Falconer.Recursion.ProfileGainParameters
import OAI.MeasureTheory.Falconer.Recursion.ProfileScaleSelection

namespace OAI

/-! Uniform gain for the actual regularized planar profile, assuming only its
finite branching-count lower growth. All decomposition and recursion parameters
are chosen before the configuration and the depth. -/
namespace Falconer
open Set Regularization

theorem uniform_profile_endpoint_gain {κ s t : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1/100)
    (hs : κ ≤ s) (hs1 : s ≤ 1-8*κ) (ht : s+8*κ ≤ t) :
    ∃ B : ℕ, 0 < B ∧ Even B ∧ ∃ lam ζ : ℝ, 0 < lam ∧ 0 < ζ ∧
    ∃ M : ℕ, 0 < M ∧ ∀ m : ℕ, M ≤ m →
    ∀ L : Finset (CellPath 2), L ⊆ cubePaths 2 (m*B) →
    (2:ℝ)^(3*(m+1))*((2*B+1:ℕ):ℝ)^(m+1) ≤ (2:ℝ)^((lam/4)*(m*B:ℕ)) ∧
    ∀ (f : CellPath 2 → List ℕ) (p : CellPath 2) (Q : DyadicCube 2), Q.side = 1 →
      (∀ i ≤ m+1,
        (blockProduct L (blockLabel L (m*B) B f (m+1)) (m*B) B i p:ℝ)/
          (blockProduct L (blockLabel L (m*B) B f (m+1)) (m*B) B (m+1) p:ℝ) ≤
        (2:ℝ)^(lam*(m*B:ℕ)-t*(blockDepth (m*B) B i:ℝ))) →
      ProfileEndpointBound (m*B) B (m+1) L f p Q m 0 s ((2:ℝ)^(lam*(m*B:ℕ)))
        ((2:ℝ)^((s+ζ)*(m*B:ℕ))) := by
  obtain ⟨eg,η,Ng,heg,heg1,hη,hNg,hendpoint⟩ := rounded_profile_endpoint_gain hκ hκ1
  obtain ⟨α,hα,hακ,hαη,hαe⟩ := exists_profile_gain_accuracy hκ hη heg
  have hα1 : α ≤ 1 := by linarith
  obtain ⟨τ,hτ,hselect⟩ := planar_profile_scale_selection hα hα1
  let J := Nat.ceil (1/τ)
  obtain ⟨β,hβ,hβα,hβη,hβe⟩ := exists_profile_gain_budget hα hκ hη heg hτ J
  obtain ⟨B,hB,hBeven,lam,hlam,N0,hN0,hbudget⟩ := exists_profile_application_budget hβ J
  obtain ⟨M,hM,hgrid⟩ := exists_incidence_profile_grid_threshold hα hτ hκ Ng N0
  refine ⟨B,hB,hBeven,lam,η*κ/2,hlam,by positivity,M,hM,?_⟩
  intro m hm L hL
  have hm0 : 0 < m := hM.trans_le hm
  have hNmin := (hgrid m hm B hB).1
  have hentry := (hbudget m hm0 hNmin).2.2.2.2
  rw [Nat.mul_comm B m] at hentry
  refine ⟨hentry,?_⟩
  intro f p Q hQ hcounts
  let N := m*B
  let K := m+1
  let F := blockLabel L N B f K
  let g := fun x => regularizedProfile L F N B K p ((N:ℝ)*x)
  let H : ℝ := (4*(N+2)+11:ℕ)
  let G := (2:ℝ)^(3*K)*((2*B+1:ℕ):ℝ)^K
  let W := profileBudgetSequence H G ((2:ℝ)^(lam*(N:ℝ)))
  have hN : 0 < N := Nat.mul_pos hm0 hB
  have hNR : (0:ℝ) < N := Nat.cast_pos.mpr hN
  obtain ⟨hNmin,hmesh,herror,hslack,hround,hlarge⟩ := hgrid m hm B hB
  have hb := hbudget m hm0 hNmin
  dsimp only at hb
  rw [Nat.mul_comm B m] at hb
  change (∀ j ≤ 2*J+1, W j ≤ (2:ℝ)^(β*(N:ℝ))) ∧
    (∀ j ≤ 2*J, ∀ A : ℝ, profileGeometryConstant K B (W j) A ≤ (2:ℝ)^((4*β)*(N:ℝ)+A)) ∧
    640*((N:ℝ)+3) ≤ (2:ℝ)^(β*(N:ℝ)) ∧ (43264*H^4)^(2*J) ≤ (2:ℝ)^(β*(N:ℝ)) ∧
    G ≤ (2:ℝ)^((lam/4)*(N:ℝ)) at hb
  have hlamβ : lam ≤ β := by
    have hh := (Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ) < 2)).mp (hb.1 0 (by omega))
    change lam*(N:ℝ) ≤ β*(N:ℝ) at hh
    exact (mul_le_mul_iff_left₀ hNR).mp hh
  have hK : N/B+1 = K := by dsimp [N,K]; rw [Nat.mul_div_cancel m hB]
  have hcounts' : ∀ i ≤ N/B+1,
      (blockProduct L F N B i p:ℝ)/(blockProduct L F N B (N/B+1) p:ℝ) ≤
        (2:ℝ)^(lam*(N:ℝ)-t*(blockDepth N B i:ℝ)) := by
    rw [hK]
    exact hcounts
  obtain ⟨S,hS,hcover⟩ := hselect N hN L hL F B hB p lam (s+κ) t hlam.le (by linarith) hcounts'
  rw [hK] at hS
  change StructuredProfilePieces g τ (2*α) (s+κ) 1 S at hS
  let χ := α^2+α+lam/(t-(s+κ))
  have hcover' : 1-χ ≤ (S.map Prod.snd).sum := by
    dsimp [χ]
    linarith only [hcover]
  have hgrowth : t-lam ≤ g 1 := by
    have hh := regularizedProfile_lower_from_ratios hN hL F hB p hcounts'
      (x := 1) (show (1:ℝ) ∈ Icc 0 1 by simp)
    rw [hK] at hh
    simpa only [g,mul_one,mul_div_cancel_right₀ lam hNR.ne'] using hh
  have hcount : S.length ≤ J := by
    have hh := ordered_interval_count_bound (by norm_num : (0:ℝ) ≤ 1) hS.ordered
      (fun c hc => ⟨(hS.bounds c hc).1,(hS.bounds c hc).2.1,hτ.le.trans (hS.bounds c hc).2.2⟩)
      (fun c hc => (hS.bounds c hc).2.2)
    have hh' : (S.length:ℝ) ≤ 1/τ := by
      apply (le_div_iff₀ hτ).2
      simpa only [sub_zero,mul_comm] using hh
    exact Nat.cast_le.mp (hh'.trans (Nat.le_ceil _))
  have hround' : (2/(m:ℝ))*(S.length:ℝ) ≤ α := by
    have hcountR : (S.length:ℝ) ≤ 1/τ := by
      have hh := ordered_interval_count_bound (by norm_num : (0:ℝ) ≤ 1) hS.ordered
        (fun c hc => ⟨(hS.bounds c hc).1,(hS.bounds c hc).2.1,hτ.le.trans (hS.bounds c hc).2.2⟩)
        (fun c hc => (hS.bounds c hc).2.2)
      apply (le_div_iff₀ hτ).2
      simpa only [sub_zero,mul_comm] using hh
    calc
      _ ≤ (2/(m:ℝ))*(1/τ) := mul_le_mul_of_nonneg_left hcountR (by positivity)
      _ = 2/((m:ℝ)*τ) := by ring
      _ ≤ α := hround
  obtain ⟨hweak,hgain⟩ := profile_gain_parameters_close hκ hκ1 hα hακ hαη
    hβα hβη hlam.le hlamβ (show s ≤ 1 by linarith) ht
  exact hendpoint m B hm0 hB hBeven L hL f p Q hQ s t (2*α) τ β lam χ α (η*κ/2)
    hs hs1 (by positivity) hτ hβ hlam J S hS hgrowth hcover' ht hweak hmesh
    (by convert herror using 1; ring) hslack hround' (by linarith) hcount hlarge hβe
    (by nlinarith only [hαe]) (by convert hgain using 1; ring)
    ⟨hb.2.1,hb.2.2.1,hb.2.2.2.1⟩

end Falconer

end OAI
