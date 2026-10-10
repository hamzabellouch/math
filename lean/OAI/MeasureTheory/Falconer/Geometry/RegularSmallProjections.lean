import OAI.MeasureTheory.Falconer.Graphs.PlanarGraphBudgetApplication
import OAI.MeasureTheory.Falconer.Estimates.PlanarWeakParameters
import OAI.MeasureTheory.Falconer.Geometry.CommonProjectionLosses

namespace OAI

/-! Strict small-projection obstruction for an actual regular planar set
and a nonconcentrated family of directions, with all weak losses chosen. -/
namespace Falconer

private theorem base_radius_identity (l : ℕ) :
    4/(2:ℝ)^(l+2) = (1/2:ℝ)^l := by
  rw [pow_add]
  norm_num
  rw [div_pow,one_pow]
  field_simp

 theorem regular_small_projection_obstruction {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ ε : ℝ, ∃ n0 : ℕ, 0 < ε ∧ 0 < n0 ∧ ∀ n : ℕ, n0 ≤ n →
      let δ := (1/2:ℝ)^n
      let W := Real.exp (ε*(n:ℝ)*Real.log 2)
      ∀ (t : ℝ) (I : Finset ℝ) (U : Finset (Space 2))
        (A : ℝ → Finset (Space 2)) (P : ℕ),
      2*κ ≤ t → t ≤ 2 → I.Nonempty → U.Nonempty → 0 < P →
      (∀ i ∈ I, |i| ≤ 1) → (∀ p ∈ U, ∀ i, |p i| ≤ 1) →
      FiniteSeparatedAt δ U → NormalizedFiniteBallBound δ t W U →
      (P:ℝ)^2 ≤ W*(U.card:ℝ) →
      (∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass I u r ≤ W*r^(2*κ)*(I.card:ℝ)) →
      (∀ i ∈ I, A i ⊆ U ∧ W⁻¹*(U.card:ℝ) ≤ ((A i).card:ℝ) ∧
        (projectionCells δ i (A i)).card ≤ P) →
      Real.log (P:ℝ) ≤ (1-4*κ)*(n:ℝ)*Real.log 2 → False := by
  obtain ⟨γ,Nmin,hγ,_,hmain⟩ := planar_graph_budget_application hκ hκ1
  obtain ⟨ε,n0,hε,hn0,hparameters⟩ := planar_weak_parameters hγ hκ hκ1 Nmin
  refine ⟨ε,n0,hε,hn0,?_⟩
  intro n hn
  dsimp only
  intro t I U A P ht ht2 hI hU hP hIbound hUbound hUsep hUreg hlarge hIball hA hPlog
  let δ := (1/2:ℝ)^n
  let W := Real.exp (ε*(n:ℝ)*Real.log 2)
  let ρ := W⁻¹
  let Z := 64*W^6
  have hδ : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  obtain ⟨l,_,hN,hW,_,hr,hr1,hδr,hselect,hbudget,hlog⟩ := hparameters n hn
  let r := (1/2:ℝ)^l
  let M : ℕ := 2^(l+2)
  let N := n+2*l+10
  obtain ⟨hρ,hρ1,hZ,hWZ,hKZ,hAZ,hρnew,hρnewZ⟩ := common_projection_losses hW
  have hballSelect : ∀ z : ℝ, scalarBallMass I z r ≤ (ρ^6/128)*(I.card:ℝ) := by
    intro z
    have hh := mul_le_mul_of_nonneg_right hselect (Nat.cast_nonneg I.card)
    exact (hIball z r hδr hr1).trans (by simpa only [mul_assoc,r,ρ,W] using hh)
  obtain ⟨a,ha,b,hb,hab,hba,J,hJI,hJ,hJsize,hV,hVU,hUV,hVreg,hpa,hpb,htriple⟩ :=
    common_projection_configuration hδ.le (zero_le_one.trans hW) hρ hρ1 hr I U A hI hU
      (fun i hi => (hA i hi).1) (fun i hi => (hA i hi).2.1) hballSelect hUreg P
      (fun i hi => (hA i hi).2.2)
  let V := A a ∩ A b
  have hVregular : NormalizedFiniteBallBound δ t Z V := by
    intro z s hs hs1
    have hh := mul_le_mul_of_nonneg_right hKZ
      (mul_nonneg (Real.rpow_nonneg (hδ.le.trans hs) t) (Nat.cast_nonneg V.card))
    exact (hVreg z s hs hs1).trans (by simpa only [mul_assoc,V,Z,ρ,W] using hh)
  have hVlarge : (P:ℝ)^2 ≤ Z*(V.card:ℝ) := by
    calc
      _ ≤ W*(U.card:ℝ) := hlarge
      _ ≤ W*((8/ρ^4)*(V.card:ℝ)) := mul_le_mul_of_nonneg_left hUV (zero_le_one.trans hW)
      _ = (W*(8/ρ^4))*(V.card:ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hKZ (Nat.cast_nonneg V.card)
  have hIJ : (I.card:ℝ) ≤ Z*(J.card:ℝ) := by
    have hh := common_projection_direction_count hρ I J hJsize
    rwa [hAZ] at hh
  have hIballZ : ∀ u s : ℝ, δ ≤ s → s ≤ 1 → scalarBallMass I u s ≤ Z*s^(2*κ)*(I.card:ℝ) := by
    intro u s hs hs1
    have hh := mul_le_mul_of_nonneg_right hWZ
      (mul_nonneg (Real.rpow_nonneg (hδ.le.trans hs) (2*κ)) (Nat.cast_nonneg I.card))
    exact (hIball u s hs hs1).trans (by simpa only [mul_assoc,Z,W] using hh)
  have hM : 1 ≤ M := one_le_pow₀ (by norm_num)
  have hMr : 4/(M:ℝ) = r := by
    simpa only [M,Nat.cast_pow,Nat.cast_ofNat,r] using base_radius_identity l
  have hcompat : (1/2:ℝ)^N = δ/(64*(M:ℝ)^2) := by
    simpa only [N,δ,M,Nat.cast_pow,Nat.cast_ofNat] using (planar_analysis_dyadic n l).symm
  have hbudget' : 4000000*Z^5*(M:ℝ)^6 ≤ Real.exp (γ*(N:ℝ)*Real.log 2) := by
    simpa only [Z,M,N,Nat.cast_pow,Nat.cast_ofNat] using hbudget
  have hlog' : Real.log (655*(M:ℝ)*(P:ℝ)) ≤ (1-κ)*(N:ℝ)*Real.log 2 := by
    simpa only [M,N,Nat.cast_pow,Nat.cast_ofNat] using hlog (P:ℝ) (Nat.cast_pos.mpr hP) hPlog
  apply hmain N hN δ Z (ρ^4/8) a b t M P I J V (fun j => V ∩ A j)
    hδ hδ1 hZ hρnew hρnewZ hM hcompat hbudget' hba (hIbound a ha) (hIbound b hb)
  · rw [hMr]
    exact hab.le
  · exact ht
  · exact ht2
  · exact hP
  · exact hJ
  · exact hV
  · intro p hp i
    exact hUbound p (hVU hp) i
  · exact finiteSeparatedAt_subset hVU hUsep
  · exact hVregular
  · exact hpa
  · exact hpb
  · exact hVlarge
  · exact hJI
  · exact hIJ
  · exact hIbound
  · exact hIballZ
  · intro j hj
    rw [hMr]
    exact ⟨(htriple j hj).1.le,(htriple j hj).2.1.le⟩
  · intro j hj
    exact Finset.inter_subset_left
  · intro j hj
    exact (htriple j hj).2.2.1
  · intro j hj
    exact (htriple j hj).2.2.2
  · exact hlog'

end Falconer

end OAI
