import OAI.NumberTheory.TotientAsymptotic.IntervalChernoff
import OAI.NumberTheory.TotientAsymptotic.NormalityTilt

namespace OAI

/-! The reciprocal-mass saving for one interval in Ford's normality grid. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

 theorem normality_interval_mass : ∃ C : ℝ, 0<C ∧
    ∀ N : ℕ, 2≤N → ∀ U T A D : ℝ,
    2≤U → U≤T → T≤N → 0<A → A≤D → B T-B U≤D →
    ∀ Q : Finset ℕ, (∀ n ∈ Q,0<n ∧ n≤N ∧
      Real.sqrt (A*D)-4≤|(omegaIn n U T:ℝ)-(B T-B U)|) →
    (∑ n ∈ Q,(n:ℝ)⁻¹) ≤ C*Real.log N*Real.exp (-A/6) := by
  classical
  obtain ⟨C,hC,hChernoff⟩ := interval_omega_chernoff
  refine ⟨2*C*Real.exp 1,by positivity,?_⟩
  intro N hN U T A D hU hUT hTN hA hAD hM Q hQ
  let δ := normalityTilt A D
  let h := Real.sqrt (A*D)-4
  let M := B T-B U
  let Qp := Q.filter (fun n => h≤(omegaIn n U T:ℝ)-M)
  let Qm := Q.filter (fun n => h≤-((omegaIn n U T:ℝ)-M))
  have hδ : 0<δ := normalityTilt_pos hA hAD
  have hδle : δ≤1/4 := normalityTilt_le hA hAD
  have hcover : Q⊆Qp∪Qm := by
    intro n hn
    have hh := (hQ n hn).2.2
    rw [le_abs] at hh
    rcases hh with hh|hh
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hn,hh⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hn,by dsimp [h,M]; linarith⟩)
  have hplus : (∑ n ∈ Qp,(n:ℝ)⁻¹) ≤ C*Real.log N*Real.exp (δ^2*M-δ*h) := by
    have hc := hChernoff N hN U T hU hUT hTN δ h
      (by rw [abs_of_pos hδ]; exact hδle) Qp
    simp only [abs_of_pos hδ] at hc
    apply hc
    intro n hn
    obtain ⟨hn,hh⟩ := Finset.mem_filter.mp hn
    refine ⟨(hQ n hn).1,(hQ n hn).2.1,?_⟩
    exact mul_le_mul_of_nonneg_left hh hδ.le
  have hminus : (∑ n ∈ Qm,(n:ℝ)⁻¹) ≤ C*Real.log N*Real.exp (δ^2*M-δ*h) := by
    have hc := hChernoff N hN U T hU hUT hTN (-δ) h
      (by rw [abs_neg,abs_of_pos hδ]; exact hδle) Qm
    simp only [neg_sq,abs_neg,abs_of_pos hδ] at hc
    apply hc
    intro n hn
    obtain ⟨hn,hh⟩ := Finset.mem_filter.mp hn
    refine ⟨(hQ n hn).1,(hQ n hn).2.1,?_⟩
    have hm := mul_le_mul_of_nonneg_left hh hδ.le
    linarith
  have he : δ^2*M-δ*h ≤ 1-A/6 := normalityTilt_exponent hA hAD hM
  have hcoef : 0≤C*Real.log N := mul_nonneg hC.le
    (Real.log_nonneg (by exact_mod_cast (show 1≤N by omega)))
  have hb : C*Real.log N*Real.exp (δ^2*M-δ*h) ≤
      C*Real.log N*(Real.exp 1*Real.exp (-A/6)) := by
    rw [← Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ hcoef
    exact Real.exp_le_exp.mpr (by linarith)
  calc
    _ ≤ ∑ n ∈ Qp∪Qm,(n:ℝ)⁻¹ := Finset.sum_le_sum_of_subset_of_nonneg hcover
      (fun n _ _ => by positivity)
    _ ≤ (∑ n ∈ Qp,(n:ℝ)⁻¹)+(∑ n ∈ Qm,(n:ℝ)⁻¹) :=
      by
        have he := Finset.sum_union_inter (s₁:=Qp) (s₂:=Qm) (f:=fun n : ℕ => (n:ℝ)⁻¹)
        have hn : 0≤∑ n ∈ Qp∩Qm,(n:ℝ)⁻¹ := Finset.sum_nonneg (fun n _ => by positivity)
        linarith
    _ ≤ 2*(C*Real.log N*Real.exp (δ^2*M-δ*h)) := by linarith
    _ ≤ 2*(C*Real.log N*(Real.exp 1*Real.exp (-A/6))) := by linarith
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
