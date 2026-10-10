import OAI.Analysis.BernoulliCone.UpperComparison

namespace OAI

section
noncomputable section
open Set Filter InnerProductSpace MeasureTheory
open scoped Topology ContDiff NNReal
namespace Bernoulli.DeSilvaJerison

/-- The constructed double-cone is a global energy minimizer against the full
arbitrary Sobolev competitor class. Upper and lower comparisons are joined by
the exact Sobolev lattice identity, including its contact-level gradients. -/
theorem U_global_minimizer : GlobalMinimizer U := by
  refine ⟨isOpen_univ,gradient U,U_h1loc,?_,?_⟩
  · simpa only [Measure.restrict_univ] using (Eventually.of_forall U_nonneg : ∀ᵐ x:Space 7 ∂volume,0≤U x)
  intro c r hr hB v V hv hvn htrace
  let B:=Metric.ball c r
  let G:=gradient U
  have hu:H1 B U G:=U_h1loc c r hr (subset_univ _)
  have hpos:=SobolevCalculus.h10_positivePart Metric.isOpen_ball htrace
  have hneg:H10 B (fun x=>max (U x-v x) 0)
      (fun x=>(if 0<U x-v x then (1:ℝ) else 0) • (G x-V x)):=by
    simpa only [neg_sub] using SobolevCalculus.h10_positivePart Metric.isOpen_ball htrace.neg
  let p:=fun x=>U x+max (v x-U x) 0
  let P:=fun x=>G x+(if 0<v x-U x then (1:ℝ) else 0) • (V x-G x)
  let m:=fun x=>U x-max (U x-v x) 0
  let M:=fun x=>G x-(if 0<U x-v x then (1:ℝ) else 0) • (G x-V x)
  have hp:H1 B p P:=hu.add hpos.1
  have hm:H1 B m M:=hu.sub hneg.1
  have hpt:H10 B (fun x=>p x-U x) (fun x=>P x-G x):=by
    apply hpos.congr
    · exact Eventually.of_forall (fun x=>by dsimp [p]; ring)
    · exact Eventually.of_forall (fun x=>by dsimp [P]; abel)
  have hmt:H10 B (fun x=>m x-U x) (fun x=>M x-G x):=by
    apply hneg.neg.congr
    · exact Eventually.of_forall (fun x=>by dsimp [m]; ring)
    · exact Eventually.of_forall (fun x=>by dsimp [M]; abel)
  have hUp:∀ᵐ x ∂volume.restrict B,U x≤p x:=
    Eventually.of_forall fun x=>le_add_of_nonneg_right (le_max_right _ _)
  have hmU:∀ᵐ x ∂volume.restrict B,m x≤U x:=
    Eventually.of_forall fun x=>sub_le_self _ (le_max_right _ _)
  have hmn:∀ᵐ x ∂volume.restrict B, 0 ≤ m x:=by
    filter_upwards [hvn] with x hx
    change 0≤U x-max (U x-v x) 0
    exact sub_nonneg.mpr (max_le (by linarith) (U_nonneg x))
  have hupper:=U_upper_comparison c r hr hp hUp hpt
  have hlower:=U_lower_comparison c r hr hm hmn hmU hmt
  let :IsFiniteMeasure (volume.restrict B):=isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hI {f:Space 7→ℝ} {F:Space 7→Space 7} (h:H1 B f F):
      Integrable (fun x=>‖F x‖^2+if 0<f x then (1:ℝ) else 0) (volume.restrict B):=
    (h.2.1.integrable_norm_pow (by norm_num)).add (integrable_phase h.1.aestronglyMeasurable)
  have henergy:energy B m M+energy B p P=energy B U G+energy B v V:=by
    rw [energy,energy,energy,energy,←integral_add (hI hm) (hI hp),←integral_add (hI hu) (hI hv)]
    apply integral_congr_ae
    filter_upwards [SobolevCalculus.gradient_zero_on_zero_set Metric.isOpen_ball htrace.1] with x hz
    rcases lt_trichotomy (v x) (U x) with hlt|he|hgt
    · have h1:¬0<v x-U x:=by linarith
      have h2:0<U x-v x:=by linarith
      have he:m x=v x:=by dsimp [m]; rw [max_eq_left h2.le]; ring
      simp only [he,p,P,M,ite_eq_right h1,ite_eq_left h2,zero_smul,one_smul,add_zero,
        sub_sub_cancel,max_eq_right (not_lt.mp h1)]
      ring
    · have hVG:V x=G x:=sub_eq_zero.mp (hz (by rw [he,sub_self]))
      simp only [p,P,m,M,he,hVG,sub_self,lt_self_iff_false,ite_false,zero_smul,
        max_self,add_zero,sub_zero]
    · have h1:0<v x-U x:=by linarith
      have h2:¬0<U x-v x:=by linarith
      have he:p x=v x:=by dsimp [p]; rw [max_eq_left h1.le]; ring
      simp only [he,m,M,P,ite_eq_left h1,ite_eq_right h2,zero_smul,one_smul,sub_zero,
        add_sub_cancel,max_eq_right (not_lt.mp h2)]
  change energy B U G≤energy B p P at hupper
  change energy B U G≤energy B m M at hlower
  linarith

theorem exists_nonflat_dimension_seven :
    ∃u:Space 7→ℝ,GlobalMinimizer u ∧ Nonzero u ∧ OneHomogeneous u ∧ ¬Flat u :=
  ⟨U,U_global_minimizer,U_nonzero,U_homogeneous,U_not_flat⟩
end Bernoulli.DeSilvaJerison

end
end

end OAI
