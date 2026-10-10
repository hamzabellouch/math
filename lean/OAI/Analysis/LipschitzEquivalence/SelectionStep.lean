import OAI.Analysis.LipschitzEquivalence.PairingEstimates

namespace OAI

universe uH uIndex

noncomputable section
namespace LipschitzCounterexample.CompactWSC
open scoped ContDiff BigOperators NNReal Topology
open Set Filter FreeSpace
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem selection_step {K Q : Set H} (hQ : IsCompact Q)
    {C ρ α : ℝ} {μ : ℕ → Space H} (hC : 0 ≤ C) (hα : 0 < α)
    (P : RowItem K C ρ μ → Prop)
    (hRich : ((triangularRows K C ρ α μ).restrict P).Rich)
    {ι : Type uIndex} [Fintype ι] (z : ι → Smooth H) (hz : ∀ i, LipschitzWith 1 (z i).val)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ (f w : Smooth H) (a : RowItem K C ρ μ),
      LipschitzWith 1 f.val ∧ f.val 0 = 0 ∧ w.val 0 = 0 ∧
      P a ∧ α ≤ smoothPair a.a f ∧
      (∀ x ∈ Q, ‖Smooth.grad x w-damping Finset.univ z x • Smooth.grad x f‖ ≤ ε) ∧
      ((triangularRows K C ρ α μ).restrict (fun b => P b ∧ gradMass b.a f ≤ η)).Rich := by
  classical
  obtain ⟨φ,D,hD,happ,hgrad⟩ := exists_smooth_multiplier z hz Q hQ (show 0<ε/2 by positivity)
  let r := ε/(4*D)
  have hr : 0 < r := div_pos hε (by positivity)
  obtain ⟨S,hSQ,hSfin,hScover⟩ := hQ.finite_cover_balls hr
  let F : Finset H := hSfin.toFinset
  let t := η/(2*(C+1))
  have ht : 0 < t := div_pos hη (by positivity)
  let δ := min (r^2) (2*t*η)
  have hδ : 0 < δ := lt_min (sq_pos_of_pos hr) (by positivity)
  obtain ⟨f,a,hf,hf0,hPa,hpair,hrich⟩ := select_block hα P hRich F hδ
  have hsmall (x : H) (hx : x ∈ Q) : |f.val x| * D ≤ ε/2 := by
    obtain ⟨row,hrow,hrowE⟩ := hrich 1
    have hE := (hrowE 0).2
    have hcover : ∃ p ∈ S, dist x p < r := by
      simpa only [Set.mem_iUnion,Metric.mem_ball,exists_prop] using hScover hx
    obtain ⟨p,hp,hxp⟩ := hcover
    have hpF : p ∈ F := hSfin.mem_toFinset.mpr hp
    have hpval : |f.val p| < r := by
      have hs := sq_value_le_augmentedEnergy (row 0).a F 1 f hpF
      have hlt : (f.val p)^2 < r^2 := by
        simp only [one_mul] at hs
        exact hs.trans_lt (hE.trans_le (min_le_left _ _))
      exact (sq_lt_sq₀ (abs_nonneg _) hr.le).mp (by simpa only [sq_abs] using hlt)
    have hdiff : |f.val x-f.val p| < r := by
      have hb : |f.val x-f.val p| ≤ dist x p := by
        simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using hf.dist_le_mul x p
      exact hb.trans_lt hxp
    have hxval : |f.val x| < 2*r := by
      have he : f.val x = (f.val x-f.val p)+f.val p := by ring
      rw [he]
      exact (abs_add_le _ _).trans_lt (by linarith)
    have he : (2*r)*D = ε/2 := by dsimp [r]; field_simp; ring
    exact (mul_le_mul_of_nonneg_right hxval.le hD.le).trans_eq he
  refine ⟨f,φ.mul f,a,hf,hf0,?_,hPa,hpair,?_,?_⟩
  · change φ.val 0*f.val 0 = 0
    rw [hf0,mul_zero]
  · intro x hx
    apply product_gradient_error Finset.univ z φ f
      (by simpa using f.grad_norm_le hf x) (hgrad x hx) (happ x) (hsmall x hx)
  · intro N
    obtain ⟨row,hrow,hrowE⟩ := hrich N
    refine ⟨row,hrow,fun i => ⟨(hrowE i).1,?_⟩⟩
    have hE : gradEnergy (row i).a f < 2*t*η :=
      (gradEnergy_le_augmentedEnergy _ F 1 f).trans_lt
        (((hrowE i).2).trans_le (min_le_right _ _))
    have hcost : t*(row i).a.cost ≤ η/2 := by
      calc
        _ ≤ t*C := mul_le_mul_of_nonneg_left (row i).cost_le ht.le
        _ ≤ η/2 := by
          have he : t*(2*(C+1)) = η := div_mul_cancel₀ _ (by positivity)
          nlinarith
    have hi : (4*t)⁻¹*gradEnergy (row i).a f ≤ η/2 := by
      have h4 : 0 < 4*t := by positivity
      apply (le_of_eq (inv_mul_eq_div _ _)).trans
      exact (div_le_iff₀ h4).mpr (by linarith)
    exact (gradMass_le_young (row i).a f ht).trans (by linarith)

end LipschitzCounterexample.CompactWSC
end

end OAI
