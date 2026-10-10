import OAI.Analysis.AncientFlat.Energy.EnergyWeight
import OAI.Analysis.AncientFlat.Evolution.TraceFour

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Laplacian
namespace ParametrixUniqueness
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def Bounded (f : V → E) : Prop := ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖f x‖ ≤ M
def Decays (f : V → E) : Prop := ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖f x‖ ≤ M * weight x
def BoundedJets (n : ℕ) (f : V → E) : Prop :=
  ∀ k : ℕ, k ≤ n → Bounded (iteratedFDeriv ℝ k f)

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [NormedSpace ℝ E] in
lemma Bounded.add {f g : V → E} (hf : Bounded f) (hg : Bounded g) : Bounded (fun x => f x+g x) := by
  obtain ⟨M,hM,hf⟩ := hf
  obtain ⟨N,hN,hg⟩ := hg
  exact ⟨M+N,add_nonneg hM hN,fun x => (norm_add_le _ _).trans (add_le_add (hf x) (hg x))⟩
omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [NormedSpace ℝ E] in
lemma Bounded.sum {ι : Type*} (s : Finset ι) (f : ι → V → E) (hf : ∀ i ∈ s, Bounded (f i)) :
    Bounded (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0,le_rfl,by simp⟩
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using (hf i (by simp)).add
      (ih (fun j hj => hf j (by simp [hj])))
omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [NormedSpace ℝ E] in
lemma Bounded.norm {f : V → E} (hf : Bounded f) : Bounded (fun x => ‖f x‖) := by
  simpa only [Bounded,norm_norm] using hf
omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] in
lemma Bounded.mul {f g : V → ℝ} (hf : Bounded f) (hg : Bounded g) :
    Bounded (fun x => f x*g x) := by
  obtain ⟨M,hM,hf⟩ := hf
  obtain ⟨N,hN,hg⟩ := hg
  refine ⟨M*N,mul_nonneg hM hN,fun x => ?_⟩
  rw [norm_mul]
  exact mul_le_mul (hf x) (hg x) (norm_nonneg _) hM
omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] in
lemma Bounded.inner {f g : V → ℂ} (hf : Bounded f) (hg : Bounded g) :
    Bounded (fun x => inner ℝ (f x) (g x)) := by
  obtain ⟨M,hM,hf⟩ := hf
  obtain ⟨N,hN,hg⟩ := hg
  exact ⟨M*N,mul_nonneg hM hN,fun x => (norm_inner_le_norm _ _).trans
    (mul_le_mul (hf x) (hg x) (norm_nonneg _) hM)⟩
lemma BoundedJets.of_le {n m : ℕ} {f : V → E} (hf : BoundedJets n f) (hmn : m≤n) :
    BoundedJets m f := fun k hk => hf k (hk.trans hmn)
lemma BoundedJets.zero {n : ℕ} {f : V → E} (hf : BoundedJets n f) : Bounded f := by
  simpa only [Bounded,norm_iteratedFDeriv_zero] using hf 0 (Nat.zero_le _)
lemma BoundedJets.dir {n : ℕ} {f : V → E} (hf : BoundedJets (n+1) f)
    (hc : ContDiff ℝ (n+1) f) (v : V) : BoundedJets n (dir v f) := by
  intro k hk
  obtain ⟨M,hM,hb⟩ := hf (k+1) (Nat.add_le_add_right hk 1)
  refine ⟨‖v‖*M,mul_nonneg (norm_nonneg _) hM,fun x => ?_⟩
  have ht : ContDiff ℝ n (fderiv ℝ f) := hc.fderiv_right (by norm_cast)
  calc
    ‖iteratedFDeriv ℝ k (ParametrixUniqueness.dir v f) x‖ ≤ ‖v‖ * ‖iteratedFDeriv ℝ k (fderiv ℝ f) x‖ :=
      norm_iteratedFDeriv_clm_apply_const ht.contDiffAt (by exact_mod_cast hk)
    _ = ‖v‖ * ‖iteratedFDeriv ℝ (k+1) f x‖ := by rw [norm_iteratedFDeriv_fderiv]
    _ ≤ ‖v‖ * M := mul_le_mul_of_nonneg_left (hb x) (norm_nonneg _)

omit [InnerProductSpace ℝ V] [NormedSpace ℝ E] in
lemma Decays.add {f g : V → E} (hf : Decays f) (hg : Decays g) : Decays (fun x => f x+g x) := by
  obtain ⟨M,hM,hf⟩ := hf
  obtain ⟨N,hN,hg⟩ := hg
  refine ⟨M+N,add_nonneg hM hN,fun x => ?_⟩
  exact (norm_add_le _ _).trans (by simpa [add_mul] using add_le_add (hf x) (hg x))
omit [InnerProductSpace ℝ V] in
lemma Decays.smul {f : V → ℝ} {g : V → E} (hf : Decays f) (hg : Bounded g) :
    Decays (fun x => f x • g x) := by
  obtain ⟨M,hM,hf⟩ := hf
  obtain ⟨N,hN,hg⟩ := hg
  refine ⟨M*N,mul_nonneg hM hN,fun x => ?_⟩
  rw [norm_smul]
  calc
    ‖f x‖ * ‖g x‖ ≤ (M*weight x)*N :=
      mul_le_mul (hf x) (hg x) (norm_nonneg _) (mul_nonneg hM (weight_pos x).le)
    _ = _ := by ring
omit [InnerProductSpace ℝ V] in
lemma Decays.inner {f g : V → ℂ} (hf : Decays f) (hg : Bounded g) :
    Decays (fun x => inner ℝ (f x) (g x)) := by
  obtain ⟨M,hM,hf⟩ := hf
  obtain ⟨N,hN,hg⟩ := hg
  refine ⟨M*N,mul_nonneg hM hN,fun x => ?_⟩
  calc
    ‖innerSL ℝ (f x) (g x)‖ ≤ ‖f x‖ * ‖g x‖ := norm_inner_le_norm (𝕜 := ℝ) (f x) (g x)
    _ ≤ (M*weight x)*N :=
      mul_le_mul (hf x) (hg x) (norm_nonneg _) (mul_nonneg hM (weight_pos x).le)
    _ = _ := by ring
omit [InnerProductSpace ℝ V] in
lemma decays_weight : Decays (weight : V → ℝ) :=
  ⟨1,by norm_num,fun x => by rw [Real.norm_eq_abs,abs_of_pos (weight_pos x),one_mul]⟩
lemma decays_dir_weight (v : V) : Decays (dir v weight : V → ℝ) := by
  refine ⟨‖v‖,norm_nonneg _,fun x => ?_⟩
  rw [dir_weight,norm_mul,norm_neg,Real.norm_eq_abs,abs_of_pos (weight_pos x),mul_comm]
  exact mul_le_mul_of_nonneg_right (radialComponent_bound v x) (weight_pos x).le
lemma decays_dir_dir_weight (v : V) : Decays (dir v (dir v weight) : V → ℝ) :=
  ⟨‖v‖^2,sq_nonneg _,fun x => by simpa [Real.norm_eq_abs,mul_comm] using dir_dir_weight_bound v x⟩

lemma dir_smul (v : V) (f : V → ℝ) (g : V → E)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    dir v (fun x => f x • g x) = fun x => dir v f x • g x + f x • dir v g x := by
  funext x
  rw [dir,fderiv_fun_smul hf.differentiableAt hg.differentiableAt]
  simp [dir,ContinuousLinearMap.smulRight_apply]
  abel
lemma dir_add (v : V) (f g : V → E) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    dir v (fun x => f x+g x) = fun x => dir v f x+dir v g x := by
  funext x
  simp [dir,fderiv_fun_add hf.differentiableAt hg.differentiableAt]

omit [InnerProductSpace ℝ V] in
lemma decays_weight_mul {a : V → ℝ} (ha : Bounded a) :
    Decays (fun x => weight x*a x) := by simpa only [smul_eq_mul] using decays_weight.smul ha
lemma decays_dir_weight_mul {a : V → ℝ} (ha : ContDiff ℝ 2 a) (hb : BoundedJets 2 a) (v : V) :
    Decays (dir v (fun x => weight x*a x)) := by
  change Decays (dir v (fun x => weight x • a x))
  rw [dir_smul _ _ _ ((contDiff_weight 2).differentiable (by norm_num)) (ha.differentiable (by norm_num))]
  exact (decays_dir_weight v |>.smul hb.zero).add (decays_weight.smul (hb.dir ha v).zero)

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
omit [NormedSpace ℝ E] in
lemma Decays.integrable {f : V → E} (hf : Decays f) (hc : Continuous f) : Integrable f := by
  obtain ⟨M,hM,hf⟩ := hf
  exact (integrable_weight.const_mul M).mono' hc.aestronglyMeasurable (Eventually.of_forall hf)

lemma integral_inner_dir (v : V) (f g : V → ℂ) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (h0 : Decays f) (h1 : Decays (dir v f)) (hb0 : Bounded g) (hb1 : Bounded (dir v g)) :
    (∫ x, inner ℝ (f x) (dir v g x)) = -(∫ x, inner ℝ (dir v f x) (g x)) := by
  apply integral_bilinear_fderiv_right_eq_neg_left_of_integrable
    (f := f) (g := g) (v := v) (B := innerSL ℝ)
  · exact (h1.inner hb0).integrable ((contDiff_dir (n := 0) v f hf).continuous.inner hg.continuous)
  · exact (h0.inner hb1).integrable (hf.continuous.inner (contDiff_dir (n := 0) v g hg).continuous)
  · exact (h0.inner hb0).integrable (hf.continuous.inner hg.continuous)
  · exact fun x _ => (hf.differentiable (by norm_num)).differentiableAt
  · exact fun x _ => (hg.differentiable (by norm_num)).differentiableAt
end ParametrixUniqueness

end

end OAI
