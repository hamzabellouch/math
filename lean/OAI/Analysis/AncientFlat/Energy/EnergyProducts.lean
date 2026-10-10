import OAI.Analysis.AncientFlat.Energy.EnergyIBP

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Laplacian
namespace ParametrixUniqueness
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [InnerProductSpace ℝ V] in
lemma Decays.const_smul {f : V → E} (hf : Decays f) (c : ℝ) :
    Decays (fun x => c • f x) := by
  obtain ⟨M,hM,hf⟩ := hf
  refine ⟨‖c‖*M,mul_nonneg (norm_nonneg _) hM,fun x => ?_⟩
  rw [norm_smul,mul_assoc]
  exact mul_le_mul_of_nonneg_left (hf x) (norm_nonneg _)

lemma dir_dir_smul (v : V) (f : V → ℝ) (g : V → E)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    dir v (dir v (fun x => f x • g x)) = fun x =>
      dir v (dir v f) x • g x + (2*dir v f x) • dir v g x + f x • dir v (dir v g) x := by
  have hd := (hf.differentiable (by norm_num))
  have he := (hg.differentiable (by norm_num))
  have hd' := (contDiff_dir (n := 1) v f hf).differentiable (by norm_num)
  have he' := (contDiff_dir (n := 1) v g hg).differentiable (by norm_num)
  rw [dir_smul _ _ _ hd he]
  rw [dir_add v (fun x => dir v f x • g x) (fun x => f x • dir v g x)
    (hd'.fun_smul he) (hd.fun_smul he')]
  rw [dir_smul _ _ _ hd' he,dir_smul _ _ _ hd he']
  funext x
  module

lemma decays_dir_smul {f : V → ℝ} {g : V → E} (v : V)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (h0 : Decays f) (h1 : Decays (dir v f)) (hb : BoundedJets 2 g) :
    Decays (dir v (fun x => f x • g x)) := by
  rw [dir_smul _ _ _ (hf.differentiable (by norm_num)) (hg.differentiable (by norm_num))]
  exact (h1.smul hb.zero).add (h0.smul (hb.dir hg v).zero)
lemma decays_dir_dir_smul {f : V → ℝ} {g : V → E} (v : V)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (h0 : Decays f) (h1 : Decays (dir v f)) (h2 : Decays (dir v (dir v f)))
    (hb : BoundedJets 2 g) : Decays (dir v (dir v (fun x => f x • g x))) := by
  rw [dir_dir_smul _ _ _ hf hg]
  exact ((h2.smul hb.zero).add ((h1.const_smul 2).smul (hb.dir hg v).zero)).add
    (h0.smul ((hb.dir hg v).dir (contDiff_dir v g hg) v).zero)
lemma decays_dir_dir_weight_mul {a : V → ℝ} (ha : ContDiff ℝ 2 a) (hb : BoundedJets 2 a) (v : V) :
    Decays (dir v (dir v (fun x => weight x*a x))) := by
  exact decays_dir_dir_smul v (contDiff_weight 2) ha decays_weight (decays_dir_weight v)
    (decays_dir_dir_weight v) hb

lemma norm_dir_le (v : V) (f : V → E) (x : V) :
    ‖dir v f x‖ ≤ ‖v‖ * ‖iteratedFDeriv ℝ 1 f x‖ := by
  rw [norm_iteratedFDeriv_one,mul_comm]
  exact (fderiv ℝ f x).le_opNorm v
lemma norm_dir_dir_le (v : V) (f : V → E) (hf : ContDiff ℝ 2 f) (x : V) :
    ‖dir v (dir v f) x‖ ≤ ‖v‖ ^ 2 * ‖iteratedFDeriv ℝ 2 f x‖ := by
  have hd : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hh : ‖iteratedFDeriv ℝ 1 (dir v f) x‖ ≤ ‖v‖ * ‖iteratedFDeriv ℝ 2 f x‖ := by
    calc
      _ ≤ ‖v‖ * ‖iteratedFDeriv ℝ 1 (fderiv ℝ f) x‖ :=
        norm_iteratedFDeriv_clm_apply_const hd.contDiffAt le_rfl
      _ = _ := by rw [norm_iteratedFDeriv_fderiv]
  exact (norm_dir_le v (dir v f) x).trans (by nlinarith [norm_nonneg v])

lemma weight_mul_bounds (a : V → ℝ) (ha : ContDiff ℝ 2 a) (C : ℝ) (hC : 0≤C)
    (hb : ∀ k : ℕ, k≤2 → ∀ x, ‖iteratedFDeriv ℝ k a x‖≤C)
    (v x : V) (hv : ‖v‖≤1) :
    |weight x*a x|≤C*weight x ∧
    |dir v (fun y => weight y*a y) x|≤(2*C)*weight x ∧
    |dir v (dir v (fun y => weight y*a y)) x|≤(4*C)*weight x := by
  have h0 : |a x|≤C := by simpa [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using hb 0 (by norm_num) x
  have h1 : |dir v a x|≤C := by
    have hh := (norm_dir_le v a x).trans
      ((mul_le_mul_of_nonneg_left (hb 1 (by norm_num) x) (norm_nonneg _)).trans
        (by simpa using mul_le_mul_of_nonneg_right hv hC))
    simpa [Real.norm_eq_abs] using hh
  have h2 : |dir v (dir v a) x|≤C := by
    have hv' : ‖v‖^2≤1 := by nlinarith [norm_nonneg v]
    have hh := (norm_dir_dir_le v a ha x).trans
      (mul_le_mul hv' (hb 2 (by norm_num) x) (norm_nonneg _) (by norm_num : (0:ℝ)≤1))
    simpa [Real.norm_eq_abs] using hh
  have w0 : |weight x|=weight x := abs_of_pos (weight_pos x)
  have w1 : |dir v weight x|≤weight x := by
    have hh := (fderiv ℝ weight x).le_opNorm v
    exact hh.trans ((mul_le_mul (norm_fderiv_weight_le x) hv (norm_nonneg _) (weight_pos x).le).trans_eq (mul_one _))
  have hw0 := (weight_pos x).le
  have hv' : ‖v‖^2≤1 := by nlinarith [norm_nonneg v]
  have w2 : |dir v (dir v weight) x|≤weight x := by
    exact (dir_dir_weight_bound v x).trans (by simpa using mul_le_mul_of_nonneg_left hv' hw0)
  constructor
  · rw [abs_mul,w0,mul_comm]
    exact mul_le_mul_of_nonneg_right h0 (weight_pos x).le
  constructor
  · have he := congrFun (dir_smul v weight a ((contDiff_weight 2).differentiable (by norm_num))
      (ha.differentiable (by norm_num))) x
    change dir v (fun y => weight y*a y) x = dir v weight x*a x+weight x*dir v a x at he
    rw [he]
    calc
      _ ≤ |dir v weight x*a x|+|weight x*dir v a x| := abs_add_le _ _
      _ ≤ weight x*C+weight x*C := by
        rw [abs_mul,abs_mul,w0]
        exact add_le_add (mul_le_mul w1 h0 (abs_nonneg _) (weight_pos x).le)
          (mul_le_mul_of_nonneg_left h1 (weight_pos x).le)
      _ = _ := by ring
  · have he := congrFun (dir_dir_smul v weight a (contDiff_weight 2) ha) x
    change dir v (dir v (fun y => weight y*a y)) x =
      dir v (dir v weight) x*a x+(2*dir v weight x)*dir v a x+
        weight x*dir v (dir v a) x at he
    rw [he]
    calc
      _ ≤ (|dir v (dir v weight) x*a x|+|(2*dir v weight x)*dir v a x|)+
          |weight x*dir v (dir v a) x| := (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ (weight x*C+2*weight x*C)+weight x*C := by
        simp only [abs_mul,w0,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
        gcongr
      _ = _ := by ring

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
lemma integral_inner_dir_dir (v : V) (f g : V → ℂ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (h0 : Decays f) (h1 : Decays (dir v f)) (h2 : Decays (dir v (dir v f)))
    (hb : BoundedJets 2 g) :
    (∫ x, inner ℝ (f x) (dir v (dir v g) x)) = ∫ x, inner ℝ (dir v (dir v f) x) (g x) := by
  rw [integral_inner_dir v f (dir v g) (hf.of_le (by norm_num)) (contDiff_dir v g hg)
    h0 h1 (hb.dir hg v).zero ((hb.dir hg v).dir (contDiff_dir v g hg) v).zero,
    integral_inner_dir v (dir v f) g (contDiff_dir v f hf) (hg.of_le (by norm_num))
      h1 h2 hb.zero (hb.dir hg v).zero,neg_neg]
end ParametrixUniqueness

end

end OAI
