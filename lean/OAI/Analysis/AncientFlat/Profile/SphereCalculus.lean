import OAI.Analysis.AncientFlat.Profile.SphereCore

namespace OAI
noncomputable section
open scoped ContDiff Laplacian
namespace CompactCore
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
lemma correction_smooth (f : V → ℂ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (correction f) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hdd : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ f)) := hd.fderiv_right (by simp)
  change ContDiff ℝ ∞ (fun x => radialJet 2 f x+29*radialJet 1 f x)
  simp only [radialJet,iteratedFDeriv_one_apply,iteratedFDeriv_two_apply]
  exact ((hdd.clm_apply contDiff_id).clm_apply contDiff_id).add
    ((contDiff_const : ContDiff ℝ ∞ (fun _ : V => (29:ℂ))).mul (hd.clm_apply contDiff_id))

lemma laplacian_smooth [FiniteDimensional ℝ V] (f : V → ℂ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (Δ f) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  apply ContDiff.sum
  intro i _
  have hd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hdd : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ f)) := hd.fderiv_right (by simp)
  simpa only [iteratedFDeriv_two_apply] using
    ((hdd.clm_apply contDiff_const).clm_apply contDiff_const)
lemma sphereLap_smooth [FiniteDimensional ℝ V] (f : V → ℂ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (sphereLap f) := (laplacian_smooth f hf).sub (correction_smooth f hf)
lemma radialJet_scaled (j : ℕ) (f : V → ℂ) (hf : ContDiff ℝ ∞ f) (q : ℝ) (x : V) :
    radialJet j (fun y => f (q • y)) x=radialJet j f (q • x) := by
  simp only [radialJet,iteratedFDeriv_comp_const_smul q
    (hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl j)),smul_apply]
  rw [(iteratedFDeriv ℝ j f (q • x)).map_smul_univ (fun _ => q) (fun _ => x)]
  simp
lemma correction_scaled (f : V → ℂ) (hf : ContDiff ℝ ∞ f) (q : ℝ) :
    correction (fun y => f (q • y))=fun x => correction f (q • x) := by
  funext x
  simp only [correction,radialJet_scaled _ f hf q]
lemma laplacian_scaled [FiniteDimensional ℝ V] (f : V → ℂ) (hf : ContDiff ℝ ∞ f) (q : ℝ) :
    Δ (fun y => f (q • y))=fun x => (q:ℂ)^2*Δ f (q • x) := by
  funext x
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp_rw [iteratedFDeriv_comp_const_smul (i := 2) q (hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))]
  simp only [smul_apply,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,Complex.real_smul,
    Complex.ofReal_pow,←Finset.mul_sum]
lemma correction_sub (f g : V → ℂ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    correction (f-g)=correction f-correction g := by
  funext x
  simp only [correction,radialJet,iteratedFDeriv_sub (i := 2) (hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) (hg.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)),
    iteratedFDeriv_sub (i := 1) (hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)) (hg.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)),
    Pi.sub_apply,sub_apply]
  ring
lemma correction_smul (f : V → ℂ) (hf : ContDiff ℝ ∞ f) (a : ℂ) :
    correction (a • f)=a • correction f := by
  funext x
  simp only [correction,radialJet,
    iteratedFDeriv_const_smul_apply (i := 2) ((hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt),
    iteratedFDeriv_const_smul_apply (i := 1) ((hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)).contDiffAt),
    smul_apply,Pi.smul_apply,smul_eq_mul]
  ring
end CompactCore

end

end OAI
