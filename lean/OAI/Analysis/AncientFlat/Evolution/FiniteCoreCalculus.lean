import OAI.Analysis.AncientFlat.Profile.SphereCore

namespace OAI
noncomputable section
open scoped ContDiff Laplacian
namespace CompactCoreFinite
open CompactCore
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
lemma correction_smooth {n : ℕ} (f : V → ℂ) (hf : ContDiff ℝ (n+2 : ℕ) f) :
    ContDiff ℝ n (correction f) := by
  have hd : ContDiff ℝ (n+1 : ℕ) (fderiv ℝ f) := hf.fderiv_right (by norm_num [Nat.cast_add, add_assoc])
  have hdd : ContDiff ℝ n (fderiv ℝ (fderiv ℝ f)) := hd.fderiv_right (by simp)
  change ContDiff ℝ n (fun x => radialJet 2 f x+29*radialJet 1 f x)
  simp only [radialJet,iteratedFDeriv_one_apply,iteratedFDeriv_two_apply]
  exact ((hdd.clm_apply contDiff_id).clm_apply contDiff_id).add
    ((contDiff_const : ContDiff ℝ n (fun _ : V => (29:ℂ))).mul
      ((hd.of_le (by simp)).clm_apply contDiff_id))
lemma laplacian_smooth [FiniteDimensional ℝ V] {n : ℕ} (f : V → ℂ) (hf : ContDiff ℝ (n+2 : ℕ) f) :
    ContDiff ℝ n (Δ f) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  apply ContDiff.sum
  intro i _
  have hd : ContDiff ℝ (n+1 : ℕ) (fderiv ℝ f) := hf.fderiv_right (by norm_num [Nat.cast_add, add_assoc])
  have hdd : ContDiff ℝ n (fderiv ℝ (fderiv ℝ f)) := hd.fderiv_right (by simp)
  simpa only [iteratedFDeriv_two_apply] using
    ((hdd.clm_apply contDiff_const).clm_apply contDiff_const)
lemma sphereLap_smooth [FiniteDimensional ℝ V] {n : ℕ} (f : V → ℂ) (hf : ContDiff ℝ (n+2 : ℕ) f) :
    ContDiff ℝ n (sphereLap f) := (laplacian_smooth f hf).sub (correction_smooth f hf)
lemma radialJet_scaled (j : ℕ) (f : V → ℂ) (hf : ContDiff ℝ j f) (q : ℝ) (x : V) :
    radialJet j (fun y => f (q • y)) x=radialJet j f (q • x) := by
  simp only [radialJet,iteratedFDeriv_comp_const_smul q
    hf,smul_apply]
  rw [(iteratedFDeriv ℝ j f (q • x)).map_smul_univ (fun _ => q) (fun _ => x)]
  simp
lemma correction_scaled (f : V → ℂ) (hf : ContDiff ℝ 2 f) (q : ℝ) :
    correction (fun y => f (q • y))=fun x => correction f (q • x) := by
  funext x
  simp only [correction,radialJet_scaled 2 f hf q,
    radialJet_scaled 1 f (hf.of_le (by norm_num)) q]
lemma laplacian_scaled [FiniteDimensional ℝ V] (f : V → ℂ) (hf : ContDiff ℝ 2 f) (q : ℝ) :
    Δ (fun y => f (q • y))=fun x => (q:ℂ)^2*Δ f (q • x) := by
  funext x
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp_rw [iteratedFDeriv_comp_const_smul (i := 2) q hf]
  simp only [smul_apply,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,Complex.real_smul,
    Complex.ofReal_pow,←Finset.mul_sum]
lemma correction_sub (f g : V → ℂ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    correction (f-g)=correction f-correction g := by
  funext x
  simp only [correction,radialJet,iteratedFDeriv_sub (i := 2) hf hg,
    iteratedFDeriv_sub (i := 1) (hf.of_le (by norm_num)) (hg.of_le (by norm_num)),
    Pi.sub_apply,sub_apply]
  ring
lemma correction_smul (f : V → ℂ) (hf : ContDiff ℝ 2 f) (a : ℂ) :
    correction (a • f)=a • correction f := by
  funext x
  simp only [correction,radialJet,
    iteratedFDeriv_const_smul_apply (i := 2) (hf.contDiffAt),
    iteratedFDeriv_const_smul_apply (i := 1) ((hf.of_le (by norm_num)).contDiffAt),
    smul_apply,Pi.smul_apply,smul_eq_mul]
  ring
end CompactCoreFinite

end

end OAI
