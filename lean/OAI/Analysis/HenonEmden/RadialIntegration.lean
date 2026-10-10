import OAI.Analysis.HenonEmden.VirialCalculus

namespace OAI

section RadialIntegration

open MeasureTheory Set Filter Topology Metric
open scoped InnerProductSpace
noncomputable section
namespace HenonLaneEmden
open WeakPDE

lemma sum_inner_mul_dir {n : ℕ} (F : Space n → ℝ) (x : Space n) :
    ∑ i : Fin n, inner ℝ (EuclideanSpace.basisFun (Fin n) ℝ i) x *
      dir F (EuclideanSpace.basisFun (Fin n) ℝ i) x = dir F x x := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have he := congrArg (fderiv ℝ F x) (b.sum_repr' x)
  simpa only [map_sum,map_smul,smul_eq_mul,dir] using he

lemma integral_radial_test {n : ℕ} {F θ : Space n → ℝ}
    (hF : ContDiffOn ℝ 1 F ({0}ᶜ : Set (Space n)))
    (hθ : ContDiff ℝ 1 θ) (hθc : HasCompactSupport θ) (hθ0 : 0 ∉ tsupport θ) :
    (∫ x, F x*((n:ℝ)*θ x+dir θ x x)) = -(∫ x, θ x*dir F x x) := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let φ (i : Fin n) (x : Space n) := θ x*inner ℝ (b i) x
  have hφ (i : Fin n) : ContDiff ℝ 1 (φ i) := hθ.mul ((innerSL ℝ (b i)).contDiff)
  have hφs (i : Fin n) : tsupport (φ i) ⊆ tsupport θ := tsupport_mul_subset_left
  have hφc (i : Fin n) : HasCompactSupport (φ i) := hθc.mul_right
  have hs : tsupport θ ⊆ ({0}ᶜ : Set (Space n)) := by
    intro x hx
    simp only [mem_compl_iff,mem_singleton_iff]
    intro he; subst x; exact hθ0 hx
  have hφD (i : Fin n) : Continuous (dir (φ i) (b i)) :=
    (contDiffOn_univ.mp (contDiffOn_dir (k := 0) (hφ i).contDiffOn isOpen_univ (b i))).continuous
  have hFD (i : Fin n) : ContinuousOn (dir F (b i)) ({0}ᶜ : Set (Space n)) :=
    (contDiffOn_dir (k := 0) hF isOpen_compl_singleton (b i)).continuousOn
  have hiL (i : Fin n) : Integrable (fun x => F x*dir (φ i) (b i) x) :=
    integrable_mul_compact (compactSupport_dir (hφc i) (b i))
      (hF.continuousOn.mono ((tsupport_dir_subset _ _).trans ((hφs i).trans hs))) (hφD i).continuousOn
  have hiR (i : Fin n) : Integrable (fun x => dir F (b i) x*φ i x) :=
    integrable_mul_compact (hφc i) ((hFD i).mono ((hφs i).trans hs)) (hφ i).continuous.continuousOn
  have hiP (i : Fin n) : Integrable (fun x => F x*φ i x) :=
    integrable_mul_compact (hφc i) (hF.continuousOn.mono ((hφs i).trans hs)) (hφ i).continuous.continuousOn
  have hI (i : Fin n) : (∫ x, F x*dir (φ i) (b i) x) = -(∫ x, dir F (b i) x*φ i x) := by
    exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (f := F) (g := φ i) (v := b i)
      (hiR i) (hiL i) (hiP i)
      (fun x hx => (hF.contDiffAt (isOpen_compl_singleton.mem_nhds (hs (hφs i hx)))).differentiableAt (by norm_num))
      (fun x _ => (hφ i).differentiable (by norm_num) x)
  have hφeq (i : Fin n) (x : Space n) : dir (φ i) (b i) x =
      inner ℝ (b i) x*dir θ (b i) x+θ x := by
    have hh := ((hθ.differentiable (by norm_num) x).hasFDerivAt).mul ((innerSL ℝ (b i)).hasFDerivAt)
    change HasFDerivAt (φ i) _ x at hh
    rw [dir,hh.fderiv]
    simp only [add_apply,smul_apply,smul_eq_mul,innerSL_apply_apply,b.inner_eq_ite,ite_true,mul_one,dir]
    ring
  have hL (x : Space n) : (∑ i : Fin n, F x*dir (φ i) (b i) x) = F x*((n:ℝ)*θ x+dir θ x x) := by
    simp_rw [hφeq,mul_add]
    rw [Finset.sum_add_distrib,← Finset.mul_sum,show (∑ i : Fin n, inner ℝ (b i) x*dir θ (b i) x) = dir θ x x from sum_inner_mul_dir θ x]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    ring
  have hR (x : Space n) : (∑ i : Fin n, dir F (b i) x*φ i x) = θ x*dir F x x := by
    simp only [φ]
    simp_rw [show ∀ i : Fin n, dir F (b i) x*(θ x*inner ℝ (b i) x) = θ x*(inner ℝ (b i) x*dir F (b i) x) from fun _ => by ring]
    rw [← Finset.mul_sum,sum_inner_mul_dir]
  calc
    _ = ∫ x, ∑ i : Fin n, F x*dir (φ i) (b i) x := by simp_rw [hL]
    _ = ∑ i : Fin n, ∫ x, F x*dir (φ i) (b i) x := integral_finsetSum _ (fun i _ => hiL i)
    _ = ∑ i : Fin n, -(∫ x, dir F (b i) x*φ i x) := by simp_rw [hI]
    _ = -(∫ x, ∑ i : Fin n, dir F (b i) x*φ i x) := by rw [integral_finsetSum _ (fun i _ => hiR i),Finset.sum_neg_distrib]
    _ = _ := by simp_rw [hR]

end HenonLaneEmden
end
end RadialIntegration

end OAI
