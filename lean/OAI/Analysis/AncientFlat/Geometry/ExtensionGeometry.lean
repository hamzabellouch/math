import OAI.Analysis.AncientFlat.Geometry.InnerExtensionCore
import OAI.Analysis.AncientFlat.Weighted.WeightedScaling

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff ENNReal
namespace FlatWeighted
open ParabolicInterior
variable {V : Type}
lemma sigma_sq [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (p : V × ℝ) : (sigma p)^2=‖p.1‖^2+Real.sqrt (-p.2) := by
  exact Real.sq_sqrt (by positivity)
lemma norm_le_sigma [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (p : V × ℝ) : ‖p.1‖≤ sigma p := by
  have hs := sigma_sq p
  have hp : 0≤ sigma p := Real.sqrt_nonneg _
  nlinarith [norm_nonneg p.1,Real.sqrt_nonneg (-p.2)]
lemma pdist_symm [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (p q : V × ℝ) : pdist p q=pdist q p := by
  simp only [pdist,norm_sub_rev,abs_sub_comm]
lemma sigma_le_add_pdist [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (p q : V × ℝ) (hp : p.2<0) (hq : q.2<0) :
    sigma p≤ sigma q+pdist p q := by
  let d := |p.2-q.2|^((1:ℝ)/4)
  have hd : 0≤d := Real.rpow_nonneg (abs_nonneg _) _
  have hd4 : d^4=|p.2-q.2| := by
    dsimp [d]
    rw [←Real.rpow_natCast,←Real.rpow_mul (abs_nonneg _)]
    norm_num
  have hq2 := Real.sq_sqrt (show 0≤ -q.2 by linarith)
  have ht : Real.sqrt (-p.2)≤Real.sqrt (-q.2)+d^2 := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (neg_pos.mpr hp).le]
    have hdiff : -p.2≤ -q.2+|p.2-q.2| := by linarith [neg_le_abs (p.2-q.2)]
    nlinarith [mul_nonneg (Real.sqrt_nonneg (-q.2)) (sq_nonneg d)]
  have hpq : ‖p.1‖≤‖q.1‖+‖p.1-q.1‖ := by
    calc
      _ = ‖q.1+(p.1-q.1)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  have hpq2 : ‖p.1‖^2≤(‖q.1‖+‖p.1-q.1‖)^2 := pow_le_pow_left₀ (norm_nonneg _) hpq 2
  have hqs := sigma_sq q
  have hnp := norm_le_sigma q
  have hh : 0≤ sigma q-‖q.1‖ := sub_nonneg.mpr hnp
  unfold sigma
  apply Real.sqrt_le_iff.mpr
  refine ⟨by dsimp [pdist]; positivity,?_⟩
  change ‖p.1‖^2+Real.sqrt (-p.2)≤(sigma q+(‖p.1-q.1‖+d))^2
  have hpos : 0 ≤ sigma q := Real.sqrt_nonneg _
  have hmul : 0 ≤ (sigma q+‖p.1-q.1‖)*d := mul_nonneg (add_nonneg hpos (norm_nonneg _)) hd
  nlinarith [mul_nonneg hh (norm_nonneg (p.1-q.1))]
def timeProject (T : ℝ) (p : V × ℝ) : V × ℝ := (p.1,max p.2 (-T))
def extensionWeight [NormedAddCommGroup V] (ψ : ℝ → ℝ) (T : ℝ) (p : V × ℝ) : ℝ :=
  if -T≤p.2 then 1 else ψ ((-p.2-T)/(‖p.1‖^2+Real.sqrt T)^2)
lemma innerExtension_eq [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (ψ : ℝ → ℝ) (T : ℝ) (f : V × ℝ → ℂ) (p : V × ℝ) :
    innerExtension ψ T f p=extensionWeight ψ T p • f (timeProject T p) := by
  by_cases h : -T≤p.2
  · simp [innerExtension,extensionWeight,timeProject,h]
  · simp [innerExtension,extensionWeight,timeProject,h,max_eq_right (not_le.mp h).le]
lemma timeProject_mem [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {T : ℝ} (hT : 0<T) (p : V × ℝ) (hp : p.2<0) :
    -T≤(timeProject T p).2 ∧ (timeProject T p).2<0 :=
  ⟨le_max_right _ _,max_lt hp (by linarith)⟩
lemma timeProject_pdist [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (T : ℝ) (p q : V × ℝ) : pdist (timeProject T p) (timeProject T q)≤pdist p q := by
  dsimp [pdist,timeProject]
  apply add_le_add_right
  exact Real.rpow_le_rpow (abs_nonneg _) (abs_max_sub_max_le_abs _ _ _) (by norm_num)
lemma sigma_project_le [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (T : ℝ) (p : V × ℝ) : sigma (timeProject T p)≤ sigma p := by
  apply Real.sqrt_le_sqrt
  exact add_le_add_right (Real.sqrt_le_sqrt (neg_le_neg (le_max_left _ _))) _
lemma extensionWeight_range [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {ψ : ℝ → ℝ} (hψ : ExtensionCutoff ψ) {T : ℝ} (hT : 0<T) (p : V × ℝ) :
    0≤extensionWeight ψ T p ∧ extensionWeight ψ T p≤1 := by
  by_cases h : -T≤p.2
  · simp [extensionWeight,h]
  · rw [extensionWeight,ite_eq_right h]
    apply hψ.2.1
    apply div_nonneg
    · linarith [not_le.mp h]
    · exact (sq_pos_of_pos (add_pos_of_nonneg_of_pos (sq_nonneg _) (Real.sqrt_pos.mpr hT))).le
lemma sigma_le_project_of_active [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {ψ : ℝ → ℝ} (hψ : ExtensionCutoff ψ) {T : ℝ} (hT : 0<T)
    (p : V × ℝ) (hp : p.2<0) (hactive : extensionWeight ψ T p≠0) :
    sigma p≤2*sigma (timeProject T p) := by
  by_cases h : -T≤p.2
  · have he : timeProject T p=p := by ext <;> simp [timeProject,max_eq_left h]
    rw [he]
    have hs : 0 ≤ sigma p := (sigma_pos p hp).le
    linarith
  have hb : 0<‖p.1‖^2+Real.sqrt T := add_pos_of_nonneg_of_pos (sq_nonneg _) (Real.sqrt_pos.2 hT)
  have harg : (-p.2-T)/(‖p.1‖^2+Real.sqrt T)^2<1 := by
    by_contra hn
    exact hactive (by rw [extensionWeight,ite_eq_right h,hψ.2.2.2 _ (not_lt.mp hn)])
  have hbnd : -p.2-T<(‖p.1‖^2+Real.sqrt T)^2 := by
    simpa only [one_mul] using (div_lt_iff₀ (sq_pos_of_pos hb)).mp harg
  have hTsq := Real.sq_sqrt hT.le
  have hrt : Real.sqrt (-p.2)≤2*(‖p.1‖^2+Real.sqrt T) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    nlinarith [sq_nonneg (‖p.1‖^2),mul_nonneg (sq_nonneg ‖p.1‖) (Real.sqrt_nonneg T)]
  change Real.sqrt (‖p.1‖^2+Real.sqrt (-p.2))≤2*Real.sqrt (‖p.1‖^2+Real.sqrt (-max p.2 (-T)))
  rw [max_eq_right (not_le.mp h).le,neg_neg]
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity,?_⟩
  rw [mul_pow,Real.sq_sqrt hb.le]
  nlinarith [sq_nonneg ‖p.1‖,Real.sqrt_nonneg T]
end FlatWeighted

end

end OAI
