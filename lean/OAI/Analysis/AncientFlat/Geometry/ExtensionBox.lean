import OAI.Analysis.AncientFlat.Geometry.ExtensionGeometry

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff
namespace FlatWeighted
open ParabolicInterior ParabolicLocalization
variable {V : Type} [NormedAddCommGroup V]
lemma pdist_triangle [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (p q r : V × ℝ) : pdist p r≤pdist p q+pdist q r := by
  have hx : ‖p.1-r.1‖≤‖p.1-q.1‖+‖q.1-r.1‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
  have ht : |p.2-r.2|≤|p.2-q.2|+|q.2-r.2| := abs_sub_le _ _ _
  have hh := (Real.rpow_le_rpow (abs_nonneg _) ht (by norm_num : (0:ℝ)≤1/4)).trans
    (Real.rpow_add_le_add_rpow (abs_nonneg _) (abs_nonneg _) (by norm_num) (by norm_num))
  dsimp [pdist]
  linarith
variable [InnerProductSpace ℝ V]
lemma chart_pdist [FiniteDimensional ℝ V] (p q r : V × ℝ) :
    pdist (chart p q) (chart p r)=sigma p*pdist q r :=
  pdist_window p (Real.sqrt_nonneg _) q r
lemma localDomain_pdist [FiniteDimensional ℝ V] {a : ℝ} (ha : 0<a)
    (p q : V × ℝ) (hq : q∈localDomain a p) :
    pdist (0:V × ℝ) q<2*a := by
  have habs : |q.2|<a^4 := abs_lt.mpr ⟨hq.2.1,hq.2.2.1⟩
  have ht : |q.2|^((1:ℝ)/4)<a := by
    have hh := Real.rpow_lt_rpow (abs_nonneg _) habs (by norm_num : (0:ℝ)<1/4)
    rw [←Real.rpow_natCast,←Real.rpow_mul ha.le] at hh
    norm_num at hh
    exact hh
  simpa only [pdist,Prod.fst_zero,Prod.snd_zero,zero_sub,norm_neg,abs_neg, ←two_mul] using
    (add_lt_add hq.1 ht)
def normBox (a : ℝ) (p : V × ℝ) : Set (V × ℝ) := chart p '' localDomain a p
lemma normBox_time [FiniteDimensional ℝ V] {a : ℝ} {p q : V × ℝ}
    (hq : q∈normBox a p) : q.2<0 := by
  obtain ⟨r,hr,rfl⟩ := hq
  exact hr.2.2.2
variable [FiniteDimensional ℝ V]
lemma normBox_dist {a : ℝ} (ha : 0<a) {p q : V × ℝ} (hs : sigma p=1) (hq : q∈normBox a p) :
    pdist p q<2*a := by
  obtain ⟨r,hr,rfl⟩ := hq
  have h := chart_pdist p 0 r
  rw [chart_zero,hs,one_mul] at h
  rw [h]
  exact localDomain_pdist ha p r hr
lemma normBox_diam {a : ℝ} (ha : 0<a) {p q r : V × ℝ} (hs : sigma p=1)
    (hq : q∈normBox a p) (hr : r∈normBox a p) : pdist q r<4*a := by
  have hq' := normBox_dist ha hs hq
  have hr' := normBox_dist ha hs hr
  have hh := pdist_triangle q p r
  rw [pdist_symm q p] at hh
  linarith
lemma normBox_sigma {a : ℝ} (ha : 0<a) (ha1 : a≤1/16) {p q : V × ℝ}
    (hp : p.2<0) (hs : sigma p=1) (hq : q∈normBox a p) :
    (7:ℝ)/8≤ sigma q ∧ sigma q≤9/8 := by
  have hq0 := normBox_time hq
  have hd := normBox_dist ha hs hq
  have h1 := sigma_le_add_pdist p q hp hq0
  have h2 := sigma_le_add_pdist q p hq0 hp
  rw [pdist_symm q p] at h2
  rw [hs] at h1 h2
  constructor <;> linarith
lemma normBox_bounds {a : ℝ} (ha : 0<a) (ha1 : a≤1/16) {p q : V × ℝ}
    (hp : p.2<0) (hs : sigma p=1) (hq : q∈normBox a p) :
    ‖q.1‖≤2 ∧ -2≤q.2 ∧ q.2<0 := by
  have hq0 := normBox_time hq
  have hsig := normBox_sigma ha ha1 hp hs hq
  have hsq := sigma_sq q
  have ht := Real.sq_sqrt (neg_pos.mpr hq0).le
  have hroot : Real.sqrt (-q.2)≤(81:ℝ)/64 := by
    nlinarith [sq_nonneg ‖q.1‖,Real.sqrt_nonneg (-q.2)]
  refine ⟨(norm_le_sigma q).trans (by linarith),?_,hq0⟩
  nlinarith [Real.sqrt_nonneg (-q.2)]
lemma normBox_project_sigma {ψ : ℝ → ℝ} (hψ : ExtensionCutoff ψ) {T a : ℝ}
    (hT : 0<T) (ha : 0<a) (ha1 : a≤1/16) {p : V × ℝ} (hp : p.2<0) (hs : sigma p=1)
    (hactive : ∃ q∈normBox a p, extensionWeight ψ T q≠0) :
    ∀ q∈normBox a p, (1:ℝ)/8≤ sigma (timeProject T q) := by
  obtain ⟨r,hr,hr0⟩ := hactive
  have hsr := (normBox_sigma ha ha1 hp hs hr).1
  have hsr' := sigma_le_project_of_active hψ hT r (normBox_time hr) hr0
  intro q hq
  have hd := normBox_diam ha hs hr hq
  have hpdt := timeProject_pdist T r q
  have hsig := sigma_le_add_pdist (timeProject T r) (timeProject T q)
    (timeProject_mem hT r (normBox_time hr)).2 (timeProject_mem hT q (normBox_time hq)).2
  linarith
end FlatWeighted

end

end OAI
