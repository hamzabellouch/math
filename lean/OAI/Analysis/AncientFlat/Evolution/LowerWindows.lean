import OAI.Analysis.AncientFlat.Regularity.LowerOrderHolder
import OAI.Analysis.AncientFlat.Geometry.WindowJets
import OAI.Analysis.AncientFlat.Geometry.WindowGeometry

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff Laplacian
namespace ParabolicLowerOrder
open ParabolicInterior ParabolicLocalization
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
def windowCoeff (p0 : V × ℝ) (q : ℝ) (c : Coefficients V) : Coefficients V :=
  fun j p => q^(3-j.val) • c j (window p0 q p)
omit [FiniteDimensional ℝ V] in
lemma lower_window (p0 : V × ℝ) (q : ℝ) (c : Coefficients V) (u : ℝ → V → ℂ)
    (hs : ∀ t, ContDiff ℝ 4 (u t)) (p : V × ℝ) :
    spatialLower (windowCoeff p0 q c) (windowValue p0 q u) p=q^4 • spatialLower c u (window p0 q p) := by
  unfold spatialLower
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [window_jet p0 q u hs (j.val+1) (by omega)]
  simp only [windowCoeff,smul_apply,map_smul,smul_smul,←pow_add]
  congr 2
  omega
lemma lower_window_equation (p0 : V × ℝ) (q : ℝ) (a : V × ℝ → ℝ) (b : V × ℝ → ℂ)
    (c : Coefficients V) (u ut f : ℝ → V → ℂ) (hs : ∀ t, ContDiff ℝ 4 (u t)) (p : V × ℝ)
    (he : ut (window p0 q p).2 (window p0 q p).1+(a (window p0 q p):ℂ)*Δ (Δ (u (window p0 q p).2)) (window p0 q p).1+
      b (window p0 q p)*u (window p0 q p).2 (window p0 q p).1+spatialLower c u (window p0 q p)=f (window p0 q p).2 (window p0 q p).1) :
    windowTime p0 q ut p.2 p.1+(a (window p0 q p):ℂ)*Δ (Δ (windowValue p0 q u p.2)) p.1+
      (q^4 • b (window p0 q p))*windowValue p0 q u p.2 p.1+
      spatialLower (windowCoeff p0 q c) (windowValue p0 q u) p=windowTime p0 q f p.2 p.1 := by
  have h := window_equation p0 q a b u ut (fun t x => f t x-spatialLower c u (x,t)) hs p (by linear_combination he)
  rw [lower_window p0 q c u hs p]
  change _=q^4 • f (window p0 q p).2 (window p0 q p).1
  change _=q^4 • (f (window p0 q p).2 (window p0 q p).1-spatialLower c u (window p0 q p)) at h
  rw [smul_sub] at h
  linear_combination h
omit [FiniteDimensional ℝ V] in
lemma small_lower_window_maps {r R q : ℝ} (hr : 0≤r) (hq : 0<q) (hgap : 8*q≤R-r)
    (p0 : V × ℝ) (hp0 : p0∈cylinder r) :
    MapsTo (window p0 q) (cylinder 8) (cylinder R) := by
  have ht : r^4+(8*q)^4≤R^4 := (pow_add_pow_le hr (by positivity) (by norm_num : (4:ℕ)≠0)).trans
    (pow_le_pow_left₀ (by positivity) (by linarith : r+8*q≤R) 4)
  intro p hp
  refine ⟨?_,?_,?_⟩
  · change ‖p0.1+q • p.1‖<R
    apply (norm_add_le _ _).trans_lt
    rw [norm_smul,Real.norm_of_nonneg hq.le]
    nlinarith [hp0.1,hp.1]
  · change -(R^4)<p0.2+q^4*p.2
    have hp' := hp.2.1
    have hp0' := hp0.2.1
    have hq4 : 0<q^4 := pow_pos hq _
    norm_num at hp'
    nlinarith
  · change p0.2+q^4*p.2≤0
    have hm := mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hq.le 4) hp.2.2
    linarith [hp0.2.2]
end ParabolicLowerOrder

end

end OAI
