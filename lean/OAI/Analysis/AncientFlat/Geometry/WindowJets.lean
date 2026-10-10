import OAI.Analysis.AncientFlat.Geometry.ParabolicWindows

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff Laplacian
namespace ParabolicLocalization
open ParabolicInterior
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma holder_window_smul {α K q : ℝ} (hα : 0≤α) (hK : 0≤K) (hq : 0<q) (hq1 : q≤1)
    (p0 : V × ℝ) (n : ℕ) {Ω S : Set (V × ℝ)} {f : V × ℝ → E}
    (hf : HolderBound α Ω f K) (hm : MapsTo (window p0 q) S Ω) :
    HolderBound α S (fun p => q^n • f (window p0 q p)) K := by
  apply ((holder_window hα hq hq1 p0 hf hm).const_smul (q^n)).mono
  rw [abs_of_nonneg (pow_nonneg hq.le n)]
  exact (mul_le_mul_of_nonneg_right (pow_le_one₀ hq.le hq1) hK).trans_eq (one_mul K)
lemma window_jet_bound {α M q : ℝ} (hα : 0≤α) (hM : 0≤M) (hq : 0<q) (hq1 : q≤1)
    (p0 : V × ℝ) {Ω S : Set (V × ℝ)} (u ut : ℝ → V → ℂ)
    (hs : ∀ t, ContDiff ℝ 4 (u t)) (hj : JetBound α Ω u ut M)
    (hm : MapsTo (window p0 q) S Ω) :
    JetBound α S (windowValue p0 q u) (windowTime p0 q ut) M := by
  constructor
  · intro n hn
    have heq : (fun p : V × ℝ => iteratedFDeriv ℝ n (windowValue p0 q u p.2) p.1)=
        (fun p => q^n • iteratedFDeriv ℝ n (u (window p0 q p).2) (window p0 q p).1) :=
      funext (window_jet p0 q u hs n hn)
    rw [heq]
    exact holder_window_smul hα hM hq hq1 p0 n (hj.1 n hn) hm
  · exact holder_window_smul hα hM hq hq1 p0 4 hj.2 hm
lemma window_top_seminorm {α H q : ℝ} (hq : 0<q) (p0 : V × ℝ)
    {Ω S : Set (V × ℝ)} (u : ℝ → V → ℂ) (hs : ∀ t, ContDiff ℝ 4 (u t))
    (hh : ∀ p∈Ω, ∀ z∈Ω,
      ‖iteratedFDeriv ℝ 4 (u p.2) p.1-iteratedFDeriv ℝ 4 (u z.2) z.1‖≤H*pdist p z^α)
    (hm : MapsTo (window p0 q) S Ω) :
    ∀ p∈S, ∀ z∈S,
      ‖iteratedFDeriv ℝ 4 (windowValue p0 q u p.2) p.1-
        iteratedFDeriv ℝ 4 (windowValue p0 q u z.2) z.1‖≤(q^4*q^α*H)*pdist p z^α := by
  intro p hp z hz
  rw [window_jet p0 q u hs 4 le_rfl,window_jet p0 q u hs 4 le_rfl,←smul_sub,
    norm_smul,Real.norm_of_nonneg (pow_nonneg hq.le 4)]
  have hh := hh _ (hm hp) _ (hm hz)
  rw [pdist_window p0 hq.le,Real.mul_rpow hq.le (pdist_nonneg p z)] at hh
  exact (mul_le_mul_of_nonneg_left hh (pow_nonneg hq.le 4)).trans_eq (by ring)
end ParabolicLocalization

end

end OAI
