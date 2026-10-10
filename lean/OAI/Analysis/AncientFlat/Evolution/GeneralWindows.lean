import OAI.Analysis.AncientFlat.Geometry.WindowJets
import OAI.Analysis.AncientFlat.Regularity.HolderProducts

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff Laplacian
namespace ParabolicLocalization
open ParabolicInterior
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {E : Type*} [NormedAddCommGroup E]
lemma holder_window_general {α K q : ℝ} (hK : 0≤K) (hq : 0<q) (p0 : V × ℝ)
    {Ω S : Set (V × ℝ)} {f : V × ℝ → E}
    (hf : HolderBound α Ω f K) (hm : MapsTo (window p0 q) S Ω) :
    HolderBound α S (fun p => f (window p0 q p)) ((1+q^α)*K) := by
  have hqα : 0≤q^α := Real.rpow_nonneg hq.le _
  refine ⟨fun p hp => (hf.1 _ (hm hp)).trans (by nlinarith),?_⟩
  intro p hp z hz
  have hh := hf.2 _ (hm hp) _ (hm hz)
  rw [pdist_window p0 hq.le,Real.mul_rpow hq.le (pdist_nonneg p z)] at hh
  nlinarith [mul_nonneg hK (Real.rpow_nonneg (pdist_nonneg p z) α)]
lemma power_le_one_add_four {q : ℝ} (hq : 0≤q) (n : ℕ) (hn : n≤4) : q^n≤1+q^4 := by
  by_cases hq1 : q≤1
  · exact (pow_le_one₀ hq hq1).trans (le_add_of_nonneg_right (pow_nonneg hq 4))
  · exact (pow_le_pow_right₀ (not_le.mp hq1).le hn).trans (by linarith)
lemma window_jet_bound_general {α M q : ℝ} (hM : 0≤M) (hq : 0<q)
    (p0 : V × ℝ) {Ω S : Set (V × ℝ)} (u ut : ℝ → V → ℂ)
    (hs : ∀ t, ContDiff ℝ 4 (u t)) (hj : JetBound α Ω u ut M)
    (hm : MapsTo (window p0 q) S Ω) :
    JetBound α S (windowValue p0 q u) (windowTime p0 q ut) ((1+q^4)*(1+q^α)*M) := by
  have H {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      (n : ℕ) (hn : n≤4) (f : V × ℝ → E) (hf : HolderBound α Ω f M) :
      HolderBound α S (fun p => q^n • f (window p0 q p)) ((1+q^4)*(1+q^α)*M) := by
    apply ((holder_window_general hM hq p0 hf hm).const_smul (q^n)).mono
    rw [abs_of_nonneg (pow_nonneg hq.le _)]
    nlinarith [mul_le_mul_of_nonneg_right (power_le_one_add_four hq.le n hn)
      (show 0≤(1+q^α)*M by positivity)]
  constructor
  · intro n hn
    have heq : (fun p : V × ℝ => iteratedFDeriv ℝ n (windowValue p0 q u p.2) p.1)=
        (fun p => q^n • iteratedFDeriv ℝ n (u (window p0 q p).2) (window p0 q p).1) :=
      funext (window_jet p0 q u hs n hn)
    rw [heq]
    exact H n hn _ (hj.1 n hn)
  · exact H 4 le_rfl _ hj.2
end ParabolicLocalization
namespace ParabolicInterior
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
lemma JetBound.const_smul {α M : ℝ} {Ω : Set (V × ℝ)} {u ut : ℝ → V → ℂ}
    (h : JetBound α Ω u ut M) (hs : ∀ t, ContDiff ℝ 4 (u t)) (c : ℝ) :
    JetBound α Ω (fun t x => c • u t x) (fun t x => c • ut t x) (|c| * M) := by
  constructor
  · intro n hn
    have he : (fun p : V × ℝ => iteratedFDeriv ℝ n (fun x => c • u p.2 x) p.1)=
        (fun p => c • iteratedFDeriv ℝ n (u p.2) p.1) := by
      funext p
      exact iteratedFDeriv_const_smul_apply' ((hs p.2).of_le (by exact_mod_cast hn)).contDiffAt
    rw [he]
    exact (h.1 n hn).const_smul c
  · exact h.2.const_smul c
end ParabolicInterior

end

end OAI
